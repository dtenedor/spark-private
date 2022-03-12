/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.spark.sql.catalyst.analysis

import org.apache.spark.sql.AnalysisException
import org.apache.spark.sql.catalyst.InternalRow
import org.apache.spark.sql.catalyst.catalog._
import org.apache.spark.sql.catalyst.expressions.{Expression, _}
import org.apache.spark.sql.catalyst.optimizer.ConstantFolding
import org.apache.spark.sql.catalyst.parser.{CatalystSqlParser, ParseException}
import org.apache.spark.sql.catalyst.plans.logical._
import org.apache.spark.sql.connector.catalog._
import org.apache.spark.sql.types._

/**
 * This class contains logic for processing DEFAULT columns in statements such as CREATE TABLE.
 */
case class DefaultColumns(catalogManager: CatalogManager) {
  val default = "default"
  val errorPrefix = "Failed to execute INSERT command because the destination table column "
  val analysisPrefix = " has a DEFAULT value which fails to analyze: "
  lazy val parser = new CatalystSqlParser()
  lazy val analyzer =
    new Analyzer(new SessionCatalog(new InMemoryCatalog, FunctionRegistry.builtin))

  /**
   * Finds DEFAULT expressions in CREATE/REPLACE TABLE commands and constant-folds then.
   *
   * Example:
   * CREATE TABLE T(a INT, b INT DEFAULT 5 + 5) becomes
   * CREATE TABLE T(a INT, b INT DEFAULT 10
   */
  def ConstantFoldDefaultExpressions(c: CreateTable): CreateTable = {
    // Get the list of column indexes in the CREATE TABLE command with DEFAULT values.
    val (fields: Array[StructField], indexes: Array[Int]) =
      c.tableSchema.fields.zipWithIndex.filter { case (f, i) => f.metadata.contains(default) }.unzip
    // Extract the list of DEFAULT column values from the CreateTable command.
    val colNames: Seq[String] = fields.map { _.name }
    val defaults: Seq[String] = fields.map { _.metadata.getString(default) }
    // Extract the list of DEFAULT column values from the CreateTable command.
    val exprs: Seq[Expression] = colNames.zip(defaults).map {
      case (name, text) => Parse(name, text)
    }
    // Analyze and constant-fold each parse result.
    val analyzed: Seq[Expression] = (exprs, defaults, colNames).zipped.map {
      case (expr, default, name) => Analyze(expr, default, name)
    }
    // Finally, replace the original struct fields with the new ones.
    val indexMap: Map[Int, StructField] = (indexes, fields, analyzed).zipped.map {
      case (index, field, expr) =>
        val newMetadata: Metadata = new MetadataBuilder().withMetadata(field.metadata)
          .putString(default, expr.sql).build()
        (index, field.copy(metadata = newMetadata))
    }.toMap
    val newFields: Seq[StructField] = c.tableSchema.fields.zipWithIndex.map {
      case (f, i) => indexMap.getOrElse(i, f)
    }
    c.copy(tableSchema = StructType(newFields))
  }

  /**
   * Parses 'colText' into an expression, returning a reasonable error message upon failure.
   */
  private def Parse(colName: String, colText: String): Expression = {
    try {
      parser.parseExpression(colText)
    } catch {
      case ex: ParseException =>
        throw new AnalysisException(
          errorPrefix + colName + analysisPrefix + s"$colText yields ${ex.getMessage}")
    }
  }

  /**
   * Analyzes 'colExpr', returning a reasonable error message upon failure.
   */
  private def Analyze(colExpr: Expression, colText: String, colName: String): Expression = {
    try {
      // Invoke the analyzer over the 'colExpr'.
      val plan = analyzer.execute(Project(Seq(Alias(colExpr, colName)()), OneRowRelation()))
      analyzer.checkAnalysis(plan)
      // Perform constant folding over the result.
      val folded = ConstantFolding(plan)
      val result = folded match {
        case Project(Seq(a: Alias), OneRowRelation()) => a.child
      }
      // Make sure the constant folding was successful.
      result match {
        case _: Literal => result
        case _ => throw new AnalysisException("non-constant value")
      }
    } catch {
      case ex: AnalysisException =>
        throw new AnalysisException(
          errorPrefix + colName + analysisPrefix + s"$colText yields ${ex.getMessage}")
    }
  }

  /**
   * Replaces unresolved "DEFAULT" column references with matching default column values.
   *
   * Background: CREATE TABLE and ALTER TABLE invocations support setting column default values for
   * later operations. Following INSERT, and INSERT MERGE commands may then reference the value
   * using the DEFAULT keyword as needed.
   *
   * Example:
   * CREATE TABLE T(a INT, b INT NOT NULL DEFAULT 5);
   * INSERT INTO T VALUES (1, 2, DEFAULT);
   * SELECT * FROM T;
   * (NULL, 0, 5)
   * (NULL, 1, 5)
   * (1, 2, 5)
   */
  def ResolveDefaultColumnReferences(i: InsertIntoStatement): InsertIntoStatement = {
    ReplaceExplicitDefaultColumnValues(AddProjectionForMissingDefaultColumnValues(i))
  }

  /**
   * Adds a projection over the logical plan in 'insert.query' generating default column values.
   */
  private def AddProjectionForMissingDefaultColumnValues(
      insert: InsertIntoStatement): InsertIntoStatement = {
    val colIndexes = insert.query.output.size until insert.table.output.size
    if (colIndexes.isEmpty) {
      // Fast path: if there are no missing default columns, there is nothing to do.
      return insert
    }
    val columns = colIndexes.map(insert.table.schema.fields(_))
    val colNames: Seq[String] = columns.map(_.name)
    val colTypes: Seq[DataType] = columns.map(_.dataType)
    val colTexts: Seq[String] = columns.map(_.metadata.getString(default))
    // Parse the DEFAULT column expression. If the parsing fails, throw an error to the user.
    val colExprs: Seq[Expression] = colNames.zip(colTexts).map {
      case (name, text) => Parse(name, text)
    }
    // Analyze and constant-fold each result.
    val analyzed = (colExprs, colTexts, colNames).zipped.map {
      case (expr, text, name) => Analyze(expr, text, name)
    }
    // Perform implicit coercion from the provided expression type to the required column type.
    val colExprsCoerced: Seq[Expression] = (analyzed, colTypes, colNames).zipped.map {
      case (expr, datatype, _)
        if datatype != expr.dataType && Cast.canUpCast(expr.dataType, datatype) =>
        Cast(expr, datatype)
      case (expr, dataType, colName)
        if dataType != expr.dataType =>
        throw new AnalysisException(
          errorPrefix + s"$colName has a DEFAULT value with type $dataType, but the query " +
            s"provided a value of incompatible type ${expr.dataType}")
      case (expr, _, _) => expr
    }
    // Finally, return a projection of the original 'insert.query' output attributes plus new
    // aliases over the DEFAULT column values.
    // If the insertQuery is an existing Project, flatten them together.
    val newAliases: Seq[NamedExpression] = {
      colExprsCoerced.zip(colNames).map { case (expr, name) => Alias(expr, name)() }
    }
    val newQuery = insert.query match {
      case Project(projectList, child) => Project(projectList ++ newAliases, child)
      case _ => Project(insert.query.output ++ newAliases, insert.query)
    }
    insert.copy(query = newQuery)
  }

  /**
   * Replaces unresolved "DEFAULT" attribute references in [[insert]] with corresponding values.
   */
  private def ReplaceExplicitDefaultColumnValues(
      insert: InsertIntoStatement): InsertIntoStatement = {
    // Extract the list of DEFAULT column values from the INSERT INTO statement.
    val defaults: Seq[Option[Expression]] = insert.table.schema.fields.map {
      case f if f.metadata.contains(default) =>
        Some(parser.parseExpression(f.metadata.getString(default)))
      case _ => None
    }
    if (defaults.isEmpty) {
      // Fast path: if there are no explicit default columns, there is nothing to do.
      return insert
    }
    // Handle two types of logical query plans in the target of the INSERT INTO statement:
    // Inline table: VALUES (0, 1, DEFAULT, ...)
    // Projection: SELECT 0, 1, DEFAULT, ...
    val newQuery: LogicalPlan = insert.query match {
      case table: LocalRelation =>
        val data: Seq[InternalRow] = table.data.map { data =>
          val rowCopy = data.copy()
          (defaults, data.toSeq(table.schema), 0 until defaults.size).zipped.map {
            case (defaultExpr: Option[Expression], value: Any, index: Int) =>
              value match {
                case u: UnresolvedAttribute
                  if u.name.equalsIgnoreCase(default) && defaultExpr.isDefined =>
                  rowCopy.update(index, defaultExpr.get.eval())
                case _ => ()
              }
          }
          rowCopy
        }
        table.copy(data = data)
      case project: Project =>
        val updated: Seq[NamedExpression] = project.projectList.map {
          expr => expr match {
            case u: UnresolvedAttribute if u.name.equalsIgnoreCase(default) => expr
            case _ => expr
          }
        }
        project.copy(projectList = updated)
      case _ => insert.query
    }
    insert.copy(query = newQuery)
  }
}
