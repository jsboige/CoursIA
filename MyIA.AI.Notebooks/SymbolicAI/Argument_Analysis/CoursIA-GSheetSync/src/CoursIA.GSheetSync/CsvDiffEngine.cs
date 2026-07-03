// Verbatim port from Argumentum.AssetConverter (LGPL-3.0 / AGPL-3.0 dual).
// Source: Argumentum/Generation/Converters/Argumentum.AssetConverter/GSheetSync/CsvDiffEngine.cs
// Original commit: ac33f607a4889d8a982093c413804ed25bef3dc0 (Argumentum master pre-tag v0.9.0)
// Upstream author: Argumentum Games <contact@argumentum.games>, Jean-Sylvain Boige <jsboige@gmail.com>
// License: GNU Lesser General Public License v3.0 (LGPL-3.0). See ../NOTICE for full attribution.
//
// Modifications from upstream (LGPL-3.0 NOTICE per section 5):
//   - Namespace: Argumentum.AssetConverter.GSheetSync
//            ->  CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.GSheetSync
//   - Target framework: net9.0-windows -> net9.0 (cross-platform; CsvHelper is OS-agnostic)
//   - Behaviour, public API, and assertions: UNCHANGED.
//
// See ../NOTICE for the full modification log, license text reference,
// and wiring plan (EPIC #4960 volet A, tranche A).

using System;
using System.Collections.Generic;
using System.Data;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text;
using CsvHelper;
using CsvHelper.Configuration;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.GSheetSync
{
	public class CellChange
	{
		public string PrimaryKey { get; set; } = "";
		public string ColumnName { get; set; } = "";
		public string OldValue { get; set; } = "";
		public string NewValue { get; set; } = "";
	}

	public class DiffResult
	{
		public int TotalRowsOld { get; set; }
		public int TotalRowsNew { get; set; }
		public int RowsAdded { get; set; }
		public int RowsDeleted { get; set; }
		public int RowsModified { get; set; }
		public int RowsUnchanged { get; set; }
		public int TotalCellsOld { get; set; }
		public int TotalCellsNew { get; set; }
		public int CellsModified { get; set; }
		public List<string> ColumnsAdded { get; set; } = new List<string>();
		public List<string> ColumnsRemoved { get; set; } = new List<string>();
		public List<CellChange> SampleOverwrites { get; set; } = new List<CellChange>();

		public bool HasColumnStructureChange => ColumnsAdded.Count > 0 || ColumnsRemoved.Count > 0;
		public double DeletionPercentage => TotalRowsOld > 0 ? (double)RowsDeleted / TotalRowsOld * 100 : 0;
		public double ModificationPercentage => TotalCellsOld > 0 ? (double)CellsModified / TotalCellsOld * 100 : 0;
	}

	public class CsvDiffEngine
	{
		private readonly string _primaryKeyColumn;
		private readonly int _maxOverwriteExamples;
		private readonly char _delimiter;

		public CsvDiffEngine(string primaryKeyColumn, int maxOverwriteExamples = 5, char delimiter = ',')
		{
			_primaryKeyColumn = primaryKeyColumn;
			_maxOverwriteExamples = maxOverwriteExamples;
			_delimiter = delimiter;
		}

		public DiffResult Compare(string oldCsv, string newCsv)
		{
			var oldTable = ParseCsv(oldCsv);
			var newTable = ParseCsv(newCsv);

			var result = new DiffResult();

			// Column structure comparison
			var oldColumns = oldTable.Columns.Cast<DataColumn>().Select(c => c.ColumnName).ToHashSet();
			var newColumns = newTable.Columns.Cast<DataColumn>().Select(c => c.ColumnName).ToHashSet();

			result.ColumnsRemoved = oldColumns.Except(newColumns).OrderBy(c => c).ToList();
			result.ColumnsAdded = newColumns.Except(oldColumns).OrderBy(c => c).ToList();

			// Common columns for cell-level comparison
			var commonColumns = oldColumns.Intersect(newColumns).OrderBy(c => c).ToList();

			// Index rows by primary key
			var oldRows = IndexRows(oldTable, _primaryKeyColumn);
			var newRows = IndexRows(newTable, _primaryKeyColumn);

			result.TotalRowsOld = oldRows.Count;
			result.TotalRowsNew = newRows.Count;

			var sampleOverwrites = new List<CellChange>();

			// Check old rows: deleted or modified
			foreach (var (pk, oldRow) in oldRows)
			{
				if (!newRows.ContainsKey(pk))
				{
					result.RowsDeleted++;
					result.TotalCellsOld += commonColumns.Count;
				}
				else
				{
					var newRow = newRows[pk];
					bool modified = false;

					foreach (var col in commonColumns)
					{
						result.TotalCellsOld++;
						result.TotalCellsNew++;

						var oldVal = NormalizeValue(oldRow[col]?.ToString() ?? "");
						var newVal = NormalizeValue(newRow[col]?.ToString() ?? "");

						if (oldVal != newVal)
						{
							result.CellsModified++;
							modified = true;

							if (sampleOverwrites.Count < _maxOverwriteExamples)
							{
								sampleOverwrites.Add(new CellChange
								{
									PrimaryKey = pk,
									ColumnName = col,
									OldValue = Truncate(oldVal, 80),
									NewValue = Truncate(newVal, 80)
								});
							}
						}
					}

					if (modified)
						result.RowsModified++;
					else
						result.RowsUnchanged++;
				}
			}

			// Check new rows: added
			foreach (var (pk, _) in newRows)
			{
				if (!oldRows.ContainsKey(pk))
				{
					result.RowsAdded++;
					result.TotalCellsNew += commonColumns.Count;
				}
			}

			result.SampleOverwrites = sampleOverwrites;
			return result;
		}

		private DataTable ParseCsv(string csvContent)
		{
			var dataTable = new DataTable();

			using var reader = new StringReader(csvContent);
			using var csv = new CsvReader(reader, new CsvConfiguration(CultureInfo.InvariantCulture)
			{
				Delimiter = _delimiter.ToString(),
				HasHeaderRecord = true,
				MissingFieldFound = null,
				BadDataFound = null,
				TrimOptions = TrimOptions.None,
			});

			// Read header
			csv.Read();
			csv.ReadHeader();
			var headers = csv.HeaderRecord;

			if (headers == null)
				return dataTable;

			foreach (var header in headers)
			{
				dataTable.Columns.Add(header);
			}

			// Read rows
			while (csv.Read())
			{
				var row = dataTable.NewRow();
				foreach (var header in headers)
				{
					row[header] = csv.GetField(header) ?? "";
				}
				dataTable.Rows.Add(row);
			}

			return dataTable;
		}

		private Dictionary<string, DataRow> IndexRows(DataTable table, string primaryKeyColumn)
		{
			var index = new Dictionary<string, DataRow>(StringComparer.OrdinalIgnoreCase);

			if (!table.Columns.Contains(primaryKeyColumn))
			{
				// Fallback: index by row position
				for (int i = 0; i < table.Rows.Count; i++)
				{
					index[$"__ROW_{i}__"] = table.Rows[i];
				}
				return index;
			}

			var duplicates = new List<string>();
			var empties = 0;

			foreach (DataRow row in table.Rows)
			{
				var key = row[primaryKeyColumn]?.ToString()?.Trim() ?? "";
				if (string.IsNullOrEmpty(key))
				{
					empties++;
					continue;
				}

				if (index.ContainsKey(key))
				{
					duplicates.Add(key);
					continue;
				}

				index[key] = row;
			}

			if (duplicates.Count > 0)
			{
				Console.ForegroundColor = ConsoleColor.Yellow;
				Console.WriteLine(
					$"  [warn] {duplicates.Count} duplicate PK value(s) in column '{primaryKeyColumn}': " +
					$"{string.Join(", ", duplicates.Take(5))}" +
					(duplicates.Count > 5 ? $" ... (+{duplicates.Count - 5} more)" : "") +
					" — only first occurrence kept for diff.");
				Console.ResetColor();
			}

			if (empties > 0)
			{
				Console.ForegroundColor = ConsoleColor.Yellow;
				Console.WriteLine(
					$"  [warn] {empties} row(s) with empty PK in column '{primaryKeyColumn}' — excluded from diff.");
				Console.ResetColor();
			}

			return index;
		}

		private static string NormalizeValue(string value)
		{
			if (string.IsNullOrEmpty(value)) return "";
			return value.Replace("\r\n", "\n").Replace("\r", "\n").Trim();
		}

		private static string Truncate(string value, int maxLength)
		{
			if (value.Length <= maxLength) return value;
			return value.Substring(0, maxLength - 3) + "...";
		}
	}
}
