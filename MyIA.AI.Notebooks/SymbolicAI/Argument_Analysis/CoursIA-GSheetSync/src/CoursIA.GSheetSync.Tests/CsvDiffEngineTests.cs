// Verbatim port from Argumentum.AssetConverter.Tests (LGPL-3.0 / AGPL-3.0 dual).
// Source: Argumentum/Generation/Converters/Argumentum.AssetConverter.Tests/GSheetSync/CsvDiffEngineTests.cs
// Original commit: ac33f607a4889d8a982093c413804ed25bef3dc0 (Argumentum master pre-tag v0.9.0)
// Upstream author: Argumentum Games <contact@argumentum.games>, Jean-Sylvain Boige <jsboige@gmail.com>
// License: GNU Lesser General Public License v3.0 (LGPL-3.0). See ../NOTICE for full attribution.
//
// Modifications from upstream (LGPL-3.0 NOTICE per section 5):
//   - Namespace: Argumentum.AssetConverter.Tests.GSheetSync
//            ->  CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Tests.GSheetSync
//   - using directive: Argumentum.AssetConverter.GSheetSync
//                  ->  CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.GSheetSync
//   - Target framework: net9.0-windows -> net9.0
//   - Behaviour, test cases, and assertions: UNCHANGED (10 [Fact] tests preserved 1:1).

using CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.GSheetSync;
using FluentAssertions;
using Xunit;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Tests.GSheetSync
{
    public class CsvDiffEngineTests
    {
        private const string HeaderPk = "pk";

        private static string MakeCsv(string[] headers, params string[][] rows)
        {
            var sb = new System.Text.StringBuilder();
            sb.AppendLine(string.Join(",", headers));
            foreach (var row in rows)
            {
                sb.AppendLine(string.Join(",", row));
            }
            return sb.ToString();
        }

        [Fact]
        public void Compare_IdenticalCsv_NoDiff()
        {
            var csv = MakeCsv(
                new[] { HeaderPk, "Name", "Value" },
                new[] { "1", "Foo", "100" },
                new[] { "2", "Bar", "200" }
            );

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(csv, csv);

            result.RowsAdded.Should().Be(0);
            result.RowsDeleted.Should().Be(0);
            result.RowsModified.Should().Be(0);
            result.RowsUnchanged.Should().Be(2);
            result.CellsModified.Should().Be(0);
            result.SampleOverwrites.Should().BeEmpty();
            result.HasColumnStructureChange.Should().BeFalse();
        }

        [Fact]
        public void Compare_AddedRows_Detected()
        {
            var oldCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", "Alpha" }
            );
            var newCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", "Alpha" },
                new[] { "2", "Beta" },
                new[] { "3", "Gamma" }
            );

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(oldCsv, newCsv);

            result.RowsAdded.Should().Be(2);
            result.RowsDeleted.Should().Be(0);
            result.TotalRowsOld.Should().Be(1);
            result.TotalRowsNew.Should().Be(3);
        }

        [Fact]
        public void Compare_DeletedRows_Detected()
        {
            var oldCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", "Alpha" },
                new[] { "2", "Beta" },
                new[] { "3", "Gamma" }
            );
            var newCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", "Alpha" }
            );

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(oldCsv, newCsv);

            result.RowsAdded.Should().Be(0);
            result.RowsDeleted.Should().Be(2);
            result.RowsUnchanged.Should().Be(1);
            result.DeletionPercentage.Should().BeApproximately(66.67, 0.1);
        }

        [Fact]
        public void Compare_ModifiedCells_DetectedWithSamples()
        {
            var oldCsv = MakeCsv(
                new[] { HeaderPk, "Name", "Value" },
                new[] { "1", "Alpha", "100" },
                new[] { "2", "Beta", "200" }
            );
            var newCsv = MakeCsv(
                new[] { HeaderPk, "Name", "Value" },
                new[] { "1", "Alpha-Modified", "100" },
                new[] { "2", "Beta", "250" }
            );

            var engine = new CsvDiffEngine(HeaderPk, maxOverwriteExamples: 5);
            var result = engine.Compare(oldCsv, newCsv);

            result.RowsModified.Should().Be(2);
            result.CellsModified.Should().Be(2);
            result.SampleOverwrites.Should().HaveCount(2);

            result.SampleOverwrites[0].PrimaryKey.Should().Be("1");
            result.SampleOverwrites[0].ColumnName.Should().Be("Name");
            result.SampleOverwrites[0].OldValue.Should().Be("Alpha");
            result.SampleOverwrites[0].NewValue.Should().Be("Alpha-Modified");

            result.SampleOverwrites[1].PrimaryKey.Should().Be("2");
            result.SampleOverwrites[1].ColumnName.Should().Be("Value");
            result.SampleOverwrites[1].OldValue.Should().Be("200");
            result.SampleOverwrites[1].NewValue.Should().Be("250");
        }

        [Fact]
        public void Compare_SampleOverwrites_LimitedByMax()
        {
            var oldCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", "A" },
                new[] { "2", "B" },
                new[] { "3", "C" },
                new[] { "4", "D" }
            );
            var newCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", "A1" },
                new[] { "2", "B1" },
                new[] { "3", "C1" },
                new[] { "4", "D1" }
            );

            var engine = new CsvDiffEngine(HeaderPk, maxOverwriteExamples: 2);
            var result = engine.Compare(oldCsv, newCsv);

            result.CellsModified.Should().Be(4);
            result.SampleOverwrites.Should().HaveCount(2);
        }

        [Fact]
        public void Compare_ColumnsAddedRemoved_Detected()
        {
            var oldCsv = MakeCsv(
                new[] { HeaderPk, "Name", "OldCol" },
                new[] { "1", "Alpha", "x" }
            );
            var newCsv = MakeCsv(
                new[] { HeaderPk, "Name", "NewCol" },
                new[] { "1", "Alpha", "y" }
            );

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(oldCsv, newCsv);

            result.HasColumnStructureChange.Should().BeTrue();
            result.ColumnsRemoved.Should().Contain("OldCol");
            result.ColumnsAdded.Should().Contain("NewCol");
        }

        [Fact]
        public void Compare_MissingPrimaryKey_FallsBackToRowPosition()
        {
            var oldCsv = MakeCsv(
                new[] { "Name", "Value" },
                new[] { "Alpha", "100" },
                new[] { "Beta", "200" }
            );
            var newCsv = MakeCsv(
                new[] { "Name", "Value" },
                new[] { "Alpha-Modified", "100" },
                new[] { "Beta", "250" }
            );

            var engine = new CsvDiffEngine("nonexistent_pk");
            var result = engine.Compare(oldCsv, newCsv);

            // Falls back to row position indexing — rows match by position
            result.RowsModified.Should().Be(2);
            result.CellsModified.Should().Be(2);
        }

        [Fact]
        public void Compare_EmptyCsv_NoDiff()
        {
            var csv = "pk,Name\n";

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(csv, csv);

            result.RowsAdded.Should().Be(0);
            result.RowsDeleted.Should().Be(0);
            result.RowsModified.Should().Be(0);
            result.TotalRowsOld.Should().Be(0);
            result.TotalRowsNew.Should().Be(0);
        }

        [Fact]
        public void Compare_SemicolonDelimiter_Parsed()
        {
            var oldCsv = "pk;Name\n1;Alpha\n";
            var newCsv = "pk;Name\n1;Alpha-Modified\n";

            var engine = new CsvDiffEngine(HeaderPk, delimiter: ';');
            var result = engine.Compare(oldCsv, newCsv);

            result.RowsModified.Should().Be(1);
            result.CellsModified.Should().Be(1);
            result.SampleOverwrites[0].OldValue.Should().Be("Alpha");
            result.SampleOverwrites[0].NewValue.Should().Be("Alpha-Modified");
        }

        [Fact]
        public void Compare_NewlineNormalization_IgnoresCRLFDiff()
        {
            var oldCsv = "pk,Name\n1,\"Alpha\r\nBeta\"\n";
            var newCsv = "pk,Name\n1,\"Alpha\nBeta\"\n";

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(oldCsv, newCsv);

            result.CellsModified.Should().Be(0);
            result.RowsModified.Should().Be(0);
        }

        [Fact]
        public void Compare_ModificationPercentage_Calculated()
        {
            var oldCsv = MakeCsv(
                new[] { HeaderPk, "A", "B" },
                new[] { "1", "x", "y" },
                new[] { "2", "x", "y" }
            );
            var newCsv = MakeCsv(
                new[] { HeaderPk, "A", "B" },
                new[] { "1", "x-modified", "y" },
                new[] { "2", "x", "y" }
            );

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(oldCsv, newCsv);

            // 2 rows * 3 common cols (pk, A, B) = 6 total cells, 1 modified
            result.TotalCellsOld.Should().Be(6);
            result.CellsModified.Should().Be(1);
            result.ModificationPercentage.Should().BeApproximately(16.67, 0.1);
        }

        [Fact]
        public void Compare_LongValue_TruncatedInSample()
        {
            var longValue = new string('A', 200);
            var oldCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", "Short" }
            );
            var newCsv = MakeCsv(
                new[] { HeaderPk, "Name" },
                new[] { "1", longValue }
            );

            var engine = new CsvDiffEngine(HeaderPk);
            var result = engine.Compare(oldCsv, newCsv);

            (result.SampleOverwrites[0].NewValue.Length <= 80).Should().BeTrue("long values should be truncated to max 80 chars");
        }
    }
}