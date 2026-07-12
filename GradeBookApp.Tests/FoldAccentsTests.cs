using GradeBookApp;
using Xunit;

namespace GradeBookApp.Tests;

/// <summary>
/// Tests for Program.FoldAccents — Lucene-based accent folding via StandardAnalyzer + ASCIIFoldingFilter.
/// Note: StandardAnalyzer tokenizes, lowercases, and removes spaces/punctuation. ASCIIFoldingFilter removes accents.
/// </summary>
public class FoldAccentsTests
{
    private static readonly Func<string, string> _foldAccents;

    static FoldAccentsTests()
    {
        var method = typeof(Program).GetMethod("FoldAccents",
            System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Static);
        Assert.NotNull(method);
        _foldAccents = (Func<string, string>)Delegate.CreateDelegate(typeof(Func<string, string>), method);
    }

    [Fact]
    public void PlainAscii_LowercasedAndSpacesRemoved()
    {
        // StandardAnalyzer lowercases and concatenates tokens
        Assert.Equal("helloworld", _foldAccents("hello world"));
    }

    [Fact]
    public void FrenchAccents_RemovedAndLowered()
    {
        Assert.Equal("aeiou", _foldAccents("aéiôù"));
    }

    [Fact]
    public void Cedilla_Removed()
    {
        Assert.Equal("francais", _foldAccents("français"));
    }

    [Fact]
    public void AccentedCapitals_RemovedAndLowered()
    {
        // StandardAnalyzer lowercases; accents removed by ASCIIFoldingFilter
        Assert.Equal("aeiou", _foldAccents("ÀÉÎÔÙ"));
    }

    [Fact]
    public void EmptyString_ReturnsEmpty()
    {
        Assert.Equal("", _foldAccents(""));
    }

    [Fact]
    public void NullInput_ReturnsNull()
    {
        // IsNullOrWhiteSpace short-circuits: returns input unchanged
        Assert.Null(_foldAccents(null!));
    }

    [Fact]
    public void MixedAccentsAndAscii_SpacesRemovedLowered()
    {
        Assert.Equal("theophilegautier", _foldAccents("Théophile Gautier"));
    }

    [Fact]
    public void GermanUmlaut_Removed()
    {
        Assert.Equal("munchen", _foldAccents("München"));
    }

    [Fact]
    public void SpanishTilde_Removed()
    {
        Assert.Equal("elnino", _foldAccents("El niño"));
    }

    [Fact]
    public void HyphenRemoved_ApostropheKept()
    {
        // StandardAnalyzer removes hyphens (token boundary) but keeps apostrophes within tokens
        Assert.Equal("test123_o'brien", _foldAccents("test-123_O'brien"));
    }

    [Fact]
    public void MultipleAccentsSameWord()
    {
        Assert.Equal("revelee", _foldAccents("Révélée"));
    }

    [Fact]
    public void AeLigature_Removed()
    {
        Assert.Equal("aether", _foldAccents("Æther"));
    }

    [Fact]
    public void WhitespaceOnly_ReturnsSame()
    {
        // IsNullOrWhiteSpace returns the input unchanged
        Assert.Equal("   ", _foldAccents("   "));
    }

    [Fact]
    public void AccentedSingleChar()
    {
        Assert.Equal("e", _foldAccents("é"));
    }

    [Fact]
    public void AccentedString_UsedForComparison()
    {
        // Real use case: compare names ignoring accents, case, and spaces
        var a = _foldAccents("Théophile Gautier");
        var b = _foldAccents("theophile gautier");
        Assert.Equal(a, b);
    }
}
