using GradeBookApp;
using Xunit;

namespace GradeBookApp.Tests;

/// <summary>
/// Tests for StudentRecord — computed properties (Moyenne, Sujets).
/// </summary>
public class StudentRecordTests
{
    // --- Moyenne ---

    [Fact]
    public void Moyenne_EmptyNotes_ReturnsZero()
    {
        var s = new StudentRecord();
        Assert.Equal(0m, s.Moyenne);
    }

    [Fact]
    public void Moyenne_SingleNote()
    {
        var s = new StudentRecord { Notes = new List<decimal> { 14m } };
        Assert.Equal(14m, s.Moyenne);
    }

    [Fact]
    public void Moyenne_MultipleNotes()
    {
        var s = new StudentRecord { Notes = new List<decimal> { 10m, 14m, 18m } };
        Assert.Equal(14m, s.Moyenne);
    }

    [Fact]
    public void Moyenne_Precision()
    {
        var s = new StudentRecord { Notes = new List<decimal> { 10m, 11m } };
        Assert.Equal(10.5m, s.Moyenne);
    }

    // --- Sujets ---

    [Fact]
    public void Sujets_BothNull_ReturnsEmpty()
    {
        var s = new StudentRecord();
        Assert.Empty(s.Sujets);
    }

    [Fact]
    public void Sujets_OneSujet()
    {
        var s = new StudentRecord { SujetProjet1 = "TSP" };
        Assert.Single(s.Sujets);
        Assert.Contains("TSP", s.Sujets);
    }

    [Fact]
    public void Sujets_TwoSujets()
    {
        var s = new StudentRecord { SujetProjet1 = "TSP", SujetProjet2 = "VRP" };
        Assert.Equal(2, s.Sujets.Count);
    }

    [Fact]
    public void Sujets_SecondOnly()
    {
        var s = new StudentRecord { SujetProjet2 = "VRP" };
        Assert.Single(s.Sujets);
        Assert.Contains("VRP", s.Sujets);
    }

    // --- Compatibility properties ---

    [Fact]
    public void FirstName_MapsToPrenom()
    {
        var s = new StudentRecord { Prénom = "Jean" };
        Assert.Equal("Jean", s.FirstName);
    }

    [Fact]
    public void LastName_MapsToNom()
    {
        var s = new StudentRecord { Nom = "Dupont" };
        Assert.Equal("Dupont", s.LastName);
    }

    [Fact]
    public void UID_MapsToEmail()
    {
        var s = new StudentRecord { Email = "jean@epita.fr" };
        Assert.Equal("jean@epita.fr", s.UID);
    }

    [Fact]
    public void Course_IsPrCon()
    {
        var s = new StudentRecord();
        Assert.Equal("PrCon", s.Course);
    }
}
