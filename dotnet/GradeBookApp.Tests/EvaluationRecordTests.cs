using GradeBookApp;
using Xunit;

namespace GradeBookApp.Tests;

/// <summary>
/// Tests for EvaluationRecord — computed properties (Note, EvaluatorName, Score).
/// </summary>
public class EvaluationRecordTests
{
    // --- Note (computed grade) ---

    [Fact]
    public void Note_AllFours_Eight()
    {
        // (4+4+4+4)*2 / 4 = 8.0
        var e = new EvaluationRecord
        {
            NoteCommunication = 4,
            NoteTheorique = 4,
            NoteTechnique = 4,
            NoteOrganisation = 4,
            NbEvalFields = 4
        };
        Assert.Equal(8m, e.Note);
    }

    [Fact]
    public void Note_AllOnes_Two()
    {
        // (1+1+1+1)*2 / 4 = 2.0
        var e = new EvaluationRecord
        {
            NoteCommunication = 1,
            NoteTheorique = 1,
            NoteTechnique = 1,
            NoteOrganisation = 1,
            NbEvalFields = 4
        };
        Assert.Equal(2m, e.Note);
    }

    [Fact]
    public void Note_MixedScores()
    {
        // (3+2+4+1)*2 / 4 = 5.0
        var e = new EvaluationRecord
        {
            NoteCommunication = 3,
            NoteTheorique = 2,
            NoteTechnique = 4,
            NoteOrganisation = 1,
            NbEvalFields = 4
        };
        Assert.Equal(5m, e.Note);
    }

    [Fact]
    public void Note_ThreeFields()
    {
        // (3+3+3)*2 / 3 = 6.0
        var e = new EvaluationRecord
        {
            NoteCommunication = 3,
            NoteTheorique = 3,
            NoteTechnique = 3,
            NoteOrganisation = 0,
            NbEvalFields = 3
        };
        Assert.Equal(6m, e.Note);
    }

    [Fact]
    public void Note_MaxScores()
    {
        // (5+5+5+5)*2 / 4 = 10.0
        var e = new EvaluationRecord
        {
            NoteCommunication = 5,
            NoteTheorique = 5,
            NoteTechnique = 5,
            NoteOrganisation = 5,
            NbEvalFields = 4
        };
        Assert.Equal(10m, e.Note);
    }

    [Fact]
    public void Note_ZeroFields_ReturnsZero()
    {
        var e = new EvaluationRecord { NbEvalFields = 0 };
        Assert.Equal(0m, e.Note);
    }

    [Fact]
    public void Note_PrecisionRounding()
    {
        // (1+2+3+4)*2 / 4 = 5.0
        var e = new EvaluationRecord
        {
            NoteCommunication = 1,
            NoteTheorique = 2,
            NoteTechnique = 3,
            NoteOrganisation = 4,
            NbEvalFields = 4
        };
        Assert.Equal(5m, e.Note);
    }

    // --- EvaluatorName ---

    [Fact]
    public void EvaluatorName_CombinesFirstAndLast()
    {
        var e = new EvaluationRecord { Prénom = "Jean", Nom = "Dupont" };
        Assert.Equal("Jean Dupont", e.EvaluatorName);
    }

    [Fact]
    public void EvaluatedName_MapsToGroupe()
    {
        var e = new EvaluationRecord { Groupe = "Group A" };
        Assert.Equal("Group A", e.EvaluatedName);
    }

    [Fact]
    public void Score_MapsToNote()
    {
        var e = new EvaluationRecord
        {
            NoteCommunication = 5,
            NoteTheorique = 5,
            NoteTechnique = 5,
            NoteOrganisation = 5,
            NbEvalFields = 4
        };
        Assert.Equal(e.Note, e.Score);
    }

    [Fact]
    public void IsTeacherEvaluation_DefaultFalse()
    {
        var e = new EvaluationRecord();
        Assert.False(e.IsTeacherEvaluation);
    }

    [Fact]
    public void GroupName_MapsToGroupe()
    {
        var e = new EvaluationRecord { Groupe = "TSP" };
        Assert.Equal("TSP", e.GroupName);
    }
}
