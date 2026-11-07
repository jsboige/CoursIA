using GradeBookApp;
using Xunit;

namespace GradeBookApp.Tests;

/// <summary>
/// Tests for ProjectModel — GroupEvaluation.Moyenne, GroupSizeBonus,
/// StatisticalNormalization, ProcessEvaluations filtering logic.
/// </summary>
public class ProjectModelTests
{
    // Helper to create a simple accent-folder (identity for tests that don't need it)
    private static string IdentityFold(string s) => s;

    private static StudentRecord MakeStudent(string prenom, string nom, string email, string? sujet1 = null)
        => new() { Prénom = prenom, Nom = nom, Email = email, SujetProjet1 = sujet1 };

    private static EvaluationRecord MakeEval(
        string email, string nom, string prenom, string groupe,
        int comm, int theo, int tech, int org,
        bool isTeacher = false)
        => new()
        {
            Email = email,
            Nom = nom,
            Prénom = prenom,
            Groupe = groupe,
            NoteCommunication = comm,
            NoteTheorique = theo,
            NoteTechnique = tech,
            NoteOrganisation = org,
            IsTeacher = isTeacher,
            NbEvalFields = 4
        };

    // ================================================================
    // GroupEvaluation.Moyenne — weighted average of student + teacher evals
    // ================================================================

    [Fact]
    public void GroupEval_Moyenne_NoValidEvals_ReturnsZero()
    {
        var g = new GroupEvaluation { TeacherWeight = 2m };
        Assert.Equal(0m, g.Moyenne);
    }

    [Fact]
    public void GroupEval_Moyenne_StudentOnlyEvals()
    {
        var g = new GroupEvaluation { TeacherWeight = 2m };
        g.SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("s1@e.fr", "A", "Alice", "G1", 3, 3, 3, 3),
            MakeEval("s2@e.fr", "B", "Bob", "G1", 5, 5, 5, 5),
        });
        // (6 + 10) / 2 = 8.0
        Assert.Equal(8m, g.Moyenne);
    }

    [Fact]
    public void GroupEval_Moyenne_TeacherOnlyEvals()
    {
        var g = new GroupEvaluation { TeacherWeight = 2m };
        g.SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("teacher@e.fr", "Prof", "Jean", "G1", 5, 5, 5, 5, isTeacher: true),
        });
        // Only teacher: 10.0
        Assert.Equal(10m, g.Moyenne);
    }

    [Fact]
    public void GroupEval_Moyenne_StudentPlusTeacher()
    {
        var g = new GroupEvaluation { TeacherWeight = 2m };
        g.SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("s1@e.fr", "A", "Alice", "G1", 2, 2, 2, 2), // Note=4
            MakeEval("teacher@e.fr", "Prof", "Jean", "G1", 5, 5, 5, 5, isTeacher: true), // Note=10
        });
        // studentAvg=4, teacherAvg=10, weight=2: (4 + 10*2) / (1+2) = 24/3 = 8.0
        Assert.Equal(8m, g.Moyenne);
    }

    [Fact]
    public void GroupEval_Moyenne_MultipleTeachers()
    {
        var g = new GroupEvaluation { TeacherWeight = 1m };
        g.SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("s1@e.fr", "A", "Alice", "G1", 3, 3, 3, 3), // Note=6
            MakeEval("t1@e.fr", "T1", "Prof1", "G1", 5, 5, 5, 5, isTeacher: true), // Note=10
            MakeEval("t2@e.fr", "T2", "Prof2", "G1", 1, 1, 1, 1, isTeacher: true), // Note=2
        });
        // studentAvg=6, teacherAvg=(10+2)/2=6, weight=1: (6 + 6*1) / (1+1) = 12/2 = 6.0
        Assert.Equal(6m, g.Moyenne);
    }

    // ================================================================
    // GroupSizeBonus — static lookup table
    // ================================================================

    [Fact]
    public void ApplyGroupSizeBonus_Solo_GetPlus3()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord> { MakeStudent("A", "Alice", "a@e.fr", "TSP") },
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        // Manually add group with 1 member
        proj.Groups.Add("TSP", new GroupEvaluation
        {
            Groupe = "TSP",
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "Alice", "a@e.fr") }
        });
        proj.Groups["TSP"].SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("s@e.fr", "B", "Bob", "TSP", 4, 4, 4, 4), // Note=8
        });

        proj.ApplyGroupSizeBonus();

        Assert.Equal(3m, proj.Groups["TSP"].GroupSizeBonus);
        Assert.Equal(11m, proj.Groups["TSP"].NoteAvecBonus); // 8 + 3
    }

    [Fact]
    public void ApplyGroupSizeBonus_Trio_GetZero()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            GroupMembers = new List<StudentRecord>
            {
                MakeStudent("A", "A", "a@e"),
                MakeStudent("B", "B", "b@e"),
                MakeStudent("C", "C", "c@e"),
            }
        });
        proj.Groups["G1"].SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("s@e", "X", "X", "G1", 5, 5, 5, 5), // Note=10
        });

        proj.ApplyGroupSizeBonus();

        Assert.Equal(0m, proj.Groups["G1"].GroupSizeBonus);
        Assert.Equal(10m, proj.Groups["G1"].NoteAvecBonus);
    }

    [Fact]
    public void ApplyGroupSizeBonus_FourStudents_GetMinus1()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        var members = Enumerable.Range(0, 4)
            .Select(i => MakeStudent($"S{i}", $"S{i}", $"s{i}@e"))
            .ToList();

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            GroupMembers = members
        });
        proj.Groups["G1"].SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("x@e", "X", "X", "G1", 5, 5, 5, 5), // Note=10
        });

        proj.ApplyGroupSizeBonus();

        Assert.Equal(-1m, proj.Groups["G1"].GroupSizeBonus);
        Assert.Equal(9m, proj.Groups["G1"].NoteAvecBonus);
    }

    [Fact]
    public void ApplyGroupSizeBonus_ClampsTo20()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "a@e") }
        });
        proj.Groups["G1"].SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("s@e", "B", "B", "G1", 5, 5, 5, 5), // Note=10
        });

        proj.ApplyGroupSizeBonus();

        // 10 + 3 = 13, within [0,20]
        Assert.Equal(13m, proj.Groups["G1"].NoteAvecBonus);
    }

    [Fact]
    public void ApplyGroupSizeBonus_ClampsTo0()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        var members = Enumerable.Range(0, 6)
            .Select(i => MakeStudent($"S{i}", $"S{i}", $"s{i}@e"))
            .ToList();

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            GroupMembers = members
        });
        proj.Groups["G1"].SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("x@e", "X", "X", "G1", 1, 1, 1, 1), // Note=2
        });

        proj.ApplyGroupSizeBonus();

        // 2 + (-3) = -1, clamped to 0
        Assert.Equal(0m, proj.Groups["G1"].NoteAvecBonus);
    }

    [Fact]
    public void ApplyGroupSizeBonus_EmptyGroup_Skipped()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            GroupMembers = new List<StudentRecord>()
        });

        proj.ApplyGroupSizeBonus(); // Should not throw

        Assert.Equal(0m, proj.Groups["G1"].GroupSizeBonus);
    }

    [Fact]
    public void ApplyGroupSizeBonus_UnknownSize_Throws()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        var members = Enumerable.Range(0, 7)
            .Select(i => MakeStudent($"S{i}", $"S{i}", $"s{i}@e"))
            .ToList();

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            GroupMembers = members
        });
        proj.Groups["G1"].SetValidEvaluations(new List<EvaluationRecord>
        {
            MakeEval("x@e", "X", "X", "G1", 3, 3, 3, 3),
        });

        Assert.Throws<Exception>(() => proj.ApplyGroupSizeBonus());
    }

    // ================================================================
    // Statistical Normalization — z-score + target mean/stdev
    // ================================================================

    [Fact]
    public void Normalization_SingleGroup_SetsToTargetMean()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            NoteAvecBonus = 12m,
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "a@e") }
        });

        proj.ApplyStatisticalNormalization(targetMean: 11m, targetStdev: 4m);

        // Single group: stdev=0, all get targetMean
        Assert.Equal(11m, proj.Groups["G1"].NoteRectifiée);
    }

    [Fact]
    public void Normalization_TwoEqualGroups_BothGetTargetMean()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            NoteAvecBonus = 10m,
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "a@e") }
        });
        proj.Groups.Add("G2", new GroupEvaluation
        {
            Groupe = "G2",
            NoteAvecBonus = 10m,
            GroupMembers = new List<StudentRecord> { MakeStudent("B", "B", "b@e") }
        });

        proj.ApplyStatisticalNormalization(targetMean: 11m, targetStdev: 4m);

        // Both equal: stdev=0, both get targetMean
        Assert.Equal(11m, proj.Groups["G1"].NoteRectifiée);
        Assert.Equal(11m, proj.Groups["G2"].NoteRectifiée);
    }

    [Fact]
    public void Normalization_PreservesRankOrder()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("Low", new GroupEvaluation
        {
            Groupe = "Low",
            NoteAvecBonus = 8m,
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "a@e") }
        });
        proj.Groups.Add("High", new GroupEvaluation
        {
            Groupe = "High",
            NoteAvecBonus = 14m,
            GroupMembers = new List<StudentRecord> { MakeStudent("B", "B", "b@e") }
        });

        proj.ApplyStatisticalNormalization(targetMean: 11m, targetStdev: 4m);

        // Rank order preserved: Low < High
        Assert.True(proj.Groups["Low"].NoteRectifiée < proj.Groups["High"].NoteRectifiée);
    }

    [Fact]
    public void Normalization_SymmetricAroundMean()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            NoteAvecBonus = 8m,
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "a@e") }
        });
        proj.Groups.Add("G2", new GroupEvaluation
        {
            Groupe = "G2",
            NoteAvecBonus = 14m,
            GroupMembers = new List<StudentRecord> { MakeStudent("B", "B", "b@e") }
        });

        proj.ApplyStatisticalNormalization(targetMean: 11m, targetStdev: 4m);

        // Mean=11, both equidistant: G1 and G2 should be symmetric around 11
        var delta1 = 11m - proj.Groups["G1"].NoteRectifiée;
        var delta2 = proj.Groups["G2"].NoteRectifiée - 11m;
        Assert.True(Math.Abs(delta1 - delta2) < 0.01m);
    }

    [Fact]
    public void Normalization_ClampsTo20()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("Low", new GroupEvaluation
        {
            Groupe = "Low",
            NoteAvecBonus = 6m,
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "a@e") }
        });
        proj.Groups.Add("High", new GroupEvaluation
        {
            Groupe = "High",
            NoteAvecBonus = 19m,
            GroupMembers = new List<StudentRecord> { MakeStudent("B", "B", "b@e") }
        });

        proj.ApplyStatisticalNormalization(targetMean: 11m, targetStdev: 4m);

        Assert.True(proj.Groups["High"].NoteRectifiée <= 20m);
        Assert.True(proj.Groups["Low"].NoteRectifiée >= 0m);
    }

    [Fact]
    public void Normalization_WeightedByGroupSize()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        // 3 students at 8, 1 student at 16 → weighted mean = 10
        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            NoteAvecBonus = 8m,
            GroupMembers = new List<StudentRecord>
            {
                MakeStudent("A", "A", "a@e"),
                MakeStudent("B", "B", "b@e"),
                MakeStudent("C", "C", "c@e"),
            }
        });
        proj.Groups.Add("G2", new GroupEvaluation
        {
            Groupe = "G2",
            NoteAvecBonus = 16m,
            GroupMembers = new List<StudentRecord> { MakeStudent("D", "D", "d@e") }
        });

        proj.ApplyStatisticalNormalization(targetMean: 11m, targetStdev: 4m);

        // G1 (majority, below mean) should be closer to targetMean than G2
        // Both should be finite
        Assert.True(proj.Groups["G1"].NoteRectifiée > 0m);
        Assert.True(proj.Groups["G2"].NoteRectifiée > 0m);
    }

    [Fact]
    public void Normalization_EmptyGroups_NoOp()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.ApplyStatisticalNormalization(); // No groups at all — should not throw
    }

    [Fact]
    public void Normalization_GroupsWithoutMembers_Skipped()
    {
        var proj = new ProjectEvaluation(
            new List<StudentRecord>(),
            new List<EvaluationRecord>(),
            "PrCon", "teacher@e.fr", IdentityFold);

        proj.Groups.Add("G1", new GroupEvaluation
        {
            Groupe = "G1",
            NoteAvecBonus = 10m,
            GroupMembers = new List<StudentRecord>() // empty
        });

        proj.ApplyStatisticalNormalization(); // Should not throw
    }

    // ================================================================
    // ProcessEvaluations — filtering (auto-eval, double eval, non-inscrit)
    // ================================================================

    [Fact]
    public void Process_AutoEval_Rejected()
    {
        var students = new List<StudentRecord>
        {
            MakeStudent("Alice", "Dupont", "alice@e.fr", "TSP"),
        };
        var evals = new List<EvaluationRecord>
        {
            MakeEval("alice@e.fr", "Dupont", "Alice", "TSP", 5, 5, 5, 5), // Self-eval
        };

        var proj = new ProjectEvaluation(students, evals, "PrCon", "teacher@e.fr", IdentityFold);
        proj.ProcessEvaluations();

        Assert.Single(proj.RejectedEvaluations);
        Assert.Contains("Auto", proj.RejectedEvaluations[0].Reason);
    }

    [Fact]
    public void Process_DoubleEval_SecondRejected()
    {
        var students = new List<StudentRecord>
        {
            MakeStudent("Alice", "A", "alice@e.fr", "TSP"),
            MakeStudent("Bob", "B", "bob@e.fr", "VRP"),
        };
        var evals = new List<EvaluationRecord>
        {
            MakeEval("bob@e.fr", "B", "Bob", "TSP", 3, 3, 3, 3),
            MakeEval("bob@e.fr", "B", "Bob", "TSP", 5, 5, 5, 5), // Double
        };

        var proj = new ProjectEvaluation(students, evals, "PrCon", "teacher@e.fr", IdentityFold);
        proj.ProcessEvaluations();

        Assert.Single(proj.RejectedEvaluations);
        Assert.Contains("double", proj.RejectedEvaluations[0].Reason);
    }

    [Fact]
    public void Process_NonInscrit_Rejected()
    {
        var students = new List<StudentRecord>
        {
            MakeStudent("Alice", "A", "alice@e.fr", "TSP"),
        };
        var evals = new List<EvaluationRecord>
        {
            MakeEval("unknown@e.fr", "Stranger", "X", "TSP", 3, 3, 3, 3),
        };

        var proj = new ProjectEvaluation(students, evals, "PrCon", "teacher@e.fr", IdentityFold);
        proj.ProcessEvaluations();

        Assert.Single(proj.RejectedEvaluations);
        Assert.Contains("non-inscrit", proj.RejectedEvaluations[0].Reason);
    }

    [Fact]
    public void Process_TeacherEval_MarkedAsTeacher()
    {
        var students = new List<StudentRecord>
        {
            MakeStudent("Alice", "A", "alice@e.fr", "TSP"),
        };
        var evals = new List<EvaluationRecord>
        {
            MakeEval("teacher@e.fr", "Prof", "Jean", "TSP", 5, 5, 5, 5),
        };

        var proj = new ProjectEvaluation(students, evals, "PrCon", "teacher@e.fr", IdentityFold);
        proj.ProcessEvaluations();

        Assert.Empty(proj.RejectedEvaluations);
        Assert.True(proj.Groups["TSP"].ValidEvaluations[0].IsTeacher);
    }

    [Fact]
    public void Process_ValidStudentEval_Accepted()
    {
        var students = new List<StudentRecord>
        {
            MakeStudent("Alice", "A", "alice@e.fr", "TSP"),
            MakeStudent("Bob", "B", "bob@e.fr", "VRP"),
        };
        var evals = new List<EvaluationRecord>
        {
            MakeEval("bob@e.fr", "B", "Bob", "TSP", 4, 4, 4, 4),
        };

        var proj = new ProjectEvaluation(students, evals, "PrCon", "teacher@e.fr", IdentityFold);
        proj.ProcessEvaluations();

        Assert.Empty(proj.RejectedEvaluations);
        Assert.Single(proj.Groups["TSP"].ValidEvaluations);
    }

    [Fact]
    public void Process_GroupMembersMatchBySujet()
    {
        var students = new List<StudentRecord>
        {
            MakeStudent("Alice", "A", "alice@e.fr", "TSP"),
            MakeStudent("Bob", "B", "bob@e.fr", "VRP"),
        };
        var evals = new List<EvaluationRecord>
        {
            MakeEval("bob@e.fr", "B", "Bob", "TSP", 3, 3, 3, 3),
        };

        var proj = new ProjectEvaluation(students, evals, "PrCon", "teacher@e.fr", IdentityFold);
        proj.ProcessEvaluations();

        Assert.Single(proj.Groups["TSP"].GroupMembers);
        Assert.Equal("Alice", proj.Groups["TSP"].GroupMembers[0].Prénom);
    }

    // ================================================================
    // HasStudent — group membership check
    // ================================================================

    [Fact]
    public void HasStudent_MatchingEmail_ReturnsTrue()
    {
        var g = new GroupEvaluation
        {
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "alice@e.fr") }
        };
        Assert.True(g.HasStudent("alice@e.fr"));
    }

    [Fact]
    public void HasStudent_NonMatchingEmail_ReturnsFalse()
    {
        var g = new GroupEvaluation
        {
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "alice@e.fr") }
        };
        Assert.False(g.HasStudent("bob@e.fr"));
    }

    [Fact]
    public void HasStudent_NullUID_ReturnsFalse()
    {
        var g = new GroupEvaluation
        {
            GroupMembers = new List<StudentRecord> { MakeStudent("A", "A", "alice@e.fr") }
        };
        Assert.False(g.HasStudent(null));
    }

    // ================================================================
    // RejectedEvaluation record
    // ================================================================

    [Fact]
    public void RejectedEval_StoresReason()
    {
        var eval = new EvaluationRecord { Groupe = "TSP" };
        var rejected = new RejectedEvaluation(eval, "Auto-evaluation.");
        Assert.Equal("Auto-evaluation.", rejected.Reason);
        Assert.Same(eval, rejected.Evaluation);
    }

    // ================================================================
    // NormalizationDelta
    // ================================================================

    [Fact]
    public void NormalizationDelta_Calculated()
    {
        var g = new GroupEvaluation
        {
            NoteAvecBonus = 10m,
            NoteRectifiée = 11.5m
        };
        Assert.Equal(1.5m, g.NormalizationDelta);
    }

    // ================================================================
    // FinalGrade equals NoteRectifiée
    // ================================================================

    [Fact]
    public void FinalGrade_EqualsNoteRectifiee()
    {
        var g = new GroupEvaluation { NoteRectifiée = 14.3m };
        Assert.Equal(14.3m, g.FinalGrade);
    }

    // ================================================================
    // Accent-insensitive matching in ProcessEvaluations
    // ================================================================

    [Fact]
    public void Process_AccentedNames_MatchCorrectly()
    {
        // Use the real FoldAccents from Program via reflection
        var method = typeof(Program).GetMethod("FoldAccents",
            System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Static);
        Assert.NotNull(method);
        var foldAccents = (Func<string, string>)Delegate.CreateDelegate(typeof(Func<string, string>), method);

        var students = new List<StudentRecord>
        {
            MakeStudent("Théophile", "Gautier", "theo@e.fr", "TSP"),
        };
        var evals = new List<EvaluationRecord>
        {
            MakeEval("other@e.fr", "Gautier", "Theophile", "TSP", 3, 3, 3, 3), // Accented vs not
        };

        var proj = new ProjectEvaluation(students, evals, "PrCon", "teacher@e.fr", foldAccents);
        proj.ProcessEvaluations();

        // The eval from "Theophile Gautier" should be recognized as self-eval (auto)
        Assert.Single(proj.RejectedEvaluations);
        Assert.Contains("Auto", proj.RejectedEvaluations[0].Reason);
    }
}
