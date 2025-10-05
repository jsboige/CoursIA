using System;
using System.Collections.Generic;
using System.Linq;

namespace GradeBookApp
{
    public class GroupEvaluation
    {
        public string Groupe { get; set; } = "";
        public List<EvaluationRecord> Evaluations { get; set; } = new();
        public List<EvaluationRecord> ValidEvaluations { get; private set; } = new();
        public List<StudentRecord> GroupMembers { get; set; } = new();
        public decimal TeacherWeight { get; set; }

        public decimal NoteAvecBonus { get; set; }
        public decimal NoteRectifiée { get; set; }

        public string GroupName => Groupe;
        public string UID => Groupe;

        public decimal Moyenne
        {
            get
            {
                if (!ValidEvaluations.Any()) return 0;
                
                var studentEvals = ValidEvaluations.Where(e => !e.IsTeacher).ToList();
                var teacherEvals = ValidEvaluations.Where(e => e.IsTeacher).ToList();

                decimal studentAvg = studentEvals.Any() ? studentEvals.Average(e => e.Note) : 0;
                decimal teacherAvg = teacherEvals.Any() ? teacherEvals.Average(e => e.Note) : 0;

                if (!studentEvals.Any() && !teacherEvals.Any()) return 0;
                if (!studentEvals.Any()) return teacherAvg;
                if (!teacherEvals.Any()) return studentAvg;
                
                return (studentAvg + (teacherAvg * TeacherWeight)) / (1 + TeacherWeight);
            }
        }
        
        public decimal GroupSizeBonus { get; set; }
        public decimal NormalizationDelta => NoteRectifiée - NoteAvecBonus;
        public decimal FinalGrade => NoteRectifiée;
        
        public bool HasStudent(string? studentUID) => studentUID != null && GroupMembers.Exists(s => s.UID == studentUID);
        
        public void SetValidEvaluations(List<EvaluationRecord> valid)
        {
            ValidEvaluations = valid;
        }
    }

    public class RejectedEvaluation
    {
        public EvaluationRecord Evaluation { get; }
        public string Reason { get; }

        public RejectedEvaluation(EvaluationRecord evaluation, string reason)
        {
            Evaluation = evaluation;
            Reason = reason;
        }
    }

    public class ProjectEvaluation
    {
        public List<StudentRecord> Students { get; }
        private readonly List<EvaluationRecord> _allEvaluations;
        public Dictionary<string, GroupEvaluation> Groups { get; } = new Dictionary<string, GroupEvaluation>();
        public List<RejectedEvaluation> RejectedEvaluations { get; } = new List<RejectedEvaluation>();
        public Func<string, string> FoldAccents { get; }
        public string CourseName { get; }
        public string TeacherIdentifier { get; }
        public decimal TeacherWeight { get; set; }

        private static readonly Dictionary<int, decimal> GroupSizeAdjustments = new()
        {
            { 1, 3.0m }, { 2, 1.0m }, { 3, 0.0m }, { 4, -1.0m }, { 5, -2.0m }, { 6, -3.0m }
        };

        public ProjectEvaluation(List<StudentRecord> students, List<EvaluationRecord> evaluations, string courseName, string teacherIdentifier, Func<string, string> foldAccents)
        {
            Students = students;
            _allEvaluations = evaluations;
            CourseName = courseName;
            TeacherIdentifier = teacherIdentifier;
            FoldAccents = foldAccents;
        }

        private bool IsMatch(StudentRecord student, EvaluationRecord eval)
        {
            return FoldAccents(student.Nom ?? "").Equals(FoldAccents(eval.Nom ?? ""), StringComparison.OrdinalIgnoreCase) && 
                   FoldAccents(student.Prénom ?? "").Equals(FoldAccents(eval.Prénom ?? ""), StringComparison.OrdinalIgnoreCase);
        }

        public void ProcessEvaluations()
        {
            // 1. Marquer les évaluations du professeur
            foreach (var eval in _allEvaluations)
            {
                if (eval.Email?.Equals(TeacherIdentifier, StringComparison.OrdinalIgnoreCase) == true ||
                    eval.Nom?.Equals(TeacherIdentifier, StringComparison.OrdinalIgnoreCase) == true)
                {
                    eval.IsTeacher = true;
                }
            }

            // 2. Grouper les évaluations par nom de groupe
            var evaluationsByGroup = _allEvaluations.Where(e => !string.IsNullOrWhiteSpace(e.Groupe)).GroupBy(e => e.Groupe!);
            foreach (var group in evaluationsByGroup)
            {
                var groupEval = new GroupEvaluation
                {
                    Groupe = group.Key,
                    Evaluations = group.ToList(),
                    TeacherWeight = this.TeacherWeight,
                    GroupMembers = Students.Where(s => s.Sujets.Contains(group.Key, StringComparer.OrdinalIgnoreCase)).ToList()
                };
                Groups.Add(group.Key, groupEval);
            }

            // 3. Filtrer les évaluations
            foreach (var groupEval in Groups.Values)
            {
                var validEvals = new List<EvaluationRecord>();
                var seenEvaluatorsForGroup = new HashSet<string>(StringComparer.OrdinalIgnoreCase);

                foreach(var eval in groupEval.Evaluations.OrderBy(e => e.Date))
                {
                    var evaluatorEmail = eval.Email ?? $"{eval.Nom}{eval.Prénom}";
                    
                    if (groupEval.GroupMembers.Any(s => IsMatch(s, eval)))
                    {
                        RejectedEvaluations.Add(new RejectedEvaluation(eval, "Auto-évaluation."));
                    }
                    else if (!seenEvaluatorsForGroup.Add(evaluatorEmail))
                    {
                        RejectedEvaluations.Add(new RejectedEvaluation(eval, "Évaluation double."));
                    }
                    else if (!eval.IsTeacher && !Students.Exists(s => IsMatch(s, eval))) {
                        RejectedEvaluations.Add(new RejectedEvaluation(eval, "Évaluateur non-inscrit."));
                    }
                    else
                    {
                        validEvals.Add(eval);
                    }
                }
                groupEval.SetValidEvaluations(validEvals);
            }
        }

        public void ApplyGroupSizeBonus()
        {
            foreach (var group in Groups.Values)
            {
                if (group.GroupMembers.Count == 0) continue; // On ignore les groupes sans membres

                if (GroupSizeAdjustments.TryGetValue(group.GroupMembers.Count, out var bonus))
                {
                    group.GroupSizeBonus = bonus;
                }
                else
                {
                    // Comportement original conservé pour les tailles de groupe non prévues mais supérieures à 0
                    throw new Exception($"Aucun ajustement de groupe n'est défini pour un groupe de taille {group.GroupMembers.Count}.");
                }
                group.NoteAvecBonus = Math.Max(0, Math.Min(20, group.Moyenne + group.GroupSizeBonus));
            }
        }
        
        public void ApplyStatisticalNormalization(decimal targetMean = 11m, decimal targetStdev = 4m)
        {
            if (!Groups.Any() || !Groups.Values.Any(g => g.GroupMembers.Any())) return;

            var groupsWithMembers = Groups.Values.Where(g => g.GroupMembers.Any()).ToList();
            int totalStudents = groupsWithMembers.Sum(g => g.GroupMembers.Count);
            if (totalStudents == 0) return;

            // 1. Calcul de la moyenne pondérée par la taille des groupes
            double sumRectified = groupsWithMembers.Sum(g => (double)g.NoteAvecBonus * g.GroupMembers.Count);
            decimal projectMean = (decimal)(sumRectified / totalStudents);

            // 2. Calcul de l'écart-type pondéré
            double sumSquaredDiffs = groupsWithMembers.Sum(g => Math.Pow((double)(g.NoteAvecBonus - projectMean), 2) * g.GroupMembers.Count);
            decimal projectStdev = (decimal)Math.Sqrt(sumSquaredDiffs / totalStudents);

            if (projectStdev == 0)
            {
                foreach (var group in Groups.Values)
                {
                    group.NoteRectifiée = targetMean;
                }
                return;
            }

            // 3. Application de la normalisation (centrage-réduction)
            foreach(var group in Groups.Values)
            {
                var zScore = (group.NoteAvecBonus - projectMean) / projectStdev;
                var normalizedGrade = zScore * targetStdev + targetMean;
                group.NoteRectifiée = Math.Max(0, Math.Min(20, normalizedGrade));
            }
        }
    }
}