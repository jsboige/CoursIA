using CsvHelper.Configuration;
using System;

namespace GradeBookApp
{
    public class EvaluationRecord
    {
        public DateTime Date { get; set; }
        public string? Email { get; set; }
        public string? Nom { get; set; }
        public string? Prénom { get; set; }
        public string? Groupe { get; set; }
        public string? SujetLibre { get; set; }
        public int NoteCommunication { get; set; }
        public int NoteTheorique { get; set; }
        public int NoteTechnique { get; set; }
        public int NoteOrganisation { get; set; }
        public string? PointsPositifs { get; set; }
        public string? PointsNegatifs { get; set; }
        public string? Recommandations { get; set; }

        public decimal Note => NbEvalFields > 0 ? ((decimal)(NoteCommunication + NoteTechnique + NoteTheorique + NoteOrganisation) * 2) / NbEvalFields : 0;
        public bool IsTeacher { get; set; }
        public int NbEvalFields { get; set; } = 4; // Valeur par défaut, peut être ajustée au chargement

        // Propriétés pour la compatibilité avec le rapporteur
        public string EvaluatorName => $"{Prénom} {Nom}";
        public string? EvaluatedName => Groupe; // L'évaluation cible le groupe
        public decimal Score => Note;
        public bool IsTeacherEvaluation => IsTeacher;
        public string? GroupName => Groupe;
    }

    public class EvaluationMap : ClassMap<EvaluationRecord>
    {
        public EvaluationMap()
        {
            Map(m => m.Date).Name("Horodateur").TypeConverterOption.Format("dd/MM/yyyy HH:mm:ss");
            Map(m => m.Email).Name("Adresse e-mail");
            Map(m => m.Nom).Name("Votre nom");
            Map(m => m.Prénom).Name("Votre prénom");
            Map(m => m.Groupe).Name("Groupe à évaluer");
            Map(m => m.SujetLibre).Name("Sujet de la présentation").Optional();
            
            Map(m => m.NoteCommunication).Name("Qualité de la présentation (communication, la forme)");
            Map(m => m.NoteTheorique).Name("Qualité théorique (principes utilisés, classe d'algorithmes, contexte et explications des performances et des problèmes, histoire etc.)");
            Map(m => m.NoteTechnique).Name("Qualité technique (livrables, commits, qualité du code, démos, résultats, perspectives)");
            // Gère les variations du nom de colonne pour "Organisation"
            Map(m => m.NoteOrganisation).Name("Organisation (planning, répartition des tâches, collaboration, intégration au projet Github)", "Organisation (planning, répartition des tâches, collaboration, intégration au projet Github) ");
            
            Map(m => m.PointsPositifs).Name("Points positifs de la présentation").Optional();
            Map(m => m.PointsNegatifs).Name("Points négatifs de la présentation").Optional();
            Map(m => m.Recommandations).Name("Recommandations pour s'améliorer").Optional();
        }
    }
}