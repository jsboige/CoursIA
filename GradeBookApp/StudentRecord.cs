using CsvHelper.Configuration;
using System.Collections.Generic;
using System.Linq;

namespace GradeBookApp
{
    public class StudentRecord
    {
        public string? Prénom { get; set; }
        public string? Nom { get; set; }
        public string? Email { get; set; }
        public string? SujetProjet1 { get; set; }
        public string? SujetProjet2 { get; set; }
        public List<string> Sujets => new List<string?> { SujetProjet1, SujetProjet2 }.Where(s => s != null).ToList()!;
        public List<decimal> Notes { get; set; } = new();
        public decimal Moyenne => Notes.Any() ? Notes.Average() : 0;

        // Propriétés pour la compatibilité avec le rapporteur
        public string? FirstName => Prénom;
        public string? LastName => Nom;
        public string? UID => Email;
        public string Course => "PrCon"; // Simplification
    }

    public class StudentMap : ClassMap<StudentRecord>
    {
        public StudentMap()
        {
            // Mappages flexibles pour gérer les fichiers PrCon et IASY
            Map(m => m.Prénom).Name("Prenom", "Prénom");
            Map(m => m.Nom).Name("Nom");
            Map(m => m.Email).Name("Mail", "Login"); // Utilise Mail ou Login comme Email
            
            // Le nom de la colonne de sujet est différent entre les deux classes
            Map(m => m.SujetProjet1).Name("Sujet Projet de Programmation par Contrainte", "Sujet IA Symbolique");

            // Rendre le deuxième sujet optionnel
            Map(m => m.SujetProjet2).Optional();
        }
    }
}