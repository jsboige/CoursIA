using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text;
using ClosedXML.Excel;
using CsvHelper;
using CsvHelper.Configuration;
using Lucene.Net.Analysis;
using Lucene.Net.Analysis.Standard;
using Lucene.Net.Analysis.Miscellaneous;

namespace GradeBookApp
{
    public class Program
    {
    private static readonly Lucene.Net.Util.LuceneVersion AppLuceneVersion = Lucene.Net.Util.LuceneVersion.LUCENE_48;

    public static string FoldAccents(string text)
    {
        if (string.IsNullOrWhiteSpace(text))
            return text;

        var analyzer = new StandardAnalyzer(AppLuceneVersion);
        var tokenStream = analyzer.GetTokenStream("content", new StringReader(text));
        tokenStream = new ASCIIFoldingFilter(tokenStream);
        var termAttribute = tokenStream.GetAttribute<Lucene.Net.Analysis.TokenAttributes.ICharTermAttribute>();
        tokenStream.Reset();
        
        var sb = new StringBuilder();
        while (tokenStream.IncrementToken())
        {
            sb.Append(termAttribute.ToString());
        }
        tokenStream.End();
        tokenStream.Dispose();
        analyzer.Dispose();
        return sb.ToString();
    }

    public static void Main(string[] args)
    {
        Console.OutputEncoding = Encoding.UTF8;
        var culture = new CultureInfo("fr-FR");
        CultureInfo.DefaultThreadCurrentCulture = culture;
        CultureInfo.DefaultThreadCurrentUICulture = culture;

        if (args.Length < 2)
        {
            Console.WriteLine("Usage: GradeBookApp <path_to_registrations.csv> <path_to_evaluations.csv> [path_to_output.xlsx]");
            return;
        }

        var registrationsPath = args[0];
        var evaluationsPath = args[1];
        var outputDirectory = Path.GetDirectoryName(registrationsPath);
        var outputFileName = "Bilan-PrCon-2025.xlsx";
        var outputPath = Path.Combine(outputDirectory, outputFileName);
        if(args.Length > 2)
        {
            outputPath = args[2];
        }

        Console.WriteLine($"Chargement des inscriptions depuis : {registrationsPath}");
        var students = LoadStudents(registrationsPath);

        Console.WriteLine($"Chargement des évaluations depuis : {evaluationsPath}");
        var evaluations = LoadEvaluations(evaluationsPath);

        Console.WriteLine("Création du projet d'évaluation...");
        var project = new ProjectEvaluation(students, evaluations, "PrCon", "Prof", FoldAccents);
        project.TeacherWeight = 2; // Poids du professeur

        Console.WriteLine("Calcul des notes initiales...");
        project.ProcessEvaluations();

        Console.WriteLine("Application des ajustements (Taille de groupe & Normalisation)...");
        project.ApplyGroupSizeBonus();
        project.ApplyStatisticalNormalization(15.5m, 2m);

        Console.WriteLine($"Génération du rapport Excel : {outputPath}");
        GenerateExcelReport(project, outputPath);
        
        Console.WriteLine("Terminé !");
    }

    private static List<StudentRecord> LoadStudents(string path)
    {
        using (var reader = new StreamReader(path))
        using (var csv = new CsvReader(reader, new CsvConfiguration(CultureInfo.InvariantCulture) { Delimiter = ",", PrepareHeaderForMatch = args => args.Header.ToLower() }))
        {
            csv.Context.RegisterClassMap<StudentMap>();
            return csv.GetRecords<StudentRecord>().ToList();
        }
    }

    private static List<EvaluationRecord> LoadEvaluations(string path)
    {
        var csvConfig = new CsvConfiguration(new CultureInfo("fr-FR"))
        {
            Delimiter = ",",
            PrepareHeaderForMatch = args => args.Header.ToLower().Trim(),
            BadDataFound = null
        };
        using (var reader = new StreamReader(path))
        using (var csv = new CsvReader(reader, csvConfig))
        {
            csv.Context.RegisterClassMap<EvaluationMap>();
            return csv.GetRecords<EvaluationRecord>().ToList();
        }
    }
    
    private static void GenerateExcelReport(ProjectEvaluation project, string path)
    {
        using (var workbook = new XLWorkbook())
        {
            // --- Feuille 1: Notes Finales ---
            var wsFinal = workbook.Worksheets.Add("Notes Finales");
            wsFinal.Cell(1, 1).Value = "Matière";
            wsFinal.Cell(1, 2).Value = "Nom";
            wsFinal.Cell(1, 3).Value = "Prénom";
            wsFinal.Cell(1, 4).Value = "Groupe";
            wsFinal.Cell(1, 5).Value = "Note Finale";
            wsFinal.Cell(1, 6).Value = "Note Base";
            wsFinal.Cell(1, 7).Value = "Bonus Taille";
            wsFinal.Cell(1, 8).Value = "Delta Normalisation";

            var row = 2;
            foreach (var student in project.Students.OrderBy(s => s.LastName).ThenBy(s => s.FirstName))
            {
                var group = project.Groups.Values.FirstOrDefault(g => g.HasStudent(student.UID));
                if (group != null)
                {
                    wsFinal.Cell(row, 1).Value = student.Course;
                    wsFinal.Cell(row, 2).Value = student.LastName;
                    wsFinal.Cell(row, 3).Value = student.FirstName;
                    wsFinal.Cell(row, 4).Value = group.GroupName;
                    wsFinal.Cell(row, 5).Value = group.FinalGrade;
                    wsFinal.Cell(row, 6).Value = group.Moyenne;
                    wsFinal.Cell(row, 7).Value = group.GroupSizeBonus;
                    wsFinal.Cell(row, 8).Value = group.NormalizationDelta;
                }
                row++;
            }
            wsFinal.Columns().AdjustToContents();

            // --- Feuille 2: Détail Évaluations ---
            var wsDetails = workbook.Worksheets.Add("Détail Évaluations");
            wsDetails.Cell(1, 1).Value = "Groupe";
            wsDetails.Cell(1, 2).Value = "Évaluateur";
            wsDetails.Cell(1, 3).Value = "Évalué";
            wsDetails.Cell(1, 4).Value = "Note";
            wsDetails.Cell(1, 5).Value = "Est Professeur";

            row = 2;
            foreach (var group in project.Groups.Values.OrderBy(g => g.GroupName))
            {
                foreach (var eval in group.ValidEvaluations)
                {
                    wsDetails.Cell(row, 1).Value = group.GroupName;
                    wsDetails.Cell(row, 2).Value = eval.EvaluatorName;
                    wsDetails.Cell(row, 3).Value = eval.EvaluatedName;
                    wsDetails.Cell(row, 4).Value = eval.Score;
                    wsDetails.Cell(row, 5).Value = eval.IsTeacherEvaluation;
                    row++;
                }
            }
            wsDetails.Columns().AdjustToContents();

            // --- Feuille 3: Évaluations Rejetées ---
            var wsRejected = workbook.Worksheets.Add("Évaluations Rejetées");
            wsRejected.Cell(1, 1).Value = "Évaluateur";
            wsRejected.Cell(1, 2).Value = "Groupe Évalué";
            wsRejected.Cell(1, 3).Value = "Note";
            wsRejected.Cell(1, 4).Value = "Raison du Rejet";
            
            row = 2;
            foreach (var rejected in project.RejectedEvaluations)
            {
                wsRejected.Cell(row, 1).Value = rejected.Evaluation.EvaluatorName;
                wsRejected.Cell(row, 2).Value = rejected.Evaluation.GroupName;
                wsRejected.Cell(row, 3).Value = rejected.Evaluation.Score;
                wsRejected.Cell(row, 4).Value = rejected.Reason;
                row++;
            }
            wsRejected.Columns().AdjustToContents();
            
            // --- Feuille 4: Feedback Qualitatif ---
            var wsFeedback = workbook.Worksheets.Add("Feedback Qualitatif");
            wsFeedback.Cell(1, 1).Value = "Groupe Évalué";
            wsFeedback.Cell(1, 2).Value = "Évaluateur";
            wsFeedback.Cell(1, 3).Value = "Points Positifs";
            wsFeedback.Cell(1, 4).Value = "Points Négatifs";
            wsFeedback.Cell(1, 5).Value = "Recommandations";

            row = 2;
            foreach (var group in project.Groups.Values.OrderBy(g => g.GroupName))
            {
                foreach (var eval in group.ValidEvaluations.OrderBy(e => e.Date))
                {
                    if (!string.IsNullOrWhiteSpace(eval.PointsPositifs) || !string.IsNullOrWhiteSpace(eval.PointsNegatifs) || !string.IsNullOrWhiteSpace(eval.Recommandations))
                    {
                        wsFeedback.Cell(row, 1).Value = group.GroupName;
                        wsFeedback.Cell(row, 2).Value = eval.EvaluatorName;
                        wsFeedback.Cell(row, 3).Value = eval.PointsPositifs;
                        wsFeedback.Cell(row, 4).Value = eval.PointsNegatifs;
                        wsFeedback.Cell(row, 5).Value = eval.Recommandations;
                        row++;
                    }
                }
            }
            wsFeedback.Columns().AdjustToContents();

            workbook.SaveAs(path);
            }
        }
    }
}
