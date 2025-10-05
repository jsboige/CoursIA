# Plan de Reconstruction pour GradeBook.ipynb

Ce document détaille toutes les modifications à appliquer au fichier `MyIA.AI.Notebooks/GradeBook.ipynb` une fois qu'il aura été restauré à une version stable via `git reset`. Les modifications incluent des corrections de bugs, des ajustements de configuration et l'ajout de nouvelles fonctionnalités.

---

## 1. Modifications de Configuration Essentielles

### Cellule 2 : Paramètres généraux
Modifier la variable `nbEvalFieldsPerProject` pour qu'elle corresponde aux nouvelles exigences d'évaluation.

**Code à modifier :**
```csharp
// Doit être changé de { 3 } à { 4 }
int[] nbEvalFieldsPerProject = { 4 }; 
```

### Cellule 4 : Mappage des données CSV (`StudentMap`)
Mettre à jour le mappage pour les colonnes "Prénom" et le sujet du projet pour correspondre exactement aux en-têtes du fichier CSV et éviter les erreurs de lecture.

**Code à modifier :**
```csharp
// Dans la classe StudentMap
public StudentMap()
{
    // Correction de l'en-tête pour "Prénom" (sans accent)
    Map(m => m.Prénom).Name("Prenom");
    Map(m => m.Nom).Name("Nom");
    
    // Correction du nom de la colonne pour le sujet du projet
    Map(m => m.SujetProjet1).Name("Sujet Projet de Programmation par Contrainte");
}
```

---

## 2. Correction de la Fonction de Normalisation (BUG PRINCIPAL)

### Cellule 6 : Fonction `ProjectName`
Remplacer l'intégralité de la cellule contenant la fonction `ProjectName` défectueuse par cette version corrigée. La nouvelle fonction se contente de normaliser le nom complet sans le tronquer, ce qui est la cause principale des erreurs "étudiant non-inscrit".

**Nouveau code complet pour la cellule :**
```csharp
using System.Text;
using System.Globalization;

public static string NormalizeString(string input)
{
    if (string.IsNullOrWhiteSpace(input))
        return string.Empty;

    var normalizedString = input.Normalize(NormalizationForm.FormD);
    var stringBuilder = new StringBuilder();

    foreach (var c in normalizedString)
    {
        var unicodeCategory = CharUnicodeInfo.GetUnicodeCategory(c);
        if (unicodeCategory != UnicodeCategory.NonSpacingMark)
        {
            stringBuilder.Append(c);
        }
    }

    return stringBuilder.ToString().Normalize(NormalizationForm.FormC).ToLowerInvariant().Trim();
}

public static string ProjectName(string studentName)
{
    // La fonction renvoie maintenant simplement le nom normalisé.
    // Plus de troncature ou de split qui causaient les erreurs.
    return NormalizeString(studentName);
}
```

---

## 3. Ajout de Nouvelles Fonctionnalités (Post-Correction)

Les cellules suivantes contiennent de nouvelles logiques qui ont été ajoutées pour le calcul et l'export des notes. Elles doivent être ajoutées au notebook.

### Nouvelle Cellule : Paramètres d'Ajustement des Notes
Ajouter une nouvelle cellule de code pour définir les bonus/malus par taille de groupe et les paramètres de rectification.

**Code à ajouter dans une nouvelle cellule :**
```csharp
// Paramétrage de bonus/malus en points par taille de groupe.
public static Dictionary<int, decimal> groupSizeAdjustments = new Dictionary<int, decimal>
{
    [1] = +3.0m,  
    [2] = +1.0m,  
    [3] = 0.0m,   // valeur de référence
    [4] = -1.0m,
    [5] = -3.0m
};

public static decimal PalierGroupSizeAdjustment(int groupSize)
{
    if (!groupSizeAdjustments.ContainsKey(groupSize))
    {
        throw new Exception($"Aucun ajustement de groupe n'est défini pour un groupe de taille {groupSize}.");
    }
    return groupSizeAdjustments[groupSize];
}

// Paramètres de rectification (Moyenne cible, Écart-type cible)
List<(decimal newMean, decimal newStdev)> rectificationParams = new List<(decimal newMean, decimal newStdev)>
{
    (15m, 2m)
};
```

### Nouvelle Cellule : Logique d'Application des Ajustements
Ajouter une nouvelle cellule de code pour appliquer la rectification des notes en deux étapes : bonus/malus puis centrage-réduction.

**Code à ajouter dans une nouvelle cellule :**
```csharp
// Fonction de centrage-réduction
public static decimal AdjustGrade(decimal originalGrade, decimal groupMean, decimal groupStdDev, decimal targetMean = 10, decimal targetStdDev = 2)
{
    if (groupStdDev == 0) return targetMean;
    decimal adjustedGrade = ((originalGrade - groupMean) / groupStdDev) * targetStdDev + targetMean;
    return Math.Max(0, Math.Min(20, adjustedGrade));
}

// Étape A : Bonus/malus en fonction de la taille du groupe
foreach (var project in projectEvaluations)
{
    foreach (var groupEval in project.GroupedEvaluations)
    {
        decimal rawAvg = groupEval.Moyenne;
        int groupSize = groupEval.GroupMembers.Count;
        decimal bonusMalus = PalierGroupSizeAdjustment(groupSize);
        decimal adjusted = rawAvg + bonusMalus;
        groupEval.NoteRectifiée = Math.Max(0, Math.Min(20, adjusted));
    }
}

// Étape B : Rectification statistique
for (int i = 0; i < projectEvaluations.Count; i++)
{
    var project = projectEvaluations[i];
    var (targetMean, targetStdev) = rectificationParams[i];

    int totalStudents = project.GroupedEvaluations.Sum(g => g.GroupMembers.Count);
    if (totalStudents == 0) continue;

    double sumRectified = project.GroupedEvaluations.Sum(g => (double)g.NoteRectifiée * g.GroupMembers.Count);
    decimal projectMean = (decimal)(sumRectified / totalStudents);

    double sumSquaredDiffs = project.GroupedEvaluations.Sum(g => Math.Pow((double)(g.NoteRectifiée - projectMean), 2) * g.GroupMembers.Count);
    decimal projectStdev = (decimal)Math.Sqrt(sumSquaredDiffs / totalStudents);

    foreach (var groupEval in project.GroupedEvaluations)
    {
        decimal currentGrade = groupEval.NoteRectifiée;
        groupEval.NoteRectifiée = AdjustGrade(currentGrade, projectMean, projectStdev, targetMean, targetStdev);
    }
}
```

### Nouvelle Cellule : Génération du Fichier Excel
Ajouter une dernière cellule de code pour générer le fichier Excel final avec les notes ajustées et les feedbacks.

**Code à ajouter dans une nouvelle cellule :**
```csharp
using ClosedXML.Excel;
using System.Text;

// Fonction utilitaire pour le retour à la ligne
public string WrapText(string text, int maxLength) {
    if (string.IsNullOrWhiteSpace(text)) return "";
    var words = text.Split(' ');
    var wrappedText = new StringBuilder();
    string line = "";
    foreach (var word in words) {
        if ((line + word).Length > maxLength) {
            wrappedText.AppendLine(line.Trim());
            line = "";
        }
        line += word + " ";
    }
    if (line.Length > 0) wrappedText.AppendLine(line.Trim());
    return wrappedText.ToString();
}

public void GenerateWorkbook(List<ProjectEvaluation> projectEvaluations, List<StudentRecord> students)
{
    var workbook = new XLWorkbook();
    var summarySheet = workbook.AddWorksheet("Résumé Étudiants");

    // En-têtes
    summarySheet.Cell(1, 1).Value = "Nom";
    summarySheet.Cell(1, 2).Value = "Prénom";
    int currentColumn = 3;
    for (int i = 0; i < projectEvaluations.Count; i++) {
        summarySheet.Cell(1, currentColumn).Value = $"Groupe Projet {i + 1}";
        summarySheet.Cell(1, currentColumn + 1).Value = $"Note Projet {i + 1}";
        currentColumn += 2;
    }
    summarySheet.Cell(1, currentColumn).Value = "Note Moyenne Finale";

    // Données
    var sortedStudents = students.OrderBy(s => s.Nom).ThenBy(s => s.Prénom).ToList();
    int row = 2;
    foreach (var student in sortedStudents) {
        decimal totalNotes = 0;
        int numberOfGrades = 0;
        summarySheet.Cell(row, 1).Value = student.Nom;
        summarySheet.Cell(row, 2).Value = student.Prénom;
        currentColumn = 3;
        for (int i = 0; i < projectEvaluations.Count; i++) {
            var eval = projectEvaluations[i].GroupedEvaluations.FirstOrDefault(g => g.GroupMembers.Any(s => s.Nom == student.Nom && s.Prénom == student.Prénom));
            if (eval != null) {
                summarySheet.Cell(row, currentColumn).Value = eval.Groupe;
                summarySheet.Cell(row, currentColumn + 1).Value = eval.NoteRectifiée;
                summarySheet.Cell(row, currentC