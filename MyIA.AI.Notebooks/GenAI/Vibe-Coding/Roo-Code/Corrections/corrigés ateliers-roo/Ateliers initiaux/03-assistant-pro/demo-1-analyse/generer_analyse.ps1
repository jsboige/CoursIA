# Définir le chemin vers le fichier de données
$dataPath = "ateliers/demo-roo-code/03-assistant-pro/demo-1-analyse/ressources/exemple-donnees-ventes.csv"

# Importer les données du fichier CSV
# Le délimiteur est spécifié pour s'assurer que les colonnes sont correctement séparées.
$donnees = Import-Csv -Path $dataPath -Delimiter ','

# --- Préparation des données ---
# Convertir les colonnes textuelles contenant des nombres en types numériques (double pour les ventes, int pour les unités).
# Une boucle ForEach-Object est utilisée pour traiter chaque ligne du fichier CSV.
$donneesCalculees = $donnees | ForEach-Object {
    # Pour chaque ligne, un nouvel objet PowerShell est créé avec les types de données corrigés.
    [PSCustomObject]@{
        Trimestre = $_.Trimestre
        Region = $_.Region
        Categorie = $_.Categorie
        Produit = $_.Produit
        # La chaîne de la colonne 'Ventes' est convertie en nombre de type [double].
        ChiffreAffaires = [double]$_.Ventes
        # La chaîne de la colonne 'Unites' est convertie en nombre de type [int].
        UnitesVendues = [int]$_.Unites
    }
}

# --- ANALYSE GLOBALE ---
# Calculer le chiffre d'affaires total en additionnant la colonne 'ChiffreAffaires' pour toutes les lignes.
$chiffreAffairesTotal = ($donneesCalculees | Measure-Object -Property ChiffreAffaires -Sum).Sum
# Calculer le total des unités vendues en additionnant la colonne 'UnitesVendues'.
$unitesVenduesTotal = ($donneesCalculees | Measure-Object -Property UnitesVendues -Sum).Sum

Write-Output "--- ANALYSE GLOBALE ---"
# Affiche le CA total formaté en euros avec deux décimales.
Write-Output "Chiffre d'affaires total: $($chiffreAffairesTotal.ToString("N2")) €"
Write-Output "Unités vendues totales: $unitesVenduesTotal"
Write-Output ""

# --- VENTES PAR PRODUIT ---
# Regrouper les données par 'Produit' et calculer les totaux pour chaque groupe.
$ventesParProduit = $donneesCalculees | Group-Object -Property Produit | ForEach-Object {
    $ca = ($_.Group | Measure-Object -Property ChiffreAffaires -Sum).Sum
    $unites = ($_.Group | Measure-Object -Property UnitesVendues -Sum).Sum
    [PSCustomObject]@{
        Produit = $_.Name
        ChiffreAffaires = $ca
        UnitesVendues = $unites
    }
} | Sort-Object -Property ChiffreAffaires -Descending

Write-Output "--- VENTES PAR PRODUIT ---"
$ventesParProduit | Format-Table -AutoSize
Write-Output ""

# --- VENTES PAR TRIMESTRE ---
# Regrouper les données par 'Trimestre' et calculer les totaux.
$ventesParTrimestre = $donneesCalculees | Group-Object -Property Trimestre | ForEach-Object {
    $ca = ($_.Group | Measure-Object -Property ChiffreAffaires -Sum).Sum
    $unites = ($_.Group | Measure-Object -Property UnitesVendues -Sum).Sum
    [PSCustomObject]@{
        Trimestre = $_.Name
        ChiffreAffaires = $ca
        UnitesVendues = $unites
    }
} | Sort-Object -Property Trimestre

Write-Output "--- VENTES PAR TRIMESTRE ---"
$ventesParTrimestre | Format-Table -AutoSize
Write-Output ""

# --- VENTES PAR RÉGION ---
# Regrouper les données par 'Region' et calculer les totaux.
$ventesParRegion = $donneesCalculees | Group-Object -Property Region | ForEach-Object {
    $ca = ($_.Group | Measure-Object -Property ChiffreAffaires -Sum).Sum
    $unites = ($_.Group | Measure-Object -Property UnitesVendues -Sum).Sum
    [PSCustomObject]@{
        Region = $_.Name
        ChiffreAffaires = $ca
        UnitesVendues = $unites
    }
} | Sort-Object -Property ChiffreAffaires -Descending

Write-Output "--- VENTES PAR RÉGION ---"
$ventesParRegion | Format-Table -AutoSize
Write-Output ""

# --- VENTES PAR CATÉGORIE ---
# Regrouper les données par 'Categorie' et calculer les totaux.
$ventesParCategorie = $donneesCalculees | Group-Object -Property Categorie | ForEach-Object {
    $ca = ($_.Group | Measure-Object -Property ChiffreAffaires -Sum).Sum
    $unites = ($_.Group | Measure-Object -Property UnitesVendues -Sum).Sum
    [PSCustomObject]@{
        Categorie = $_.Name
        ChiffreAffaires = $ca
        UnitesVendues = $unites
    }
} | Sort-Object -Property ChiffreAffaires -Descending

Write-Output "--- VENTES PAR CATÉGORIE ---"
$ventesParCategorie | Format-Table -AutoSize
Write-Output ""