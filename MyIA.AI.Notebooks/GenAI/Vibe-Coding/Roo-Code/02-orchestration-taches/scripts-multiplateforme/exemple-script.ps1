<#
.SYNOPSIS
    Organisateur de Fichiers - Script PowerShell pour organiser vos fichiers
.DESCRIPTION
    Ce script vous aide à organiser vos fichiers (photos, documents, etc.) en les triant
    selon différents critères (date, type, nom) et en les déplaçant dans des dossiers appropriés.
    Il peut également générer un rapport des opérations effectuées.
.NOTES
    Auteur: Roo Code Assistant
    Date: Mai 2025
    Version: 2.0
.EXAMPLE
    .\exemple-script.ps1 -SourceFolder "C:\Mes Photos" -DestinationFolder "C:\Photos Organisées" -OrganisationCritere "date" -GenererRapport $true
#>

param (
    [Parameter(Mandatory=$false)]
    [string]$SourceFolder = "",
    
    [Parameter(Mandatory=$false)]
    [string]$DestinationFolder = "",
    
    [Parameter(Mandatory=$false)]
    [ValidateSet("date", "type", "nom")]
    [string]$OrganisationCritere = "date",
    
    [Parameter(Mandatory=$false)]
    [bool]$GenererRapport = $true,
    
    [Parameter(Mandatory=$false)]
    [bool]$ModeSimulation = $false
)

# Configuration
$ErrorActionPreference = "Stop"
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$LogFile = Join-Path -Path $ScriptDir -ChildPath "OrganisationFichiers_$(Get-Date -Format 'yyyyMMdd_HHmmss').log"
$RapportFile = Join-Path -Path $ScriptDir -ChildPath "Rapport_Organisation_$(Get-Date -Format 'yyyyMMdd_HHmmss').html"

# Fonction pour écrire dans le journal
function Write-Log {
    param (
        [Parameter(Mandatory=$true)]
        [string]$Message,
        
        [Parameter(Mandatory=$false)]
        [ValidateSet("INFO", "SUCCESS", "WARNING", "ERROR")]
        [string]$Level = "INFO"
    )
    
    $Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $LogEntry = "[$Timestamp] [$Level] $Message"
    
    # Afficher dans la console avec couleur
    switch ($Level) {
        "INFO" { Write-Host $LogEntry -ForegroundColor Cyan }
        "SUCCESS" { Write-Host $LogEntry -ForegroundColor Green }
        "WARNING" { Write-Host $LogEntry -ForegroundColor Yellow }
        "ERROR" { Write-Host $LogEntry -ForegroundColor Red }
    }
    
    # Écrire dans le fichier journal
    Add-Content -Path $LogFile -Value $LogEntry
}

# Fonction pour demander un dossier à l'utilisateur
function Get-FolderFromUser {
    param (
        [string]$Message,
        [string]$DefaultPath = ""
    )
    
    Add-Type -AssemblyName System.Windows.Forms
    $FolderBrowser = New-Object System.Windows.Forms.FolderBrowserDialog
    $FolderBrowser.Description = $Message
    
    if ($DefaultPath -and (Test-Path -Path $DefaultPath)) {
        $FolderBrowser.SelectedPath = $DefaultPath
    }
    
    $Result = $FolderBrowser.ShowDialog()
    
    if ($Result -eq [System.Windows.Forms.DialogResult]::OK) {
        return $FolderBrowser.SelectedPath
    } else {
        return $null
    }
}

# Fonction pour vérifier et créer un répertoire
function Ensure-Directory {
    param (
        [Parameter(Mandatory=$true)]
        [string]$Path
    )
    
    if (-not (Test-Path -Path $Path)) {
        Write-Log "Création du répertoire: $Path"
        if (-not $ModeSimulation) {
            New-Item -Path $Path -ItemType Directory | Out-Null
        }
        return $true
    } else {
        Write-Log "Le répertoire existe déjà: $Path"
        return $false
    }
}

# Fonction pour obtenir l'extension d'un fichier sans le point
function Get-FileExtensionWithoutDot {
    param (
        [string]$FileName
    )
    
    $Extension = [System.IO.Path]::GetExtension($FileName)
    if ($Extension.StartsWith(".")) {
        $Extension = $Extension.Substring(1)
    }
    return $Extension.ToLower()
}

# Fonction pour obtenir le type de fichier à partir de l'extension
function Get-FileType {
    param (
        [string]$Extension
    )
    
    $ImageExtensions = @("jpg", "jpeg", "png", "gif", "bmp", "tiff", "webp", "heic")
    $DocumentExtensions = @("pdf", "doc", "docx", "xls", "xlsx", "ppt", "pptx", "txt", "rtf", "odt")
    $VideoExtensions = @("mp4", "avi", "mov", "wmv", "mkv", "flv", "webm")
    $AudioExtensions = @("mp3", "wav", "ogg", "flac", "aac", "wma")
    $ArchiveExtensions = @("zip", "rar", "7z", "tar", "gz")
    
    if ($ImageExtensions -contains $Extension) {
        return "Images"
    } elseif ($DocumentExtensions -contains $Extension) {
        return "Documents"
    } elseif ($VideoExtensions -contains $Extension) {
        return "Videos"
    } elseif ($AudioExtensions -contains $Extension) {
        return "Audio"
    } elseif ($ArchiveExtensions -contains $Extension) {
        return "Archives"
    } else {
        return "Autres"
    }
}

# Fonction pour organiser les fichiers
function Organize-Files {
    param (
        [string]$SourcePath,
        [string]$DestinationPath,
        [string]$Critere
    )
    
    # Vérifier que les chemins existent
    if (-not (Test-Path -Path $SourcePath)) {
        Write-Log "Le dossier source n'existe pas: $SourcePath" -Level "ERROR"
        return $false
    }
    
    Ensure-Directory -Path $DestinationPath
    
    # Récupérer tous les fichiers du dossier source (y compris les sous-dossiers)
    $AllFiles = Get-ChildItem -Path $SourcePath -File -Recurse
    $TotalFiles = $AllFiles.Count
    
    if ($TotalFiles -eq 0) {
        Write-Log "Aucun fichier trouvé dans le dossier source." -Level "WARNING"
        return $false
    }
    
    Write-Log "Début de l'organisation de $TotalFiles fichiers selon le critère: $Critere"
    
    # Statistiques pour le rapport
    $Stats = @{
        TotalFiles = $TotalFiles
        ProcessedFiles = 0
        SkippedFiles = 0
        OrganizedByType = @{}
        OrganizedByDate = @{}
        OrganizedByName = @{}
    }
    
    # Traiter chaque fichier
    foreach ($File in $AllFiles) {
        $FileName = $File.Name
        $Extension = Get-FileExtensionWithoutDot -FileName $FileName
        $FileType = Get-FileType -Extension $Extension
        $FileDate = $File.LastWriteTime
        $FirstLetter = $FileName.Substring(0, 1).ToUpper()
        
        # Déterminer le dossier de destination selon le critère
        $DestinationSubFolder = ""
        
        switch ($Critere) {
            "date" {
                $Year = $FileDate.Year.ToString()
                $Month = $FileDate.ToString("MM - MMMM")
                $DestinationSubFolder = Join-Path -Path $DestinationPath -ChildPath $Year
                $DestinationSubFolder = Join-Path -Path $DestinationSubFolder -ChildPath $Month
                
                # Mettre à jour les statistiques
                if (-not $Stats.OrganizedByDate.ContainsKey($Year)) {
                    $Stats.OrganizedByDate[$Year] = @{}
                }
                if (-not $Stats.OrganizedByDate[$Year].ContainsKey($Month)) {
                    $Stats.OrganizedByDate[$Year][$Month] = 0
                }
                $Stats.OrganizedByDate[$Year][$Month]++
            }
            "type" {
                $DestinationSubFolder = Join-Path -Path $DestinationPath -ChildPath $FileType
                
                # Mettre à jour les statistiques
                if (-not $Stats.OrganizedByType.ContainsKey($FileType)) {
                    $Stats.OrganizedByType[$FileType] = 0
                }
                $Stats.OrganizedByType[$FileType]++
            }
            "nom" {
                $DestinationSubFolder = Join-Path -Path $DestinationPath -ChildPath $FirstLetter
                
                # Mettre à jour les statistiques
                if (-not $Stats.OrganizedByName.ContainsKey($FirstLetter)) {
                    $Stats.OrganizedByName[$FirstLetter] = 0
                }
                $Stats.OrganizedByName[$FirstLetter]++
            }
        }
        
        # Créer le dossier de destination s'il n'existe pas
        Ensure-Directory -Path $DestinationSubFolder
        
        # Chemin complet du fichier de destination
        $DestinationFilePath = Join-Path -Path $DestinationSubFolder -ChildPath $FileName
        
        # Vérifier si le fichier existe déjà à destination
        if (Test-Path -Path $DestinationFilePath) {
            $FileNameOnly = [System.IO.Path]::GetFileNameWithoutExtension($FileName)
            $NewFileName = "$FileNameOnly ($(Get-Date -Format 'yyyyMMdd_HHmmss')).$Extension"
            $DestinationFilePath = Join-Path -Path $DestinationSubFolder -ChildPath $NewFileName
            Write-Log "Le fichier existe déjà, renommage en: $NewFileName" -Level "WARNING"
        }
        
        # Copier le fichier
        try {
            Write-Log "Déplacement du fichier: $FileName vers $DestinationSubFolder"
            if (-not $ModeSimulation) {
                Copy-Item -Path $File.FullName -Destination $DestinationFilePath -Force
            }
            $Stats.ProcessedFiles++
        } catch {
            Write-Log "Erreur lors du déplacement du fichier $FileName : $_" -Level "ERROR"
            $Stats.SkippedFiles++
        }
    }
    
    Write-Log "Organisation terminée. $($Stats.ProcessedFiles) fichiers traités, $($Stats.SkippedFiles) fichiers ignorés." -Level "SUCCESS"
    return $Stats
}

# Fonction pour générer un rapport HTML
function Generate-Report {
    param (
        [hashtable]$Stats,
        [string]$SourcePath,
        [string]$DestinationPath,
        [string]$Critere
    )
    
    $ReportDate = Get-Date -Format "dd/MM/yyyy HH:mm:ss"
    
    # Créer le contenu HTML
    $HtmlContent = @"
<!DOCTYPE html>
<html lang="fr">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Rapport d'Organisation de Fichiers</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            line-height: 1.6;
            margin: 0;
            padding: 20px;
            color: #333;
        }
        h1, h2, h3 {
            color: #2c3e50;
        }
        .container {
            max-width: 1000px;
            margin: 0 auto;
            background: #f9f9f9;
            padding: 20px;
            border-radius: 5px;
            box-shadow: 0 0 10px rgba(0,0,0,0.1);
        }
        .summary {
            background: #e8f4fc;
            padding: 15px;
            border-radius: 5px;
            margin-bottom: 20px;
        }
        .success {
            color: #27ae60;
            font-weight: bold;
        }
        .warning {
            color: #f39c12;
            font-weight: bold;
        }
        table {
            width: 100%;
            border-collapse: collapse;
            margin-bottom: 20px;
        }
        th, td {
            padding: 10px;
            border: 1px solid #ddd;
            text-align: left;
        }
        th {
            background-color: #f2f2f2;
        }
        tr:nth-child(even) {
            background-color: #f9f9f9;
        }
        .chart {
            margin-top: 20px;
            margin-bottom: 40px;
        }
        .bar {
            height: 25px;
            background-color: #3498db;
            margin-bottom: 5px;
            border-radius: 3px;
        }
        .bar-label {
            display: flex;
            justify-content: space-between;
            margin-bottom: 15px;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>Rapport d'Organisation de Fichiers</h1>
        <p>Rapport généré le: $ReportDate</p>
        
        <div class="summary">
            <h2>Résumé</h2>
            <p>Dossier source: <strong>$SourcePath</strong></p>
            <p>Dossier destination: <strong>$DestinationPath</strong></p>
            <p>Critère d'organisation: <strong>$Critere</strong></p>
            <p>Fichiers traités: <span class="success">$($Stats.ProcessedFiles)</span> sur $($Stats.TotalFiles)</p>
            <p>Fichiers ignorés: <span class="warning">$($Stats.SkippedFiles)</span></p>
        </div>
"@

    # Ajouter les détails selon le critère
    switch ($Critere) {
        "type" {
            $HtmlContent += @"
        <h2>Organisation par Type de Fichier</h2>
        <table>
            <tr>
                <th>Type de Fichier</th>
                <th>Nombre de Fichiers</th>
            </tr>
"@
            foreach ($Type in $Stats.OrganizedByType.Keys | Sort-Object) {
                $Count = $Stats.OrganizedByType[$Type]
                $Percentage = [math]::Round(($Count / $Stats.TotalFiles) * 100, 1)
                $BarWidth = [math]::Round(($Count / $Stats.TotalFiles) * 100, 0)
                
                $HtmlContent += @"
            <tr>
                <td>$Type</td>
                <td>$Count ($Percentage%)</td>
            </tr>
"@
            }
            
            $HtmlContent += @"
        </table>
        
        <div class="chart">
            <h3>Répartition graphique</h3>
"@
            
            foreach ($Type in $Stats.OrganizedByType.Keys | Sort-Object) {
                $Count = $Stats.OrganizedByType[$Type]
                $Percentage = [math]::Round(($Count / $Stats.TotalFiles) * 100, 1)
                $BarWidth = [math]::Round(($Count / $Stats.TotalFiles) * 100, 0)
                
                $HtmlContent += @"
            <div class="bar-label">
                <span>$Type</span>
                <span>$Count ($Percentage%)</span>
            </div>
            <div class="bar" style="width: $BarWidth%;"></div>
"@
            }
            
            $HtmlContent += @"
        </div>
"@
        }
        "date" {
            $HtmlContent += @"
        <h2>Organisation par Date</h2>
"@
            
            foreach ($Year in $Stats.OrganizedByDate.Keys | Sort-Object) {
                $HtmlContent += @"
        <h3>$Year</h3>
        <table>
            <tr>
                <th>Mois</th>
                <th>Nombre de Fichiers</th>
            </tr>
"@
                
                foreach ($Month in $Stats.OrganizedByDate[$Year].Keys | Sort-Object) {
                    $Count = $Stats.OrganizedByDate[$Year][$Month]
                    $HtmlContent += @"
            <tr>
                <td>$Month</td>
                <td>$Count</td>
            </tr>
"@
                }
                
                $HtmlContent += @"
        </table>
"@
            }
        }
        "nom" {
            $HtmlContent += @"
        <h2>Organisation par Nom</h2>
        <table>
            <tr>
                <th>Première Lettre</th>
                <th>Nombre de Fichiers</th>
            </tr>
"@
            
            foreach ($Letter in $Stats.OrganizedByName.Keys | Sort-Object) {
                $Count = $Stats.OrganizedByName[$Letter]
                $HtmlContent += @"
            <tr>
                <td>$Letter</td>
                <td>$Count</td>
            </tr>
"@
            }
            
            $HtmlContent += @"
        </table>
"@
        }
    }
    
    # Fermer le HTML
    $HtmlContent += @"
    </div>
</body>
</html>
"@
    
    # Écrire le rapport dans un fichier
    if (-not $ModeSimulation) {
        Set-Content -Path $RapportFile -Value $HtmlContent
    }
    
    Write-Log "Rapport généré: $RapportFile" -Level "SUCCESS"
    return $RapportFile
}

# Fonction principale
function Main {
    Write-Log "Démarrage de l'Organisateur de Fichiers"
    
    # Si les dossiers ne sont pas spécifiés, demander à l'utilisateur
    if (-not $SourceFolder -or -not (Test-Path -Path $SourceFolder)) {
        Write-Log "Dossier source non spécifié ou invalide, demande à l'utilisateur"
        $SourceFolder = Get-FolderFromUser -Message "Sélectionnez le dossier contenant les fichiers à organiser"
        
        if (-not $SourceFolder) {
            Write-Log "Aucun dossier source sélectionné, arrêt du script" -Level "ERROR"
            return
        }
    }
    
    if (-not $DestinationFolder) {
        Write-Log "Dossier destination non spécifié, demande à l'utilisateur"
        $DestinationFolder = Get-FolderFromUser -Message "Sélectionnez le dossier où organiser les fichiers" -DefaultPath $SourceFolder
        
        if (-not $DestinationFolder) {
            Write-Log "Aucun dossier destination sélectionné, arrêt du script" -Level "ERROR"
            return
        }
    }
    
    # Afficher les informations de configuration
    Write-Log "Configuration:"
    Write-Log "  - Dossier source: $SourceFolder"
    Write-Log "  - Dossier destination: $DestinationFolder"
    Write-Log "  - Critère d'organisation: $OrganisationCritere"
    Write-Log "  - Générer rapport: $GenererRapport"
    Write-Log "  - Mode simulation: $ModeSimulation"
    
    if ($ModeSimulation) {
        Write-Log "Mode simulation activé - Aucun fichier ne sera réellement déplacé" -Level "WARNING"
    }
    
    # Organiser les fichiers
    $Stats = Organize-Files -SourcePath $SourceFolder -DestinationPath $DestinationFolder -Critere $OrganisationCritere
    
    # Générer le rapport si demandé
    if ($GenererRapport -and $Stats) {
        $ReportPath = Generate-Report -Stats $Stats -SourcePath $SourceFolder -DestinationPath $DestinationFolder -Critere $OrganisationCritere
        
        # Ouvrir le rapport dans le navigateur par défaut
        if (-not $ModeSimulation -and (Test-Path -Path $ReportPath)) {
            Write-Log "Ouverture du rapport dans le navigateur"
            Start-Process $ReportPath
        }
    }
    
    Write-Log "Script terminé avec succès" -Level "SUCCESS"
}

# Gestion des erreurs
try {
    Main
} catch {
    Write-Log "Erreur non gérée: $_" -Level "ERROR"
    exit 1
}