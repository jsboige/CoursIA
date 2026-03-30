#requires -Version 5.1
<#
.SYNOPSIS
    Script d'automatisation avancé pour la gestion de projets et le traitement de données.

.DESCRIPTION
    Ce script PowerShell démontre des techniques avancées d'automatisation avec Roo:
    - Traitement par lots de fichiers (analyse, transformation, validation)
    - Intégration avec des APIs externes
    - Génération de rapports et visualisations
    - Gestion avancée des erreurs et reprise
    - Logging structuré et notifications
    - Parallélisation des tâches

.PARAMETER ProjectPath
    Chemin vers le répertoire du projet à traiter

.PARAMETER OutputPath
    Chemin où les résultats seront générés

.PARAMETER ApiKey
    Clé API pour les services externes (optionnel)

.PARAMETER LogLevel
    Niveau de détail des logs (Verbose, Info, Warning, Error)

.PARAMETER MaxThreads
    Nombre maximum de threads parallèles à utiliser

.PARAMETER SendNotifications
    Active l'envoi de notifications par email

.EXAMPLE
    .\automatisation-windows.ps1 -ProjectPath "C:\Projets\MonProjet" -OutputPath "C:\Rapports" -LogLevel "Info"

.NOTES
    Auteur: Roo
    Version: 1.0.0
    Date de création: 19/05/2025
#>

param (
    [Parameter(Mandatory = $true)]
    [ValidateScript({ Test-Path $_ -PathType Container })]
    [string]$ProjectPath,
    
    [Parameter(Mandatory = $true)]
    [string]$OutputPath,
    
    [Parameter(Mandatory = $false)]
    [string]$ApiKey = $env:API_KEY,
    
    [Parameter(Mandatory = $false)]
    [ValidateSet("Verbose", "Info", "Warning", "Error")]
    [string]$LogLevel = "Info",
    
    [Parameter(Mandatory = $false)]
    [int]$MaxThreads = 4,
    
    [Parameter(Mandatory = $false)]
    [switch]$SendNotifications = $false
)

#region Configuration et initialisation

# Configuration globale
$script:Config = @{
    ProjectPath      = $ProjectPath
    OutputPath       = $OutputPath
    TempPath         = Join-Path $OutputPath "temp"
    LogPath          = Join-Path $OutputPath "logs"
    ReportPath       = Join-Path $OutputPath "reports"
    ApiEndpoint      = "https://api.example.com/v1"
    ApiKey           = $ApiKey
    MaxRetries       = 3
    RetryDelay       = 5  # secondes
    LogLevel         = $LogLevel
    MaxThreads       = $MaxThreads
    SendNotifications = $SendNotifications
    StartTime        = Get-Date
    ProcessedFiles   = 0
    ErrorCount       = 0
    WarningCount     = 0
}

# Création des répertoires nécessaires
function Initialize-Environment {
    $paths = @($Config.OutputPath, $Config.TempPath, $Config.LogPath, $Config.ReportPath)
    
    foreach ($path in $paths) {
        if (-not (Test-Path -Path $path)) {
            try {
                New-Item -Path $path -ItemType Directory -Force | Out-Null
                Write-Log -Message "Répertoire créé: $path" -Level "Verbose"
            }
            catch {
                Write-Log -Message "Erreur lors de la création du répertoire $path : $_" -Level "Error"
                throw "Échec de l'initialisation de l'environnement"
            }
        }
    }
    
    # Initialisation du fichier de log
    $logFileName = "AutomationLog_$(Get-Date -Format 'yyyyMMdd_HHmmss').log"
    $script:LogFile = Join-Path $Config.LogPath $logFileName
    
    Write-Log -Message "=== Démarrage de l'automatisation ===" -Level "Info"
    Write-Log -Message "Projet: $($Config.ProjectPath)" -Level "Info"
    Write-Log -Message "Sortie: $($Config.OutputPath)" -Level "Info"
    Write-Log -Message "Threads: $($Config.MaxThreads)" -Level "Info"
}

#endregion

#region Logging et gestion des erreurs

# Fonction de logging avancée
function Write-Log {
    param (
        [Parameter(Mandatory = $true)]
        [string]$Message,
        
        [Parameter(Mandatory = $false)]
        [ValidateSet("Verbose", "Info", "Warning", "Error")]
        [string]$Level = "Info",
        
        [Parameter(Mandatory = $false)]
        [switch]$NoConsole = $false
    )
    
    # Vérification du niveau de log
    $logLevels = @{
        "Verbose" = 0
        "Info"    = 1
        "Warning" = 2
        "Error"   = 3
    }
    
    if ($logLevels[$Level] -lt $logLevels[$Config.LogLevel]) {
        return
    }
    
    # Formatage du message
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logEntry = "[$timestamp] [$Level] $Message"
    
    # Écriture dans le fichier de log
    if ($script:LogFile) {
        Add-Content -Path $script:LogFile -Value $logEntry
    }
    
    # Affichage dans la console
    if (-not $NoConsole) {
        $color = switch ($Level) {
            "Verbose" { "Gray" }
            "Info"    { "White" }
            "Warning" { "Yellow" }
            "Error"   { "Red" }
            default   { "White" }
        }
        
        Write-Host $logEntry -ForegroundColor $color
    }
    
    # Mise à jour des compteurs
    if ($Level -eq "Warning") { $script:Config.WarningCount++ }
    if ($Level -eq "Error") { $script:Config.ErrorCount++ }
}

# Fonction de gestion des erreurs avec retry
function Invoke-WithRetry {
    param (
        [Parameter(Mandatory = $true)]
        [scriptblock]$ScriptBlock,
        
        [Parameter(Mandatory = $false)]
        [string]$Operation = "Opération",
        
        [Parameter(Mandatory = $false)]
        [int]$MaxRetries = $Config.MaxRetries,
        
        [Parameter(Mandatory = $false)]
        [int]$RetryDelay = $Config.RetryDelay
    )
    
    $attempt = 1
    $success = $false
    $result = $null
    $lastError = $null
    
    while (-not $success -and $attempt -le $MaxRetries) {
        try {
            if ($attempt -gt 1) {
                Write-Log -Message "Tentative $attempt/$MaxRetries pour: $Operation" -Level "Warning"
                Start-Sleep -Seconds $RetryDelay
            }
            
            $result = & $ScriptBlock
            $success = $true
        }
        catch {
            $lastError = $_
            Write-Log -Message "Échec de $Operation (tentative $attempt/$MaxRetries): $_" -Level "Warning"
            $attempt++
        }
    }
    
    if (-not $success) {
        Write-Log -Message "Échec définitif de $Operation après $MaxRetries tentatives: $lastError" -Level "Error"
        throw "Échec de $Operation: $lastError"
    }
    
    return $result
}

# Fonction d'envoi de notifications
function Send-Notification {
    param (
        [Parameter(Mandatory = $true)]
        [string]$Subject,
        
        [Parameter(Mandatory = $true)]
        [string]$Body,
        
        [Parameter(Mandatory = $false)]
        [string]$Priority = "Normal"
    )
    
    if (-not $Config.SendNotifications) {
        Write-Log -Message "Notification non envoyée (désactivé): $Subject" -Level "Verbose"
        return
    }
    
    try {
        # Simulation d'envoi d'email (à remplacer par votre système de notification)
        Write-Log -Message "Envoi de notification: $Subject" -Level "Info"
        Write-Log -Message "Contenu: $Body" -Level "Verbose"
        
        # Exemple avec Send-MailMessage (nécessite configuration SMTP)
#region Traitement de fichiers

# Fonction pour obtenir tous les fichiers à traiter
function Get-FilesToProcess {
    param (
        [Parameter(Mandatory = $true)]
        [string]$Path,
        
        [Parameter(Mandatory = $false)]
        [string[]]$Extensions = @(".txt", ".csv", ".json", ".xml", ".md", ".log")
    )
    
    try {
        $files = Get-ChildItem -Path $Path -Recurse -File | Where-Object {
            $_.Extension -in $Extensions
        }
        
        Write-Log -Message "Trouvé $($files.Count) fichiers à traiter" -Level "Info"
        return $files
    }
    catch {
        Write-Log -Message "Erreur lors de la recherche des fichiers: $_" -Level "Error"
        throw "Impossible de récupérer les fichiers à traiter"
    }
}

# Fonction d'analyse de fichier
function Analyze-File {
    param (
        [Parameter(Mandatory = $true)]
        [System.IO.FileInfo]$File
    )
    
    Write-Log -Message "Analyse du fichier: $($File.FullName)" -Level "Verbose"
    
    try {
        $result = @{
            FileName = $File.Name
            FilePath = $File.FullName
            FileSize = $File.Length
            Extension = $File.Extension
            LastModified = $File.LastWriteTime
            Content = $null
            Metrics = @{}
            Tags = @()
            Status = "Unknown"
        }
        
        # Lecture et analyse du contenu selon le type de fichier
        switch ($File.Extension) {
            ".txt" {
                $content = Get-Content -Path $File.FullName -Raw
                $result.Content = $content
                $result.Metrics.LineCount = ($content -split "`n").Count
                $result.Metrics.WordCount = ($content -split '\s+').Count
                $result.Status = "Processed"
            }
            ".csv" {
                $csv = Import-Csv -Path $File.FullName
                $result.Metrics.RowCount = $csv.Count
                $result.Metrics.ColumnCount = ($csv | Get-Member -MemberType NoteProperty).Count
                $result.Status = "Processed"
            }
            ".json" {
                $json = Get-Content -Path $File.FullName -Raw | ConvertFrom-Json
                $result.Metrics.ObjectCount = if ($json -is [array]) { $json.Count } else { 1 }
                $result.Status = "Processed"
            }
            ".xml" {
                [xml]$xml = Get-Content -Path $File.FullName
                $result.Metrics.ElementCount = $xml.SelectNodes("//*").Count
                $result.Status = "Processed"
            }
            default {
                $result.Status = "Skipped"
                Write-Log -Message "Type de fichier non pris en charge pour l'analyse détaillée: $($File.Extension)" -Level "Warning"
            }
        }
        
        # Détection de mots-clés et tagging
        if ($result.Content) {
            $keywords = @("important", "urgent", "critique", "révision", "TODO", "FIXME", "BUG")
            foreach ($keyword in $keywords) {
                if ($result.Content -match $keyword) {
                    $result.Tags += $keyword
                }
            }
        }
        
        return $result
    }
    catch {
        Write-Log -Message "Erreur lors de l'analyse du fichier $($File.Name): $_" -Level "Error"
        return @{
            FileName = $File.Name
            FilePath = $File.FullName
            Status = "Error"
            ErrorMessage = $_.ToString()
        }
    }
}

# Fonction de transformation de fichier
function Transform-File {
    param (
        [Parameter(Mandatory = $true)]
        [hashtable]$FileAnalysis,
        
        [Parameter(Mandatory = $false)]
        [hashtable]$TransformationRules = @{}
    )
    
    if ($FileAnalysis.Status -ne "Processed") {
        Write-Log -Message "Impossible de transformer le fichier $($FileAnalysis.FileName): statut $($FileAnalysis.Status)" -Level "Warning"
        return $FileAnalysis
    }
    
    try {
        $outputFile = Join-Path $Config.TempPath "transformed_$($FileAnalysis.FileName)"
        
        Write-Log -Message "Transformation du fichier: $($FileAnalysis.FileName)" -Level "Verbose"
        
        # Appliquer les transformations selon le type de fichier
        switch ($FileAnalysis.Extension) {
            ".txt" {
                $content = $FileAnalysis.Content
                
                # Exemple de transformations
                if ($TransformationRules.ToUpperCase) {
                    $content = $content.ToUpper()
                }
                
                if ($TransformationRules.AddTimestamp) {
                    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
                    $content = "# Processed: $timestamp`n$content"
                }
                
                # Écriture du fichier transformé
                $content | Out-File -FilePath $outputFile -Encoding utf8
            }
            ".csv" {
                $csv = Import-Csv -Path $FileAnalysis.FilePath
                
                # Exemple de transformations sur CSV
                if ($TransformationRules.AddCalculatedColumn) {
                    $csv | ForEach-Object {
                        if ($_.Value1 -and $_.Value2) {
                            $_ | Add-Member -MemberType NoteProperty -Name "Total" -Value ([int]$_.Value1 + [int]$_.Value2)
                        }
                    }
                }
                
                # Écriture du fichier transformé
                $csv | Export-Csv -Path $outputFile -NoTypeInformation -Encoding utf8
            }
            default {
                Write-Log -Message "Transformation non implémentée pour le type $($FileAnalysis.Extension)" -Level "Warning"
                Copy-Item -Path $FileAnalysis.FilePath -Destination $outputFile
            }
        }
        
        $FileAnalysis.TransformedPath = $outputFile
        $FileAnalysis.Status = "Transformed"
        
        return $FileAnalysis
    }
    catch {
        Write-Log -Message "Erreur lors de la transformation du fichier $($FileAnalysis.FileName): $_" -Level "Error"
        $FileAnalysis.Status = "TransformError"
        $FileAnalysis.ErrorMessage = $_.ToString()
        return $FileAnalysis
    }
}

#endregion
        <#
        Send-MailMessage -From "automation@example.com" `
                        -To "admin@example.com" `
                        -Subject $Subject `
                        -Body $Body `
                        -SmtpServer "smtp.example.com" `
                        -Port 587 `
                        -UseSSL `
                        -Credential $emailCredential `
                        -Priority $Priority
        #>
    }
    catch {
        Write-Log -Message "Erreur lors de l'envoi de la notification: $_" -Level "Error"
    }
}

#endregion
#region Intégration API et services externes

# Fonction pour appeler une API externe
function Invoke-ApiRequest {
    param (
        [Parameter(Mandatory = $true)]
        [string]$Endpoint,
        
        [Parameter(Mandatory = $false)]
        [string]$Method = "GET",
        
        [Parameter(Mandatory = $false)]
        [object]$Body = $null,
        
        [Parameter(Mandatory = $false)]
        [hashtable]$Headers = @{},
        
        [Parameter(Mandatory = $false)]
        [switch]$UseApiKey = $true
    )
    
    # Ajout de la clé API si nécessaire
    if ($UseApiKey -and $Config.ApiKey) {
        $Headers["Authorization"] = "Bearer $($Config.ApiKey)"
    }
    
    $Headers["Content-Type"] = "application/json"
    $uri = "$($Config.ApiEndpoint)/$Endpoint"
    
    Write-Log -Message "Appel API: $Method $uri" -Level "Verbose"
    
    try {
        $params = @{
            Uri = $uri
            Method = $Method
            Headers = $Headers
            UseBasicParsing = $true
        }
        
        if ($Body -and $Method -ne "GET") {
            $jsonBody = if ($Body -is [string]) { $Body } else { $Body | ConvertTo-Json -Depth 10 }
            $params.Body = $jsonBody
        }
        
        $response = Invoke-WithRetry -ScriptBlock {
            Invoke-RestMethod @params
        } -Operation "Appel API $Method $Endpoint"
        
        return $response
    }
    catch {
        Write-Log -Message "Erreur API $Method $Endpoint : $_" -Level "Error"
        throw "Échec de l'appel API: $_"
    }
}

# Fonction pour enrichir les données avec des informations externes
function Enrich-Data {
    param (
        [Parameter(Mandatory = $true)]
        [hashtable]$FileAnalysis
    )
    
    if ($FileAnalysis.Status -notin @("Processed", "Transformed")) {
        return $FileAnalysis
    }
    
    try {
        Write-Log -Message "Enrichissement des données pour: $($FileAnalysis.FileName)" -Level "Verbose"
        
        # Exemple d'enrichissement avec des métadonnées supplémentaires
        $FileAnalysis.EnrichmentData = @{
            ProcessedAt = Get-Date
            MachineName = $env:COMPUTERNAME
            ProcessedBy = $env:USERNAME
            Environment = if ($env:ENVIRONMENT) { $env:ENVIRONMENT } else { "Development" }
        }
        
        # Exemple d'enrichissement avec API externe (simulé)
        if ($Config.ApiKey) {
            try {
                # Simulation d'appel API pour enrichissement
                # Dans un cas réel, vous appelleriez une API externe avec Invoke-ApiRequest
                
                <#
                $apiData = Invoke-ApiRequest -Endpoint "enrich" -Method "POST" -Body @{
                    fileName = $FileAnalysis.FileName
                    fileType = $FileAnalysis.Extension
                    tags = $FileAnalysis.Tags
                }
                
                $FileAnalysis.EnrichmentData.ApiClassification = $apiData.classification
                $FileAnalysis.EnrichmentData.ApiTags = $apiData.tags
                $FileAnalysis.EnrichmentData.ApiConfidence = $apiData.confidence
                #>
                
                # Simulation pour l'exemple
                $FileAnalysis.EnrichmentData.ApiClassification = "Document"
                $FileAnalysis.EnrichmentData.ApiTags = @("automatisation", "exemple")
                $FileAnalysis.EnrichmentData.ApiConfidence = 0.85
            }
            catch {
                Write-Log -Message "Erreur lors de l'enrichissement API pour $($FileAnalysis.FileName): $_" -Level "Warning"
            }
        }
        
        $FileAnalysis.Status = "Enriched"
        return $FileAnalysis
    }
    catch {
        Write-Log -Message "Erreur lors de l'enrichissement des données pour $($FileAnalysis.FileName): $_" -Level "Error"
        $FileAnalysis.Status = "EnrichmentError"
        $FileAnalysis.ErrorMessage = $_.ToString()
        return $FileAnalysis
    }
}

#endregion
#region Génération de rapports

# Fonction pour générer un rapport HTML
function Generate-HtmlReport {
    param (
        [Parameter(Mandatory = $true)]
        [array]$ProcessedFiles,
        
        [Parameter(Mandatory = $true)]
        [string]$OutputPath
    )
    
    try {
        Write-Log -Message "Génération du rapport HTML" -Level "Info"
        
        $reportDate = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        $executionTime = (Get-Date) - $Config.StartTime
        $executionTimeFormatted = "{0:hh\:mm\:ss}" -f $executionTime
        
        $successCount = ($ProcessedFiles | Where-Object { $_.Status -in @("Processed", "Transformed", "Enriched") }).Count
        $errorCount = ($ProcessedFiles | Where-Object { $_.Status -like "*Error*" }).Count
        $skippedCount = ($ProcessedFiles | Where-Object { $_.Status -eq "Skipped" }).Count
        
        # Création du contenu HTML
        $html = @"
<!DOCTYPE html>
<html lang="fr">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Rapport d'automatisation - $reportDate</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; color: #333; }
        h1, h2, h3 { color: #2c3e50; }
        .container { max-width: 1200px; margin: 0 auto; }
        .summary { background-color: #f8f9fa; padding: 15px; border-radius: 5px; margin-bottom: 20px; }
        .success { color: #28a745; }
        .warning { color: #ffc107; }
        .error { color: #dc3545; }
        table { width: 100%; border-collapse: collapse; margin-bottom: 20px; }
        th, td { padding: 8px; text-align: left; border-bottom: 1px solid #ddd; }
        th { background-color: #f2f2f2; }
        tr:hover { background-color: #f5f5f5; }
        .status-Processed, .status-Transformed, .status-Enriched { background-color: #d4edda; }
        .status-Skipped { background-color: #fff3cd; }
        .status-Error, .status-TransformError, .status-EnrichmentError { background-color: #f8d7da; }
        .chart-container { width: 100%; height: 300px; margin-bottom: 20px; }
    </style>
</head>
<body>
    <div class="container">
        <h1>Rapport d'automatisation</h1>
        <p>Généré le: $reportDate</p>
        
        <div class="summary">
            <h2>Résumé</h2>
            <p><strong>Projet:</strong> $($Config.ProjectPath)</p>
            <p><strong>Durée d'exécution:</strong> $executionTimeFormatted</p>
            <p><strong>Fichiers traités:</strong> $($ProcessedFiles.Count)</p>
            <p><strong class="success">Succès:</strong> $successCount</p>
            <p><strong class="warning">Ignorés:</strong> $skippedCount</p>
            <p><strong class="error">Erreurs:</strong> $errorCount</p>
        </div>
        
        <h2>Détails des fichiers</h2>
        <table>
            <thead>
                <tr>
                    <th>Nom du fichier</th>
                    <th>Type</th>
                    <th>Taille</th>
                    <th>Statut</th>
                    <th>Tags</th>
                </tr>
            </thead>
            <tbody>
"@

        # Ajout des lignes pour chaque fichier
        foreach ($file in $ProcessedFiles) {
            $statusClass = "status-$($file.Status)"
            $tagsString = if ($file.Tags) { $file.Tags -join ", " } else { "" }
            $sizeFormatted = if ($file.FileSize) { 
                if ($file.FileSize -gt 1MB) {
                    "{0:N2} MB" -f ($file.FileSize / 1MB)
                } elseif ($file.FileSize -gt 1KB) {
                    "{0:N2} KB" -f ($file.FileSize / 1KB)
                } else {
                    "$($file.FileSize) B"
                }
            } else { "N/A" }
            
            $html += @"
                <tr class="$statusClass">
                    <td>$($file.FileName)</td>
                    <td>$($file.Extension)</td>
                    <td>$sizeFormatted</td>
                    <td>$($file.Status)</td>
                    <td>$tagsString</td>
                </tr>
"@
        }

        # Fermeture du tableau et ajout de graphiques
        $html += @"
            </tbody>
        </table>
        
        <h2>Statistiques</h2>
        <div class="chart-container">
            <!-- Ici, vous pourriez intégrer des graphiques avec une bibliothèque JavaScript comme Chart.js -->
            <p>Les graphiques détaillés seraient générés ici dans une implémentation complète.</p>
        </div>
        
        <h2>Logs</h2>
        <p>Fichier de log complet: $($script:LogFile)</p>
    </div>
</body>
</html>
"@

        # Écriture du fichier HTML
        $reportFilePath = Join-Path $OutputPath "AutomationReport_$(Get-Date -Format 'yyyyMMdd_HHmmss').html"
        $html | Out-File -FilePath $reportFilePath -Encoding utf8
        
        Write-Log -Message "Rapport HTML généré: $reportFilePath" -Level "Info"
        return $reportFilePath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération du rapport HTML: $_" -Level "Error"
        throw "Échec de la génération du rapport"
    }
}

# Fonction pour générer un rapport JSON
function Generate-JsonReport {
    param (
        [Parameter(Mandatory = $true)]
        [array]$ProcessedFiles,
        
        [Parameter(Mandatory = $true)]
        [string]$OutputPath
    )
    
    try {
        Write-Log -Message "Génération du rapport JSON" -Level "Info"
        
        $report = @{
            GeneratedAt = Get-Date -Format "o"
            ExecutionTimeSeconds = ((Get-Date) - $Config.StartTime).TotalSeconds
            ProjectPath = $Config.ProjectPath
            Summary = @{
                TotalFiles = $ProcessedFiles.Count
                SuccessCount = ($ProcessedFiles | Where-Object { $_.Status -in @("Processed", "Transformed", "Enriched") }).Count
                ErrorCount = ($ProcessedFiles | Where-Object { $_.Status -like "*Error*" }).Count
                SkippedCount = ($ProcessedFiles | Where-Object { $_.Status -eq "Skipped" }).Count
            }
            Files = $ProcessedFiles | ForEach-Object {
                # Création d'une version simplifiée pour le rapport
                @{
                    FileName = $_.FileName
                    FilePath = $_.FilePath
                    FileSize = $_.FileSize
                    Extension = $_.Extension
                    LastModified = $_.LastModified
                    Status = $_.Status
                    Tags = $_.Tags
                    Metrics = $_.Metrics
                    ErrorMessage = $_.ErrorMessage
                }
            }
            Config = @{
                LogLevel = $Config.LogLevel
                MaxThreads = $Config.MaxThreads
                MaxRetries = $Config.MaxRetries
            }
        }
        
        # Écriture du fichier JSON
        $reportFilePath = Join-Path $OutputPath "AutomationReport_$(Get-Date -Format 'yyyyMMdd_HHmmss').json"
        $report | ConvertTo-Json -Depth 10 | Out-File -FilePath $reportFilePath -Encoding utf8
        
        Write-Log -Message "Rapport JSON généré: $reportFilePath" -Level "Info"
        return $reportFilePath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération du rapport JSON: $_" -Level "Error"
        throw "Échec de la génération du rapport JSON"
    }
}

#endregion
#region Traitement parallèle

# Fonction pour traiter un fichier (pipeline complet)
function Process-FilePipeline {
    param (
        [Parameter(Mandatory = $true)]
        [System.IO.FileInfo]$File
    )
    
    try {
        # Pipeline de traitement
        $analysis = Analyze-File -File $File
        
        if ($analysis.Status -eq "Processed") {
            $transformRules = @{
                ToUpperCase = $false
                AddTimestamp = $true
                AddCalculatedColumn = $true
            }
            
            $transformed = Transform-File -FileAnalysis $analysis -TransformationRules $transformRules
            $enriched = Enrich-Data -FileAnalysis $transformed
            
            return $enriched
        }
        
        return $analysis
    }
    catch {
        Write-Log -Message "Erreur dans le pipeline de traitement pour $($File.Name): $_" -Level "Error"
        return @{
            FileName = $File.Name
            FilePath = $File.FullName
            Status = "PipelineError"
            ErrorMessage = $_.ToString()
        }
    }
}

# Fonction pour exécuter le traitement en parallèle
function Invoke-ParallelProcessing {
    param (
        [Parameter(Mandatory = $true)]
        [System.IO.FileInfo[]]$Files
    )
    
    Write-Log -Message "Démarrage du traitement parallèle pour $($Files.Count) fichiers avec $($Config.MaxThreads) threads" -Level "Info"
    
    try {
        # Utilisation de jobs PowerShell pour le traitement parallèle
        $jobs = @()
        $results = @()
        $processedCount = 0
        $totalFiles = $Files.Count
        
        # Traitement par lots pour éviter de créer trop de jobs simultanément
        $batchSize = [Math]::Min($Config.MaxThreads * 2, $totalFiles)
        $batches = [Math]::Ceiling($totalFiles / $batchSize)
        
        for ($batchIndex = 0; $batchIndex -lt $batches; $batchIndex++) {
            $start = $batchIndex * $batchSize
            $end = [Math]::Min($start + $batchSize - 1, $totalFiles - 1)
            $batchFiles = $Files[$start..$end]
            
            Write-Log -Message "Traitement du lot $($batchIndex + 1)/$batches ($($batchFiles.Count) fichiers)" -Level "Info"
            
            # Création des jobs pour ce lot
            foreach ($file in $batchFiles) {
                $jobScript = {
                    param($filePath, $configPath)
                    
                    # Charger le script pour avoir accès aux fonctions
                    # Note: Dans une implémentation réelle, vous utiliseriez un module
                    $scriptContent = Get-Content -Path $configPath.ScriptPath -Raw
                    $null = New-Module -ScriptBlock ([ScriptBlock]::Create($scriptContent)) -AsCustomObject
                    
                    # Exécuter le pipeline de traitement
                    $file = Get-Item -Path $filePath
                    $result = Process-FilePipeline -File $file
                    return $result
                }
                
                # Configuration à passer au job
                $jobConfig = @{
                    ScriptPath = $PSCommandPath
                    Config = $Config
                }
                
                # Démarrage du job
                $job = Start-Job -ScriptBlock $jobScript -ArgumentList $file.FullName, $jobConfig
                $jobs += $job
                
                # Limiter le nombre de jobs simultanés
                if ($jobs.Count -ge $Config.MaxThreads) {
                    $completedJob = $jobs | Wait-Job -Any
                    $jobResult = $completedJob | Receive-Job
                    $results += $jobResult
                    $completedJob | Remove-Job
                    $jobs = $jobs | Where-Object { $_ -ne $completedJob }
                    
                    $processedCount++
                    Write-Progress -Activity "Traitement des fichiers" -Status "$processedCount / $totalFiles fichiers traités" -PercentComplete (($processedCount / $totalFiles) * 100)
                }
            }
            
            # Attendre que tous les jobs du lot soient terminés
            while ($jobs.Count -gt 0) {
                $completedJob = $jobs | Wait-Job -Any
                $jobResult = $completedJob | Receive-Job
                $results += $jobResult
                $completedJob | Remove-Job
                $jobs = $jobs | Where-Object { $_ -ne $completedJob }
                
                $processedCount++
                Write-Progress -Activity "Traitement des fichiers" -Status "$processedCount / $totalFiles fichiers traités" -PercentComplete (($processedCount / $totalFiles) * 100)
            }
        }
        
        Write-Progress -Activity "Traitement des fichiers" -Completed
        Write-Log -Message "Traitement parallèle terminé: $($results.Count) fichiers traités" -Level "Info"
        
        return $results
    }
    catch {
        Write-Log -Message "Erreur lors du traitement parallèle: $_" -Level "Error"
        throw "Échec du traitement parallèle: $_"
    }
}

#endregion

#region Fonction principale

# Fonction principale d'exécution
function Start-Automation {
    param (
        [Parameter(Mandatory = $false)]
        [switch]$GenerateHtmlReport = $true,
        
        [Parameter(Mandatory = $false)]
        [switch]$GenerateJsonReport = $true
    )
    
    try {
        # Initialisation
        Initialize-Environment
        
        # Notification de démarrage
        if ($Config.SendNotifications) {
            Send-Notification -Subject "Démarrage de l'automatisation" -Body "Traitement démarré pour le projet: $($Config.ProjectPath)" -Priority "Normal"
        }
        
        # Récupération des fichiers à traiter
        $files = Get-FilesToProcess -Path $Config.ProjectPath
        
        if ($files.Count -eq 0) {
            Write-Log -Message "Aucun fichier à traiter trouvé dans $($Config.ProjectPath)" -Level "Warning"
            return
        }
        
        # Traitement des fichiers
        $processedFiles = if ($Config.MaxThreads -gt 1) {
            Invoke-ParallelProcessing -Files $files
        }
        else {
            # Traitement séquentiel si un seul thread est demandé
            $results = @()
            $fileCount = $files.Count
            $currentFile = 0
            
            foreach ($file in $files) {
                $currentFile++
                Write-Progress -Activity "Traitement des fichiers" -Status "$currentFile / $fileCount" -PercentComplete (($currentFile / $fileCount) * 100)
                $results += Process-FilePipeline -File $file
            }
            
            Write-Progress -Activity "Traitement des fichiers" -Completed
            $results
        }
        
        # Mise à jour des statistiques
        $Config.ProcessedFiles = $processedFiles.Count
        $Config.ErrorCount = ($processedFiles | Where-Object { $_.Status -like "*Error*" }).Count
        
        # Génération des rapports
        $reportPaths = @()
        
        if ($GenerateHtmlReport) {
            $htmlReportPath = Generate-HtmlReport -ProcessedFiles $processedFiles -OutputPath $Config.ReportPath
            $reportPaths += $htmlReportPath
        }
        
        if ($GenerateJsonReport) {
            $jsonReportPath = Generate-JsonReport -ProcessedFiles $processedFiles -OutputPath $Config.ReportPath
            $reportPaths += $jsonReportPath
        }
        
        # Notification de fin
        if ($Config.SendNotifications) {
            $subject = if ($Config.ErrorCount -gt 0) {
                "Automatisation terminée avec $($Config.ErrorCount) erreurs"
            }
            else {
                "Automatisation terminée avec succès"
            }
            
            $body = @"
Traitement terminé pour le projet: $($Config.ProjectPath)
Fichiers traités: $($Config.ProcessedFiles)
Erreurs: $($Config.ErrorCount)
Durée: $([math]::Round(((Get-Date) - $Config.StartTime).TotalMinutes, 2)) minutes
Rapports générés: $($reportPaths -join ", ")
"@
            
            $priority = if ($Config.ErrorCount -gt 0) { "High" } else { "Normal" }
            Send-Notification -Subject $subject -Body $body -Priority $priority
        }
        
        # Résumé final
        Write-Log -Message "=== Automatisation terminée ===" -Level "Info"
        Write-Log -Message "Fichiers traités: $($Config.ProcessedFiles)" -Level "Info"
        Write-Log -Message "Erreurs: $($Config.ErrorCount)" -Level "Info"
        Write-Log -Message "Avertissements: $($Config.WarningCount)" -Level "Info"
        Write-Log -Message "Durée: $([math]::Round(((Get-Date) - $Config.StartTime).TotalMinutes, 2)) minutes" -Level "Info"
        Write-Log -Message "Rapports générés: $($reportPaths -join ", ")" -Level "Info"
        
        return @{
            ProcessedFiles = $processedFiles
            ReportPaths = $reportPaths
            Summary = @{
                TotalFiles = $Config.ProcessedFiles
                ErrorCount = $Config.ErrorCount
                WarningCount = $Config.WarningCount
                Duration = ((Get-Date) - $Config.StartTime)
            }
        }
    }
    catch {
        Write-Log -Message "Erreur critique lors de l'automatisation: $_" -Level "Error"
        
        if ($Config.SendNotifications) {
            Send-Notification -Subject "ERREUR CRITIQUE - Échec de l'automatisation" -Body "Une erreur critique est survenue: $_" -Priority "High"
        }
        
        throw "Échec de l'automatisation: $_"
    }
}

#endregion

# Exécution du script si appelé directement
if ($MyInvocation.InvocationName -ne ".") {
    # Exécution de l'automatisation avec les paramètres fournis
    $result = Start-Automation
    
    # Affichage du résumé
    Write-Host "`nRésumé de l'exécution:" -ForegroundColor Cyan
    Write-Host "- Fichiers traités: $($result.Summary.TotalFiles)" -ForegroundColor White
    Write-Host "- Erreurs: $($result.Summary.ErrorCount)" -ForegroundColor $(if ($result.Summary.ErrorCount -gt 0) { "Red" } else { "Green" })
    Write-Host "- Avertissements: $($result.Summary.WarningCount)" -ForegroundColor $(if ($result.Summary.WarningCount -gt 0) { "Yellow" } else { "Green" })
    Write-Host "- Durée: $([math]::Round($result.Summary.Duration.TotalMinutes, 2)) minutes" -ForegroundColor White
    
    if ($result.ReportPaths.Count -gt 0) {
        Write-Host "`nRapports générés:" -ForegroundColor Cyan
        foreach ($reportPath in $result.ReportPaths) {
            Write-Host "- $reportPath" -ForegroundColor White
        }
    }
}