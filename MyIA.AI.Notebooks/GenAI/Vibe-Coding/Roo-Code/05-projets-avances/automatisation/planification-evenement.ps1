#requires -Version 5.1
<#
.SYNOPSIS
    Script d'automatisation pour la planification d'un événement d'entreprise.

.DESCRIPTION
    Ce script PowerShell automatise la planification d'un événement d'entreprise avec les fonctionnalités suivantes:
    - Création automatique d'une structure de dossiers pour organiser les documents
    - Génération de documents de base (agenda, liste de participants, budget prévisionnel)
    - Création d'un tableau de bord pour suivre l'avancement de la planification
    - Intégration avec des outils externes (génération de calendrier, notifications)
    - Gestion des tâches et des échéances

.PARAMETER EventName
    Nom de l'événement à planifier

.PARAMETER EventDate
    Date de l'événement (format: YYYY-MM-DD)

.PARAMETER OutputPath
    Chemin où les fichiers de l'événement seront générés

.PARAMETER ParticipantsCount
    Nombre estimé de participants (par défaut: 50)

.PARAMETER BudgetTotal
    Budget total disponible pour l'événement (par défaut: 10000)

.PARAMETER SendNotifications
    Active l'envoi de notifications par email

.EXAMPLE
    .\planification-evenement.ps1 -EventName "Conférence Annuelle 2025" -EventDate "2025-09-15" -OutputPath "C:\Evenements"

.NOTES
    Auteur: Roo
    Version: 1.0.0
    Date de création: 20/05/2025
#>

param (
    [Parameter(Mandatory = $true)]
    [string]$EventName,
    
    [Parameter(Mandatory = $true)]
    [ValidatePattern("^\d{4}-\d{2}-\d{2}$")]
    [string]$EventDate,
    
    [Parameter(Mandatory = $true)]
    [string]$OutputPath,
    
    [Parameter(Mandatory = $false)]
    [int]$ParticipantsCount = 50,
    
    [Parameter(Mandatory = $false)]
    [decimal]$BudgetTotal = 10000,
    
    [Parameter(Mandatory = $false)]
    [switch]$SendNotifications = $false
)
#region Configuration et initialisation

# Configuration globale
$script:Config = @{
    EventName        = $EventName
    EventDate        = [datetime]::ParseExact($EventDate, "yyyy-MM-dd", $null)
    OutputPath       = $OutputPath
    EventFolder      = Join-Path $OutputPath ($EventName -replace '[\\/:*?"<>|]', '_')
    ParticipantsCount = $ParticipantsCount
    BudgetTotal      = $BudgetTotal
    SendNotifications = $SendNotifications
    StartTime        = Get-Date
    DaysUntilEvent   = 0
    TasksTotal       = 0
    TasksCompleted   = 0
}

# Calcul du nombre de jours jusqu'à l'événement
$Config.DaysUntilEvent = ($Config.EventDate - (Get-Date)).Days

# Structure des dossiers à créer
$script:FolderStructure = @(
    "01-Administration",
    "02-Logistique",
    "03-Programme",
    "04-Communication",
    "05-Budget",
    "06-Participants",
    "07-Présentations",
    "08-Médias",
    "09-Évaluation",
    "10-Archives"
)

# Structure des tâches principales
$script:MainTasks = @(
    @{
        Name = "Planification initiale"
        Deadline = -90 # Jours avant l'événement
        SubTasks = @(
            @{ Name = "Définir les objectifs de l'événement"; Status = "À faire" },
            @{ Name = "Établir le budget prévisionnel"; Status = "À faire" },
            @{ Name = "Sélectionner la date et le lieu"; Status = "À faire" },
            @{ Name = "Constituer l'équipe organisatrice"; Status = "À faire" }
        )
    },
    @{
        Name = "Logistique"
        Deadline = -60
        SubTasks = @(
            @{ Name = "Réserver le lieu"; Status = "À faire" },
            @{ Name = "Organiser la restauration"; Status = "À faire" },
            @{ Name = "Planifier l'hébergement"; Status = "À faire" },
            @{ Name = "Organiser le transport"; Status = "À faire" }
        )
    },
    @{
        Name = "Programme et contenu"
        Deadline = -45
        SubTasks = @(
            @{ Name = "Définir le programme détaillé"; Status = "À faire" },
            @{ Name = "Contacter les intervenants"; Status = "À faire" },
            @{ Name = "Planifier les ateliers"; Status = "À faire" },
            @{ Name = "Préparer les supports"; Status = "À faire" }
        )
    },
    @{
        Name = "Communication"
        Deadline = -30
        SubTasks = @(
            @{ Name = "Créer les supports de communication"; Status = "À faire" },
            @{ Name = "Envoyer les invitations"; Status = "À faire" },
            @{ Name = "Mettre en place l'inscription en ligne"; Status = "À faire" },
            @{ Name = "Communiquer sur les réseaux sociaux"; Status = "À faire" }
        )
    },
    @{
        Name = "Finalisation"
        Deadline = -7
        SubTasks = @(
            @{ Name = "Confirmer avec tous les prestataires"; Status = "À faire" },
            @{ Name = "Préparer les badges et la documentation"; Status = "À faire" },
            @{ Name = "Briefer l'équipe organisatrice"; Status = "À faire" },
            @{ Name = "Vérifier tous les aspects techniques"; Status = "À faire" }
        )
    },
    @{
        Name = "Jour J"
        Deadline = 0
        SubTasks = @(
            @{ Name = "Installation et préparation"; Status = "À faire" },
            @{ Name = "Accueil des participants"; Status = "À faire" },
            @{ Name = "Coordination des activités"; Status = "À faire" },
            @{ Name = "Gestion des imprévus"; Status = "À faire" }
        )
    },
    @{
        Name = "Après l'événement"
        Deadline = 7
        SubTasks = @(
            @{ Name = "Envoyer les remerciements"; Status = "À faire" },
            @{ Name = "Collecter les retours"; Status = "À faire" },
            @{ Name = "Analyser le budget final"; Status = "À faire" },
            @{ Name = "Rédiger le bilan"; Status = "À faire" }
        )
    }
)

# Calcul du nombre total de tâches
foreach ($task in $MainTasks) {
    $Config.TasksTotal += $task.SubTasks.Count
}

# Fonction d'initialisation
function Initialize-EventEnvironment {
    # Création du dossier principal de l'événement
    if (-not (Test-Path -Path $Config.EventFolder)) {
        try {
            New-Item -Path $Config.EventFolder -ItemType Directory -Force | Out-Null
            Write-Log -Message "Dossier principal créé: $($Config.EventFolder)" -Level "Info"
        }
        catch {
            Write-Log -Message "Erreur lors de la création du dossier principal: $_" -Level "Error"
            throw "Echec de l'initialisation de l'environnement"
        }
    }
    
    # Création de la structure de dossiers
    foreach ($folder in $FolderStructure) {
        $folderPath = Join-Path $Config.EventFolder $folder
        if (-not (Test-Path -Path $folderPath)) {
            try {
                New-Item -Path $folderPath -ItemType Directory -Force | Out-Null
                Write-Log -Message "Dossier créé: $folder" -Level "Verbose"
            }
            catch {
                Write-Log -Message "Erreur lors de la création du dossier $folder : $_" -Level "Error"
            }
        }
    }
    
    # Initialisation du fichier de log
    $logFileName = "EventPlanning_$(Get-Date -Format 'yyyyMMdd_HHmmss').log"
    $script:LogFile = Join-Path $Config.EventFolder $logFileName
    
    Write-Log -Message "=== Démarrage de la planification de l'événement ===" -Level "Info"
    Write-Log -Message "Événement: $($Config.EventName)" -Level "Info"
    Write-Log -Message "Date: $($Config.EventDate.ToString('dd/MM/yyyy'))" -Level "Info"
    Write-Log -Message "Jours restants: $($Config.DaysUntilEvent)" -Level "Info"
    Write-Log -Message "Participants estimés: $($Config.ParticipantsCount)" -Level "Info"
    Write-Log -Message "Budget total: $($Config.BudgetTotal) €" -Level "Info"
}

#endregion
#region Logging et gestion des erreurs

# Fonction de logging
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
}

# Fonction de gestion des erreurs avec retry
function Invoke-WithRetry {
    param (
        [Parameter(Mandatory = $true)]
        [scriptblock]$ScriptBlock,
        
        [Parameter(Mandatory = $false)]
        [string]$Operation = "Opération",
        
        [Parameter(Mandatory = $false)]
        [int]$MaxRetries = 3,
        
        [Parameter(Mandatory = $false)]
        [int]$RetryDelay = 5
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
            Write-Log -Message "Echec de $Operation (tentative $attempt/$MaxRetries): $_" -Level "Warning"
            $attempt++
        }
    }
    
    if (-not $success) {
        Write-Log -Message "Echec définitif de $Operation après $MaxRetries tentatives: $lastError" -Level "Error"
        throw "Echec de $Operation`: $lastError"
    }
    
    return $result
}

# Fonction d'envoi de notifications
function Send-EventNotification {
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
        # Simulation d'envoi d'email
        Write-Log -Message "Envoi de notification: $Subject" -Level "Info"
        Write-Log -Message "Contenu: $Body" -Level "Verbose"
        
        # Exemple avec Send-MailMessage (nécessite configuration SMTP)
        <#
        Send-MailMessage -From "evenements@example.com" `
                        -To "organisateurs@example.com" `
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
#region Génération de documents

# Fonction pour générer l'agenda de l'événement
function Generate-EventAgenda {
    param (
        [Parameter(Mandatory = $true)]
        [string]$OutputPath
    )
    
    try {
        Write-Log -Message "Génération de l'agenda de l'événement" -Level "Info"
        
        $eventDate = $Config.EventDate
        $eventDateStr = $eventDate.ToString("dd/MM/yyyy")
        
        # Création du contenu de l'agenda
        $agendaContent = @"
# Agenda: $($Config.EventName)
Date: $eventDateStr

## Programme de la journée

### Matinée

| Horaire | Activité | Lieu | Intervenant |
|---------|----------|------|-------------|
| 08:30 - 09:00 | Accueil et enregistrement | Hall d'entrée | Équipe d'accueil |
| 09:00 - 09:30 | Discours d'ouverture | Salle principale | Directeur Général |
| 09:30 - 10:30 | Présentation principale | Salle principale | Intervenant principal |
| 10:30 - 11:00 | Pause café | Espace détente | - |
| 11:00 - 12:30 | Sessions parallèles | Salles A, B et C | Divers intervenants |

### Déjeuner

| Horaire | Activité | Lieu |
|---------|----------|------|
| 12:30 - 14:00 | Déjeuner networking | Restaurant |

### Après-midi

| Horaire | Activité | Lieu | Intervenant |
|---------|----------|------|-------------|
| 14:00 - 15:30 | Ateliers pratiques | Salles de workshop | Animateurs d'ateliers |
| 15:30 - 16:00 | Pause café | Espace détente | - |
| 16:00 - 17:00 | Table ronde | Salle principale | Panel d'experts |
| 17:00 - 17:30 | Conclusion et prochaines étapes | Salle principale | Directeur de projet |
| 17:30 - 19:00 | Cocktail de clôture | Terrasse | - |

## Informations pratiques

- Wifi disponible: Réseau "Event_Network", mot de passe fourni à l'accueil
- Points de recharge pour appareils électroniques disponibles dans chaque salle
- Équipe d'assistance disponible tout au long de la journée (badges rouges)

## Sessions parallèles (11:00 - 12:30)

### Salle A: Innovation et Tendances
Animé par: Expert Innovation
Description: Découvrez les dernières tendances et innovations du secteur.

### Salle B: Stratégies de Développement
Animé par: Consultant Stratégie
Description: Atelier pratique sur l'élaboration de stratégies efficaces.

### Salle C: Retours d'Expérience
Animé par: Panel de clients
Description: Témoignages et études de cas de projets réussis.

## Ateliers pratiques (14:00 - 15:30)

### Workshop 1: Implémentation Technique
Animé par: Équipe technique
Prérequis: Connaissances de base en programmation

### Workshop 2: Optimisation des Processus
Animé par: Consultant en organisation
Prérequis: Aucun, ouvert à tous

### Workshop 3: Certification et Conformité
Animé par: Responsable qualité
Prérequis: Connaissance des normes du secteur

---

*Ce programme est susceptible de modifications. La version finale sera distribuée le jour de l'événement.*
"@
        
        # Écriture du fichier agenda
        $agendaPath = Join-Path $OutputPath "03-Programme\agenda.md"
        $agendaContent | Out-File -FilePath $agendaPath -Encoding utf8
        
        Write-Log -Message "Agenda généré: $agendaPath" -Level "Info"
        return $agendaPath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération de l'agenda: $_" -Level "Error"
        throw "Echec de la génération de l'agenda"
    }
}

# Fonction pour générer la liste des participants
function Generate-ParticipantsList {
    param (
        [Parameter(Mandatory = $true)]
        [string]$OutputPath,
        
        [Parameter(Mandatory = $true)]
        [int]$ParticipantsCount
    )
    
    try {
        Write-Log -Message "Génération de la liste des participants" -Level "Info"
        
        # Création du contenu de la liste des participants
        $participantsContent = @"
# Liste des participants: $($Config.EventName)
Date: $($Config.EventDate.ToString("dd/MM/yyyy"))
Nombre de participants estimé: $ParticipantsCount

## Tableau de suivi des inscriptions

| # | Nom | Prénom | Entreprise | Fonction | Email | Téléphone | Statut | Besoins spécifiques |
|---|-----|--------|------------|----------|-------|-----------|--------|---------------------|
"@
        
        # Ajout de lignes vides pour remplissage manuel
        for ($i = 1; $i -le $ParticipantsCount; $i++) {
            $participantsContent += "`n| $i | | | | | | | À confirmer | |"
        }
        
        $participantsContent += @"

## Statistiques des inscriptions

- Inscriptions confirmées: 0
- En attente de confirmation: $ParticipantsCount
- Désistements: 0

## Catégories de participants

- VIP: 0
- Intervenants: 0
- Participants standard: $ParticipantsCount
- Presse/Médias: 0
- Staff: 0

## Instructions pour l'équipe d'accueil

1. Vérifier l'identité de chaque participant
2. Remettre le badge et le kit de bienvenue
3. Indiquer l'emplacement des vestiaires et sanitaires
4. Orienter vers la salle principale
5. Noter les besoins spécifiques et les transmettre au responsable

## Gestion des imprévus

- Participants non inscrits: Procéder à l'inscription sur place si places disponibles
- Perte de badge: Émettre un badge temporaire après vérification d'identité
- Demandes spéciales: Rediriger vers le responsable de l'événement

---

*Document à usage interne - Mise à jour régulière nécessaire*
"@
        
        # Écriture du fichier de liste des participants
        $participantsPath = Join-Path $OutputPath "06-Participants\liste-participants.md"
        $participantsContent | Out-File -FilePath $participantsPath -Encoding utf8
        
        Write-Log -Message "Liste des participants générée: $participantsPath" -Level "Info"
        return $participantsPath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération de la liste des participants: $_" -Level "Error"
        throw "Echec de la génération de la liste des participants"
    }
}

# Fonction pour générer le budget prévisionnel
function Generate-BudgetPlan {
    param (
        [Parameter(Mandatory = $true)]
        [string]$OutputPath,
        
        [Parameter(Mandatory = $true)]
        [decimal]$BudgetTotal,
        
        [Parameter(Mandatory = $true)]
        [int]$ParticipantsCount
    )
    
    try {
        Write-Log -Message "Génération du budget prévisionnel" -Level "Info"
        
        # Calcul des postes budgétaires
        $locationBudget = [Math]::Round($BudgetTotal * 0.30, 2)
        $cateringBudget = [Math]::Round($BudgetTotal * 0.25, 2)
        $speakersBudget = [Math]::Round($BudgetTotal * 0.15, 2)
        $marketingBudget = [Math]::Round($BudgetTotal * 0.10, 2)
        $staffBudget = [Math]::Round($BudgetTotal * 0.08, 2)
        $materialsBudget = [Math]::Round($BudgetTotal * 0.07, 2)
        $contingencyBudget = [Math]::Round($BudgetTotal * 0.05, 2)
        
        $cateringPerPerson = [Math]::Round($cateringBudget / $ParticipantsCount, 2)
        $materialsPerPerson = [Math]::Round($materialsBudget / $ParticipantsCount, 2)
        
        # Création du contenu du budget
        $budgetContent = @"
# Budget prévisionnel: $($Config.EventName)
Date: $($Config.EventDate.ToString("dd/MM/yyyy"))
Participants estimés: $ParticipantsCount
Budget total: $BudgetTotal €

## Répartition du budget

| Poste de dépense | Montant (€) | % du budget | Détails |
|------------------|-------------|------------|---------|
| Location et logistique | $locationBudget € | 30% | Salle, équipement technique, mobilier |
| Restauration | $cateringBudget € | 25% | Café d'accueil, pauses, déjeuner, cocktail |
| Intervenants | $speakersBudget € | 15% | Honoraires, transport, hébergement |
| Marketing et communication | $marketingBudget € | 10% | Invitations, signalétique, supports de communication |
| Personnel | $staffBudget € | 8% | Hôtesses, techniciens, sécurité |
| Matériel et documentation | $materialsBudget € | 7% | Badges, kits participants, impression |
| Imprévus | $contingencyBudget € | 5% | Réserve pour dépenses non planifiées |
| **TOTAL** | **$BudgetTotal €** | **100%** | |

## Détails par participant

- Coût par participant: $([Math]::Round($BudgetTotal / $ParticipantsCount, 2)) €
- Restauration par participant: $cateringPerPerson €
- Matériel par participant: $materialsPerPerson €

## Détail des postes budgétaires

### Location et logistique ($locationBudget €)
- Location de salle: $([Math]::Round($locationBudget * 0.60, 2)) €
- Équipement audiovisuel: $([Math]::Round($locationBudget * 0.25, 2)) €
- Mobilier et décoration: $([Math]::Round($locationBudget * 0.15, 2)) €

### Restauration ($cateringBudget €)
- Café d'accueil: $([Math]::Round($cateringBudget * 0.10, 2)) €
- Pauses café: $([Math]::Round($cateringBudget * 0.15, 2)) €
- Déjeuner: $([Math]::Round($cateringBudget * 0.50, 2)) €
- Cocktail de clôture: $([Math]::Round($cateringBudget * 0.25, 2)) €

### Intervenants ($speakersBudget €)
- Honoraires: $([Math]::Round($speakersBudget * 0.60, 2)) €
- Transport: $([Math]::Round($speakersBudget * 0.25, 2)) €
- Hébergement: $([Math]::Round($speakersBudget * 0.15, 2)) €

### Marketing et communication ($marketingBudget €)
- Conception graphique: $([Math]::Round($marketingBudget * 0.30, 2)) €
- Impression: $([Math]::Round($marketingBudget * 0.25, 2)) €
- Signalétique: $([Math]::Round($marketingBudget * 0.25, 2)) €
- Communication digitale: $([Math]::Round($marketingBudget * 0.20, 2)) €

### Personnel ($staffBudget €)
- Équipe d'accueil: $([Math]::Round($staffBudget * 0.40, 2)) €
- Support technique: $([Math]::Round($staffBudget * 0.40, 2)) €
- Coordination: $([Math]::Round($staffBudget * 0.20, 2)) €

### Matériel et documentation ($materialsBudget €)
- Badges et lanyards: $([Math]::Round($materialsBudget * 0.20, 2)) €
- Kits participants: $([Math]::Round($materialsBudget * 0.40, 2)) €
- Impression documents: $([Math]::Round($materialsBudget * 0.30, 2)) €
- Signalétique: $([Math]::Round($materialsBudget * 0.10, 2)) €

## Suivi budgétaire

| Poste | Budget prévu | Dépenses engagées | Reste à engager | % consommé |
|-------|-------------|-------------------|----------------|-----------|
| Location et logistique | $locationBudget € | 0 € | $locationBudget € | 0% |
| Restauration | $cateringBudget € | 0 € | $cateringBudget € | 0% |
| Intervenants | $speakersBudget € | 0 € | $speakersBudget € | 0% |
| Marketing et communication | $marketingBudget € | 0 € | $marketingBudget € | 0% |
| Personnel | $staffBudget € | 0 € | $staffBudget € | 0% |
| Matériel et documentation | $materialsBudget € | 0 € | $materialsBudget € | 0% |
| Imprévus | $contingencyBudget € | 0 € | $contingencyBudget € | 0% |
| **TOTAL** | **$BudgetTotal €** | **0 €** | **$BudgetTotal €** | **0%** |

## Notes et recommandations

- Rechercher des sponsors pour réduire les coûts
- Négocier des tarifs préférentiels pour les réservations anticipées
- Prévoir une marge de sécurité pour les variations de nombre de participants
- Suivre régulièrement les dépenses engagées

---

*Document de travail - Mise à jour: $(Get-Date -Format "dd/MM/yyyy")*
"@
        
        # Écriture du fichier budget
        $budgetPath = Join-Path $OutputPath "05-Budget\budget-previsionnel.md"
        $budgetContent | Out-File -FilePath $budgetPath -Encoding utf8
        
        Write-Log -Message "Budget prévisionnel généré: $budgetPath" -Level "Info"
        return $budgetPath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération du budget prévisionnel: $_" -Level "Error"
        throw "Echec de la génération du budget prévisionnel"
    }
}

#endregion
#region Tableau de bord et intégration externe

# Fonction pour générer le tableau de bord de suivi
function Generate-Dashboard {
    param (
        [Parameter(Mandatory = $true)]
        [string]$OutputPath
    )
    
    try {
        Write-Log -Message "Génération du tableau de bord de suivi" -Level "Info"
        
        # Calcul des statistiques
        $daysUntilEvent = $Config.DaysUntilEvent
        $completionPercentage = 0
        
        # Création du contenu du tableau de bord
        $dashboardContent = @"
# Tableau de bord: $($Config.EventName)
Date de l'événement: $($Config.EventDate.ToString("dd/MM/yyyy"))
Jours restants: **$daysUntilEvent**
Mise à jour: $(Get-Date -Format "dd/MM/yyyy HH:mm")

## Résumé de l'événement

- **Nom**: $($Config.EventName)
- **Date**: $($Config.EventDate.ToString("dd/MM/yyyy"))
- **Participants attendus**: $($Config.ParticipantsCount)
- **Budget total**: $($Config.BudgetTotal) €

## État d'avancement global

- Tâches totales: $($Config.TasksTotal)
- Tâches complétées: $($Config.TasksCompleted)
- Progression: $([Math]::Round(($Config.TasksCompleted / $Config.TasksTotal) * 100, 1))%

## Planning des tâches principales

| Phase | Deadline | Jours restants | Progression | Statut |
|-------|----------|----------------|------------|--------|
"@
        
        # Ajout des tâches principales
        foreach ($task in $MainTasks) {
            $taskDeadline = $Config.EventDate.AddDays($task.Deadline)
            $daysUntilDeadline = ($taskDeadline - (Get-Date)).Days
            
            # Calcul de la progression pour cette tâche
            $completedSubTasks = ($task.SubTasks | Where-Object { $_.Status -ne "À faire" }).Count
            $totalSubTasks = $task.SubTasks.Count
            $taskProgress = if ($totalSubTasks -gt 0) { [Math]::Round(($completedSubTasks / $totalSubTasks) * 100, 0) } else { 0 }
            
            # Détermination du statut
            $status = if ($taskProgress -eq 100) {
                "Terminé"
            } elseif ($daysUntilDeadline -lt 0) {
                "En retard"
            } elseif ($daysUntilDeadline -lt 7) {
                "Urgent"
            } else {
                "En cours"
            }
            
            # Ajout de la ligne au tableau
            $dashboardContent += "`n| $($task.Name) | $($taskDeadline.ToString('dd/MM/yyyy')) | $daysUntilDeadline | $taskProgress% | $status |"
        }
        
        # Ajout des détails des sous-tâches
        $dashboardContent += @"

## Détail des tâches

"@
        
        foreach ($task in $MainTasks) {
            $dashboardContent += @"

### $($task.Name)

| Tâche | Statut | Responsable | Notes |
|-------|--------|-------------|-------|
"@
            
            foreach ($subTask in $task.SubTasks) {
                $dashboardContent += "`n| $($subTask.Name) | $($subTask.Status) | | |"
            }
        }
        
        # Ajout des indicateurs clés
        $dashboardContent += @"

## Indicateurs clés

- **Budget**: $($Config.BudgetTotal) € (0% consommé)
- **Inscriptions**: 0 / $($Config.ParticipantsCount) (0%)
- **Intervenants confirmés**: 0
- **Documents préparés**: 3 / 10 (30%)

## Prochaines étapes critiques

1. Finaliser la réservation du lieu
2. Confirmer les intervenants principaux
3. Lancer les invitations
4. Finaliser le programme détaillé

---

*Tableau de bord généré automatiquement le $(Get-Date -Format "dd/MM/yyyy à HH:mm")*
"@
        
        # Écriture du fichier de tableau de bord
        $dashboardPath = Join-Path $OutputPath "tableau-de-bord.md"
        $dashboardContent | Out-File -FilePath $dashboardPath -Encoding utf8
        
        Write-Log -Message "Tableau de bord généré: $dashboardPath" -Level "Info"
        return $dashboardPath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération du tableau de bord: $_" -Level "Error"
        throw "Echec de la génération du tableau de bord"
    }
}

# Fonction pour générer un fichier de calendrier ICS
function Generate-CalendarFile {
    param (
        [Parameter(Mandatory = $true)]
        [string]$OutputPath,
        
        [Parameter(Mandatory = $true)]
        [datetime]$EventDate,
        
        [Parameter(Mandatory = $true)]
        [string]$EventName,
        
        [Parameter(Mandatory = $false)]
        [string]$EventLocation = "À déterminer",
        
        [Parameter(Mandatory = $false)]
        [string]$EventDescription = "",
        
        [Parameter(Mandatory = $false)]
        [int]$DurationHours = 8
    )
    
    try {
        Write-Log -Message "Génération du fichier calendrier ICS" -Level "Info"
        
        # Formatage des dates au format ICS
        $startDate = $EventDate.ToString("yyyyMMddTHHmmssZ")
        $endDate = $EventDate.AddHours($DurationHours).ToString("yyyyMMddTHHmmssZ")
        $createdDate = (Get-Date).ToString("yyyyMMddTHHmmssZ")
        
        # Création du contenu ICS
        $icsContent = @"
BEGIN:VCALENDAR
VERSION:2.0
PRODID:-//Roo//Event Planning Automation//FR
CALSCALE:GREGORIAN
METHOD:PUBLISH
BEGIN:VEVENT
DTSTART:$startDate
DTEND:$endDate
DTSTAMP:$createdDate
UID:$(New-Guid)@roo-event-planning
CREATED:$createdDate
DESCRIPTION:$EventDescription
LAST-MODIFIED:$createdDate
LOCATION:$EventLocation
SEQUENCE:0
STATUS:CONFIRMED
SUMMARY:$EventName
TRANSP:OPAQUE
END:VEVENT
END:VCALENDAR
"@
        
        # Écriture du fichier ICS
        $icsPath = Join-Path $OutputPath "04-Communication\evenement.ics"
        $icsContent | Out-File -FilePath $icsPath -Encoding utf8
        
        Write-Log -Message "Fichier calendrier ICS généré: $icsPath" -Level "Info"
        return $icsPath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération du fichier calendrier: $_" -Level "Error"
        throw "Echec de la génération du fichier calendrier"
    }
}

# Fonction pour générer un modèle d'email d'invitation
function Generate-InvitationEmail {
    param (
        [Parameter(Mandatory = $true)]
        [string]$OutputPath,
        
        [Parameter(Mandatory = $true)]
        [string]$EventName,
        
        [Parameter(Mandatory = $true)]
        [datetime]$EventDate,
        
        [Parameter(Mandatory = $false)]
        [string]$EventLocation = "À déterminer"
    )
    
    try {
        Write-Log -Message "Génération du modèle d'email d'invitation" -Level "Info"
        
        # Création du contenu de l'email
        $emailContent = @"
Objet: Invitation - $EventName - $($EventDate.ToString("dd/MM/yyyy"))

Madame, Monsieur,

Nous avons le plaisir de vous inviter à participer à l'événement :

**$EventName**

qui se tiendra le **$($EventDate.ToString("dddd dd MMMM yyyy"))** à **$EventLocation**.

## À propos de l'événement

Cet événement réunira des professionnels du secteur pour échanger sur les dernières tendances et innovations. Vous aurez l'opportunité de participer à des sessions interactives, des ateliers pratiques et des moments de networking.

## Programme

- 08:30 - 09:00 : Accueil et enregistrement
- 09:00 - 09:30 : Discours d'ouverture
- 09:30 - 10:30 : Présentation principale
- 10:30 - 11:00 : Pause café
- 11:00 - 12:30 : Sessions parallèles
- 12:30 - 14:00 : Déjeuner networking
- 14:00 - 15:30 : Ateliers pratiques
- 15:30 - 16:00 : Pause café
- 16:00 - 17:00 : Table ronde
- 17:00 - 17:30 : Conclusion
- 17:30 - 19:00 : Cocktail de clôture

## Inscription

Pour confirmer votre participation, merci de vous inscrire via le lien suivant :
[LIEN_INSCRIPTION]

## Informations pratiques

- Lieu : $EventLocation
- Date : $($EventDate.ToString("dd/MM/yyyy"))
- Horaires : 08:30 - 19:00
- Contact : [EMAIL_CONTACT] | [TELEPHONE_CONTACT]

Vous trouverez en pièce jointe une invitation au format calendrier que vous pouvez ajouter à votre agenda.

Nous nous réjouissons de vous accueillir lors de cet événement.

Cordialement,

L'équipe organisatrice
$EventName
"@
        
        # Écriture du fichier modèle d'email
        $emailPath = Join-Path $OutputPath "04-Communication\modele-invitation.md"
        $emailContent | Out-File -FilePath $emailPath -Encoding utf8
        
        Write-Log -Message "Modèle d'email d'invitation généré: $emailPath" -Level "Info"
        return $emailPath
    }
    catch {
        Write-Log -Message "Erreur lors de la génération du modèle d'email: $_" -Level "Error"
        throw "Echec de la génération du modèle d'email"
    }
}

#endregion
#region Fonction principale

# Fonction principale d'exécution
function Start-EventPlanning {
    param (
        [Parameter(Mandatory = $false)]
        [switch]$GenerateDashboard = $true
    )
    
    try {
        # Initialisation
        Initialize-EventEnvironment
        
        # Notification de démarrage
        if ($Config.SendNotifications) {
            Send-EventNotification -Subject "Démarrage de la planification de l'événement" `
                                  -Body "Planification démarrée pour l'événement: $($Config.EventName) prévu le $($Config.EventDate.ToString('dd/MM/yyyy'))" `
                                  -Priority "Normal"
        }
        
        # Génération des documents de base
        Write-Log -Message "Génération des documents de base..." -Level "Info"
        
        $agendaPath = Generate-EventAgenda -OutputPath $Config.EventFolder
        $participantsPath = Generate-ParticipantsList -OutputPath $Config.EventFolder -ParticipantsCount $Config.ParticipantsCount
        $budgetPath = Generate-BudgetPlan -OutputPath $Config.EventFolder -BudgetTotal $Config.BudgetTotal -ParticipantsCount $Config.ParticipantsCount
        
        # Génération des documents d'intégration
        Write-Log -Message "Génération des documents d'intégration..." -Level "Info"
        
        $calendarPath = Generate-CalendarFile -OutputPath $Config.EventFolder `
                                            -EventDate $Config.EventDate `
                                            -EventName $Config.EventName `
                                            -EventLocation "À déterminer" `
                                            -EventDescription "Événement: $($Config.EventName)" `
                                            -DurationHours 10
        
        $emailPath = Generate-InvitationEmail -OutputPath $Config.EventFolder `
                                            -EventName $Config.EventName `
                                            -EventDate $Config.EventDate `
                                            -EventLocation "À déterminer"
        
        # Génération du tableau de bord
        $dashboardPath = $null
        if ($GenerateDashboard) {
            $dashboardPath = Generate-Dashboard -OutputPath $Config.EventFolder
        }
        
        # Création d'un fichier README à la racine
        $readmePath = Join-Path $Config.EventFolder "README.md"
        $readmeContent = @"
# $($Config.EventName)

Ce dossier contient tous les documents relatifs à l'organisation de l'événement "$($Config.EventName)" prévu le $($Config.EventDate.ToString('dd/MM/yyyy')).

## Structure des dossiers

$(($FolderStructure | ForEach-Object { "- $_ " }) -join "`n")

## Documents principaux

- [Agenda]($($agendaPath -replace [regex]::Escape($Config.EventFolder), '.'))
- [Liste des participants]($($participantsPath -replace [regex]::Escape($Config.EventFolder), '.'))
- [Budget prévisionnel]($($budgetPath -replace [regex]::Escape($Config.EventFolder), '.'))
- [Tableau de bord]($($dashboardPath -replace [regex]::Escape($Config.EventFolder), '.'))

## Intégration

- [Fichier calendrier ICS]($($calendarPath -replace [regex]::Escape($Config.EventFolder), '.'))
- [Modèle d'email d'invitation]($($emailPath -replace [regex]::Escape($Config.EventFolder), '.'))

## Prochaines étapes

1. Compléter les informations manquantes dans les documents
2. Réserver le lieu de l'événement
3. Contacter les intervenants potentiels
4. Établir le programme détaillé

---

*Généré automatiquement par le script de planification d'événement le $(Get-Date -Format "dd/MM/yyyy")*
"@
        
        $readmeContent | Out-File -FilePath $readmePath -Encoding utf8
        Write-Log -Message "Fichier README généré: $readmePath" -Level "Info"
        
        # Notification de fin
        if ($Config.SendNotifications) {
            $body = @"
Planification initiale terminée pour l'événement: $($Config.EventName)
Date: $($Config.EventDate.ToString('dd/MM/yyyy'))
Dossier: $($Config.EventFolder)

Documents générés:
- Agenda
- Liste des participants
- Budget prévisionnel
- Tableau de bord
- Fichier calendrier
- Modèle d'email d'invitation
"@
            
            Send-EventNotification -Subject "Planification de l'événement initialisée" -Body $body -Priority "Normal"
        }
        
        # Résumé final
        Write-Log -Message "=== Planification de l'événement initialisée ===" -Level "Info"
        Write-Log -Message "Événement: $($Config.EventName)" -Level "Info"
        Write-Log -Message "Date: $($Config.EventDate.ToString('dd/MM/yyyy'))" -Level "Info"
        Write-Log -Message "Dossier: $($Config.EventFolder)" -Level "Info"
        Write-Log -Message "Documents générés: agenda, participants, budget, tableau de bord, calendrier, email" -Level "Info"
        
        return @{
            EventName = $Config.EventName
            EventDate = $Config.EventDate
            EventFolder = $Config.EventFolder
            Documents = @{
                Agenda = $agendaPath
                Participants = $participantsPath
                Budget = $budgetPath
                Dashboard = $dashboardPath
                Calendar = $calendarPath
                EmailTemplate = $emailPath
                Readme = $readmePath
            }
        }
    }
    catch {
        Write-Log -Message "Erreur critique lors de la planification de l'événement: $_" -Level "Error"
        
        if ($Config.SendNotifications) {
            Send-EventNotification -Subject "ERREUR - Echec de la planification de l'événement" -Body "Une erreur critique est survenue: $_" -Priority "High"
        }
        
        throw "Echec de la planification de l'événement: $_"
    }
}

#endregion

# Exécution du script si appelé directement
if ($MyInvocation.InvocationName -ne ".") {
    # Exécution de la planification avec les paramètres fournis
    $result = Start-EventPlanning
    
    # Affichage du résumé
    Write-Host "`nRésumé de la planification:" -ForegroundColor Cyan
    Write-Host "- Événement: $($result.EventName)" -ForegroundColor White
    Write-Host "- Date: $($result.EventDate.ToString('dd/MM/yyyy'))" -ForegroundColor White
    Write-Host "- Dossier: $($result.EventFolder)" -ForegroundColor White
    
    Write-Host "`nDocuments générés:" -ForegroundColor Cyan
    foreach ($doc in $result.Documents.GetEnumerator()) {
        if ($doc.Value) {
            Write-Host "- $($doc.Key): $($doc.Value)" -ForegroundColor White
        }
    }
    
    Write-Host "`nLa structure de l'événement a été créée avec succès!" -ForegroundColor Green
    Write-Host "Vous pouvez maintenant compléter les informations dans les documents générés." -ForegroundColor White
}