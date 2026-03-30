# VERSION FINALE - Sans emojis pour compatibilite
# Analyse et conversion de traces d'orchestration Roo

param(
    [Parameter(Position=0)]
    [string]$TracePath = "corriges/demo-roo-code/04-creation-contenu/demo-1-web-orchestration-optimisee/roo_task_sep-8-2025_11-11-29-pm.md",
    [Parameter(Position=1)]
    [string]$OutputPath = "",
    [switch]$ShowDetails,
    [ValidateSet("Full", "Messages", "Summary", "NoTools", "NoResults", "UserOnly")]
    [string]$DetailLevel = "Full",
    [Parameter(HelpMessage="Nombre de caracteres maximum pour les balises <content>. 0 = pas de troncature")]
    [int]$TruncationChars = 0,
    [switch]$CompactStats,
    [switch]$GenerateAllVariants
)

# Configuration automatique UTF-8 PowerShell
$OutputEncoding = [console]::InputEncoding = [console]::OutputEncoding = New-Object System.Text.UTF8Encoding

Write-Host "Configuration UTF-8 chargee automatiquement" -ForegroundColor Green

# Fonction utilitaire pour nettoyer les messages utilisateur
function Clean-UserMessage {
    param([string]$Content)
    
    if ([string]::IsNullOrWhiteSpace($Content)) { return "" }
    
    $cleaned = $Content
    
    # Supprimer les environment_details tres verbeux
    $cleaned = $cleaned -replace '(?s)<environment_details>.*?</environment_details>', '[Environment details supprimes pour lisibilite]'
    
    # Supprimer les listes de fichiers tres longues
    $cleaned = $cleaned -replace '(?s)# Current Workspace Directory.*?(?=# [A-Z]|\n\n|$)', '[Liste des fichiers workspace supprimee]'
    
    # Garder les informations importantes mais raccourcir
    $cleaned = $cleaned -replace '(?s)# VSCode Visible Files\n([^\n]*)\n\n# VSCode Open Tabs\n([^\n]*(?:\n[^\n#]*)*)', "**Fichiers actifs:** `$1"
    
    # Supprimer les metadonnees redondantes
    $cleaned = $cleaned -replace '(?s)# Current (Cost|Time).*?\n', ''
    
    # Nettoyer les espaces multiples
    $cleaned = $cleaned -replace '\n{3,}', "`n`n"
    $cleaned = $cleaned.Trim()
    
    # Si le message devient trop court, extraire l'essentiel
    if ($cleaned.Length -lt 50 -and $Content.Length -gt 200) {
        if ($Content -match '<user_message>(.*?)</user_message>') {
            $cleaned = $matches[1].Trim()
        }
    }
    
    return $cleaned
}

# Fonction pour detecter et inclure les images
# Fonction pour extraire la premiere ligne et la tronquer
function Get-TruncatedFirstLine {
    param([string]$Content, [int]$MaxLength = 100)
    
    if ([string]::IsNullOrWhiteSpace($Content)) {
        return ""
    }
    
    # Cas special: detecter les messages utilisateur avec balises <user_message>
    if ($Content -match '(?s)<user_message>(.*?)</user_message>') {
        $userMessageContent = $matches[1].Trim()
        # Prendre la premiere ligne non vide du contenu du user_message
        $lines = $userMessageContent -split '\r?\n'
        foreach ($line in $lines) {
            $trimmedLine = $line.Trim()
            if (-not [string]::IsNullOrWhiteSpace($trimmedLine)) {
                if ($trimmedLine.Length -gt $MaxLength) {
                    return $trimmedLine.Substring(0, $MaxLength) + "..."
                }
                return $trimmedLine
            }
        }
    }
    
    # Extraire la premiere ligne non vide (comportement standard)
    $lines = $Content -split '\r?\n'
    $firstLine = ""
    foreach ($line in $lines) {
        $trimmedLine = $line.Trim()
        if (-not [string]::IsNullOrWhiteSpace($trimmedLine) -and -not $trimmedLine.StartsWith('<')) {
            $firstLine = $trimmedLine
            break
        }
    }
    
    # Tronquer si necessaire
    if ($firstLine.Length -gt $MaxLength) {
        $firstLine = $firstLine.Substring(0, $MaxLength) + "..."
    }
    
    return $firstLine
}

# Fonction pour convertir un index de position en numero de ligne
function Get-LineNumber {
    param(
        [string]$Content,
        [int]$Index
    )
    
    if ($Index -le 0) { return 1 }
    
    $substring = $Content.Substring(0, [Math]::Min($Index, $Content.Length))
    $lineNumber = ($substring -split '\r?\n').Count
    
    return $lineNumber
}

# Fonction pour detecter le type de balise technique
function Get-ToolType {
    param([string]$Content)
    
    if ($Content -match '<(read_file|list_files|write_to_file|apply_diff|execute_command|browser_action|search_files|codebase_search|new_task|ask_followup_question|attempt_completion|insert_content|search_and_replace)>') {
        return $matches[1]
    }
    
    return "outil"
}

# Fonction pour detecter le type d'entite dans un resultat
function Get-ResultType {
    param([string]$Content)
    
    if ($Content -match '<files>') {
        return "files"
    } elseif ($Content -match '<file_write_result>') {
        return "ecriture fichier"
    } elseif ($Content -match 'Command executed') {
        return "execution commande"
    } elseif ($Content -match 'Browser launched|Browser.*action') {
        return "navigation web"
    } elseif ($Content -match '<environment_details>') {
        return "details environnement"
    } elseif ($Content -match 'Result:.*Error' -or $Content -match 'Unable to apply diff') {
        return "erreur"
    } elseif ($Content -match 'Todo list updated') {
        return "mise a jour todo"
    } elseif ($Content -match '<insert_content>') {
        return "insertion contenu"
    }
    
    return "resultat"
}

function Include-Images {
    param([string]$Content)
    
    $enhanced = $Content
    
    # Detecter les screenshots avec chemins
    $enhanced = $enhanced -replace '([Ss]creenshot[s]?)[^.]*?([a-zA-Z0-9_/-]+\.(png|jpg|jpeg|webp))', '![Screenshot]($2)'
    
    # Detecter les references a des images
    $enhanced = $enhanced -replace '`([^`]+\.(png|jpg|jpeg|webp))`', '![Image]($1)'
    
    return $enhanced
}

function Convert-TraceToSummary {
    param(
        [Parameter(Mandatory=$true)]
        [string]$TracePath,
        [Parameter(Mandatory=$true)]
        [string]$OutputPath,
        [switch]$ShowDetails,
        [ValidateSet("Full", "NoTools", "NoResults", "Messages", "Summary", "UserOnly")]
        [string]$DetailLevel = "Full",
        [switch]$CompactStats
    )
    
    if (-not (Test-Path $TracePath)) {
        Write-Error "Fichier non trouve : $TracePath"
        return @{Success = $false; Error = "Fichier non trouve"}
    }
    
    Write-Host "=== CONVERSION TRACE VERS RESUME ===" -ForegroundColor Yellow
    Write-Host "Source: $(Split-Path $TracePath -Leaf)" -ForegroundColor Cyan
    Write-Host "Destination: $(Split-Path $OutputPath -Leaf)" -ForegroundColor Cyan
    
    # Lecture et analyse du fichier
    $content = Get-Content -Path $TracePath -Raw -Encoding UTF8
    $sourceSize = $content.Length
    Write-Host "Taille source: $([math]::Round($sourceSize/1024, 2)) KB" -ForegroundColor Green
    
    # Analyse des sections avec regex robuste
    $userMatches = [regex]::Matches($content, '(?s)\*\*User:\*\*(.*?)(?=\*\*(?:User|Assistant):\*\*|$)')
    $assistantMatches = [regex]::Matches($content, '(?s)\*\*Assistant:\*\*(.*?)(?=\*\*(?:User|Assistant):\*\*|$)')
    
    Write-Host "Sections User: $($userMatches.Count)" -ForegroundColor Magenta
    Write-Host "Sections Assistant: $($assistantMatches.Count)" -ForegroundColor Green
    
    # Creer et trier toutes les sections avec numeros de ligne
    $allSections = @()
    $originalContent = Get-Content -Path $TracePath -Raw -Encoding UTF8
    
    foreach ($match in $userMatches) {
        $content = $match.Groups[1].Value.Trim()
        $subType = if ($content -match '^\[([^\]]+)\] Result:') { "ToolResult" } else { "UserMessage" }
        $lineNumber = Get-LineNumber -Content $originalContent -Index $match.Index
        $allSections += [PSCustomObject]@{Type="User"; SubType=$subType; Index=$match.Index; LineNumber=$lineNumber; Content=$content}
    }
    foreach ($match in $assistantMatches) {
        $content = $match.Groups[1].Value.Trim()
        $subType = if ($content -match '<attempt_completion>') { "Completion" } else { "ToolCall" }
        $allSections += [PSCustomObject]@{Type="Assistant"; SubType=$subType; Index=$match.Index; Content=$content}
    }
    
    $allSections = $allSections | Sort-Object Index
    Write-Host "Total sections: $($allSections.Count)" -ForegroundColor Green
    
    # Construction du resume
    $summary = [System.Text.StringBuilder]::new()
    
    # En-tete moderne et informatif avec CSS pour les couleurs
    $summary.AppendLine("# RESUME DE TRACE D'ORCHESTRATION ROO") | Out-Null
    $summary.AppendLine("") | Out-Null
    $summary.AppendLine("<style>") | Out-Null
    $summary.AppendLine(".user-message {") | Out-Null
    $summary.AppendLine("    background-color: #FFEBEE;") | Out-Null
    $summary.AppendLine("    border-left: 4px solid #F44336;") | Out-Null
    $summary.AppendLine("    padding: 15px;") | Out-Null
    $summary.AppendLine("    margin: 10px 0;") | Out-Null
    $summary.AppendLine("    border-radius: 5px;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".assistant-message {") | Out-Null
    $summary.AppendLine("    background-color: #E8F4FD;") | Out-Null
    $summary.AppendLine("    border-left: 4px solid #2196F3;") | Out-Null
    $summary.AppendLine("    padding: 15px;") | Out-Null
    $summary.AppendLine("    margin: 10px 0;") | Out-Null
    $summary.AppendLine("    border-radius: 5px;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".tool-message {") | Out-Null
    $summary.AppendLine("    background-color: #FFF8E1;") | Out-Null
    $summary.AppendLine("    border-left: 4px solid #FF9800;") | Out-Null
    $summary.AppendLine("    padding: 15px;") | Out-Null
    $summary.AppendLine("    margin: 10px 0;") | Out-Null
    $summary.AppendLine("    border-radius: 5px;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".completion-message {") | Out-Null
    $summary.AppendLine("    background-color: #E8F5E8;") | Out-Null
    $summary.AppendLine("    border-left: 4px solid #4CAF50;") | Out-Null
    $summary.AppendLine("    padding: 15px;") | Out-Null
    $summary.AppendLine("    margin: 10px 0;") | Out-Null
    $summary.AppendLine("    border-radius: 5px;") | Out-Null
    $summary.AppendLine("    box-shadow: 0 2px 4px rgba(76,175,80,0.1);") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".toc {") | Out-Null
    $summary.AppendLine("    background-color: #f8f9fa;") | Out-Null
    $summary.AppendLine("    border: 1px solid #dee2e6;") | Out-Null
    $summary.AppendLine("    border-radius: 8px;") | Out-Null
    $summary.AppendLine("    padding: 20px;") | Out-Null
    $summary.AppendLine("    margin: 15px 0;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".toc h3 {") | Out-Null
    $summary.AppendLine("    margin-top: 0;") | Out-Null
    $summary.AppendLine("    color: #495057;") | Out-Null
    $summary.AppendLine("    border-bottom: 2px solid #6c757d;") | Out-Null
    $summary.AppendLine("    padding-bottom: 10px;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".toc-user {") | Out-Null
    $summary.AppendLine("    color: #F44336 !important;") | Out-Null
    $summary.AppendLine("    font-weight: bold;") | Out-Null
    $summary.AppendLine("    text-decoration: none;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".toc-user:hover { background-color: #FFEBEE; padding: 2px 4px; border-radius: 3px; }") | Out-Null
    $summary.AppendLine(".toc-assistant {") | Out-Null
    $summary.AppendLine("    color: #2196F3 !important;") | Out-Null
    $summary.AppendLine("    font-weight: bold;") | Out-Null
    $summary.AppendLine("    text-decoration: none;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".toc-assistant:hover { background-color: #E8F4FD; padding: 2px 4px; border-radius: 3px; }") | Out-Null
    $summary.AppendLine(".toc-tool {") | Out-Null
    $summary.AppendLine("    color: #FF9800 !important;") | Out-Null
    $summary.AppendLine("    font-weight: bold;") | Out-Null
    $summary.AppendLine("    text-decoration: none;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".toc-tool:hover { background-color: #FFF8E1; padding: 2px 4px; border-radius: 3px; }") | Out-Null
    $summary.AppendLine(".toc-completion {") | Out-Null
    $summary.AppendLine("    color: #4CAF50 !important;") | Out-Null
    $summary.AppendLine("    font-weight: bold;") | Out-Null
    $summary.AppendLine("    text-decoration: none;") | Out-Null
    $summary.AppendLine("}") | Out-Null
    $summary.AppendLine(".toc-completion:hover { background-color: #E8F5E8; padding: 2px 4px; border-radius: 3px; }") | Out-Null
    $summary.AppendLine("</style>") | Out-Null
    $summary.AppendLine("") | Out-Null
    $summary.AppendLine("**Fichier source :** $(Split-Path $TracePath -Leaf)") | Out-Null
    $summary.AppendLine("**Date de generation :** $(Get-Date -Format 'dd/MM/yyyy a HH:mm')") | Out-Null
    $summary.AppendLine("**Taille source :** $([math]::Round($sourceSize/1024, 2)) KB") | Out-Null
    $summary.AppendLine("") | Out-Null
    
    # Les statistiques sont maintenant calculées sur la base du SubType
    $userMessageCount = ($allSections | Where-Object { $_.SubType -eq 'UserMessage' }).Count
    $userTotalSize = ($allSections | Where-Object { $_.SubType -eq 'UserMessage' } | ForEach-Object { $_.Content.Length } | Measure-Object -Sum).Sum
    $toolResultsCount = ($allSections | Where-Object { $_.SubType -eq 'ToolResult' }).Count
    $toolResultsSize = ($allSections | Where-Object { $_.SubType -eq 'ToolResult' } | ForEach-Object { $_.Content.Length } | Measure-Object -Sum).Sum
    $assistantTotalSize = ($assistantMatches | ForEach-Object { $_.Groups[1].Value.Length } | Measure-Object -Sum).Sum
    
    $totalContentSize = $userTotalSize + $assistantTotalSize + $toolResultsSize
    if ($totalContentSize -eq 0) { $totalContentSize = 1 }

    $userPercentage = [math]::Round(($userTotalSize / $totalContentSize) * 100, 1)
    $assistantPercentage = [math]::Round(($assistantTotalSize / $totalContentSize) * 100, 1)
    $toolResultsPercentage = [math]::Round(($toolResultsSize / $totalContentSize) * 100, 1)
    
    # Statistiques avec choix de format selon CompactStats
    if ($CompactStats) {
        $summary.AppendLine("## STATISTIQUES") | Out-Null
        $summary.AppendLine("") | Out-Null
        $summary.AppendLine("| Metrique | Valeur | % |") | Out-Null
        $summary.AppendLine("|----------|--------|---|") | Out-Null
        $summary.AppendLine("| Messages User | $userMessageCount | $userPercentage% |") | Out-Null
        $summary.AppendLine("| Reponses Assistant | $($assistantMatches.Count) | $assistantPercentage% |") | Out-Null
        $summary.AppendLine("| Resultats d'outils | $toolResultsCount | $toolResultsPercentage% |") | Out-Null
        $summary.AppendLine("| Total echanges | $($allSections.Count) | 100% |") | Out-Null
    } else {
        $summary.AppendLine("## STATISTIQUES DETAILLEES") | Out-Null
        $summary.AppendLine("") | Out-Null
        $summary.AppendLine("| Metrique | Valeur | Taille | % |") | Out-Null
        $summary.AppendLine("|----------|--------|--------|---|") | Out-Null
        $summary.AppendLine("| Messages User | $userMessageCount | $([math]::Round($userTotalSize/1024, 1)) KB | $userPercentage% |") | Out-Null
        $summary.AppendLine("| Reponses Assistant | $($assistantMatches.Count) | $([math]::Round($assistantTotalSize/1024, 1)) KB | $assistantPercentage% |") | Out-Null
        $summary.AppendLine("| Resultats d'outils | $toolResultsCount | $([math]::Round($toolResultsSize/1024, 1)) KB | $toolResultsPercentage% |") | Out-Null
        $summary.AppendLine("| **Total echanges** | **$($allSections.Count)** | **$([math]::Round($totalContentSize/1024, 1)) KB** | **100%** |") | Out-Null
    }
    $summary.AppendLine("") | Out-Null
    
    # Generer le sommaire des messages avec code couleur
    $summary.AppendLine('<div class="toc">') | Out-Null
    $summary.AppendLine("") | Out-Null
    $summary.AppendLine("### SOMMAIRE DES MESSAGES {#table-des-matieres}") | Out-Null
    $summary.AppendLine("") | Out-Null
    $userMessageCounterToc = 1
    $assistantMessageCounterToc = 1
    $toolResultCounterToc = 1
    $isFirstUser = $true
    
    foreach ($section in $allSections) {
        $firstLine = Get-TruncatedFirstLine -Content $section.Content -MaxLength 200
        
        if ($section.SubType -eq "UserMessage") {
            $lineInfo = ""
            if ($section.LineNumber) {
                $lineInfo = " [L$($section.LineNumber)]"
            }
            
            $originalFileLink = ""
            if ($section.LineNumber -and $DetailLevel -eq "Summary") {
                $originalFileName = (Split-Path $TracePath -Leaf)
                $originalFileLink = " -> $originalFileName#L$($section.LineNumber)"
            }
            
            if ($isFirstUser) {
                if ($DetailLevel -eq "Summary") {
                    $summary.AppendLine("- **Instruction de tache initiale**$lineInfo$originalFileLink") | Out-Null
                } else {
                    $summary.AppendLine("- [Instruction de tache initiale](#instruction-de-tache-initiale)$lineInfo") | Out-Null
                }
                $isFirstUser = $false
            } else {
                $messageAnchor = "message-utilisateur-$userMessageCounterToc"
                if ($DetailLevel -eq "Summary") {
                    # Mode Summary: liens vers fichier source
                    $originalFileName = (Split-Path $TracePath -Leaf)
                    if ($section.LineNumber) {
                        $sourceLink = "$originalFileName#L$($section.LineNumber)"
                    } else {
                        $sourceLink = $originalFileName
                    }
                    $summary.AppendLine("- <a href=`"$sourceLink`" class=`"toc-user`">**MESSAGE UTILISATEUR #$userMessageCounterToc** - $firstLine</a>$lineInfo") | Out-Null
                } else {
                    # Autres modes: liens internes avec couleurs
                    $summary.AppendLine("- <a href=`"#$messageAnchor`" class=`"toc-user`">MESSAGE UTILISATEUR #$userMessageCounterToc - $firstLine</a>$lineInfo") | Out-Null
                }
                $userMessageCounterToc++
            }
        } elseif ($section.SubType -eq "ToolResult") {
            $lineInfo = ""
            if ($section.LineNumber) {
                $lineInfo = " [L$($section.LineNumber)]"
            }
            
            $originalFileLink = ""
            if ($section.LineNumber -and $DetailLevel -eq "Summary") {
                $originalFileName = (Split-Path $TracePath -Leaf)
                $originalFileLink = " -> $originalFileName#L$($section.LineNumber)"
            }
            
            $messageAnchor = "outil-$toolResultCounterToc"
            if ($DetailLevel -eq "Summary") {
                # Mode Summary: liens externes vers fichier source
                $originalFileName = (Split-Path $TracePath -Leaf)
                if ($section.LineNumber) {
                    $sourceLink = "$originalFileName#L$($section.LineNumber)"
                } else {
                    $sourceLink = $originalFileName
                }
                $summary.AppendLine("- <a href=`"$sourceLink`" class=`"toc-tool`">**RESULTAT OUTIL #$toolResultCounterToc** - $firstLine</a>$lineInfo") | Out-Null
            } else {
                # Autres modes: liens internes avec couleurs
                $summary.AppendLine("- <a href=`"#$messageAnchor`" class=`"toc-tool`">RESULTAT OUTIL #$toolResultCounterToc - $firstLine</a>$lineInfo") | Out-Null
            }
            $toolResultCounterToc++
        } elseif ($section.Type -eq "Assistant") {
            $lineInfo = ""
            if ($section.LineNumber) {
                $lineInfo = " [L$($section.LineNumber)]"
            }
            
            $originalFileLink = ""
            if ($section.LineNumber -and $DetailLevel -eq "Summary") {
                $originalFileName = (Split-Path $TracePath -Leaf)
                $originalFileLink = " -> $originalFileName#L$($section.LineNumber)"
            }
            
            $messageAnchor = "reponse-assistant-$assistantMessageCounterToc"
            if ($section.SubType -eq "Completion") {
                if ($DetailLevel -eq "Summary") {
                    # Mode Summary: liens externes vers fichier source
                    $originalFileName = (Split-Path $TracePath -Leaf)
                    if ($section.LineNumber) {
                        $sourceLink = "$originalFileName#L$($section.LineNumber)"
                    } else {
                        $sourceLink = $originalFileName
                    }
                    $summary.AppendLine("- <a href=`"$sourceLink`" class=`"toc-assistant`">**REPONSE ASSISTANT #$assistantMessageCounterToc (Terminaison)** - $firstLine</a>$lineInfo") | Out-Null
                } else {
                    # Autres modes: liens internes avec couleurs
                    $summary.AppendLine("- <a href=`"#$messageAnchor`" class=`"toc-assistant`">REPONSE ASSISTANT #$assistantMessageCounterToc (Terminaison) - $firstLine</a>$lineInfo") | Out-Null
                }
            } else {
                if ($DetailLevel -eq "Summary") {
                    # Mode Summary: liens externes vers fichier source
                    $originalFileName = (Split-Path $TracePath -Leaf)
                    if ($section.LineNumber) {
                        $sourceLink = "$originalFileName#L$($section.LineNumber)"
                    } else {
                        $sourceLink = $originalFileName
                    }
                    $summary.AppendLine("- <a href=`"$sourceLink`" class=`"toc-assistant`">**REPONSE ASSISTANT #$assistantMessageCounterToc** - $firstLine</a>$lineInfo") | Out-Null
                } else {
                    # Autres modes: liens internes avec couleurs
                    $summary.AppendLine("- <a href=`"#$messageAnchor`" class=`"toc-assistant`">REPONSE ASSISTANT #$assistantMessageCounterToc - $firstLine</a>$lineInfo") | Out-Null
                }
            }
            $assistantMessageCounterToc++
        }
    }
    $summary.AppendLine("") | Out-Null
    $summary.AppendLine("</div>") | Out-Null
    $summary.AppendLine("") | Out-Null
    
    # Mode Summary : s'arrêter après la table des matières
    if ($DetailLevel -eq "Summary") {
        # Footer pour le mode Summary
        $summary.AppendLine("---") | Out-Null
        $summary.AppendLine("") | Out-Null
        $summary.AppendLine("**Resume genere automatiquement par Convert-TraceToSummary-Final.ps1**") | Out-Null
        $summary.AppendLine("**Date :** $(Get-Date -Format 'dd/MM/yyyy a HH:mm:ss')") | Out-Null
        $summary.AppendLine("**Mode :** Summary (Table des matières uniquement)") | Out-Null
    } else {
        # Traitement des sections pour les autres modes
        $taskExtracted = $false
        $userMessageCounter = 1
        $assistantMessageCounter = 1
        $toolResultCounter = 1
        
        foreach ($section in $allSections) {
            if ($section.SubType -eq "UserMessage") {
                if (-not $taskExtracted) {
                    $summary.AppendLine("## INSTRUCTION DE TACHE INITIALE") | Out-Null
                    $summary.AppendLine("") | Out-Null
                    
                    if ($section.Content -match '(?s)(.*?)<environment_details>.*?</environment_details>(.*)') {
                        $mainContent = $matches[1].Trim()
                        $afterDetails = $matches[2].Trim()
                        
                        $summary.AppendLine('```markdown') | Out-Null
                        $summary.AppendLine($mainContent) | Out-Null
                        $summary.AppendLine('```') | Out-Null
                        $summary.AppendLine("") | Out-Null
                        
                        $summary.AppendLine("<details>") | Out-Null
                        $summary.AppendLine("<summary>**Environment Details** - Cliquez pour afficher</summary>") | Out-Null
                        $summary.AppendLine("") | Out-Null
                        
                        $envMatch = [regex]::Match($section.Content, '(?s)<environment_details>.*?</environment_details>')
                        if ($envMatch.Success) {
                            $summary.AppendLine('```') | Out-Null
                            $summary.AppendLine($envMatch.Value) | Out-Null
                            $summary.AppendLine('```') | Out-Null
                        }
                        $summary.AppendLine("</details>") | Out-Null
                        
                        if (-not [string]::IsNullOrWhiteSpace($afterDetails)) {
                            $summary.AppendLine("") | Out-Null
                            $summary.AppendLine('```markdown') | Out-Null
                            $summary.AppendLine($afterDetails) | Out-Null
                            $summary.AppendLine('```') | Out-Null
                        }
                    } else {
                        $summary.AppendLine('```markdown') | Out-Null
                        $summary.AppendLine($section.Content) | Out-Null
                        $summary.AppendLine('```') | Out-Null
                    }
                    $summary.AppendLine("") | Out-Null
                    $summary.AppendLine("---") | Out-Null
                    $summary.AppendLine("") | Out-Null
                    $summary.AppendLine("## ECHANGES DE CONVERSATION") | Out-Null
                    $summary.AppendLine("") | Out-Null
                    $taskExtracted = $true
                } else {
                     if ($DetailLevel -ne "AssistantOnly") {
                        $firstLine = Get-TruncatedFirstLine -Content $section.Content -MaxLength 200
                        $messageAnchor = "message-utilisateur-$userMessageCounter"
                        $summary.AppendLine("") | Out-Null
                        $summary.AppendLine("### MESSAGE UTILISATEUR #$userMessageCounter - $firstLine {#$messageAnchor}") | Out-Null
                        $summary.AppendLine("") | Out-Null
                        
                        $summary.AppendLine('<div class="user-message">') | Out-Null
                        $cleanedUserContent = Clean-UserMessage -Content $section.Content
                        $summary.AppendLine($cleanedUserContent) | Out-Null
                        $summary.AppendLine('</div>') | Out-Null
                        $summary.AppendLine("") | Out-Null
                        $summary.AppendLine('<div style="text-align: right; font-size: 0.9em; color: #666;"><a href="#table-des-matieres">^ Table des matieres</a></div>') | Out-Null
                    }
                    $summary.AppendLine("") | Out-Null
                    $userMessageCounter++
                }
            } elseif ($section.SubType -eq "ToolResult") {
                if ($DetailLevel -ne "UserOnly") {
                    if ($section.Content -match '\[([^\]]+)\] Result:') {
                        $toolName = $matches[1]
                        $firstLine = Get-TruncatedFirstLine -Content $toolName -MaxLength 200
                        $messageAnchor = "outil-$toolResultCounter"
                        $summary.AppendLine("") | Out-Null
                        $summary.AppendLine("### RESULTAT OUTIL #$toolResultCounter - $firstLine {#$messageAnchor}") | Out-Null
                        $summary.AppendLine("") | Out-Null
                        
                        $summary.AppendLine('<div class="tool-message">') | Out-Null
                        $summary.AppendLine("**Resultat d'outil :** ``$toolName``") | Out-Null
                        
                        $toolResultPattern = '\[([^\]]+)\] Result:\s*(.*?)(?=\n\n|\n$|$)'
                        $toolResultMatch = [regex]::Match($section.Content, $toolResultPattern, [System.Text.RegularExpressions.RegexOptions]::Singleline)
                        
                        if ($toolResultMatch.Success) {
                            $toolResult = $toolResultMatch.Groups[2].Value.Trim()
                             if ([string]::IsNullOrWhiteSpace($toolResult)) {
                                $resultStartIndex = $section.Content.IndexOf("] Result:")
                                if ($resultStartIndex -gt -1) {
                                    $toolResult = $section.Content.Substring($resultStartIndex + 9).Trim()
                                }
                            }
                            $resultType = Get-ResultType -Content $toolResult
                            $beforeResult = ($section.Content -split '\[([^\]]+)\] Result:')[0].Trim()
                            if (-not [string]::IsNullOrWhiteSpace($beforeResult)) {
                                $cleanedBefore = Clean-UserMessage -Content $beforeResult
                                $summary.AppendLine("") | Out-Null; $summary.AppendLine("**Contexte :**") | Out-Null; $summary.AppendLine($cleanedBefore) | Out-Null; $summary.AppendLine("") | Out-Null
                            }
                            if (-not [string]::IsNullOrWhiteSpace($toolResult)) {
                                if ($DetailLevel -in @("Full", "NoTools")) {
                                    # Full et NoTools: affichage complet des détails des résultats
                                    $summary.AppendLine("") | Out-Null
                                    $summary.AppendLine("<details>") | Out-Null
                                    $summary.AppendLine("<summary>**$resultType :** Cliquez pour afficher</summary>") | Out-Null
                                    $summary.AppendLine("") | Out-Null
                                    $summary.AppendLine('```') | Out-Null; $summary.AppendLine($toolResult) | Out-Null; $summary.AppendLine('```') | Out-Null
                                    $summary.AppendLine("</details>") | Out-Null
                                } elseif ($DetailLevel -in @("NoResults", "Messages")) {
                                    # NoResults et Messages: garder la section collapsible mais vider le contenu
                                    $summary.AppendLine("") | Out-Null
                                    $summary.AppendLine("<details>") | Out-Null
                                    $summary.AppendLine("<summary>**$resultType :** [Contenu masqué en mode $DetailLevel]</summary>") | Out-Null
                                    $summary.AppendLine("") | Out-Null
                                    $summary.AppendLine("*Contenu des résultats masqué - utilisez -DetailLevel Full pour afficher*") | Out-Null
                                    $summary.AppendLine("</details>") | Out-Null
                                }
                            }
                        }
                        $summary.AppendLine('</div>') | Out-Null
                        $summary.AppendLine("") | Out-Null
                        $summary.AppendLine('<div style="text-align: right; font-size: 0.9em; color: #666;"><a href="#table-des-matieres">^ Table des matieres</a></div>') | Out-Null
                    }
                    $summary.AppendLine("") | Out-Null
                    $toolResultCounter++
                }
            } elseif ($section.Type -eq "Assistant") {
                if ($DetailLevel -ne "UserOnly") {
                    $firstLine = Get-TruncatedFirstLine -Content $section.Content -MaxLength 200
                    $messageAnchor = "reponse-assistant-$assistantMessageCounter"
                    
                    $summary.AppendLine("") | Out-Null
                    if ($section.SubType -eq "Completion") {
                        $summary.AppendLine("### REPONSE ASSISTANT #$assistantMessageCounter (Terminaison) - $firstLine {#$messageAnchor}") | Out-Null
                    } else {
                        $summary.AppendLine("### REPONSE ASSISTANT #$assistantMessageCounter - $firstLine {#$messageAnchor}") | Out-Null
                    }
                    $summary.AppendLine("") | Out-Null
                    
                    if ($section.SubType -eq "Completion") {
                        $summary.AppendLine('<div class="completion-message">') | Out-Null
                    } else {
                        $summary.AppendLine('<div class="assistant-message">') | Out-Null
                    }
                    
                    $assistantContent = $section.Content
                    $assistantContent = Include-Images -Content $assistantContent
                    
                    $textContent = $assistantContent
                    $technicalBlocks = @()
                    
                    # Extraction des blocs <thinking>
                    while ($textContent -match '(?s)<thinking>.*?</thinking>') {
                        $match = [regex]::Match($textContent, '(?s)<thinking>.*?</thinking>')
                        if ($match.Success) {
                            $technicalBlocks += [PSCustomObject]@{Type="Reflexion"; Content=$match.Value}
                            $textContent = $textContent.Replace($match.Value, '')
                        } else {
                            break
                        }
                    }
                    
                    # Extraction des blocs d'outils XML
                    while ($true) {
                        $match = [regex]::Match($textContent, '(?s)<([a-zA-Z_][a-zA-Z0-9_\-:]+)(?:\s+[^>]*)?>.*?</\1>')
                        if (-not $match.Success) { break }

                        $fullXml = $match.Value
                        $tagName = $match.Groups[1].Value
                        
                        if ($tagName -ne "thinking") {
                            $technicalBlocks += [PSCustomObject]@{Type="Outil"; Content=$fullXml; Tag=$tagName}
                            $textContent = $textContent.Replace($fullXml, '')
                        }
                    }
                    
                    $textContent = $textContent.Trim()
                    
                    # Affichage du contenu textuel principal
                    if (-not [string]::IsNullOrWhiteSpace($textContent)) {
                        $summary.AppendLine($textContent) | Out-Null
                        $summary.AppendLine("") | Out-Null
                    }
                    
                    # Traitement des blocs techniques selon le DetailLevel
                    if ($technicalBlocks.Count -gt 0) {
                        if ($DetailLevel -eq "Full") {
                            # Mode Full : affichage complet des détails techniques
                            foreach ($block in $technicalBlocks) {
                                if ($block.Type -eq "Outil") {
                                    # Affichage séquentiel pour les outils XML - sections légères et séquentielles
                                    try {
                                        [xml]$xmlContent = $block.Content
                                        $rootElement = $xmlContent.DocumentElement
                                        
                                        # Section principale LÉGÈRE pour l'outil (juste le titre, pas le contenu XML)
                                        $summary.AppendLine("<details>") | Out-Null
                                        $summary.AppendLine("<summary>OUTIL - $($block.Tag)</summary>") | Out-Null
                                        $summary.AppendLine("") | Out-Null
                                        $summary.AppendLine("*Voir sections detaillees ci-dessous*") | Out-Null
                                        $summary.AppendLine("</details>") | Out-Null
                                        
                                        # Fonction récursive pour collecter tous les éléments
                                        function Get-AllElements($node) {
                                            $allElements = @()
                                            foreach ($childNode in $node.ChildNodes) {
                                                if ($childNode.NodeType -eq [System.Xml.XmlNodeType]::Element) {
                                                    $allElements += $childNode
                                                    # Récursivement collecter les enfants
                                                    if ($childNode.HasChildNodes) {
                                                        $allElements += Get-AllElements $childNode
                                                    }
                                                }
                                            }
                                            return $allElements
                                        }
                                        
                                        # Collecter tous les éléments
                                        $allElements = Get-AllElements $rootElement
                                        
                                        # Créer des sections séquentielles au même niveau
                                        foreach ($element in $allElements) {
                                            $summary.AppendLine("<details>") | Out-Null
                                            $summary.AppendLine("<summary>$($element.Name)</summary>") | Out-Null
                                            $summary.AppendLine("") | Out-Null
                                            $summary.AppendLine('```xml') | Out-Null
                                            $summary.AppendLine($element.OuterXml) | Out-Null
                                            $summary.AppendLine('```') | Out-Null
                                            $summary.AppendLine("</details>") | Out-Null
                                        }
                                        
                                    } catch {
                                        Write-Host "Erreur parsing XML pour $($block.Tag): $($_.Exception.Message)" -ForegroundColor Yellow
                                        # Fallback en cas d'erreur XML
                                        $summary.AppendLine("<details>") | Out-Null
                                        $summary.AppendLine("<summary>OUTIL - $($block.Tag) [Erreur parsing]</summary>") | Out-Null
                                        $summary.AppendLine("") | Out-Null
                                        $summary.AppendLine('```xml') | Out-Null
                                        $summary.AppendLine($block.Content) | Out-Null
                                        $summary.AppendLine('```') | Out-Null
                                        $summary.AppendLine("</details>") | Out-Null
                                    }
                                } else {
                                    # Traitement classique pour les autres types (reflexion, etc.)
                                    $summary.AppendLine("<details>") | Out-Null
                                    $summary.AppendLine("<summary>DETAILS TECHNIQUE - $($block.Type)</summary>") | Out-Null
                                    $summary.AppendLine("") | Out-Null
                                    $summary.AppendLine('```xml') | Out-Null
                                    $summary.AppendLine($block.Content) | Out-Null
                                    $summary.AppendLine('```') | Out-Null
                                    $summary.AppendLine("</details>") | Out-Null
                                }
                                $summary.AppendLine("") | Out-Null
                            }
                        } elseif ($DetailLevel -eq "NoResults") {
                            # Mode NoResults : affichage complet des détails techniques assistants (garde les compléments assistants)
                            foreach ($block in $technicalBlocks) {
                                if ($block.Type -eq "Outil") {
                                    # Affichage séquentiel pour les outils XML - sections légères et séquentielles
                                    try {
                                        [xml]$xmlContent = $block.Content
                                        $rootElement = $xmlContent.DocumentElement
                                        
                                        # Section principale LÉGÈRE pour l'outil (juste le titre, pas le contenu XML)
                                        $summary.AppendLine("<details>") | Out-Null
                                        $summary.AppendLine("<summary>OUTIL - $($block.Tag)</summary>") | Out-Null
                                        $summary.AppendLine("") | Out-Null
                                        $summary.AppendLine("*Voir sections detaillees ci-dessous*") | Out-Null
                                        $summary.AppendLine("</details>") | Out-Null
                                        
                                        # Fonction récursive pour collecter tous les éléments
                                        function Get-AllElements($node) {
                                            $allElements = @()
                                            foreach ($childNode in $node.ChildNodes) {
                                                if ($childNode.NodeType -eq [System.Xml.XmlNodeType]::Element) {
                                                    $allElements += $childNode
                                                    # Récursivement collecter les enfants
                                                    if ($childNode.HasChildNodes) {
                                                        $allElements += Get-AllElements $childNode
                                                    }
                                                }
                                            }
                                            return $allElements
                                        }
                                        
                                        # Collecter tous les éléments
                                        $allElements = Get-AllElements $rootElement
                                        
                                        # Créer des sections séquentielles au même niveau
                                        foreach ($element in $allElements) {
                                            $summary.AppendLine("<details>") | Out-Null
                                            $summary.AppendLine("<summary>$($element.Name)</summary>") | Out-Null
                                            $summary.AppendLine("") | Out-Null
                                            $summary.AppendLine('```xml') | Out-Null
                                            $summary.AppendLine($element.OuterXml) | Out-Null
                                            $summary.AppendLine('```') | Out-Null
                                            $summary.AppendLine("</details>") | Out-Null
                                        }
                                        
                                    } catch {
                                        Write-Host "Erreur parsing XML pour $($block.Tag): $($_.Exception.Message)" -ForegroundColor Yellow
                                        # Fallback en cas d'erreur XML
                                        $summary.AppendLine("<details>") | Out-Null
                                        $summary.AppendLine("<summary>OUTIL - $($block.Tag) [Erreur parsing]</summary>") | Out-Null
                                        $summary.AppendLine("") | Out-Null
                                        $summary.AppendLine('```xml') | Out-Null
                                        $summary.AppendLine($block.Content) | Out-Null
                                        $summary.AppendLine('```') | Out-Null
                                        $summary.AppendLine("</details>") | Out-Null
                                    }
                                } else {
                                    # Traitement classique pour les autres types (reflexion, etc.)
                                    $summary.AppendLine("<details>") | Out-Null
                                    $summary.AppendLine("<summary>DETAILS TECHNIQUE - $($block.Type)</summary>") | Out-Null
                                    $summary.AppendLine("") | Out-Null
                                    $summary.AppendLine('```xml') | Out-Null
                                    $summary.AppendLine($block.Content) | Out-Null
                                    $summary.AppendLine('```') | Out-Null
                                    $summary.AppendLine("</details>") | Out-Null
                                }
                                $summary.AppendLine("") | Out-Null
                            }
                        } elseif ($DetailLevel -in @("NoTools", "Messages")) {
                            # Mode NoTools et Messages : garder les sections collapsibles mais vider le contenu des outils assistants
                            foreach ($block in $technicalBlocks) {
                                if ($block.Type -eq "Outil") {
                                    $summary.AppendLine("<details>") | Out-Null
                                    $summary.AppendLine("<summary>OUTIL - $($block.Tag) [Paramètres masqués en mode $DetailLevel]</summary>") | Out-Null
                                    $summary.AppendLine("") | Out-Null
                                    $summary.AppendLine("*Contenu des paramètres d'outil masqué - utilisez -DetailLevel Full pour afficher*") | Out-Null
                                    $summary.AppendLine("</details>") | Out-Null
                                    $summary.AppendLine("") | Out-Null
                                } else {
                                    # Pour Messages: masquer aussi les autres blocs techniques, pour NoTools: les afficher
                                    if ($DetailLevel -eq "NoTools") {
                                        $summary.AppendLine("<details>") | Out-Null
                                        $summary.AppendLine("<summary>DETAILS TECHNIQUE - $($block.Type)</summary>") | Out-Null
                                        $summary.AppendLine("") | Out-Null
                                        $summary.AppendLine('```xml') | Out-Null
                                        $summary.AppendLine($block.Content) | Out-Null
                                        $summary.AppendLine('```') | Out-Null
                                        $summary.AppendLine("</details>") | Out-Null
                                        $summary.AppendLine("") | Out-Null
                                    }
                                }
                            }
                        }
                    }
                    
                    $summary.AppendLine('</div>') | Out-Null
                    $summary.AppendLine("") | Out-Null
                    $summary.AppendLine('<div style="text-align: right; font-size: 0.9em; color: #666;"><a href="#table-des-matieres">^ Table des matieres</a></div>') | Out-Null
                    $assistantMessageCounter++
                }
            }
        }
        
        # Footer standard pour les modes autres que Summary
        $summary.AppendLine("---") | Out-Null
        $summary.AppendLine("") | Out-Null
        $summary.AppendLine("**Resume genere automatiquement par Convert-TraceToSummary-Final.ps1**") | Out-Null
        $summary.AppendLine("**Date :** $(Get-Date -Format 'dd/MM/yyyy a HH:mm:ss')") | Out-Null
    }
    
    # Footer avec informations utiles
    $summary.AppendLine("---") | Out-Null
    $summary.AppendLine("") | Out-Null
    $summary.AppendLine("**Resume genere automatiquement par Convert-TraceToSummary-Final.ps1**") | Out-Null
    $summary.AppendLine("**Date :** $(Get-Date -Format 'dd/MM/yyyy a HH:mm:ss')") | Out-Null
    
    # Ecriture du fichier avec gestion robuste de l'encodage
    Write-Host "Ecriture du resume..." -ForegroundColor Green
    $summaryContent = $summary.ToString()
    
    try {
        $utf8NoBom = New-Object System.Text.UTF8Encoding $false
        [System.IO.File]::WriteAllText($OutputPath, $summaryContent, $utf8NoBom)
        
        $outputSize = $summaryContent.Length
        $compressionRatio = [math]::Round(($sourceSize / $outputSize), 2)
        
        Write-Host "CONVERSION REUSSIE !" -ForegroundColor Green
        Write-Host "Fichier cree : $OutputPath" -ForegroundColor Cyan
        Write-Host "Statistiques finales :" -ForegroundColor Yellow
        Write-Host "   - Taille source : $([math]::Round($sourceSize/1024, 2)) KB" -ForegroundColor White
        Write-Host "   - Taille resume : $([math]::Round($outputSize/1024, 2)) KB" -ForegroundColor White
        Write-Host "   - Compression : ${compressionRatio}x" -ForegroundColor Green
        
        # Affichage des statistiques détaillees dans la console
        Write-Host ""
        $statsData = @(
            [pscustomobject]@{Type="Messages User"; Count=$userMessageCount; Taille="$([math]::Round($userTotalSize/1024, 1)) KB"; Pct="$userPercentage%"};
            [pscustomobject]@{Type="Reponses Assistant"; Count=$assistantMatches.Count; Taille="$([math]::Round($assistantTotalSize/1024, 1)) KB"; Pct="$assistantPercentage%"};
            [pscustomobject]@{Type="Resultats d'outils"; Count=$toolResultsCount; Taille="$([math]::Round($toolResultsSize/1024, 1)) KB"; Pct="$toolResultsPercentage%"}
        )
        Write-Host "Repartition du contenu :" -ForegroundColor Yellow
        $statsData | Format-Table -AutoSize | Out-String | Write-Host
        
        return @{
            Success = $true
            SourceFile = $TracePath
            OutputFile = $OutputPath
            SourceSize = $sourceSize
            OutputSize = $outputSize
            CompressionRatio = $compressionRatio
            Sections = $allSections.Count
        }
    } catch {
        Write-Error "Erreur lors de l'ecriture: $($_.Exception.Message)"
        return @{
            Success = $false
            SourceFile = $TracePath
            OutputPath = $OutputPath
            Error = $_.Exception.Message
        }
    }
}

# Fonction pour appliquer la troncature basee sur le nombre de caracteres
function Apply-ContentTruncation {
    param(
        [string]$OutputPath,
        [int]$MaxChars
    )
    
    Write-Host "Application de la troncature: $MaxChars caracteres max" -ForegroundColor Yellow
    $content = Get-Content $OutputPath -Raw -Encoding UTF8
    $originalSize = $content.Length
    $truncationsApplied = 0
    
    # Appliquer troncature sur toutes les balises de contenu volumineux
    $patternsToTruncate = @(
        '(?s)(<content>)(.*?)(</content>)',
        '(?s)(<arguments>)(.*?)(</arguments>)',
        '(?s)(```[^\n]*\n)(.*?)(```)',
        '(?s)(<diff>)(.*?)(</diff>)',
        '(?s)(<command>)(.*?)(</command>)'
    )
    
    foreach ($pattern in $patternsToTruncate) {
        $content = $content -replace $pattern, {
        param($match)
        $before = $match.Groups[1].Value
        $fullContent = $match.Groups[2].Value
        $after = $match.Groups[3].Value
        
        if ($fullContent.Length -gt $MaxChars) {
            $truncationsApplied++
            $keepStart = [math]::Floor($MaxChars * 0.4)
            $keepEnd = [math]::Floor($MaxChars * 0.4)
            $omitted = $fullContent.Length - $keepStart - $keepEnd
            
            $truncated = $fullContent.Substring(0, $keepStart) +
                         "`n[... $omitted caracteres omis ...]`n" +
                         $fullContent.Substring($fullContent.Length - $keepEnd, $keepEnd)
            return $before + $truncated + $after
        }
        return $match.Value
        }
    }
    
    # Si aucune troncature appliquée, ne pas réécrire le fichier
    if ($truncationsApplied -gt 0) {
        [System.IO.File]::WriteAllText($OutputPath, $content, [System.Text.Encoding]::UTF8)
        $newSize = $content.Length
        $gain = [math]::Round((($originalSize - $newSize) / $originalSize * 100), 2)
        Write-Host "-> Troncatures appliquees: $truncationsApplied" -ForegroundColor Green
        Write-Host "-> Nouvelle taille: $newSize octets (gain de $gain %)" -ForegroundColor Green
    } else {
        Write-Host "-> Aucune troncature nécessaire (pas de contenu > $MaxChars caractères)" -ForegroundColor Yellow
        Write-Host "-> Fichier inchangé: $originalSize octets" -ForegroundColor Yellow
    }
}

# Execution principale avec parametres de ligne de commande
if ($TracePath -and $TracePath -ne "") {
    Write-Host "EXECUTION DU SCRIPT AVEC PARAMETRES" -ForegroundColor Yellow
    Write-Host "TracePath: $TracePath" -ForegroundColor Cyan
    
    # Si GenerateAllVariants est specifie, generer toutes les combinaisons
    if ($GenerateAllVariants) {
        $baseName = [System.IO.Path]::GetFileNameWithoutExtension($TracePath)
        # Résoudre le chemin absolu pour éviter les problèmes de Join-Path avec chemins relatifs
        $resolvedTracePath = (Resolve-Path $TracePath -ErrorAction SilentlyContinue).Path
        if (-not $resolvedTracePath) { $resolvedTracePath = $TracePath }
        $baseDir = [System.IO.Path]::GetDirectoryName($resolvedTracePath)
        $detailLevels = @("Full", "Messages", "Summary")
        Write-Host "GENERATION DES VARIANTES DE LECTURE..." -ForegroundColor Yellow
        Write-Host "Fichier source: $baseName" -ForegroundColor Cyan
        Write-Host "Repertoire: $baseDir" -ForegroundColor Cyan
        
        foreach ($detail in $detailLevels) {
            $readableFileName = "${baseName}_lecture_${detail}.md"
            $currentOutputPath = Join-Path $baseDir $readableFileName
            
            Write-Host "Generation: $readableFileName" -ForegroundColor Green
            
            $result = Convert-TraceToSummary -TracePath $TracePath -OutputPath $currentOutputPath -ShowDetails:$ShowDetails -DetailLevel $detail -CompactStats:$CompactStats
        }
        
        Write-Host "GENERATION DE TOUTES LES VARIANTES TERMINEE" -ForegroundColor Green
        exit 0
    }
    
    if ([string]::IsNullOrWhiteSpace($OutputPath)) {
        $baseName = [System.IO.Path]::GetFileNameWithoutExtension($TracePath)
        # Résoudre le chemin absolu pour éviter les problèmes de Join-Path avec chemins relatifs
        $resolvedTracePath = (Resolve-Path $TracePath -ErrorAction SilentlyContinue).Path
        if (-not $resolvedTracePath) { $resolvedTracePath = $TracePath }
        $baseDir = [System.IO.Path]::GetDirectoryName($resolvedTracePath)
        $suffix = "_$DetailLevel"
        if ($TruncationChars -gt 0) { $suffix += "_T$TruncationChars" }
        if ($CompactStats) { $suffix += "_Compact" }
        $OutputPath = Join-Path $baseDir "${baseName}${suffix}.md"
    }
    Write-Host "OutputPath: $OutputPath" -ForegroundColor Cyan
    Write-Host "TruncationChars: $TruncationChars" -ForegroundColor Magenta
    
    $result = Convert-TraceToSummary -TracePath $TracePath -OutputPath $OutputPath -ShowDetails:$ShowDetails -DetailLevel $DetailLevel -CompactStats:$CompactStats
    
    if ($result.Success) {
        # POST-TRAITEMENT: Appliquer la troncature si demandee
        if ($TruncationChars -gt 0) {
            Apply-ContentTruncation -OutputPath $OutputPath -MaxChars $TruncationChars
        }
        
        Write-Host "CONVERSION TERMINEE AVEC SUCCES" -ForegroundColor Green
        exit 0
    } else {
        Write-Host "CONVERSION ECHOUEE" -ForegroundColor Red
        Write-Host "Erreur: $($result.Error)" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "Usage: .\Convert-TraceToSummary-Optimized.ps1 <TracePath> [OutputPath] [-ShowDetails]" -ForegroundColor Yellow
    Write-Host "Exemple: .\Convert-TraceToSummary-Optimized.ps1 'input.md'" -ForegroundColor Yellow
    Write-Host "" -ForegroundColor Yellow
    Write-Host "Options:" -ForegroundColor Yellow
    Write-Host "  -DetailLevel       : Full, NoTools, NoResults, Messages, Summary, UserOnly (defaut: Full)" -ForegroundColor Gray
    Write-Host "  -TruncationChars   : Nombre max de caracteres pour <content> (defaut: 0 = pas de troncature)" -ForegroundColor Gray
    Write-Host "  -GenerateAllVariants : Genere toutes les combinaisons possibles" -ForegroundColor Gray
}