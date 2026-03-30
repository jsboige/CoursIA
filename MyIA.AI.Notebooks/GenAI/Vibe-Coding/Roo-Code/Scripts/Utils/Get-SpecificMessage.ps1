# -*- coding: utf-8 -*-

function Get-SpecificMessage {
    param(
        [Parameter(Mandatory = $true)]
        [string]$InputFile,
        
        [Parameter(Mandatory = $true)]
        [int]$MessageNumber
    )
    
    # Configurer l'encodage UTF-8
    $OutputEncoding = [console]::OutputEncoding = [console]::InputEncoding = [System.Text.Encoding]::UTF8
    [Console]::OutputEncoding = [System.Text.UTF8Encoding]::new()
    
    Write-Host "Configuration UTF-8 chargée automatiquement" -ForegroundColor Green
    
    if (-not (Test-Path $InputFile)) {
        Write-Error "Le fichier $InputFile n'existe pas."
        return
    }
    
    Write-Host "Lecture du fichier: $InputFile" -ForegroundColor Cyan
    $content = Get-Content -Path $InputFile -Raw -Encoding UTF8
    
    # Supprimer les environment_details
    $content = [System.Text.RegularExpressions.Regex]::Replace($content, '(?ms)<environment_details>.*?</environment_details>', '')
    
    # Patterns pour identifier les sections
    $userPattern = '---\s*\r?\n\s*\*\*User:\*\*'
    $assistantPattern = '---\s*\r?\n\s*\*\*Assistant:\*\*'
    $combinedPattern = '---\s*\r?\n\s*\*\*(User|Assistant):\*\*'
    
    # Patterns pour filtrer le contenu d'outil
    $toolPatterns = @(
        '^(.*Result:)',
        '^\[.*\] Result:',
        '^\s*<files>',
        '^\s*<file>',
        '^Command executed in terminal',
        '^Output:',
        '^Exit code:',
        '^The .* has been',
        '^<.*>$'
    )
    
    # Diviser le contenu en sections
    Write-Host "Division en sections..." -ForegroundColor Yellow
    $sections = [System.Text.RegularExpressions.Regex]::Split($content, $combinedPattern)
    
    if ($sections.Length -lt 2) {
        Write-Host "Aucune section trouvée avec les patterns définis." -ForegroundColor Red
        return
    }
    
    Write-Host "Sections trouvées: $($sections.Length)" -ForegroundColor Yellow
    
    $messageCount = 0
    
    # Parcourir les sections par groupes de 2 (header + content)
    for ($i = 1; $i -lt $sections.Length - 1; $i += 2) {
        $header = $sections[$i].Trim()
        $content = $sections[$i + 1].Trim()
        
        if ($header -eq 'User' -and -not [string]::IsNullOrWhiteSpace($content)) {
            # Vérifier si c'est un message utilisateur authentique
            $isToolOutput = $false
            foreach ($pattern in $toolPatterns) {
                if ($content -match $pattern) {
                    $isToolOutput = $true
                    break
                }
            }
            
            if (-not $isToolOutput) {
                $messageCount++
                if ($messageCount -eq $MessageNumber) {
                    Write-Host "=== MESSAGE #$MessageNumber TROUVÉ ===" -ForegroundColor Green
                    Write-Host "Longueur: $($content.Length) caractères" -ForegroundColor Cyan
                    Write-Host "Contenu:" -ForegroundColor Yellow
                    Write-Host "----------------------------------------" -ForegroundColor Gray
                    return $content
                }
            }
        }
    }
    
    Write-Host "Message #$MessageNumber non trouvé. Total des messages authentiques: $messageCount" -ForegroundColor Red
}

# Exporter la fonction pour utilisation directe
Export-ModuleMember -Function Get-SpecificMessage