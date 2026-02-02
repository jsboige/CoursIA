param(
    [string]$InputFile,
    [switch]$ShowPreview
)

if (-not (Test-Path $InputFile)) {
    Write-Error "Le fichier $InputFile n'existe pas."
    exit 1
}

Write-Host "Analyse du fichier: $InputFile" -ForegroundColor Green

# Lire tout le contenu
$content = Get-Content $InputFile -Raw -Encoding UTF8

# Patterns des retours d'outils à exclure
$toolPatterns = @(
    '^\[.*\] Result:',
    '^\s*<files>',
    '^\s*<file><path>',
    '^\s*</files>',
    '^\s*<environment_details>',
    '^Tool \[.*\] was not executed'
)

# Split en sections basé sur les délimiteurs User/Assistant
$sections = $content -split '(?s)(?=\*\*(?:User|Assistant):\*\*)'

Write-Host "Sections trouvees: $($sections.Count)" -ForegroundColor Yellow

$authenticUserMessages = @()
$messageNumber = 0

foreach ($section in $sections) {
    if ($section -match '^\*\*User:\*\*(.*)') {
        $messageNumber++
        $userContent = $section.Substring($section.IndexOf("**User:**") + "**User:**".Length).Trim()
        
        # Vérifier si c'est un retour d'outil
        $isToolResult = $false
        foreach ($pattern in $toolPatterns) {
            if ($userContent -match $pattern) {
                $isToolResult = $true
                break
            }
        }
        
        # Si ce n'est pas un retour d'outil, c'est un vrai message utilisateur
        if (-not $isToolResult) {
            $authenticMessage = @{
                MessageNumber = $messageNumber
                Preview = ($userContent -split "`n" | Select-Object -First 1) -join ""
                FullContent = $userContent
                Length = $userContent.Length
            }
            
            $authenticUserMessages += $authenticMessage
        }
    }
}

# Afficher les résultats
Write-Host ""
Write-Host "Messages utilisateur authentiques trouves: $($authenticUserMessages.Count)" -ForegroundColor Green

foreach ($msg in $authenticUserMessages) {
    Write-Host ""
    Write-Host "Message #$($msg.MessageNumber)" -ForegroundColor Yellow
    Write-Host "   Longueur: $($msg.Length) caracteres" -ForegroundColor Gray
    
    if ($ShowPreview) {
        $previewText = $msg.Preview
        if ($previewText.Length -gt 100) {
            $previewText = $previewText.Substring(0, 100) + "..."
        }
        Write-Host "   Apercu: $previewText" -ForegroundColor Cyan
    }
}

Write-Host ""
Write-Host "Analyse terminee!" -ForegroundColor Green
Write-Host "   Total messages User trouves: $messageNumber" -ForegroundColor Yellow
Write-Host "   Messages authentiques: $($authenticUserMessages.Count)" -ForegroundColor Green