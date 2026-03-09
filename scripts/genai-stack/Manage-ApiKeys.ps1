<#
.SYNOPSIS
    Generate and manage API keys for AI services.

.DESCRIPTION
    This script generates secure API keys and configures IIS URL Rewrite rules
    to validate API keys on protected services.

.PARAMETER Action
    Action: Generate, Configure, List, Export

.PARAMETER ServiceName
    Specific service name (optional, defaults to all API services)

.PARAMETER OutputPath
    Path to save API keys (defaults to D:\Production\.secrets\api-keys.json)

.EXAMPLE
    .\Manage-ApiKeys.ps1 -Action Generate
    .\Manage-ApiKeys.ps1 -Action Configure -ServiceName "embeddings.myia.io"
    .\Manage-ApiKeys.ps1 -Action Export -OutputPath "C:\secure\api-keys.json"
#>

param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("Generate", "Configure", "List", "Export")]
    [string]$Action,

    [string]$ServiceName,

    [string]$OutputPath = "D:\Production\.secrets\api-keys.json"
)

# =============================================================================
# Configuration
# =============================================================================

$ApiServices = @(
    @{ Name = "whisper-api.myia.io"; Description = "Whisper Speech-to-Text API" },
    @{ Name = "tts-api.myia.io"; Description = "Text-to-Speech API" },
    @{ Name = "musicgen-api.myia.io"; Description = "MusicGen Music Generation API" },
    @{ Name = "demucs-api.myia.io"; Description = "Demucs Audio Separation API" },
    @{ Name = "mcp-tools.myia.io"; Description = "MCP Tools API" },
    @{ Name = "skagents.myia.io"; Description = "Semantic Kernel Agents API" },
    @{ Name = "embeddings.myia.io"; Description = "Embeddings API" },
    @{ Name = "qdrant.myia.io"; Description = "Qdrant Vector Database" },
    @{ Name = "students.qdrant.myia.io"; Description = "Qdrant Students Instance" },
    @{ Name = "search.myia.io"; Description = "Search API" },
    @{ Name = "api.micro.text-generation-webui.myia.io"; Description = "Text Generation API (micro)" },
    @{ Name = "api.mini.text-generation-webui.myia.io"; Description = "Text Generation API (mini)" },
    @{ Name = "api.medium.text-generation-webui.myia.io"; Description = "Text Generation API (medium)" },
    @{ Name = "api.large.text-generation-webui.myia.io"; Description = "Text Generation API (large)" }
)

# =============================================================================
# Helper Functions
# =============================================================================

function New-SecureApiKey {
    param([int]$Length = 32)

    # Generate cryptographically secure random bytes
    $bytes = New-Object byte[] $Length
    [Security.Cryptography.RNGCryptoServiceProvider]::Create().GetBytes($bytes)

    # Convert to base64 and make URL-safe
    $base64 = [Convert]::ToBase64String($bytes)
    return $base64 -replace '\+', '-' -replace '/', '_' -replace '=', ''
}

function Get-ApiKeyConfig {
    if (Test-Path $OutputPath) {
        $content = Get-Content $OutputPath -Raw -Encoding UTF8
        # Handle BOM
        $content = $content -replace '^\xEF\xBB\xBF', ''
        return $content | ConvertFrom-Json
    }
    return @{
        keys = @()
        generated = $null
        version = "1.0"
    }
}

function Save-ApiKeyConfig {
    param($Config)

    $dir = Split-Path $OutputPath -Parent
    if (-not (Test-Path $dir)) {
        New-Item -ItemType Directory -Path $dir -Force | Out-Null
    }

    $Config | ConvertTo-Json -Depth 10 | Set-Content $OutputPath -Encoding UTF8

    # Set restrictive permissions
    $acl = Get-Acl $OutputPath
    $acl.SetAccessRuleProtection($true, $false)
    $rule = New-Object System.Security.AccessControl.FileSystemAccessRule(
        $env:USERNAME, "FullControl", "Allow"
    )
    $acl.SetAccessRule($rule)
    Set-Acl $OutputPath $acl
}

function Add-ApiKeyRewriteRule {
    param(
        [string]$SiteName,
        [string]$ApiKey
    )

    $webConfigPath = "D:\Production\$SiteName\web.config"

    if (-not (Test-Path $webConfigPath)) {
        Write-Host "  ERROR: web.config not found at $webConfigPath" -ForegroundColor Red
        return $false
    }

    [xml]$webConfig = Get-Content $webConfigPath

    # Check if API key rule already exists
    $rulesNode = $webConfig.configuration."system.webServer".rewrite.rules
    $existingRule = $rulesNode.rule | Where-Object { $_.name -eq "ApiKeyValidation" }

    if ($existingRule) {
        Write-Host "  Updating existing API key rule..."
        # Update the condition
        $condition = $existingRule.conditions.add
        $condition.pattern = "^$ApiKey$"
    } else {
        Write-Host "  Creating new API key validation rule..."

        # Create the rule element
        $newRule = $webConfig.CreateElement("rule")
        $newRule.SetAttribute("name", "ApiKeyValidation")
        $newRule.SetAttribute("stopProcessing", "true")

        # Create match element
        $match = $webConfig.CreateElement("match")
        $match.SetAttribute("url", ".*")
        $newRule.AppendChild($match) | Out-Null

        # Create conditions element
        $conditions = $webConfig.CreateElement("conditions")

        # Add health check exclusion
        $condHealth = $webConfig.CreateElement("add")
        $condHealth.SetAttribute("input", "{URL}")
        $condHealth.SetAttribute("pattern", "^/(health|status|ping)$")
        $condHealth.SetAttribute("negate", "true")
        $conditions.AppendChild($condHealth) | Out-Null

        # Add API key header check
        $condKey = $webConfig.CreateElement("add")
        $condKey.SetAttribute("input", "{HTTP_X_API_KEY}")
        $condKey.SetAttribute("pattern", "^$ApiKey$")
        $conditions.AppendChild($condKey) | Out-Null

        $newRule.AppendChild($conditions) | Out-Null

        # Create action element (return 401 if no valid key)
        $action = $webConfig.CreateElement("action")
        $action.SetAttribute("type", "CustomResponse")
        $action.SetAttribute("statusCode", "401")
        $action.SetAttribute("statusReason", "Unauthorized")
        $action.SetAttribute("statusDescription", "Valid API key required")
        $newRule.AppendChild($action) | Out-Null

        # Insert at beginning of rules
        $rulesNode.PrependChild($newRule) | Out-Null
    }

    # Save the modified config
    $webConfig.Save($webConfigPath)
    Write-Host "  web.config updated successfully" -ForegroundColor Green
    return $true
}

# =============================================================================
# Main Actions
# =============================================================================

switch ($Action) {
    "Generate" {
        Write-Host "`n========================================" -ForegroundColor Cyan
        Write-Host "Generating API Keys" -ForegroundColor Cyan
        Write-Host "========================================`n" -ForegroundColor Cyan

        $config = @{
            keys = @()
            generated = (Get-Date -Format "o")
            version = "1.0"
        }

        foreach ($service in $ApiServices) {
            $apiKey = New-SecureApiKey -Length 32

            $keyEntry = @{
                service = $service.Name
                description = $service.Description
                apiKey = $apiKey
                created = (Get-Date -Format "o")
            }

            $config.keys += $keyEntry

            # Show key (only during generation)
            Write-Host "$($service.Name):" -ForegroundColor Yellow
            Write-Host "  API Key: $apiKey"
            Write-Host "  Description: $($service.Description)"
            Write-Host ""
        }

        # Ensure directory exists
        $dir = Split-Path $OutputPath -Parent
        if (-not (Test-Path $dir)) {
            New-Item -ItemType Directory -Path $dir -Force | Out-Null
            Write-Host "Created directory: $dir" -ForegroundColor Green
        }

        Save-ApiKeyConfig -Config $config
        Write-Host "API keys saved to: $OutputPath" -ForegroundColor Green
        Write-Host "`nWARNING: Store these keys securely!" -ForegroundColor Yellow
    }

    "Configure" {
        Write-Host "`n========================================" -ForegroundColor Cyan
        Write-Host "Configuring IIS API Key Validation" -ForegroundColor Cyan
        Write-Host "========================================`n" -ForegroundColor Cyan

        $config = Get-ApiKeyConfig

        if ($config.keys.Count -eq 0) {
            Write-Host "No API keys found. Run -Action Generate first." -ForegroundColor Red
            exit 1
        }

        $servicesToProcess = if ($ServiceName) {
            $config.keys | Where-Object { $_.service -eq $ServiceName }
        } else {
            $config.keys
        }

        if (-not $servicesToProcess) {
            Write-Host "Service not found: $ServiceName" -ForegroundColor Red
            exit 1
        }

        $successCount = 0
        foreach ($keyEntry in $servicesToProcess) {
            Write-Host "Configuring: $($keyEntry.service)"
            if (Add-ApiKeyRewriteRule -SiteName $keyEntry.service -ApiKey $keyEntry.apiKey) {
                $successCount++
            }
        }

        Write-Host "`nConfigured $successCount of $($servicesToProcess.Count) services." -ForegroundColor Green
        Write-Host "Restart IIS to apply changes: iisreset" -ForegroundColor Yellow
    }

    "List" {
        Write-Host "`n========================================" -ForegroundColor Cyan
        Write-Host "API Keys Summary" -ForegroundColor Cyan
        Write-Host "========================================`n" -ForegroundColor Cyan

        $config = Get-ApiKeyConfig

        if ($config.keys.Count -eq 0) {
            Write-Host "No API keys configured." -ForegroundColor Yellow
            Write-Host "Run: .\Manage-ApiKeys.ps1 -Action Generate" -ForegroundColor Yellow
            exit 0
        }

        Write-Host "Generated: $($config.generated)"
        Write-Host "Total keys: $($config.keys.Count)`n"

        foreach ($keyEntry in $config.keys) {
            $maskedKey = $keyEntry.apiKey.Substring(0, 8) + "..." + $keyEntry.apiKey.Substring($keyEntry.apiKey.Length - 4)
            Write-Host "$($keyEntry.service):" -ForegroundColor Yellow
            Write-Host "  Key: $maskedKey"
            Write-Host "  Description: $($keyEntry.description)"
            Write-Host "  Created: $($keyEntry.created)"
        }
    }

    "Export" {
        $config = Get-ApiKeyConfig

        if ($config.keys.Count -eq 0) {
            Write-Host "No API keys to export." -ForegroundColor Red
            exit 1
        }

        $exportPath = if ($OutputPath) { $OutputPath } else { ".\api-keys-export.json" }
        $config | ConvertTo-Json -Depth 10 | Set-Content $exportPath -Encoding UTF8

        Write-Host "Exported $($config.keys.Count) API keys to: $exportPath" -ForegroundColor Green
        Write-Host "`nWARNING: This file contains sensitive data. Store securely!" -ForegroundColor Red
    }
}
