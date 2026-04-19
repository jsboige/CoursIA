<#
.SYNOPSIS
    Configure IIS authentication for AI services security.

.DESCRIPTION
    This script configures authentication for AI services exposed via IIS reverse proxy.
    - UIs with native login: Disable anonymous, let the app handle auth
    - APIs: Enable basic authentication or configure API key validation

.PARAMETER Action
    Action to perform: Audit, Configure, or Test

.PARAMETER ServiceType
    Type of services to configure: UI, API, or All

.PARAMETER DryRun
    Preview changes without applying them

.EXAMPLE
    .\Configure-IISAuthentication.ps1 -Action Audit
    .\Configure-IISAuthentication.ps1 -Action Configure -ServiceType API -DryRun
#>

param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("Audit", "Configure", "Test")]
    [string]$Action,

    [Parameter(Mandatory=$false)]
    [ValidateSet("UI", "API", "All")]
    [string]$ServiceType = "All",

    [switch]$DryRun
)

# =============================================================================
# Service Definitions
# =============================================================================

$UIServices = @(
    "stable-diffusion-webui-forge.myia.io",
    "turbo.stable-diffusion-webui-forge.myia.io",
    "sdnext.myia.io",
    "micro.text-generation-webui.myia.io",
    "mini.text-generation-webui.myia.io",
    "medium.text-generation-webui.myia.io",
    "large.text-generation-webui.myia.io",
    "whisper-webui.myia.io"
)

$APIServices = @(
    "whisper-api.myia.io",
    "tts-api.myia.io",
    "musicgen-api.myia.io",
    "demucs-api.myia.io",
    "mcp-tools.myia.io",
    "skagents.myia.io",
    "embeddings.myia.io",
    "qdrant.myia.io",
    "students.qdrant.myia.io",
    "search.myia.io",
    "api.micro.text-generation-webui.myia.io",
    "api.mini.text-generation-webui.myia.io",
    "api.medium.text-generation-webui.myia.io",
    "api.large.text-generation-webui.myia.io"
)

# Already secured services (have their own auth)
$SecuredServices = @(
    "open-webui.myia.io",
    "dify.myia.io",
    "sillytavern.myia.io",
    "epf.open-webui.myia.io",
    "esg.open-webui.myia.io",
    "ece.open-webui.myia.io",
    "pipelines.open-webui.myia.io",
    "genai.epf.open-webui.myia.io",
    "epita.open-webui.myia.io",
    "tika.open-webui.myia.io",
    "pauwels.open-webui.myia.io",
    "michelle.myia.io"
)

# =============================================================================
# Helper Functions
# =============================================================================

function Get-AuthStatus {
    param([string]$SiteName)

    try {
        $anonConfig = Get-IISConfigSection -SectionPath 'system.webServer/security/authentication/anonymousAuthentication' -Location $SiteName
        $anonEnabled = $anonConfig | Get-IISConfigAttributeValue -AttributeName 'enabled'

        $basicConfig = Get-IISConfigSection -SectionPath 'system.webServer/security/authentication/basicAuthentication' -Location $SiteName
        $basicEnabled = $basicConfig | Get-IISConfigAttributeValue -AttributeName 'enabled'

        return @{
            Site = $SiteName
            Anonymous = $anonEnabled
            Basic = $basicEnabled
            Secured = (-not $anonEnabled) -or $basicEnabled
        }
    } catch {
        return @{
            Site = $SiteName
            Anonymous = "Error"
            Basic = "Error"
            Secured = $false
            Error = $_.Exception.Message
        }
    }
}

function Set-UIAuthentication {
    param([string]$SiteName, [bool]$DryRun)

    Write-Host "Configuring UI authentication for: $SiteName"

    if ($DryRun) {
        Write-Host "  [DRYRUN] Would disable anonymous authentication"
        return $true
    }

    try {
        # Disable anonymous authentication - let the app handle auth
        $anonConfig = Get-IISConfigSection -SectionPath 'system.webServer/security/authentication/anonymousAuthentication' -Location $SiteName
        $anonConfig | Set-IISConfigAttributeValue -AttributeName 'enabled' -AttributeValue $false

        Write-Host "  Disabled anonymous authentication" -ForegroundColor Green
        return $true
    } catch {
        Write-Host "  Error: $($_.Exception.Message)" -ForegroundColor Red
        return $false
    }
}

function Set-APIAuthentication {
    param([string]$SiteName, [bool]$DryRun)

    Write-Host "Configuring API authentication for: $SiteName"

    if ($DryRun) {
        Write-Host "  [DRYRUN] Would disable anonymous and enable basic authentication"
        return $true
    }

    try {
        # Disable anonymous authentication
        $anonConfig = Get-IISConfigSection -SectionPath 'system.webServer/security/authentication/anonymousAuthentication' -Location $SiteName
        $anonConfig | Set-IISConfigAttributeValue -AttributeName 'enabled' -AttributeValue $false

        # Enable basic authentication
        $basicConfig = Get-IISConfigSection -SectionPath 'system.webServer/security/authentication/basicAuthentication' -Location $SiteName
        $basicConfig | Set-IISConfigAttributeValue -AttributeName 'enabled' -AttributeValue $true

        Write-Host "  Configured basic authentication" -ForegroundColor Green
        return $true
    } catch {
        Write-Host "  Error: $($_.Exception.Message)" -ForegroundColor Red
        return $false
    }
}

function Test-ServiceAccess {
    param([string]$SiteName)

    try {
        $url = "https://$SiteName"
        $response = Invoke-WebRequest -Uri $url -Method Get -TimeoutSec 5 -UseBasicParsing -ErrorAction Stop
        return @{
            Site = $SiteName
            Status = $response.StatusCode
            AuthRequired = $false
        }
    } catch {
        $statusCode = $_.Exception.Response.StatusCode.value__
        if ($statusCode -eq 401) {
            return @{
                Site = $SiteName
                Status = 401
                AuthRequired = $true
            }
        }
        return @{
            Site = $SiteName
            Status = $statusCode
            AuthRequired = ($statusCode -eq 401)
            Error = $_.Exception.Message
        }
    }
}

# =============================================================================
# Main Actions
# =============================================================================

switch ($Action) {
    "Audit" {
        Write-Host "`n========================================" -ForegroundColor Cyan
        Write-Host "IIS Authentication Audit Report" -ForegroundColor Cyan
        Write-Host "========================================`n" -ForegroundColor Cyan

        $servicesToCheck = @()
        if ($ServiceType -in @("UI", "All")) { $servicesToCheck += $UIServices }
        if ($ServiceType -in @("API", "All")) { $servicesToCheck += $APIServices }

        $results = @()
        foreach ($service in $servicesToCheck) {
            $status = Get-AuthStatus -SiteName $service
            $results += $status

            $statusIcon = if ($status.Secured) { "[SECURED]" } else { "[EXPOSED]" }
            $color = if ($status.Secured) { "Green" } else { "Red" }
            Write-Host "$statusIcon $($status.Site)" -ForegroundColor $color
            Write-Host "  Anonymous: $($status.Anonymous), Basic: $($status.Basic)"
        }

        # Summary
        $exposed = $results | Where-Object { -not $_.Secured }
        $secured = $results | Where-Object { $_.Secured }

        Write-Host "`n--- Summary ---" -ForegroundColor Yellow
        Write-Host "Total services checked: $($results.Count)"
        Write-Host "Secured: $($secured.Count)" -ForegroundColor Green
        Write-Host "Exposed (need configuration): $($exposed.Count)" -ForegroundColor Red

        if ($exposed.Count -gt 0) {
            Write-Host "`nServices requiring configuration:" -ForegroundColor Yellow
            $exposed | ForEach-Object { Write-Host "  - $($_.Site)" }
        }
    }

    "Configure" {
        Write-Host "`n========================================" -ForegroundColor Cyan
        Write-Host "Configuring IIS Authentication" -ForegroundColor Cyan
        if ($DryRun) {
            Write-Host "[DRYRUN MODE - No changes will be made]" -ForegroundColor Yellow
        }
        Write-Host "========================================`n" -ForegroundColor Cyan

        # Configure UI services
        if ($ServiceType -in @("UI", "All")) {
            Write-Host "`n--- UI Services (app-native auth) ---" -ForegroundColor Yellow
            foreach ($service in $UIServices) {
                Set-UIAuthentication -SiteName $service -DryRun $DryRun
            }
        }

        # Configure API services
        if ($ServiceType -in @("API", "All")) {
            Write-Host "`n--- API Services (basic auth) ---" -ForegroundColor Yellow
            foreach ($service in $APIServices) {
                Set-APIAuthentication -SiteName $service -DryRun $DryRun
            }
        }

        if (-not $DryRun) {
            Write-Host "`nConfiguration complete. Testing access..." -ForegroundColor Green
        }
    }

    "Test" {
        Write-Host "`n========================================" -ForegroundColor Cyan
        Write-Host "Testing Service Access" -ForegroundColor Cyan
        Write-Host "========================================`n" -ForegroundColor Cyan

        $servicesToTest = @()
        if ($ServiceType -in @("UI", "All")) { $servicesToTest += $UIServices }
        if ($ServiceType -in @("API", "All")) { $servicesToTest += $APIServices }

        foreach ($service in $servicesToTest) {
            $result = Test-ServiceAccess -SiteName $service
            $statusIcon = if ($result.AuthRequired) { "[AUTH OK]" } else { "[NO AUTH]" }
            $color = if ($result.AuthRequired) { "Green" } else { "Red" }
            Write-Host "$statusIcon $($result.Site) - Status: $($result.Status)" -ForegroundColor $color
        }
    }
}
