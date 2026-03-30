# Script de configuration IIS Reverse Proxy pour TTS Multi Gateway
# Service: tts-multi (Kokoro + TADA + Qwen3)
# Date: 2026-03-19

param(
    [string]$SiteName = "tts-multi.myia.io",
    [string]$SitePath = "D:\Production\tts-multi.myia.io",
    [int]$Port = 8196
)

Write-Host ""
Write-Host "Configuration IIS Reverse Proxy - TTS Multi Gateway" -ForegroundColor Cyan
Write-Host "Site: $SiteName -> localhost:$Port" -ForegroundColor Cyan
Write-Host ""

# Verifier si execute en admin
$isAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
if (-not $isAdmin) {
    Write-Host "ERREUR: Ce script doit etre execute en tant qu'Administrateur" -ForegroundColor Red
    exit 1
}

# Import module IIS
try {
    Import-Module WebAdministration -ErrorAction Stop
    Write-Host "[OK] Module WebAdministration charge" -ForegroundColor Green
}
catch {
    Write-Host "ERREUR: Module WebAdministration introuvable" -ForegroundColor Red
    Write-Host "  Installez IIS avec ARR:" -ForegroundColor Yellow
    Write-Host "  Install-WindowsFeature -Name Web-Server -IncludeManagementTools" -ForegroundColor White
    exit 1
}

# Creer repertoire site
New-Item -ItemType Directory -Path $SitePath -Force | Out-Null
Write-Host "[OK] Repertoire cree: $SitePath" -ForegroundColor Green

# Creer web.config avec reverse proxy
$webConfig = @"
<?xml version="1.0" encoding="UTF-8"?>
<configuration>
    <system.webServer>
        <!-- Reverse Proxy for TTS Multi Gateway -->
        <rewrite>
            <rules>
                <rule name="ReverseProxyInbound" stopProcessing="true">
                    <match url="(.*)" />
                    <action type="Rewrite" url="http://localhost:$Port/{R:1}" />
                    <serverVariables>
                        <set name="HTTP_X_ORIGINAL_ACCEPT_ENCODING" value="{HTTP_ACCEPT_ENCODING}" />
                        <set name="HTTP_ACCEPT_ENCODING" value="" />
                        <set name="HTTP_X_FORWARDED_FOR" value="{REMOTE_ADDR}" />
                        <set name="HTTP_X_FORWARDED_PROTO" value="https" />
                        <set name="HTTP_X_FORWARDED_HOST" value="{HTTP_HOST}" />
                    </serverVariables>
                </rule>
            </rules>
            <outboundRules>
                <rule name="RestoreAcceptEncoding" preCondition="NeedsRestore">
                    <match serverVariable="HTTP_ACCEPT_ENCODING" pattern="^(.*)" />
                    <action type="Rewrite" value="{HTTP_X_ORIGINAL_ACCEPT_ENCODING}" />
                </rule>
                <preConditions>
                    <preCondition name="NeedsRestore">
                        <add input="{HTTP_X_ORIGINAL_ACCEPT_ENCODING}" pattern=".+" />
                    </preCondition>
                </preConditions>
            </outboundRules>
        </rewrite>

        <!-- CORS Headers for TTS API -->
        <httpProtocol>
            <customHeaders>
                <add name="Access-Control-Allow-Origin" value="*" />
                <add name="Access-Control-Allow-Methods" value="GET, POST, OPTIONS" />
                <add name="Access-Control-Allow-Headers" value="Content-Type, Authorization, X-Requested-With" />
            </customHeaders>
        </httpProtocol>

        <!-- Request size limit for audio uploads (10MB) -->
        <security>
            <requestFiltering>
                <requestLimits maxAllowedContentLength="10485760" />
            </requestFiltering>
        </security>

        <!-- WebSocket support for streaming -->
        <webSocket enabled="true" />
    </system.webServer>
</configuration>
"@

$webConfig | Out-File -FilePath "$SitePath\web.config" -Encoding UTF8 -Force
Write-Host "[OK] web.config cree" -ForegroundColor Green

# Verifier si le site existe deja
$existingSite = Get-WebSite -Name $SiteName -ErrorAction SilentlyContinue
if ($existingSite) {
    Write-Host "[INFO] Site $SiteName existe deja, mise a jour..." -ForegroundColor Yellow
    Set-ItemProperty "IIS:\Sites\$SiteName" -Name physicalPath -Value $SitePath
} else {
    # Creer le site IIS
    # Port 80 d'abord, SSL sera ajoute apres
    New-WebSite -Name $SiteName -PhysicalPath $SitePath -HostHeader $SiteName -Port 80 -Force
    Write-Host "[OK] Site IIS cree: $SiteName" -ForegroundColor Green
}

# Configurer les Server Variables necessaires pour URL Rewrite
$serverVariables = @(
    "HTTP_X_ORIGINAL_ACCEPT_ENCODING",
    "HTTP_ACCEPT_ENCODING",
    "HTTP_X_FORWARDED_FOR",
    "HTTP_X_FORWARDED_PROTO",
    "HTTP_X_FORWARDED_HOST"
)

foreach ($var in $serverVariables) {
    try {
        # Check si la variable existe deja au niveau global
        $existing = Get-WebConfigurationProperty -PSPath "MACHINE/WEBROOT/APPHOST" -Filter "system.webServer/rewrite/allowedServerVariables/add[@name='$var']" -Name "." -ErrorAction SilentlyContinue
        if (-not $existing) {
            Add-WebConfigurationProperty -PSPath "MACHINE/WEBROOT/APPHOST" -Filter "system.webServer/rewrite/allowedServerVariables" -Name "." -Value @{name=$var}
            Write-Host "  [OK] Server variable ajoutee: $var" -ForegroundColor Gray
        }
    }
    catch {
        Write-Host "  [WARN] Server variable existante: $var" -ForegroundColor Yellow
    }
}

# Ajouter binding HTTPS si certificat wildcard *.myia.io existe
$cert = Get-ChildItem -Path "Cert:\LocalMachine\My" | Where-Object { $_.Subject -match "\*\.myia\.io" } | Select-Object -First 1
if ($cert) {
    try {
        New-WebBinding -Name $SiteName -Protocol "https" -Port 443 -HostHeader $SiteName -SslFlags 1
        $binding = Get-WebBinding -Name $SiteName -Protocol "https"
        $binding.AddSslCertificate($cert.Thumbprint, "My")
        Write-Host "[OK] HTTPS binding configure avec certificat *.myia.io" -ForegroundColor Green
    }
    catch {
        Write-Host "[WARN] HTTPS binding deja configure ou erreur: $_" -ForegroundColor Yellow
    }
} else {
    Write-Host "[WARN] Certificat *.myia.io non trouve - HTTPS non configure" -ForegroundColor Yellow
    Write-Host "  Ajoutez manuellement le binding HTTPS apres installation du certificat" -ForegroundColor Yellow
}

# Demarrer le site
Start-WebSite -Name $SiteName -ErrorAction SilentlyContinue
Write-Host "[OK] Site $SiteName demarre" -ForegroundColor Green

Write-Host ""
Write-Host "Configuration terminee!" -ForegroundColor Green
Write-Host ""
Write-Host "Endpoints disponibles:" -ForegroundColor Cyan
Write-Host "  Kokoro (defaut) : https://$SiteName/v1/audio/speech" -ForegroundColor White
Write-Host "  TADA            : https://$SiteName/tada/v1/audio/speech" -ForegroundColor White
Write-Host "  Qwen3           : https://$SiteName/qwen/v1/audio/speech" -ForegroundColor White
Write-Host "  Health          : https://$SiteName/health" -ForegroundColor White
Write-Host "  Models          : https://$SiteName/v1/models" -ForegroundColor White
Write-Host ""
Write-Host "Test:" -ForegroundColor Cyan
Write-Host "  curl https://$SiteName/health" -ForegroundColor White
Write-Host "  curl -X POST https://$SiteName/v1/audio/speech -H 'Content-Type: application/json' -d '{""input"":""Hello"",""voice"":""alloy""}' -o test.wav" -ForegroundColor White
