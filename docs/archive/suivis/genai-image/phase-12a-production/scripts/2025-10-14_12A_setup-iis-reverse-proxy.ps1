# Script de configuration IIS Reverse Proxy pour ComfyUI + Qwen
# Phase 12A: Production ComfyUI + Qwen Image-Edit
# Date: 2025-10-14

$SiteName = "qwen-image-edit.myia.io"
$SitePath = "D:\Production\$SiteName"
$Port = 8188

Write-Host ""
Write-Host "╔════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   Configuration IIS Reverse Proxy - Phase 12A         ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Vérifier si exécuté en admin
$isAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
if (-not $isAdmin) {
    Write-Host "❌ ERREUR: Ce script doit être exécuté en tant qu'Administrateur" -ForegroundColor Red
    Write-Host "   Clic droit > Exécuter en tant qu'administrateur" -ForegroundColor Yellow
    exit 1
}

# Import module IIS
try {
    Import-Module WebAdministration -ErrorAction Stop
    Write-Host "✅ Module WebAdministration chargé" -ForegroundColor Green
}
catch {
    Write-Host "❌ ERREUR: Module WebAdministration introuvable" -ForegroundColor Red
    Write-Host ""
    Write-Host "   Installez IIS avec Application Request Routing:" -ForegroundColor Yellow
    Write-Host "   Install-WindowsFeature -Name Web-Server -IncludeManagementTools" -ForegroundColor White
    Write-Host "   Install-WindowsFeature -Name Web-WebServer -IncludeManagementTools" -ForegroundColor White
    Write-Host ""
    exit 1
}

# Créer répertoire site
Write-Host ""
Write-Host "📁 Création du répertoire site..." -ForegroundColor Cyan
New-Item -ItemType Directory -Path $SitePath -Force | Out-Null
Write-Host "✅ Répertoire créé: $SitePath" -ForegroundColor Green

# Créer web.config avec reverse proxy
Write-Host ""
Write-Host "📝 Création du fichier web.config..." -ForegroundColor Cyan
$webConfig = @"
<?xml version="1.0" encoding="UTF-8"?>
<configuration>
    <system.webServer>
        <!-- Reverse Proxy Configuration -->
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
        
        <!-- CORS Headers pour ComfyUI -->
        <httpProtocol>
            <customHeaders>
                <add name="Access-Control-Allow-Origin" value="*" />
                <add name="Access-Control-Allow-Methods" value="GET, POST, PUT, DELETE, OPTIONS" />
                <add name="Access-Control-Allow-Headers" value="Content-Type, Authorization" />
            </customHeaders>
        </httpProtocol>
        
        <!-- Limites pour uploads d'images (100MB) -->
        <security>
            <requestFiltering>
                <requestLimits maxAllowedContentLength="104857600" />
            </requestFiltering>
        </security>
    </system.webServer>
</configuration>
"@

Set-Content -Path "$SitePath\web.config" -Value $webConfig -Encoding UTF8
Write-Host "✅ Fichier web.config créé" -ForegroundColor Green

# Supprimer site si existe
if (Get-Website -Name $SiteName -ErrorAction SilentlyContinue) {
    Write-Host ""
    Write-Host "⚠️ Site existant trouvé, suppression..." -ForegroundColor Yellow
    Remove-Website -Name $SiteName
    Write-Host "✅ Ancien site supprimé" -ForegroundColor Green
}

# Créer site HTTP
Write-Host ""
Write-Host "🌐 Création du site HTTP..." -ForegroundColor Cyan
New-Website -Name $SiteName `
    -PhysicalPath $SitePath `
    -HostHeader $SiteName `
    -Port 80 `
    -Force | Out-Null

Write-Host "✅ Site HTTP créé: http://$SiteName" -ForegroundColor Green

# Configurer HTTPS avec certificat wildcard
Write-Host ""
Write-Host "🔒 Configuration HTTPS..." -ForegroundColor Cyan
$cert = Get-ChildItem Cert:\LocalMachine\My | Where-Object { 
    $_.Subject -like "*myia.io*" -and $_.NotAfter -gt (Get-Date)
} | Sort-Object NotAfter -Descending | Select-Object -First 1

if ($cert) {
    Write-Host "✅ Certificat trouvé:" -ForegroundColor Green
    Write-Host "   Subject: $($cert.Subject)" -ForegroundColor White
    Write-Host "   Expire: $($cert.NotAfter.ToString('yyyy-MM-dd'))" -ForegroundColor White
    
    # Ajouter binding HTTPS
    New-WebBinding -Name $SiteName `
        -Protocol "https" `
        -Port 443 `
        -HostHeader $SiteName `
        -SslFlags 1 | Out-Null
    
    # Associer certificat
    $binding = Get-WebBinding -Name $SiteName -Protocol "https"
    $binding.AddSslCertificate($cert.Thumbprint, "My")
    
    Write-Host "✅ HTTPS configuré avec certificat *.myia.io" -ForegroundColor Green
}
else {
    Write-Host "⚠️ Aucun certificat *.myia.io trouvé" -ForegroundColor Yellow
    Write-Host "   HTTPS non configuré - à configurer manuellement" -ForegroundColor Yellow
    Write-Host ""
    Write-Host "   Pour générer un certificat:" -ForegroundColor Cyan
    Write-Host "   - Utilisez Let's Encrypt via Certbot" -ForegroundColor White
    Write-Host "   - Ou créez un certificat auto-signé pour tests" -ForegroundColor White
}

# Démarrer site
Write-Host ""
Write-Host "▶️ Démarrage du site..." -ForegroundColor Cyan
Start-Website -Name $SiteName
Write-Host "✅ Site démarré" -ForegroundColor Green

Write-Host ""
Write-Host "╔════════════════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║              Configuration Terminée!                    ║" -ForegroundColor Green
Write-Host "╚════════════════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""
Write-Host "🌐 URLs disponibles:" -ForegroundColor Cyan
Write-Host "   HTTP:  http://$SiteName" -ForegroundColor White
if ($cert) {
    Write-Host "   HTTPS: https://$SiteName" -ForegroundColor White
}
Write-Host ""
Write-Host "📋 Tests de validation:" -ForegroundColor Cyan
Write-Host "   # Test local direct" -ForegroundColor Yellow
Write-Host "   curl http://localhost:$Port/system_stats" -ForegroundColor White
Write-Host ""
Write-Host "   # Test reverse proxy" -ForegroundColor Yellow
if ($cert) {
    Write-Host "   curl https://$SiteName/system_stats" -ForegroundColor White
}
else {
    Write-Host "   curl http://$SiteName/system_stats" -ForegroundColor White
}
Write-Host ""
Write-Host "📂 Configuration:" -ForegroundColor Cyan
Write-Host "   Site path: $SitePath" -ForegroundColor White
Write-Host "   web.config: $SitePath\web.config" -ForegroundColor White
Write-Host ""