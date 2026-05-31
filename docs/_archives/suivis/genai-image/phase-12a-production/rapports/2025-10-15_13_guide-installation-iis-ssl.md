# Guide d'Installation IIS + SSL pour ComfyUI Production

**Date:** 2025-10-15  
**Objectif:** Configurer IIS + certificat SSL pour exposer ComfyUI (port 8188) via `https://qwen-image-edit.myia.io`

## 📋 Prérequis

- ✅ ComfyUI opérationnel sur `http://localhost:8188`
- ✅ GPU RTX 3090 avec VRAM disponible
- ✅ Répertoire de production: `D:\Production\qwen-image-edit.myia.io`
- ✅ Fichier `web.config` configuré pour reverse proxy
- ⚠️ **Privilèges Administrateur requis**

## 🎯 Étape 1: Créer le Site IIS

### Option A: Via Script PowerShell (Recommandé)

**Ouvrir PowerShell en tant qu'Administrateur:**
1. Rechercher "PowerShell" dans le menu Démarrer
2. Clic droit → "Exécuter en tant qu'administrateur"
3. Naviguer vers le répertoire du projet:
   ```powershell
   cd D:\Dev\CoursIA
   ```

**Exécuter le script de création:**
```powershell
.\docs\genai-suivis\2025-10-15_13_create-iis-site-comfyui.ps1
```

**Sortie attendue:**
```
=== Création du site IIS pour ComfyUI + Qwen ===
Création du site IIS: qwen-image-edit.myia.io
Ajout du binding HTTPS (port 443)...
Démarrage du site...

=== État du site ===
Name         : qwen-image-edit.myia.io
State        : Started
PhysicalPath : D:\Production\qwen-image-edit.myia.io
Bindings     : http/*:80:qwen-image-edit.myia.io
               https/*:443:qwen-image-edit.myia.io

✓ Site IIS créé avec succès!
  - HTTP:  http://qwen-image-edit.myia.io (port 80)
  - HTTPS: https://qwen-image-edit.myia.io (port 443, certificat à configurer)

Prochaine étape: Configurer le certificat SSL avec win-acme
```

### Option B: Commandes Manuelles IIS

Si le script échoue, utiliser ces commandes PowerShell (en admin):

```powershell
# 1. Importer le module IIS
Import-Module WebAdministration

# 2. Supprimer le site s'il existe
if (Get-Website -Name "qwen-image-edit.myia.io" -ErrorAction SilentlyContinue) {
    Remove-Website -Name "qwen-image-edit.myia.io"
}

# 3. Créer le site
New-Website -Name "qwen-image-edit.myia.io" `
    -PhysicalPath "D:\Production\qwen-image-edit.myia.io" `
    -HostHeader "qwen-image-edit.myia.io" `
    -Port 80 `
    -Force

# 4. Ajouter le binding HTTPS
New-WebBinding -Name "qwen-image-edit.myia.io" `
    -Protocol https `
    -Port 443 `
    -HostHeader "qwen-image-edit.myia.io" `
    -SslFlags 1

# 5. Démarrer le site
Start-Website -Name "qwen-image-edit.myia.io"

# 6. Vérifier l'état
Get-Website -Name "qwen-image-edit.myia.io" | Format-List Name, State, PhysicalPath, Bindings
```

### Vérification Étape 1

**Test backend local:**
```powershell
curl http://localhost:8188/system_stats
```
Doit retourner les stats système de ComfyUI.

**Test reverse proxy HTTP:**
```powershell
curl http://qwen-image-edit.myia.io/system_stats
```
Doit retourner les mêmes stats via le reverse proxy IIS.

**Ouvrir dans le navigateur:**
```powershell
Start-Process "http://qwen-image-edit.myia.io"
```
L'interface ComfyUI doit s'afficher (sans HTTPS pour l'instant).

---

## 🔐 Étape 2: Générer le Certificat SSL

### Localisation de win-acme

```powershell
cd D:\Production\win-acme.v2.2.9.1701.x64.pluggable
```

### Option A: Ajouter au Plan Existant (Recommandé)

Si un plan de renouvellement existe déjà pour `www.myia.io`:

1. **Lancer win-acme en admin:**
   ```powershell
   .\wacs.exe
   ```

2. **Menu principal - Choisir "M: Manage renewals"**

3. **Trouver le plan existant:**
   - Chercher le plan contenant `www.myia.io`
   - Noter son ID (ex: `ID 1: www.myia.io`)

4. **Modifier le plan:**
   - Choisir l'option pour modifier le plan
   - Ajouter `qwen-image-edit.myia.io` comme SAN (Subject Alternative Name)

5. **Tester le renouvellement:**
   ```
   T: Test renewal
   ```
   - Sélectionner le plan modifié
   - Confirmer que le certificat inclut le nouveau domaine

### Option B: Créer un Nouveau Certificat

Si pas de plan existant ou préférence pour un certificat dédié:

1. **Lancer win-acme en admin:**
   ```powershell
   .\wacs.exe
   ```

2. **Menu principal - Choisir "N: Create certificate (full options)"**

3. **Source:**
   - Choisir "4: Manual input"
   - Entrer: `qwen-image-edit.myia.io`

4. **Validation:**
   - Choisir "2: [http-01] Save verification files on (network) path"
   - Chemin: `D:\Production\qwen-image-edit.myia.io\.well-known\acme-challenge`
   - Confirmer que le chemin est accessible via IIS

5. **Store:**
   - Choisir "3: Certificate Store (Local computer)"
   - Store: `WebHosting`

6. **Installation:**
   - Choisir "2: IIS Web"
   - Sélectionner le site: `qwen-image-edit.myia.io`
   - Binding: port 443

7. **Confirmer et tester:**
   - win-acme va tenter l'émission du certificat
   - Vérifier que le certificat est associé au binding HTTPS

### Sortie Attendue win-acme

```
[INFO] Authorize identifier: qwen-image-edit.myia.io
[INFO] Cached authorization result: valid
[INFO] Store with CertificateStore...
[INFO] Installing certificate in the certificate store
[INFO] Installation with IIS...
[INFO] Updating renewal
[INFO] Renewal saved

Certificate created successfully!
```

### Vérification Étape 2

**Test HTTPS dans PowerShell:**
```powershell
# Ignorer les erreurs de certificat pour test initial
[System.Net.ServicePointManager]::ServerCertificateValidationCallback = {$true}
(Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/system_stats").Content
```

**Ouvrir dans le navigateur:**
```powershell
Start-Process "https://qwen-image-edit.myia.io"
```
Le navigateur doit afficher:
- ✅ Cadenas vert (certificat valide)
- ✅ Interface ComfyUI chargée
- ✅ Pas d'avertissement de sécurité

---

## 🧪 Étape 3: Tests de Validation

### Test 1: Backend Local
```powershell
curl http://localhost:8188/system_stats
```
**Attendu:** JSON avec `system`, `devices`, etc.

### Test 2: HTTP Reverse Proxy
```powershell
curl http://qwen-image-edit.myia.io/system_stats
```
**Attendu:** Même JSON que Test 1

### Test 3: HTTPS Reverse Proxy
```powershell
curl https://qwen-image-edit.myia.io/system_stats
```
**Attendu:** Même JSON avec certificat SSL valide

### Test 4: Interface Utilisateur
```powershell
Start-Process "https://qwen-image-edit.myia.io"
```
**Vérifications visuelles:**
- [ ] Interface ComfyUI visible
- [ ] Canvas/graphique chargé
- [ ] Boutons fonctionnels (Queue, Clear, etc.)
- [ ] Pas de messages d'erreur dans la console navigateur (F12)

---

## 📸 Étape 4: Tests Playwright (Validation Visuelle)

### Préparer l'Environnement Playwright

```powershell
.\docs\genai-suivis\2025-10-15_13_test-playwright-ui.ps1
```

Ce script va:
1. Créer `D:\Production\playwright-tests\`
2. Installer les dépendances npm
3. Installer le navigateur Chromium
4. Créer le script de test `test-ui.js`

### Exécuter les Tests

```powershell
cd D:\Production\playwright-tests
npm test
```

**Sortie attendue:**
```
🚀 Démarrage des tests Playwright...

📸 Test 1: ComfyUI à https://qwen-image-edit.myia.io
  ✅ ComfyUI UI capturée: D:\Production\playwright-tests\results\comfyui-ui.png
  - Canvas détecté: ✓
  - Bouton Queue détecté: ✓

📸 Test 2: Forge à https://turbo.stable-diffusion-webui-forge.myia.io
  ✅ Forge UI capturée: D:\Production\playwright-tests\results\forge-ui.png
  - Bouton Generate détecté: ✓
  - Zone de prompt détectée: ✓

✅ Tests terminés. Screenshots dans: D:\Production\playwright-tests\results
```

### Vérifier les Screenshots

Ouvrir les captures d'écran:
```powershell
explorer D:\Production\playwright-tests\results
```

**Vérifications:**
- [ ] `comfyui-ui.png` montre l'interface ComfyUI complète
- [ ] `forge-ui.png` montre l'interface Forge inchangée
- [ ] Pas d'erreurs visibles dans les deux interfaces

---

## 📊 Étape 5: Vérifier les Métriques GPU

### Métriques Initiales

```powershell
wsl nvidia-smi --query-gpu=memory.used,memory.total,temperature.gpu,utilization.gpu --format=csv,noheader,nounits -i 1
```

**Exemple de sortie attendue:**
```
1030, 24576, 45, 0
```
- VRAM utilisée: 1030 MiB / 24576 MiB (4.2%)
- Température: 45°C
- Utilisation GPU: 0%

### Monitoring Continu

Si un script de monitoring existe:
```powershell
.\docs\genai-suivis\2025-10-14_12A_monitor-gpu-performance.ps1
```

Sinon, monitoring manuel toutes les 5 secondes:
```powershell
while ($true) {
    Clear-Host
    Write-Host "=== GPU RTX 3090 (ComfyUI) ===" -ForegroundColor Cyan
    wsl nvidia-smi --query-gpu=index,name,memory.used,memory.total,temperature.gpu,utilization.gpu --format=csv,noheader,nounits -i 1
    Write-Host "`nAppuyez sur Ctrl+C pour arrêter" -ForegroundColor Yellow
    Start-Sleep -Seconds 5
}
```

---

## ✅ Checklist Finale

### Configuration IIS
- [ ] Site IIS créé: `qwen-image-edit.myia.io`
- [ ] Binding HTTP (port 80) configuré
- [ ] Binding HTTPS (port 443) configuré
- [ ] Site démarré et actif
- [ ] web.config avec reverse proxy vers localhost:8188

### Certificat SSL
- [ ] win-acme exécuté avec succès
- [ ] Certificat émis par Let's Encrypt
- [ ] Certificat associé au binding HTTPS
- [ ] Renouvellement automatique configuré

### Tests HTTP
- [ ] Backend local accessible: `http://localhost:8188`
- [ ] Reverse proxy HTTP fonctionnel: `http://qwen-image-edit.myia.io`
- [ ] Réponse JSON correcte de `/system_stats`

### Tests HTTPS
- [ ] HTTPS accessible: `https://qwen-image-edit.myia.io`
- [ ] Certificat SSL valide (cadenas vert)
- [ ] Pas d'avertissements de sécurité
- [ ] Interface ComfyUI chargée correctement

### Validation Visuelle
- [ ] Screenshots Playwright capturés
- [ ] ComfyUI UI complète visible
- [ ] Forge UI inchangée (non-régression)
- [ ] Pas d'erreurs console navigateur

### Performance GPU
- [ ] VRAM RTX 3090 monitored
- [ ] Température GPU acceptable (< 80°C)
- [ ] Pas de conflit avec Forge (GPU 3080 Ti, port 7860)

---

## 📝 URLs Finales

| Service | URL | Status Attendu |
|---------|-----|---------------|
| ComfyUI Backend | `http://localhost:8188` | ✅ Actif |
| ComfyUI HTTP | `http://qwen-image-edit.myia.io` | ✅ Reverse Proxy |
| ComfyUI HTTPS | `https://qwen-image-edit.myia.io` | ✅ Production |
| Forge Backend | `http://localhost:7860` | ✅ Inchangé |
| Forge HTTPS | `https://turbo.stable-diffusion-webui-forge.myia.io` | ✅ Inchangé |

---

## 🐛 Dépannage

### Problème 1: Site IIS ne démarre pas

**Symptômes:**
- Erreur lors de `Start-Website`
- Site en état "Stopped"

**Solutions:**
```powershell
# Vérifier les logs IIS
Get-EventLog -LogName Application -Source "IIS*" -Newest 10

# Vérifier si le port 80/443 est déjà utilisé
netstat -ano | findstr ":80 "
netstat -ano | findstr ":443 "

# Redémarrer IIS
iisreset /restart
```

### Problème 2: Reverse Proxy ne fonctionne pas

**Symptômes:**
- Erreur 502 Bad Gateway
- Erreur 503 Service Unavailable

**Solutions:**
```powershell
# Vérifier que ComfyUI est actif
curl http://localhost:8188/system_stats

# Vérifier les permissions du pool d'application
# Dans IIS Manager: Application Pools → [pool] → Advanced Settings → Identity

# Vérifier le web.config
Get-Content D:\Production\qwen-image-edit.myia.io\web.config
```

### Problème 3: Certificat SSL non émis

**Symptômes:**
- Erreur Let's Encrypt lors de l'émission
- Validation échouée

**Solutions:**
```powershell
# Vérifier que le domaine pointe bien vers le serveur
nslookup qwen-image-edit.myia.io

# Vérifier que le port 80 est accessible depuis l'extérieur
# (nécessaire pour http-01 challenge)

# Consulter les logs win-acme
Get-Content D:\Production\win-acme.v2.2.9.1701.x64.pluggable\Log\*.txt -Tail 50
```

### Problème 4: Interface ComfyUI ne charge pas

**Symptômes:**
- Page blanche
- Erreurs JavaScript dans console

**Solutions:**
```powershell
# Vérifier les en-têtes HTTP
curl -I https://qwen-image-edit.myia.io

# Vérifier les WebSockets (nécessaires pour ComfyUI)
# Dans le navigateur, F12 → Network → WS

# Vérifier la configuration proxy
Get-Content D:\Production\qwen-image-edit.myia.io\web.config | Select-String -Pattern "websocket"
```

---

## 📚 Ressources

- [Documentation IIS](https://learn.microsoft.com/en-us/iis/)
- [win-acme Documentation](https://www.win-acme.com/manual/getting-started)
- [Let's Encrypt](https://letsencrypt.org/)
- [ComfyUI Documentation](https://github.com/comfyanonymous/ComfyUI)
- [Playwright Documentation](https://playwright.dev/)

---

**Fin du Guide**  
*Pour toute question ou problème, consulter la section Dépannage ou créer une issue.*