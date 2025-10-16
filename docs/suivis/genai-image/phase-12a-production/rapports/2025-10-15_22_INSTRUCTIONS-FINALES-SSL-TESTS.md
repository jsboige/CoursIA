# Instructions Finales - Configuration SSL et Tests Playwright

**Date:** 2025-10-15 22:38 UTC (00:38 heure locale)  
**Statut Déploiement:** 🟡 90% COMPLET - SSL en attente

---

## 📊 État Actuel - Résumé

### ✅ Complété (90%)

| Composant | Statut | Détails |
|-----------|--------|---------|
| **ComfyUI** | ✅ OPÉRATIONNEL | Port 8188, PID 838, GPU 3090, 15s démarrage |
| **Site IIS** | ✅ CRÉÉ | `qwen-image-edit.myia.io`, bindings HTTP + HTTPS |
| **Reverse Proxy HTTP** | ✅ FONCTIONNEL | http://qwen-image-edit.myia.io accessible |
| **Binding HTTPS** | ⚠️ CRÉÉ | Port 443 prêt, certificat SSL à configurer |
| **Forge** | ✅ PRÉSERVÉ | GPU 0, aucun impact du déploiement |
| **GPU 3090** | ✅ OPTIMAL | 1078 MB VRAM (4.4%), 28°C température |

### ⏸️ En Attente (10%)

1. **Configuration certificat SSL** (5%) - Action utilisateur requise
2. **Tests Playwright UI** (5%) - Après configuration SSL

---

## 🔐 ÉTAPE 1: Configuration Certificat SSL

### Résultat Recherche Certificats

✅ **Recherche effectuée:** Aucun certificat wildcard `*.myia.io` existant trouvé  
📝 **Action requise:** Génération nouveau certificat via win-acme

### Script Interactif Préparé

**📄 Fichier:** [`docs/genai-suivis/2025-10-15_22_configure-ssl-win-acme.ps1`](2025-10-15_22_configure-ssl-win-acme.ps1)

**Exécution:**
```powershell
# Ouvrir PowerShell en ADMINISTRATEUR
cd D:\Dev\CoursIA
.\docs\genai-suivis\2025-10-15_22_configure-ssl-win-acme.ps1
```

**Ce que le script fait:**
1. ✅ Vérifie win-acme disponible
2. 📋 Affiche instructions détaillées (2 options)
3. 🚀 Propose de lancer win-acme automatiquement
4. ✅ Vérifie le binding HTTPS après configuration
5. 🧪 Teste HTTPS automatiquement
6. 💾 Sauvegarde infos certificat dans JSON
7. 🌐 Propose d'ouvrir navigateur pour validation visuelle

### Options de Configuration SSL

#### Option A: Ajouter au plan existant (SI plan `www.myia.io` existe)
```
Menu win-acme:
1. M → Manage renewals
2. Trouver plan "www.myia.io"
3. Modifier le plan
4. Ajouter "qwen-image-edit.myia.io" comme SAN
5. Tester le renouvellement
```

#### Option B: Nouveau certificat dédié (RECOMMANDÉ si pas de plan)
```
Menu win-acme:
1. N → Create certificate (full options)
2. Source: 2 (Manual input)
3. Entrer: qwen-image-edit.myia.io
4. Validation: 2 ([http-01] Save on path)
5. Path: D:\Production\qwen-image-edit.myia.io
6. CSR: 2 (RSA key)
7. Store: 3 (Certificate Store - Local)
8. Installation: 2 (IIS Web)
9. Sélectionner: qwen-image-edit.myia.io
```

**Certificat sera automatiquement associé au binding HTTPS**

### Vérification Post-Configuration

Après exécution du script, vous devriez avoir:

✅ **Certificat SSL configuré:**
- Subject: CN=qwen-image-edit.myia.io
- Thumbprint: [généré par Let's Encrypt]
- Expire: [date + 90 jours]
- Fichier info: `docs/genai-suivis/certificat-ssl-info.json`

✅ **HTTPS fonctionnel:**
```powershell
# Test automatique dans script
Invoke-WebRequest https://qwen-image-edit.myia.io/system_stats
# Devrait retourner Status 200
```

✅ **Navigateur:**
- Cadenas vert visible
- Certificat valide affiché
- Interface ComfyUI chargée

---

## 🧪 ÉTAPE 2: Tests Playwright UI

### Script Playwright Préparé

**📄 Fichier:** [`docs/genai-suivis/2025-10-15_13_test-playwright-ui.ps1`](2025-10-15_13_test-playwright-ui.ps1)

### Exécution Tests

**Option 1: Installation + Exécution complète**
```powershell
# Si environnement Playwright pas encore installé
cd D:\Dev\CoursIA
.\docs\genai-suivis\2025-10-15_13_test-playwright-ui.ps1
```

Ce script va:
1. ✅ Créer `D:\Production\playwright-tests`
2. ✅ Créer `package.json` et `test-ui.js`
3. ✅ Installer dépendances npm (playwright)
4. ✅ Installer navigateur Chromium
5. 📋 Afficher commandes pour exécution tests

**Option 2: Exécution directe (si déjà installé)**
```powershell
cd D:\Production\playwright-tests
npm test
```

### Tests Exécutés

**Test 1: ComfyUI** (`https://qwen-image-edit.myia.io`)
- ✅ Page charge (timeout 30s)
- ✅ Canvas détecté (interface graph)
- ✅ Bouton Queue détecté
- 📸 Screenshot: `D:\Production\playwright-tests\results\comfyui-ui.png`

**Test 2: Forge** (`https://turbo.stable-diffusion-webui-forge.myia.io`)
- ✅ Page charge (vérification non-régression)
- ✅ Bouton Generate détecté
- ✅ Zone prompt détectée
- 📸 Screenshot: `D:\Production\playwright-tests\results\forge-ui.png`

### Copie Screenshots Documentation

```powershell
# Après tests, copier screenshots dans docs
$screenshotDir = "D:\Production\playwright-tests\results"
$docsDir = "docs\genai-suivis\screenshots"

# Créer répertoire docs screenshots
New-Item -ItemType Directory -Path $docsDir -Force

# Copier screenshots
Copy-Item "$screenshotDir\*.png" -Destination $docsDir -Force

# Vérifier
Get-ChildItem $docsDir
```

**Résultat attendu:**
- `docs/genai-suivis/screenshots/comfyui-ui.png`
- `docs/genai-suivis/screenshots/forge-ui.png`

---

## 📝 ÉTAPE 3: Mise à Jour Documentation

### À Compléter Manuellement

**Fichier:** [`docs/genai-suivis/2025-10-15_22_execution-deploiement-final.md`](2025-10-15_22_execution-deploiement-final.md)

Ajouter section après Phase 4:

```markdown
## Phase 3 BIS: Configuration SSL (Complétée)

### [22:XX:XX] Exécution Script SSL

**Script utilisé:** `2025-10-15_22_configure-ssl-win-acme.ps1`

**Certificat configuré:**
- Subject: [à compléter]
- Thumbprint: [à compléter]
- Expire: [à compléter]
- Jours restants: [à compléter]
- Fichier info: certificat-ssl-info.json

**Binding HTTPS vérifié:**
- Port: 443
- IP: *
- SNI: Activé
- Certificat associé: ✅

**Tests HTTPS:**
```powershell
curl https://qwen-image-edit.myia.io/system_stats
# Status: 200 OK
```

**Browser:** ✅ Cadenas vert, certificat valide

### Statut Phase 3 BIS
✅ **SUCCÈS COMPLET**
- Certificat SSL généré et associé
- HTTPS fonctionnel
- Validation visuelle réussie

---

## Phase 5: Tests Playwright (Complétée)

### [22:XX:XX] Installation Environnement

**Script:** `2025-10-15_13_test-playwright-ui.ps1`

**Installation:**
- Répertoire: D:\Production\playwright-tests
- Node.js: [version]
- Playwright: ^1.40.0
- Browser: Chromium installé

### [22:XX:XX] Exécution Tests UI

**Test ComfyUI:**
- URL: https://qwen-image-edit.myia.io
- Canvas détecté: ✅
- Bouton Queue: ✅
- Screenshot: ✅ comfyui-ui.png ([taille] KB)

**Test Forge:**
- URL: https://turbo.stable-diffusion-webui-forge.myia.io
- Bouton Generate: ✅
- Zone prompt: ✅
- Screenshot: ✅ forge-ui.png ([taille] KB)

**Screenshots copiés:**
- `docs/genai-suivis/screenshots/comfyui-ui.png`
- `docs/genai-suivis/screenshots/forge-ui.png`

### Statut Phase 5
✅ **SUCCÈS COMPLET**
- Tests Playwright exécutés
- Screenshots générés et documentés
- Forge non impacté (validé)
```

---

## 🎯 Checklist Finale

### Avant de Marquer Complet

- [ ] Script SSL exécuté avec succès
- [ ] Certificat SSL associé au binding HTTPS
- [ ] Test HTTPS manuel réussi (curl + browser)
- [ ] Script Playwright installé/exécuté
- [ ] Screenshots générés (2 fichiers PNG)
- [ ] Screenshots copiés dans docs/genai-suivis/screenshots/
- [ ] Rapport d'exécution mis à jour avec timestamps réels
- [ ] Checkpoint sémantique mis à jour

### URLs Production Finales à Valider

| Service | URL | Test | Résultat |
|---------|-----|------|----------|
| Backend local | http://localhost:8188 | `curl http://localhost:8188/system_stats` | [ ] |
| HTTP public | http://qwen-image-edit.myia.io | `curl http://qwen-image-edit.myia.io/system_stats` | [ ] |
| **HTTPS public** | **https://qwen-image-edit.myia.io** | `curl https://qwen-image-edit.myia.io/system_stats` | [ ] |
| Forge | https://turbo.stable-diffusion-webui-forge.myia.io | Browser | [ ] |

---

## 📊 Métriques Performance Attendues

| Métrique | Target | À Mesurer |
|----------|--------|-----------|
| Temps démarrage ComfyUI | <30s | ✅ 15s |
| VRAM idle GPU 3090 | <2GB | ✅ 1078 MB |
| Température GPU 3090 | <40°C | ✅ 28°C |
| Latence reverse proxy | <100ms | [ ] À tester HTTPS |
| Certificat SSL valide | Oui | [ ] À configurer |
| Tests Playwright | 2/2 succès | [ ] À exécuter |

---

## 🔄 Commandes Utiles Post-Déploiement

### Vérifier ComfyUI
```powershell
# Status
curl http://localhost:8188/system_stats

# Arrêter si nécessaire
wsl kill 838

# Relancer
wsl -e bash /mnt/d/Dev/CoursIA/docs/genai-suivis/2025-10-15_13_test-comfyui-launch.sh
```

### Vérifier Site IIS
```powershell
Import-Module WebAdministration
Get-Website -Name "qwen-image-edit.myia.io"
Get-WebBinding -Name "qwen-image-edit.myia.io"
```

### Vérifier Certificat
```powershell
# Lister certificats
Get-ChildItem Cert:\LocalMachine\My | Where-Object { $_.Subject -like '*myia.io*' }

# Voir détails certificat associé
$binding = Get-WebBinding -Name "qwen-image-edit.myia.io" -Protocol "https"
$cert = Get-ChildItem Cert:\LocalMachine\My | Where-Object { $_.Thumbprint -eq $binding.certificateHash }
$cert | Format-List Subject, Thumbprint, NotAfter
```

### Métriques GPU
```powershell
wsl nvidia-smi --query-gpu=index,name,memory.used,memory.total,temperature.gpu --format=csv
```

---

## 🎉 Conclusion

Une fois ces étapes complétées:

✅ **Infrastructure 100% Opérationnelle:**
- ComfyUI accessible via HTTPS
- Certificat SSL Let's Encrypt valide
- Tests UI validés avec screenshots
- Forge préservé et fonctionnel
- Monitoring GPU actif

🚀 **Prochaine Phase:** 12B - Notebooks bridge pédagogiques

📝 **Documentation:**
- Rapport exécution final complet
- Checkpoint sémantique mis à jour
- Screenshots UI disponibles

---

**Timestamp:** 2025-10-15 22:38 UTC  
**Durée estimée restante:** 15-20 minutes (SSL + tests)