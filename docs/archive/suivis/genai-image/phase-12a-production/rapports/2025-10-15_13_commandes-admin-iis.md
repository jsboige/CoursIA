# Commandes Administrateur Requises pour IIS

**Date:** 2025-10-15  
**Contexte:** Déploiement infrastructure IIS pour ComfyUI + Qwen

## ⚠️ Étapes Nécessitant des Privilèges Administrateur

### 1. Création du Site IIS

Exécuter dans PowerShell **en tant qu'Administrateur**:

```powershell
cd D:\Dev\CoursIA
.\docs\genai-suivis\2025-10-15_13_create-iis-site-comfyui.ps1
```

**Résultat attendu:**
- Site IIS créé: `qwen-image-edit.myia.io`
- Binding HTTP (port 80) configuré
- Binding HTTPS (port 443) configuré (certificat à ajouter)

### 2. Génération Certificat SSL avec win-acme

Exécuter dans PowerShell **en tant qu'Administrateur**:

```powershell
cd D:\Production\win-acme.v2.2.9.1701.x64.pluggable
.\wacs.exe
```

**Configuration certificat:**
- Choisir l'option pour ajouter au plan global existant (`www.myia.io`)
- Ajouter le domaine: `qwen-image-edit.myia.io`
- Le certificat sera automatiquement associé au site IIS

### 3. Alternative: Commande Manuelle IIS

Si le script échoue, commandes manuelles:

```powershell
Import-Module WebAdministration

# Créer le site
New-Website -Name "qwen-image-edit.myia.io" `
    -PhysicalPath "D:\Production\qwen-image-edit.myia.io" `
    -HostHeader "qwen-image-edit.myia.io" `
    -Port 80 `
    -Force

# Ajouter binding HTTPS
New-WebBinding -Name "qwen-image-edit.myia.io" `
    -Protocol https `
    -Port 443 `
    -HostHeader "qwen-image-edit.myia.io" `
    -SslFlags 1

# Démarrer le site
Start-Website -Name "qwen-image-edit.myia.io"

# Vérifier l'état
Get-Website -Name "qwen-image-edit.myia.io"
```

## 📋 État Actuel

- [x] Répertoire créé: `D:\Production\qwen-image-edit.myia.io`
- [x] web.config adapté (port 8188, domaine qwen-image-edit.myia.io)
- [ ] Site IIS créé (nécessite admin)
- [ ] Certificat SSL généré (nécessite admin)
- [ ] ComfyUI démarré
- [ ] Tests validation

## 🔄 Prochaines Étapes Non-Admin

Pendant que les étapes admin sont en attente, on peut:

1. Démarrer ComfyUI avec le watchdog
2. Tester l'accès local: `http://localhost:8188`
3. Préparer les tests de validation
4. Vérifier que Forge fonctionne toujours

Une fois les privilèges admin disponibles:
1. Exécuter le script de création IIS
2. Générer le certificat SSL
3. Tester l'accès via reverse proxy
4. Validation finale avec Playwright