# Rapport 36 : Inventaire Scripts Tests API ComfyUI
**Phase 29 - Validation Tests API**  
**Date** : 2025-11-02 17:34:22 UTC+1  
**Auteur** : Roo (Mode Code)  
**Statut** : ✅ Inventaire Complet

---

## 📋 Contexte

Suite au succès de la génération d'images Qwen via le wrapper d'installation complet ([`Rapport 22`](./22-installation-complete-test-final-20251102-160948.md)), cette mission consiste à valider systématiquement tous les tests API ComfyUI développés durant les phases précédentes.

### Objectifs de l'Inventaire

1. **Lister** tous les scripts de test existants
2. **Catégoriser** par type (authentification, custom nodes, génération, workflows)
3. **Identifier** les scripts actifs vs archivés
4. **Préparer** l'exécution systématique des tests

---

## 🗂️ Inventaire Complet des Scripts de Test

### 1️⃣ Scripts Actifs de Production

**Localisation** : `scripts/genai-auth/`

#### 1.1. Tests d'Authentification

| Fichier | Localisation | Lignes | Description |
|---------|-------------|--------|-------------|
| `test_comfyui_auth_simple.py` | `scripts/genai-auth/utils/` | 98 | Test authentification basique avec hash bcrypt |

**Fonctionnalités clés** :
- ✅ Authentification avec hash bcrypt comme Bearer token
- ✅ Test endpoint `/system_stats`
- ✅ Affichage informations système (RAM, GPU, versions)
- ✅ Gestion d'erreurs HTTP 401
- ✅ Credentials hardcodés (à mettre à jour)

**Credentials actuels** :
```python
COMFYUI_URL = "http://localhost:8188"
BCRYPT_HASH = "$2b$12$2jPJrb7dmsM7fw0..PoEqu8nmGarw0vnYYdGw5BFmcZ52bGfwf5M2"
```

⚠️ **ACTION REQUISE** : Mettre à jour avec credentials de `.secrets/.env.generated`

---

### 2️⃣ Scripts Transients (Phase 29)

**Localisation** : `docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/transient-scripts/`

#### 2.1. Tests d'Authentification Transients

| Fichier | Lignes | Date | Description |
|---------|--------|------|-------------|
| `05-test-auth-final-20251101-171300.py` | 66 | 2025-11-01 | Test authentification final avec credentials `.env.generated` |
| `07-verification-complete-auth-20251101-232300.py` | 210 | 2025-11-01 | Vérification complète authentification |

**Évolution** :
- ✅ **05** : Lecture dynamique token depuis `.secrets/.env.generated`
- ✅ **07** : Validation complète post-régénération credentials

#### 2.2. Tests de Custom Nodes

| Fichier | Lignes | Date | Description |
|---------|--------|------|-------------|
| `01-validation-custom-nodes-20251031-120000.py` | 619 | 2025-10-31 | Validation custom nodes Qwen |
| `10-diagnostic-nodes-disponibles-20251102-095800.py` | 146 | 2025-11-02 | Diagnostic nodes disponibles |

**Contrainte Architecture** :
⚠️ **ATTENTION** : Le workflow final validé ([`Rapport 22`](./22-installation-complete-test-final-20251102-160948.md)) **n'utilise AUCUN custom node Qwen** - uniquement nodes natifs ComfyUI avec modèles FP8 officiels.

#### 2.3. Tests de Génération d'Images

| Fichier | Lignes | Date | Description | Statut |
|---------|--------|------|-------------|--------|
| `03-test-generation-images-20251031-230500.py` | 729 | 2025-10-31 | Test génération images (workflow ancien) | ❌ Obsolète |
| `09-test-generation-image-qwen-20251102-093800.py` | 356 | 2025-11-02 | Test génération Qwen (phase expérimentale) | ❌ Obsolète |
| `09-test-generation-image-workflow-officiel-20251102-105027.py` | 563 | 2025-11-02 | **Test workflow officiel FP8** | ✅ **VALIDÉ** |
| `14-test-generation-images-final-20251102-005300.py` | 382 | 2025-11-02 | Test génération final (pré-FP8) | ❌ Obsolète |
| `31-test-generation-image-fp8-officiel-20251102-131900.py` | 553 | 2025-11-02 | Test génération FP8 officiel | ✅ **VALIDÉ** |

**Scripts Validés à Réexécuter** :
1. ✅ **09-test-generation-image-workflow-officiel** (563 lignes)
   - Workflow JSON officiel ComfyUI
   - Adaptation dynamique modèles disponibles
   - Polling statut exécution
   - Copie image vers rapports/

2. ✅ **31-test-generation-image-fp8-officiel** (553 lignes)
   - Architecture FP8 (UNET + CLIP + VAE séparés)
   - Génération d'image réussie ([`Rapport 22`](./22-installation-complete-test-final-20251102-160948.md))

#### 2.4. Tests de Vérification Système

| Fichier | Lignes | Date | Description |
|---------|--------|------|-------------|
| `02-verification-modeles-qwen-20251031-121500.py` | 720 | 2025-10-31 | Vérification modèles Qwen disponibles |
| `07-verify-installer-dependencies-20251102-013546.py` | 170 | 2025-11-02 | Vérification dépendances installer |
| `08-verification-finale-complete-20251102-043000.py` | 124 | 2025-11-02 | Vérification finale système |

#### 2.5. Tests de Synchronisation Credentials

| Fichier | Lignes | Date | Description |
|---------|--------|------|-------------|
| `04-resync-test-final-20251101-145700.py` | 505 | 2025-11-01 | Test resync credentials (pré-Rapport 18) |
| `06-fix-wsl-token-file-20251101-171400.py` | 77 | 2025-11-01 | Fix token WSL |
| `06-regeneration-complete-auth-20251101-173400.py` | 206 | 2025-11-01 | Régénération complète auth |

#### 2.6. Tests de Diagnostic Docker/WSL

| Fichier | Lignes | Date | Description |
|---------|--------|------|-------------|
| `08-force-docker-reload-auth-20251101-232700.py` | 179 | 2025-11-01 | Force reload Docker auth |
| `09-diagnostic-bind-mount-wsl-20251101-232900.py` | 203 | 2025-11-01 | Diagnostic bind mounts WSL |
| `10-force-all-token-locations-20251101-233400.py` | 223 | 2025-11-01 | Force tokens toutes localisations |
| `11-inspect-container-token-20251101-233700.py` | 128 | 2025-11-01 | Inspection token container |
| `12-rebuild-complet-docker-20251101-234400.py` | 256 | 2025-11-01 | Rebuild complet Docker |
| `13-inspect-comfyui-auth-code-20251101-234800.py` | 194 | 2025-11-01 | Inspection code auth ComfyUI |

#### 2.7. Tests de Téléchargement Modèles

| Fichier | Lignes | Date | Description |
|---------|--------|------|-------------|
| `10-download-qwen2-vl-q4-20251102-114500.py` | 293 | 2025-11-02 | Téléchargement Qwen2-VL Q4 (expérimental) |
| `30-download-qwen-fp8-officiel-20251102-121200.py` | 440 | 2025-11-02 | **Téléchargement FP8 officiel** ✅ |

---

### 3️⃣ Scripts Archivés (Phase 29)

**Localisation** : `docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/scripts-archives/`

| Fichier | Lignes | Description | Raison Archive |
|---------|--------|-------------|----------------|
| `list-qwen-nodes.py` | 45 | Liste nodes Qwen | Remplacé par diagnostic nodes |
| `qwen-custom-nodes-installer.py` | 630 | Installation custom nodes Qwen | **Non requis** pour workflow FP8 |
| `resync-credentials-complete.py` | 241 | Resync credentials | Remplacé par `install_comfyui_login.py` |
| `test_comfyui_image_simple.py` | 188 | Test génération simple | Remplacé par workflow officiel |
| `test-comfyui-image-qwen-correct.py` | 296 | Test génération Qwen correct | Obsolète (architecture FP8) |

---

## 📊 Catégorisation des Tests par Type

### Type 1️⃣ : Tests d'Authentification

**Objectif** : Valider l'authentification ComfyUI-Login avec hash bcrypt

| Script | Statut | Credentials | Priorité |
|--------|--------|-------------|----------|
| `test_comfyui_auth_simple.py` | ✅ Actif | ⚠️ Hardcodés | 🔴 **P0** |
| `05-test-auth-final-20251101-171300.py` | ✅ Validé | ✅ `.env.generated` | 🟢 **P1** |
| `07-verification-complete-auth-20251101-232300.py` | ✅ Validé | ✅ `.env.generated` | 🟢 **P2** |

**Tests à Exécuter** :
1. ✅ Mettre à jour `test_comfyui_auth_simple.py` avec credentials `.env.generated`
2. ✅ Réexécuter `05-test-auth-final`
3. ✅ Réexécuter `07-verification-complete-auth`

---

### Type 2️⃣ : Tests de Custom Nodes

**Objectif** : Valider la disponibilité des custom nodes (si nécessaire)

| Script | Statut | Architecture | Priorité |
|--------|--------|--------------|----------|
| `01-validation-custom-nodes-20251031-120000.py` | ⚠️ Transient | Qwen custom nodes | 🟡 **P3** (optionnel) |
| `10-diagnostic-nodes-disponibles-20251102-095800.py` | ✅ Validé | Nodes natifs | 🟢 **P1** |

**⚠️ CONTRAINTE ARCHITECTURE** :
Le workflow FP8 officiel validé ([`Rapport 22`](./22-installation-complete-test-final-20251102-160948.md)) **n'utilise AUCUN custom node Qwen**. Les tests de custom nodes sont donc **optionnels** et **non prioritaires**.

**Tests à Exécuter** :
1. ✅ Réexécuter `10-diagnostic-nodes-disponibles` pour confirmer nodes natifs
2. ❌ **SKIP** `01-validation-custom-nodes` (non requis pour architecture FP8)

---

### Type 3️⃣ : Tests de Génération d'Images

**Objectif** : Valider la génération d'images end-to-end

| Script | Statut | Architecture | Priorité |
|--------|--------|--------------|----------|
| `09-test-generation-image-workflow-officiel-20251102-105027.py` | ✅ **VALIDÉ** | Workflow JSON officiel | 🔴 **P0** |
| `31-test-generation-image-fp8-officiel-20251102-131900.py` | ✅ **VALIDÉ** | FP8 (UNET+CLIP+VAE) | 🔴 **P0** |
| `03-test-generation-images-20251031-230500.py` | ❌ Obsolète | Workflow ancien | ❌ **SKIP** |
| `09-test-generation-image-qwen-20251102-093800.py` | ❌ Obsolète | Phase expérimentale | ❌ **SKIP** |
| `14-test-generation-images-final-20251102-005300.py` | ❌ Obsolète | Pré-FP8 | ❌ **SKIP** |

**Tests à Exécuter** :
1. ✅ Réexécuter `09-test-generation-image-workflow-officiel`
2. ✅ Réexécuter `31-test-generation-image-fp8-officiel`

**Images Générées Attendues** :
- Préfixe : `qwen_test_workflow_officiel_*.png`
- Localisation : `docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/`

---

### Type 4️⃣ : Tests de Vérification Système

**Objectif** : Valider la configuration système et modèles

| Script | Statut | Cible | Priorité |
|--------|--------|-------|----------|
| `02-verification-modeles-qwen-20251031-121500.py` | ⚠️ Transient | Modèles Qwen | 🟡 **P2** |
| `07-verify-installer-dependencies-20251102-013546.py` | ✅ Validé | Dépendances installer | 🟢 **P2** |
| `08-verification-finale-complete-20251102-043000.py` | ✅ Validé | Système complet | 🟢 **P1** |

**Tests à Exécuter** :
1. ✅ Réexécuter `02-verification-modeles-qwen` pour confirmer FP8 disponibles
2. ✅ Réexécuter `08-verification-finale-complete`

---

## 🔧 Actions de Mise à Jour Requises

### Action 1 : Mise à Jour Credentials `test_comfyui_auth_simple.py`

**Fichier** : [`scripts/genai-auth/utils/test_comfyui_auth_simple.py`](../../../scripts/genai-auth/utils/test_comfyui_auth_simple.py:19)

**Changements requis** :

```python
# AVANT (ligne 19)
BCRYPT_HASH = "$2b$12$2jPJrb7dmsM7fw0..PoEqu8nmGarw0vnYYdGw5BFmcZ52bGfwf5M2"

# APRÈS
# Lire depuis .secrets/.env.generated
import os
from pathlib import Path

SECRETS_FILE = Path(__file__).parent.parent.parent.parent / ".secrets" / ".env.generated"

def load_auth_token():
    if not SECRETS_FILE.exists():
        raise FileNotFoundError(f"Fichier secrets non trouvé : {SECRETS_FILE}")
    
    with open(SECRETS_FILE, 'r') as f:
        for line in f:
            if line.startswith("QWEN_API_USER_TOKEN="):
                return line.split("=", 1)[1].strip().strip('"')
    
    raise ValueError("Variable QWEN_API_USER_TOKEN non trouvée")

BCRYPT_HASH = load_auth_token()
```

---

## 📈 Plan d'Exécution des Tests

### Phase 1 : Tests d'Authentification (Rapport 37)

1. ✅ Mettre à jour `test_comfyui_auth_simple.py` avec credentials dynamiques
2. ✅ Exécuter `test_comfyui_auth_simple.py` (test basique)
3. ✅ Exécuter `05-test-auth-final` (test avec `.env.generated`)
4. ✅ Exécuter `07-verification-complete-auth` (validation complète)

**Critères de Succès** :
- HTTP 200 sur `/system_stats`
- Informations système retournées
- Pas d'erreur HTTP 401

---

### Phase 2 : Tests de Custom Nodes (Rapport 38)

1. ✅ Exécuter `10-diagnostic-nodes-disponibles` (nodes natifs)
2. ❌ **SKIP** `01-validation-custom-nodes` (non requis)

**Critères de Succès** :
- Nodes natifs détectés : `UNETLoader`, `CLIPLoader`, `VAELoader`, `KSampler`, `VAEDecode`, `SaveImage`
- Pas de custom nodes Qwen requis

---

### Phase 3 : Tests de Génération d'Images (Rapport 39)

1. ✅ Exécuter `02-verification-modeles-qwen` (vérification FP8)
2. ✅ Exécuter `09-test-generation-image-workflow-officiel` (workflow JSON)
3. ✅ Exécuter `31-test-generation-image-fp8-officiel` (architecture FP8)
4. ✅ Exécuter `08-verification-finale-complete` (validation système)

**Critères de Succès** :
- Image générée avec workflow JSON officiel
- Image générée avec architecture FP8
- Fichiers PNG copiés dans `rapports/`
- Taille fichier > 100 KB

---

## 📊 Résumé Inventaire

| Catégorie | Scripts Actifs | Scripts Transients | Scripts Archivés | Scripts à Exécuter |
|-----------|----------------|---------------------|------------------|---------------------|
| **Authentification** | 1 | 2 | 1 | 3 |
| **Custom Nodes** | 0 | 2 | 2 | 1 (optionnel) |
| **Génération Images** | 0 | 5 (2 validés) | 2 | 4 |
| **Vérification Système** | 0 | 3 | 0 | 3 |
| **TOTAL** | **1** | **12** | **5** | **11** |

---

## ✅ Conclusion

### Scripts Validés à Réexécuter

**Priorité P0 (Critique)** :
1. ✅ `test_comfyui_auth_simple.py` (après mise à jour credentials)
2. ✅ `09-test-generation-image-workflow-officiel`
3. ✅ `31-test-generation-image-fp8-officiel`

**Priorité P1 (Haute)** :
4. ✅ `05-test-auth-final`
5. ✅ `10-diagnostic-nodes-disponibles`
6. ✅ `08-verification-finale-complete`

**Priorité P2 (Moyenne)** :
7. ✅ `07-verification-complete-auth`
8. ✅ `02-verification-modeles-qwen`

**Priorité P3 (Optionnelle)** :
9. ⚠️ `01-validation-custom-nodes` (non requis pour workflow FP8)

### Scripts Archivés (Non Réexécutés)

❌ **SKIP** :
- `03-test-generation-images` (obsolète)
- `09-test-generation-image-qwen` (obsolète)
- `14-test-generation-images-final` (obsolète)
- `04-resync-test-final` (remplacé)
- `06-fix-wsl-token-file` (diagnostic unique)
- `06-regeneration-complete-auth` (diagnostic unique)
- `08-force-docker-reload-auth` (diagnostic unique)
- `09-diagnostic-bind-mount-wsl` (diagnostic unique)
- `10-force-all-token-locations` (diagnostic unique)
- `11-inspect-container-token` (diagnostic unique)
- `12-rebuild-complet-docker` (diagnostic unique)
- `13-inspect-comfyui-auth-code` (diagnostic unique)
- `10-download-qwen2-vl-q4` (expérimental)
- `30-download-qwen-fp8-officiel` (téléchargement unique)

---

## 📝 Prochaines Étapes

1. **Rapport 37** : Exécution tests d'authentification + Rapport validation
2. **Rapport 38** : Exécution tests custom nodes + Rapport validation
3. **Rapport 39** : Exécution tests génération images + Rapport validation
4. **Rapport 40** : Synthèse finale validation tests API

---

**Rapport généré le** : 2025-11-02 17:34:22 UTC+1  
**Rapports liés** :
- [`Rapport 22`](./22-installation-complete-test-final-20251102-160948.md) : Installation complète + Test final
- [`Rapport 18`](./18-resolution-finale-authentification-comfyui-login-20251101-232000.md) : Résolution authentification
- [`Rapport 26`](./26-extraction-documentation-officielle-qwen-20251102-101620.md) : Documentation workflow officiel