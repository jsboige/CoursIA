# Notebook: Stable Diffusion Forge - SD XL Turbo

**Fichier**: [`01-4-Forge-SD-XL-Turbo.ipynb`](01-4-Forge-SD-XL-Turbo.ipynb)  
**Niveau**: Intermédiaire  
**Durée estimée**: 45-60 minutes  
**Prérequis**: Python 3.x, connaissances API REST basiques

---

## 📚 Objectifs d'Apprentissage

Ce notebook pédagogique vous permettra de :

1. ✅ **Comprendre l'API REST Stable Diffusion Forge**
   - Architecture requête/réponse
   - Endpoint principal `txt2img`
   - Paramètres de génération

2. ✅ **Maîtriser la génération texte→image rapide**
   - Utilisation SD XL Turbo (4 steps)
   - Optimisation temps de génération
   - Prototypage créatif rapide

3. ✅ **Explorer les paramètres optimaux SD XL Turbo**
   - Configuration recommandée (`steps=4`, `cfg_scale=2.0`)
   - Impact des paramètres sur qualité/vitesse
   - Bonnes pratiques usage API

4. ✅ **Développer une fonction helper réutilisable**
   - Gestion erreurs robuste
   - Logging coloré (pattern LocalLlama)
   - Interface Python propre

---

## 🔧 Prérequis Techniques

### Packages Python Requis

```bash
pip install requests Pillow matplotlib
```

**Détails**:
- `requests` : Communication HTTP avec API Forge
- `Pillow` (PIL) : Manipulation images Python
- `matplotlib` : Affichage images dans notebook

### Accès API Forge

- **Service**: Stable Diffusion Forge (MyIA.io)
- **Modèle**: SD XL Turbo
- **URL Base**: `https://turbo.stable-diffusion-webui-forge.myia.io`
- **Status**: ✅ Opérationnel (validé Phase 16)
- **Performance**: ~18.78s par génération (512×512, 4 steps)

**Vérification disponibilité**:
```python
import requests
response = requests.get("https://turbo.stable-diffusion-webui-forge.myia.io/")
print(f"API Status: {response.status_code}")  # Attendu: 200
```

---

## 📖 Structure du Notebook

Le notebook est organisé en **7 sections progressives** (15 cellules total):

### 1. Introduction (Cellules 0-1)
- **Markdown** : Présentation objectifs + contexte API Forge
- **Code** : Configuration initiale (imports + URL API)

### 2. Compréhension API (Cellules 2-3)
- **Markdown** : Explication endpoint `txt2img` et architecture
- **Code** : Fonction helper `generate_image_forge()` complète avec docstrings

### 3. Exemple Simple (Cellules 4-5)
- **Markdown** : Introduction génération basique
- **Code** : Premier exemple reproductible (paysage montagne)

### 4. Optimisation Paramètres (Cellules 6-7)
- **Markdown** : Détails paramètres SD XL Turbo optimaux
- **Code** : Tests paramètres (`steps`, `cfg_scale`, `sampler`)

### 5. Cas d'Usage Avancé (Cellules 8-9)
- **Markdown** : Stratégies comparaison prompts
- **Code** : Génération grid 3 variations prompts

### 6. Bonnes Pratiques (Cellules 10-11)
- **Markdown** : Recommandations usage API + tips performance
- **Code** : Version améliorée fonction helper avec logging coloré

### 7. Exercice Pratique (Cellules 12-14)
- **Markdown** : Consignes exercice autonome
- **Code** : Template code à compléter par l'étudiant
- **Markdown** : Ressources + documentation externe

---

## 🚀 Utilisation du Notebook

### Démarrage Rapide

1. **Cloner/Télécharger** le notebook :
   ```bash
   git clone https://github.com/MyIA/CoursIA.git
   cd CoursIA/MyIA.AI.Notebooks/GenAI/01-Images-Foundation
   ```

2. **Installer dépendances** :
   ```bash
   pip install -r requirements.txt  # Si disponible
   # OU
   pip install requests Pillow matplotlib
   ```

3. **Lancer Jupyter** :
   ```bash
   jupyter notebook 01-4-Forge-SD-XL-Turbo.ipynb
   ```

4. **Exécuter cellules** dans l'ordre (Shift+Enter)

### Exécution Recommandée

#### ⚠️ **IMPORTANT: Ordre Séquentiel**
Les cellules doivent être exécutées **dans l'ordre** pour garantir :
- Imports disponibles
- Fonction helper définie avant usage
- Variables configurées correctement

#### 📍 Points d'Attention

**Cellule 3** (Fonction Helper) :
```python
# ⚠️ CRITIQUE: Exécuter cette cellule avant toute génération
def generate_image_forge(...):
    # Fonction centrale réutilisée dans tout le notebook
```

**Cellule 5** (Premier Exemple) :
```python
# 🎨 Test API : Vérifier que l'API répond correctement
# Attendu: Image 512×512 d'un paysage montagne
```

**Cellule 11** (Helper Avancé) :
```python
# 🌈 Logging coloré : Remplace fonction basique (cellule 3)
# Utiliser cette version pour meilleure UX
```

### Temps d'Exécution Estimés

| Cellule | Temps | Commentaire |
|---------|-------|-------------|
| Config (1) | < 1s | Imports instantanés |
| Helper (3) | < 1s | Définition fonction |
| Exemple simple (5) | ~20s | Génération 1 image 512×512 |
| Tests params (7) | ~20s | Génération 1 image |
| Grid 3 prompts (9) | ~60s | 3 générations séquentielles |
| Exercice (13) | Variable | Dépend créativité étudiant |

**Total notebook complet** : ~10-15 minutes (sans exercice)

---

## 🎯 Exercice Pratique Final

### Objectif
Créer votre propre génération d'image en complétant le template fourni (cellule 13).

### Consignes
1. **Choisir un thème** personnel (paysage, objet, scène, style artistique)
2. **Écrire prompt descriptif** en anglais (recommandé pour SD XL)
3. **Définir negative_prompt** (éléments à éviter)
4. **Tester variations** de paramètres (`width`, `height`, `cfg_scale`)
5. **Afficher résultat** avec matplotlib

### Exemple Template (fourni dans notebook)
```python
# 🎯 EXERCICE PRATIQUE: Complétez ce code avec vos propres choix

# TODO 1: Définir votre prompt créatif
mon_prompt = "A ___________"  # Remplacer par description détaillée

# TODO 2: Définir negative prompt (optionnel)
mon_negative_prompt = "___________"  # Ex: "blurry, low quality"

# TODO 3: Ajuster paramètres si nécessaire
mes_parametres = {
    "width": ___,   # 512, 768, ou 1024
    "height": ___,  # 512, 768, ou 1024
    "steps": 4,     # Garder 4 pour Turbo
    "cfg_scale": 2.0  # Garder 2.0 pour Turbo
}

# TODO 4: Générer et afficher
# [Code à compléter]
```

### Critères de Réussite
- ✅ Génération réussie sans erreur
- ✅ Image cohérente avec prompt fourni
- ✅ Résultat affiché dans notebook
- ✅ (Bonus) Comparaison 2-3 variations

---

## 📊 Résultats Attendus

### Exemples de Sorties

**Cellule 5 - Paysage Montagne** :
```
🎨 Génération en cours: 'A serene mountain landscape at sunset'...
✅ Image générée (512×512)
[Affichage image matplotlib]
```

**Cellule 9 - Grid Comparaison** :
```
🎨 Génération 1/3: 'A futuristic city at night'...
✅ Image générée (512×512)
🎨 Génération 2/3: 'A futuristic city at night, neon lights'...
✅ Image générée (512×512)
🎨 Génération 3/3: 'A futuristic city at night, cyberpunk style'...
✅ Image générée (512×512)
[Grid 1×3 images comparatives]
```

### Gestion Erreurs

Le notebook gère automatiquement les erreurs courantes :

**API Indisponible** :
```
❌ Erreur requête: Connection refused
⚠️ Vérifier disponibilité API: https://turbo.stable-diffusion-webui-forge.myia.io
```

**Timeout** :
```
⏱️ Timeout après 60s
⚠️ Réduire résolution (width/height) ou steps
```

**JSON invalide** :
```
❌ Erreur: Aucune image générée
⚠️ Vérifier paramètres prompt (caractères spéciaux?)
```

---

## 📚 Ressources Complémentaires

### Documentation Officielle

1. **Stable Diffusion Forge API** :
   - Documentation : [GitHub Forge WebUI](https://github.com/lllyasviel/stable-diffusion-webui-forge)
   - Endpoints : `/sdapi/v1/txt2img`, `/sdapi/v1/img2img`
   - Paramètres : Voir [API Wiki](https://github.com/AUTOMATIC1111/stable-diffusion-webui/wiki/API)

2. **SD XL Turbo (Stability AI)** :
   - Paper : [SDXL-Turbo](https://stability.ai/news/sdxl-turbo)
   - Hugging Face : [stabilityai/sdxl-turbo](https://huggingface.co/stabilityai/sdxl-turbo)

3. **Guide Étudiants MyIA** :
   - [`GUIDE-APIS-ETUDIANTS.md`](../../../../docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md)
   - Status APIs : [Phase 16 Audit](../../../../docs/suivis/genai-image/phase-16-execution-tests/)

### Tutoriels Supplémentaires

- **Prompting SD XL** : [Prompt Engineering Guide](https://platform.stability.ai/docs/features/prompting)
- **Paramètres Avancés** : [Sampler Comparison](https://stable-diffusion-art.com/samplers/)
- **Python PIL/Matplotlib** : [Pillow Docs](https://pillow.readthedocs.io/)

---

## ⚙️ Configuration Avancée

### Variables d'Environnement (Optionnel)

Pour automatiser configuration API :

```bash
# Linux/Mac
export FORGE_API_URL="https://turbo.stable-diffusion-webui-forge.myia.io"
export FORGE_TIMEOUT=120

# Windows PowerShell
$env:FORGE_API_URL = "https://turbo.stable-diffusion-webui-forge.myia.io"
$env:FORGE_TIMEOUT = 120
```

Puis dans notebook :
```python
import os
API_BASE_URL = os.getenv("FORGE_API_URL", "https://turbo.stable-diffusion-webui-forge.myia.io")
TIMEOUT = int(os.getenv("FORGE_TIMEOUT", 60))
```

### Sauvegarde Automatique Images

Modifier fonction helper (cellule 11) :
```python
# Activer sauvegarde automatique
save_directory = "./generated_images"
os.makedirs(save_directory, exist_ok=True)

image = generate_image_forge_advanced(
    prompt="...",
    save_path=f"{save_directory}/image_{timestamp}.png"
)
```

---

## 🐛 Dépannage

### Problèmes Fréquents

**1. `ModuleNotFoundError: No module named 'requests'`**
```bash
pip install requests Pillow matplotlib
# OU si virtualenv
python -m pip install requests Pillow matplotlib
```

**2. `ConnectionError: [Errno 111] Connection refused`**
- Vérifier disponibilité API via navigateur : https://turbo.stable-diffusion-webui-forge.myia.io
- Vérifier connexion internet
- Contacter support si API down

**3. Images floues ou de mauvaise qualité**
- Augmenter `steps` (4 → 6-8, mais plus lent)
- Ajuster `cfg_scale` (2.0 → 3.0-5.0)
- Améliorer descriptivité prompt
- Utiliser negative_prompt (ex: "blurry, low quality, distorted")

**4. Timeout fréquents**
- Réduire résolution (`width=512, height=512`)
- Augmenter `TIMEOUT` variable (60 → 120s)
- Vérifier charge serveur API

---

## 📞 Support

### Assistance Technique

- **Issues GitHub** : [CoursIA/issues](https://github.com/MyIA/CoursIA/issues)
- **Email Support** : support@myia.io
- **Documentation** : [docs.myia.io](https://docs.myia.io)

### Contribution

Pour signaler bugs ou proposer améliorations :
1. Fork du repository
2. Branch feature (`git checkout -b feature/amelioration-notebook`)
3. Commit changements (`git commit -m 'Add: amélioration XYZ'`)
4. Push branch (`git push origin feature/amelioration-notebook`)
5. Pull Request

---

## 📄 Licence et Crédits

**Notebook créé par** : Équipe pédagogique MyIA.io  
**Date de création** : 2025-10-18  
**Version** : 1.0.0  
**Licence** : MIT License

**Technologies utilisées** :
- **Stable Diffusion XL Turbo** : Stability AI
- **Forge WebUI** : lllyasviel
- **Python** : requests, Pillow, matplotlib
- **Infrastructure** : MyIA.io Cloud Platform

---

## 🔄 Historique Versions

| Version | Date | Changements |
|---------|------|-------------|
| 1.0.0 | 2025-10-18 | Version initiale (Phase 18) |

---

**Bon apprentissage avec Stable Diffusion Forge ! 🎨🚀**