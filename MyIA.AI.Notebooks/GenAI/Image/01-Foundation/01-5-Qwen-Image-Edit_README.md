# Notebook: Qwen-Image-Edit (ComfyUI API)

**Niveau**: Débutant à Intermédiaire  
**Durée Estimée**: 45-60 minutes  
**Prérequis**: Python 3.x, connaissances API REST basiques  

---

## 📚 Objectifs d'Apprentissage

À l'issue de ce notebook, vous serez capable de:

1. **Comprendre l'architecture ComfyUI** et son système de workflows JSON
2. **Maîtriser l'édition d'images** via l'API Qwen Vision-Language Model
3. **Explorer des workflows** simples puis avancés de génération/édition d'images
4. **Créer vos propres workflows** ComfyUI personnalisés

---

## 🎯 Use Cases Pratiques

Ce notebook vous apprendra à:

- ✅ Générer des images à partir de prompts textuels (text-to-image)
- ✅ Éditer des images existantes avec des instructions en langage naturel
- ✅ Comparer différentes variations de prompts pour optimiser vos résultats
- ✅ Créer des workflows ComfyUI réutilisables pour vos projets

**Exemples Concrets**:
- Modifier l'atmosphère d'une photo (ajouter un coucher de soleil, changer le ciel)
- Appliquer des transformations stylistiques (noir et blanc, effet dramatique)
- Générer des variantes créatives d'une image source

---

## 🔧 Prérequis Techniques

### Environnement Python

**Version Recommandée**: Python 3.10 ou supérieur

### Packages Requis

Installez les dépendances suivantes:

```bash
pip install requests Pillow matplotlib python-dotenv
```

**Détails Packages**:
- **`requests`**: Communication HTTP avec l'API ComfyUI
- **`Pillow` (PIL)**: Manipulation images (chargement, sauvegarde, redimensionnement)
- **`matplotlib`**: Affichage visuel des résultats dans le notebook
- **`python-dotenv`**: Chargement variables d'environnement depuis `.env` (authentification - Phase 23C)

### Vérification Installation

Exécutez dans un terminal Python:

```python
import requests
import PIL
import matplotlib
print("✅ Tous les packages sont installés correctement")
```

---

## 🚀 Démarrage Rapide

### 1. Ouvrir le Notebook

Lancez Jupyter Notebook ou JupyterLab dans votre environnement:

```bash
jupyter notebook
```

Naviguez vers:  
`MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-5-Qwen-Image-Edit.ipynb`

### 2. Exécuter Séquentiellement

⚠️ **IMPORTANT**: Exécutez les cellules **dans l'ordre** (de haut en bas) pour:
1. Charger les imports et configurations (cellules 1-2)
2. Définir la classe helper `ComfyUIClient` (cellule 4)
3. Tester les workflows d'exemple (cellules 6, 10, 12)
4. Compléter l'exercice pratique final (cellule 14)

### 3. Workflow Minimal "Hello World"

La cellule 6 contient un workflow minimal de test. Exécutez-la pour valider votre connexion à l'API:

```python
# Workflow de test (cellule 6)
workflow_hello = { ... }
client = ComfyUIClient()
result = client.execute_workflow(workflow_hello)
print(result)
```

**Résultat Attendu**: Message de confirmation API ou image générée simple

---

## 📖 Structure du Notebook

### Partie 1: Fondamentaux ComfyUI (Cellules 1-4)

**Cellule 1**: Introduction & objectifs pédagogiques  
**Cellule 2**: Imports Python & configuration API  
**Cellule 3**: Explication architecture ComfyUI (workflows JSON, nodes)  
**Cellule 4**: **Classe Helper `ComfyUIClient`** (abstraction API asynchrone)

### Partie 2: Workflows Simples (Cellules 5-7)

**Cellule 5**: Théorie workflow "Hello World"  
**Cellule 6**: **Exemple Code: Workflow Minimal**  
**Cellule 7**: Explications édition images avec Qwen VLM

### Partie 3: Édition Images (Cellules 8-10)

**Cellule 8**: **Fonction Upload Image** vers ComfyUI  
**Cellule 9**: Architecture workflow édition (Load → VLM → Save)  
**Cellule 10**: **Exemple Code: Workflow Édition Image**

### Partie 4: Cas Avancés & Exercice (Cellules 11-15)

**Cellule 11**: Use cases workflows complexes  
**Cellule 12**: **Exemple Code: Comparaison Prompts** (grid affichage)  
**Cellule 13**: Bonnes pratiques ComfyUI (gestion erreurs, optimisation)  
**Cellule 14**: **Exercice Pratique: Créez Votre Workflow**  
**Cellule 15**: Ressources complémentaires & documentation

---

## 🎓 Approche Pédagogique

### Progression Scaffolding

Le notebook suit une progression **simple → complexe**:

1. **Comprendre**: Architecture ComfyUI + concepts JSON workflows
2. **Observer**: Exemples concrets fonctionnels (hello world, édition image)
3. **Expérimenter**: Modifier prompts + comparer résultats
4. **Créer**: Exercice pratique autonome (workflow personnalisé)

### Abstraction Technique

La classe **`ComfyUIClient`** (cellule 4) encapsule la complexité de l'API ComfyUI:

- ✅ Gestion asynchrone (queue ComfyUI + polling résultats)
- ✅ Gestion erreurs HTTP/timeout
- ✅ Interface simple pour étudiants: `execute_workflow(workflow_json)`

**Avantage**: Vous pouvez vous concentrer sur la **logique métier** (workflows JSON) sans gérer les détails techniques API.

### Apprentissage Visuel

Toutes les cellules de génération/édition d'images incluent:
- Affichage **matplotlib** des résultats
- Comparaisons **avant/après** pour validation visuelle
- Grids de variantes pour analyse comparative

---

## 🌐 API Utilisée

### Service ComfyUI + Qwen VLM

**URL API**: `https://qwen-image-edit.myia.io`

**Architecture**:
- **Backend**: ComfyUI (système nodes graphiques)
- **Modèle VLM**: Qwen-VL (Vision-Language Model)
- **Protocole**: API REST (endpoints `/prompt`, `/history`)

### Endpoints Clés

| Endpoint | Méthode | Usage |
|----------|---------|-------|
| `/prompt` | POST | Soumettre workflow JSON pour exécution |
| `/history/{prompt_id}` | GET | Récupérer résultats workflow |
| `/upload/image` | POST | Uploader image source pour édition |

**Détails Techniques**: Voir cellule 3 (Architecture ComfyUI) dans le notebook

---

## 📊 Résultats Attendus

### Workflow "Hello World" (Cellule 6)

**Input**: Workflow JSON minimal  
**Output**: Message de confirmation ou image test simple

### Workflow Édition Image (Cellule 10)

**Input**:
- Image source (upload via `upload_image_to_comfyui()`)
- Prompt édition (ex: "Make the sky more dramatic")

**Output**:
- Image éditée selon prompt
- Affichage avant/après via matplotlib

### Comparaison Prompts (Cellule 12)

**Input**: 3 prompts variations (ex: coucher de soleil, noir et blanc, effet dramatique)  
**Output**: Grid 3 images comparatives avec prompts annotés

### Exercice Pratique (Cellule 14)

**Input**: Workflow template à compléter (TODO: personnaliser nodes)  
**Output**: Votre workflow personnalisé fonctionnel + image générée

---

## ⚠️ Troubleshooting

### Erreur: `ConnectionError` ou `Timeout`

**Cause**: API ComfyUI non accessible ou timeout dépassé

**Solutions**:
1. Vérifier connexion internet
2. Tester URL API dans navigateur: `https://qwen-image-edit.myia.io`
3. Augmenter timeout dans `ComfyUIClient` (ligne `timeout=60`)

### Erreur: `ModuleNotFoundError: No module named 'PIL'`

**Cause**: Package Pillow non installé

**Solution**:
```bash
pip install Pillow
```

### Erreur: Workflow JSON invalide

**Cause**: Syntaxe JSON incorrecte ou nodes ComfyUI incompatibles

**Solutions**:
1. Valider JSON via `json.loads(workflow_json_string)`
2. Vérifier noms nodes exactement comme dans exemples
3. Consulter documentation ComfyUI (cellule 15)

### Images non affichées

**Cause**: Matplotlib backend non configuré

**Solution**:
```python
%matplotlib inline  # Ajouter en début de notebook
```

---

## 📚 Ressources Complémentaires

### Documentation Officielle

- **ComfyUI GitHub**: [https://github.com/comfyanonymous/ComfyUI](https://github.com/comfyanonymous/ComfyUI)
- **Guide Workflows ComfyUI**: [https://comfyanonymous.github.io/ComfyUI_examples/](https://comfyanonymous.github.io/ComfyUI_examples/)
- **Qwen-VL Model**: [https://huggingface.co/Qwen/Qwen-VL](https://huggingface.co/Qwen/Qwen-VL)

### Tutoriels Recommandés

- **ComfyUI Beginners Guide**: [YouTube Tutorial](https://www.youtube.com/results?search_query=comfyui+beginner+tutorial)
- **API REST Python**: [Real Python - Working with APIs](https://realpython.com/python-api/)

### Notebooks Associés

- **`01-4-Forge-SD-XL-Turbo.ipynb`**: Génération images Stable Diffusion (comparaison API)
- **`01-Images-Foundation/`**: Série complète notebooks GenAI images

---

## 💡 Conseils Utilisation

### Bonnes Pratiques Workflows

1. **Commencez Simple**: Testez d'abord workflow "hello world" avant workflows complexes
2. **Itérez Progressivement**: Ajoutez 1 node à la fois pour identifier bugs
3. **Validez JSON**: Utilisez `json.dumps()` pour vérifier syntaxe avant exécution
4. **Gérez Erreurs**: Encapsulez appels API dans `try/except` (pattern dans `ComfyUIClient`)

### Optimisation Performances

- **Timeout Adaptatif**: Augmentez timeout pour workflows lourds (>60s)
- **Qualité Images**: Réduisez résolution pour tests rapides, augmentez pour production
- **Batch Processing**: Utilisez boucles pour générer variantes (cellule 12)

### Exploration Créative

- **Testez Prompts**: Expérimentez formulations différentes (descriptif vs. artistique)
- **Combinez Nodes**: Chaînez éditions (ex: style → couleur → composition)
- **Analysez Résultats**: Comparez grids pour identifier patterns efficaces

---

## 🎯 Exercice Final (Cellule 14)

### Objectif

Créer un workflow ComfyUI personnalisé pour:
1. Uploader votre propre image
2. Appliquer 2 éditions séquentielles (ex: style + couleur)
3. Afficher résultat comparaison avant/après

### Template Fourni

Le notebook contient un template workflow `workflow_exercice` avec:
- Structure nodes de base
- TODO: commentaires pour customisation
- Placeholders pour vos paramètres

### Critères Réussite

- ✅ Workflow JSON valide (sans erreurs parsing)
- ✅ Exécution API réussie (image générée)
- ✅ Affichage résultat via matplotlib

**Bonus**: Comparez 3 variations de votre workflow en grid

---

## 📞 Support

### Contact Formation

- **Email**: support-formation@myia.io
- **Documentation Projet**: [`docs/suivis/genai-image/phase-20-notebook-qwen/`](../../../docs/suivis/genai-image/phase-20-notebook-qwen/)

### Issues Connues

Consultez les rapports de tests:
- **Validation Notebook**: [`2025-10-20_20_07_resultats-tests-fonctionnels.md`](../../../docs/suivis/genai-image/phase-20-notebook-qwen/2025-10-20_20_07_resultats-tests-fonctionnels.md)
- **Checkpoint Qualité**: [`2025-10-20_20_08_checkpoint-sddd-validation.md`](../../../docs/suivis/genai-image/phase-20-notebook-qwen/2025-10-20_20_08_checkpoint-sddd-validation.md)

---

## 📜 Licence & Crédits

**Auteur**: MyIA.AI - Formation GenAI  
**Phase Projet**: Phase 20 (Développement Notebook Qwen)  
**Date Création**: 2025-10-19  

**Modèles Utilisés**:
- ComfyUI (Licence GPL-3.0)
- Qwen-VL (Alibaba Cloud, Apache 2.0)

**License Notebook**: MIT License (usage éducatif libre)

---

**Bon apprentissage avec ComfyUI et Qwen-VL! 🚀**

*N'hésitez pas à expérimenter et personnaliser les workflows selon vos besoins créatifs.*