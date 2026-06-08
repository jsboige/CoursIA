# CaseStudies - Projets etudiants en IA Generative

<!-- CATALOG-STATUS
series: GenAI-CaseStudies
pedagogical_count: 4
breakdown: Barbie-Schreck=1, Recipe-Maker=1, Medical-Chatbot=1, Fort-Boyard=1
maturity: BETA
-->

Projets etudiants en IA generative : generation d'images, agents conversationnels, et jeux interactifs.

**4 notebooks** | **4 projets** | **~4-6h**

## Structure

```text
CaseStudies/
├── Barbie-Schreck/     # Generation d'images hybrides (DALL-E)
├── Recipe-Maker/       # Generateur de recettes (Semantic Kernel)
├── Medical-Chatbot/    # Chatbot medical (Semantic Kernel)
└── Fort-Boyard/        # Jeu interactif (OpenAI GPT)
```

## Projets

| Projet | Notebook | Technologies | Difficulte |
|--------|----------|-------------|-----------|
| [Barbie-Schreck](Barbie-Schreck/README.md) | barbie-schreck.ipynb | OpenAI DALL-E, PIL | Intermédiaire |
| [Recipe-Maker](Recipe-Maker/README.md) | receipe_maker.ipynb | Semantic Kernel, OpenAI | Intermédiaire |
| [Medical-Chatbot](Medical-Chatbot/README.md) | medical_chatbot.ipynb | Semantic Kernel, OpenAI | Avance |
| [Fort-Boyard](Fort-Boyard/README.md) | fort-boyard-python.ipynb | OpenAI GPT | Intermédiaire |

## Prerequis communs

```bash
pip install openai pandas numpy semantic-kernel
```

## FAQ

### Quelle cle API est requise pour les projets ?

- **Barbie-Schreck** et **Fort-Boyard** : `OPENAI_API_KEY` uniquement (modeaux GPT et DALL-E).
- **Recipe-Maker** et **Medical-Chatbot** : `OPENAI_API_KEY` + un service Semantic Kernel configure (Azure OpenAI ou OpenAI direct).

Configurer les cles dans `GenAI/.env` (voir [00-GenAI-Environment](../00-GenAI-Environment/README.md) pour le setup complet).

### Peut-on executer Medical-Chatbot sans Semantic Kernel ?

Medical-Chatbot utilise Semantic Kernel pour l'orchestration des plugins (requete vers API, parsing, formatage de reponse). Pour le faire sans SK, remplacer les appels `kernel.invoke()` par des appels directs `openai.chat.completions.create()` -- la logique metier reste la meme, seule la couche d'orchestration change.

### Quelle difference entre CaseStudies et les autres series GenAI ?

| Serie | Focus | Prerequis |
|-------|-------|-----------|
| **CaseStudies** (ici) | Projets complets bout-en-bout | Python basique + cle API |
| [Texte](../Texte/README.md) | Techniques NLL/prompting avancees | Python intermediaire |
| [SemanticKernel](../SemanticKernel/README.md) | Orchestration agents multi-services | Python + concepts SK |
| [Image](../Image/README.md) | Generation/edition d'images | Docker + GPU |

CaseStudies est le point d'entree ideal pour decouvrir les capacites GenAI avant d'approfondir dans les series thematiques.
