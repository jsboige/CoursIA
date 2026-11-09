# Charge de distillation partagee (issue #14499, point 3)

Provenance : MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb,
cellules 0..8 a la tete 8e9eaaaa0 (figees : les repliques
P2/MAF et P3/ADK distillent CE fichier, pas le carnet vivant -- la charge est
byte-stable entre moteurs et entre executions).

Ecart declare : la cellule 8 (l'unique cellule d'authentification de la section,
`import os / load_dotenv() / api_key = os.getenv("OPENAI_API_KEY")...`) est
TRONQUEE par le budget de fixture -- les 8 autres cellules sont reprises
verbatim. La section distillee ne couvre donc pas l'authentification ; c'est un
choix de borne, pas une caracteristique de la charge reelle.

---

## [cellule 0 | markdown]

# SK-1-Fundamentals : Introduction a Semantic Kernel

**Navigation** : [Index](README.md) | [02-Functions >>](02-SemanticKernel-Advanced.ipynb)

***

## Objectifs d'apprentissage

A la fin de ce notebook, vous saurez :
1. Installer et configurer **Semantic Kernel** pour Python
2. Comprendre le rôle du **Kernel** comme orchestrateur central
3. Ajouter des **services LLM** (OpenAI, Azure, Hugging Face)
4. Charger et utiliser des **plugins** (prompts templates)
5. Créer des **fonctions sémantiques inline**
6. Gerer un **chat conversationnel** avec historique

### Prerequis

- Python 3.10+
- Cle API OpenAI (ou Azure OpenAI)
- Fichier `.env` configure

### Duree estimee : 45 minutes

***

## Sommaire

| Section | Contenu | Concepts cles |
|---------|---------|---------------|
| 1 | Installation | pip install semantic-kernel |
| 2 | Configuration | .env, Kernel, Services |
| 3 | Premier Kernel | Initialisation, service LLM |
| 4 | Plugins | Chargement depuis fichiers |
| 5 | Fonctions inline | Prompts dynamiques |
| 6 | Chat | Historique, KernelArguments |

> **Qu'est-ce que Semantic Kernel ?** Un SDK Microsoft open-source pour integrer des LLMs dans vos applications. Il orchestre les appels aux modèles, gere les plugins, et permet de créer des agents intelligents.


## [cellule 1 | code]

# Installation de Semantic Kernel (si nécessaire)

# Vérification de la version installée
from semantic_kernel import __version__
print(f"Semantic Kernel version : {__version__}")


## [cellule 2 | markdown]


### 📌 **Importation des bibliothèques nécessaires**
Dans cette cellule, nous allons importer les modules principaux.


## [cellule 3 | code]

import os
import json
from dotenv import load_dotenv
from semantic_kernel import Kernel
from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion
from semantic_kernel.connectors.ai.open_ai import OpenAIChatPromptExecutionSettings
from semantic_kernel.functions import KernelArguments  # Correction de l'import
from semantic_kernel.prompt_template import PromptTemplateConfig
from semantic_kernel.prompt_template.input_variable import InputVariable
print("Imports OK : Kernel, OpenAIChatCompletion, KernelArguments, PromptTemplateConfig, InputVariable")


## [cellule 4 | markdown]

## **📁 2. Chargement des paramètres de configuration**
### 📌 **Lecture des paramètres depuis un fichier `.env` ou JSON**
Le fichier de configuration `.env` doit contenir les clés nécessaires pour accéder aux services OpenAI/Azure OpenAI.

💡 **Vérifiez que vous avez bien créé un fichier `.env`** dans le même dossier que ce notebook avec ces valeurs :

```plaintext
GLOBAL_LLM_SERVICE="OpenAI"
OPENAI_API_KEY="sk-..."
OPENAI_CHAT_MODEL_ID="gpt-5-mini"
```

👉 Nous allons maintenant **charger ces paramètres en Python** :


## [cellule 5 | code]

# Chargement du fichier .env
load_dotenv()

# Récupération des clés API et du modèle
llm_service = os.getenv("GLOBAL_LLM_SERVICE", "OpenAI")
api_key = os.getenv("OPENAI_API_KEY")
model_id = os.getenv("OPENAI_CHAT_MODEL_ID", "gpt-5-mini")

# Vérification
print(f"Service sélectionné : {llm_service}")
print(f"Modèle utilisé : {model_id}")


## [cellule 6 | code]

# Importer le Kernel depuis Semantic Kernel
from semantic_kernel import Kernel

# Créer une instance du Kernel
kernel = Kernel()
print("Kernel initialisé avec succès.")


## [cellule 7 | markdown]

### Interpretation : Chargement de la configuration et initialisation du Kernel

Les deux cellules précédentes ont respectivement charge les variables d'environnement et instancie le Kernel Semantic Kernel. Ces deux étapes sont preconditionnees l'une par l'autre :

| Étape | Action | Résultat |
|-------|--------|----------|
| Lecture `.env` | `load_dotenv()` + `os.getenv()` | Recuperation de la cle API et du modèle |
| Initialisation Kernel | `Kernel()` | Orchestrateur central pret a recevoir des services |

Le Kernel est actuellement "nu" : il ne possede pas encore de service LLM. La cellule suivante va verifier la connectivite avec l'API OpenAI avant d'ajouter le service ChatCompletion au Kernel.


## [cellule 8 | code]

(tronquee par le budget de fixture)
