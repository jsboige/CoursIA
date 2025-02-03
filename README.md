# 📘 CoursIA

Bienvenue dans le dépôt **CoursIA**, qui contient les ressources et TPs pour le cours d'intelligence artificielle en C#.

## 🚀 Mise en route : Environnement Jupyter avec OpenAI sous VSCode

Ce guide explique comment configurer un environnement Jupyter avec OpenAI sous VSCode pour expérimenter l'IA de manière interactive.

### 🛠 Prérequis

Avant de commencer, assure-toi d'avoir installé :

- [Python 3.9+](https://www.python.org/downloads/)
- [Visual Studio Code](https://code.visualstudio.com/)
- L'extension **Python** et **Jupyter** dans VSCode
- [Extension **.Net extension pack**](https://marketplace.visualstudio.com/items?itemName=ms-dotnettools.vscode-dotnet-pack)
- [OpenAI API key](https://platform.openai.com/signup/) (si utilisation de l'API OpenAI)

### 🔧 Installation des dépendances

1. **Créer et activer un environnement virtuel :**

   ```sh
   python -m venv venv
   source venv/bin/activate  # macOS/Linux
   venv\Scripts\activate      # Windows
   ```

2. **Installer Jupyter et les bibliothèques nécessaires :**

   ```sh
   pip install --upgrade pip
   pip install jupyter openai
   ```

3. **Ajouter l'environnement à Jupyter :**

   ```sh
   python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"
   ```

### ▶️ Lancer Jupyter Notebook

Dans VSCode :

1. **Ouvre le dossier du projet** avec VSCode.
2. **Lance Jupyter** en ouvrant un fichier `.ipynb` ou avec la commande :

   ```sh
   jupyter notebook
   ```

3. **Sélectionne le kernel** `"Python (CoursIA)"` dans Jupyter.

### 🔗 Utilisation de l'API OpenAI

Dans un notebook, charge l'API OpenAI avec ton **clé API** :

```python
import openai

openai.api_key = "sk-XXXXXXXXXXXXXXXXXXXXXXXXXXXX"

response = openai.ChatCompletion.create(
    model="gpt-4",
    messages=[{"role": "user", "content": "Explique-moi le machine learning en une phrase."}]
)

print(response["choices"][0]["message"]["content"])
```

### 🎯 Bonnes pratiques

- ⚡ **Utilise un fichier `.env`** pour stocker ta clé API et charge-le avec `dotenv` :
  
  ```sh
  pip install python-dotenv
  ```

  ```python
  from dotenv import load_dotenv
  import os

  load_dotenv()
  openai.api_key = os.getenv("OPENAI_API_KEY")
  ```

- 📁 **Organise ton projet** avec des dossiers `notebooks/`, `data/`, `src/`.
- 🔄 **Utilise Git** (`.gitignore` pour exclure `venv/`, `.env`).

### 📚 Ressources utiles

- [Documentation OpenAI](https://platform.openai.com/docs/)
- [Jupyter Notebook Guide](https://jupyter.org/)
- [VSCode Jupyter Extension](https://marketplace.visualstudio.com/items?itemName=ms-toolsai.jupyter)

🚀
