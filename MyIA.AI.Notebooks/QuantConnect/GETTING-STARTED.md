# Guide de Démarrage Rapide - QuantConnect AI Trading

Bienvenue dans la série QuantConnect AI Trading ! Ce guide vous permettra de démarrer en **moins de 10 minutes**.

## Qu'allez-vous faire ?

1. Créer un compte QuantConnect gratuit
2. Exécuter votre premier backtest dans le cloud
3. Comprendre le workflow de la série
4. (Optionnel) Configurer LEAN CLI pour développement local

**Temps estimé** : 5-10 minutes pour l'option cloud (recommandé)

---

## Option A : Cloud QuantConnect (Recommandé)

### Étape 1 : Créer un Compte Gratuit

1. Visitez [https://www.quantconnect.com/signup](https://www.quantconnect.com/signup)
2. Créez un compte avec votre email
3. Confirmez votre email
4. Connectez-vous au **QuantConnect Lab**

**Free Tier Inclus** :
- Backtests illimités
- Données Equity/Crypto/Forex depuis 2010
- 8 heures de calcul par mois
- IDE cloud intégré

### Étape 2 : Créer Votre Premier Projet

Dans le QuantConnect Lab :

1. **File → New Project**
2. Nom : `My First Strategy`
3. Langage : **Python** (ou C# si vous préférez)
4. Template : `Basic Template Algorithm`

Vous verrez un code de base avec la structure d'un algorithme QuantConnect :

```python
from AlgorithmImports import *

class MyFirstAlgorithm(QCAlgorithm):
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)
        self.AddEquity("SPY", Resolution.Daily)

    def OnData(self, data):
        if not self.Portfolio.Invested:
            self.SetHoldings("SPY", 1.0)
```

### Étape 3 : Exécuter Votre Premier Backtest

1. Cliquez sur **"Backtest"** en haut à droite
2. Attendez quelques secondes
3. Visualisez les résultats :
   - Equity curve (courbe de performance)
   - Sharpe Ratio
   - Drawdown maximum
   - Nombre de trades

**Félicitations !** Vous venez d'exécuter votre premier algorithme de trading.

### Etape 4 : Utiliser les ressources CoursIA

Les notebooks `QC-Py-XX` sont des **supports de cours** a lire sur GitHub ou en Jupyter local. Ils ne sont pas conçus pour etre uploades dans QC Lab.

**Pour votre projet QC, utilisez plutot** :

1. **Projets prets a backtester** : Copiez un `main.py` depuis `projects/` dans votre projet QC Lab
2. **Templates ESGF** : Partez d'un template (`ESGF-2026/templates/starter/`) adapte a votre niveau
3. **Notebooks de reference** : Lisez les `QC-Py-XX` pour comprendre la theorie et les patterns

**Exemple concret** :
1. Ouvrez `projects/EMA-Cross-Alpha/main.py` sur GitHub
2. Copiez le contenu dans le `main.py` de votre projet QC Lab
3. Cliquez **Backtest** pour verifier que ça marche
4. Lisez `QC-Py-13-Alpha-Models.ipynb` pour comprendre l'architecture
5. Modifiez le code pour implementer votre approche

**Pour les etudiants ECE Projet 2** : Consultez le guide detaille [ECE-QC-QUICKSTART.md](ECE-QC-QUICKSTART.md)

---

## Option B : Développement Local (Optionnel)

Cette option est pour les utilisateurs avancés qui souhaitent développer en local avec VSCode.

### Prérequis

- **Python 3.11+** installé
- **Docker Desktop** installé et en cours d'exécution
- **Git** pour cloner le repository
- **(Optionnel) .NET 9.0 SDK** pour les notebooks C#

### Étape 1 : Cloner le Repository CoursIA

```bash
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA/MyIA.AI.Notebooks/QuantConnect
```

### Étape 2 : Configurer l'Environnement Python

```bash
# Créer environnement virtuel
python -m venv venv

# Activer (Windows)
venv\Scripts\activate

# Activer (Linux/macOS)
source venv/bin/activate

# Installer dépendances
pip install -r requirements.txt
```

### Étape 3 : Installer LEAN CLI

```bash
# Installer LEAN CLI
pip install lean

# Vérifier installation
lean --version
```

### Étape 4 : Authentification QuantConnect

```bash
# Login avec vos credentials QuantConnect
lean login

# Entrer User ID et API Token
# (Obtenables dans Account → API Access sur quantconnect.com)
```

### Étape 5 : Créer un Workspace Local

```bash
# Initialiser workspace LEAN
lean init

# Créer votre premier projet
lean project-create --language python MyFirstStrategy
```

### Étape 6 : Configuration Locale

Copiez `.env.example` vers `.env` et configurez :

```bash
cp .env.example .env
```

Éditez `.env` et ajoutez :

```env
# QuantConnect API (pour sync cloud)
QC_API_USER_ID=12345
QC_API_ACCESS_TOKEN=abc...

# Chemins locaux
LEAN_DATA_PATH=./data
LEAN_RESULTS_PATH=./results
```

### Étape 7 : Télécharger des Données (Optionnel)

```bash
# Télécharger données US Equity (gratuit)
lean data download --dataset us-equity --start 20200101 --end 20231231

# Télécharger crypto (gratuit)
lean data download --dataset crypto --start 20200101
```

### Étape 8 : Exécuter un Backtest Local

```bash
# Backtest d'un projet local
lean backtest MyFirstStrategy

# Voir les résultats
lean report MyFirstStrategy
```

### Étape 9 : Lancer Jupyter Lab

```bash
# Installer Jupyter kernel
python -m ipykernel install --user --name=quantconnect --display-name "Python (QuantConnect)"

# Lancer Jupyter Lab
jupyter lab

# Ouvrir Python/QC-Py-01-Setup.ipynb
```

---

## Workflow Recommandé

### Pour Débutants : Cloud-First

1. **Développer dans QuantConnect Lab** (IDE cloud)
2. **Tester rapidement** avec données cloud gratuites
3. **Commencer par le notebook QC-Py-04** : C'est le tutorial de référence pour le workflow QuantBook → Algorithm
4. **Utiliser les projets `projects/`** comme base de code (copier main.py dans votre projet QC Lab)

### Pour Avancés : Hybride

1. **Développer en local** avec VSCode + LEAN CLI
2. **Itérer rapidement** avec données locales
3. **Déployer sur cloud** pour backtests longs ou paper trading
4. **Utiliser MCP QuantConnect** (Claude Code) pour automatisation

---

## Vérification de l'Installation

### Cloud QuantConnect

✅ Compte créé et email confirmé
✅ Premier backtest exécuté avec succès
✅ Notebook `QC-Py-01-Setup.ipynb` uploadé et exécuté

### Local LEAN CLI (Optionnel)

✅ Python 3.11+ installé (`python --version`)
✅ Docker Desktop running
✅ LEAN CLI installé (`lean --version`)
✅ Authentification réussie (`lean cloud status`)
✅ Données téléchargées (`lean data list`)
✅ Premier backtest local exécuté

---

## Problèmes Courants

### Cloud QuantConnect

**Problème** : "Backtest timed out"
**Solution** : Réduire la période de backtest ou passer en résolution Daily

**Problème** : "Data not available"
**Solution** : Vérifier que l'asset est dans le free tier (Equity US, Crypto, Forex)

**Problème** : "Out of compute hours"
**Solution** : Free tier = 8h/mois. Attendez le reset mensuel ou optimisez votre algorithme

### Local LEAN CLI

**Problème** : "Docker container won't start"
**Solution** : Vérifier que Docker Desktop est en cours d'exécution

**Problème** : "Market data not found"
**Solution** : Télécharger les données avec `lean data download`

**Problème** : "Permission denied"
**Solution** : Windows : Vérifier que Docker a accès au disque C:\
              Linux : Ajouter votre user au groupe `docker`

---

## Prochaines Étapes

Une fois votre environnement configuré :

1. **Commencer par QC-Py-04** : Le notebook [QC-Py-04-Research-Workflow.ipynb](Python/QC-Py-04-Research-Workflow.ipynb) est le tutorial de référence pour maîtriser le workflow QuantBook → Algorithm.

2. **Suivre la série** dans l'ordre :
   - Phase 1 : Fondations LEAN (Notebooks 01-04)
   - Phase 2 : Universe et Asset Classes (Notebooks 05-08)
   - Phase 3 : Trading Avancé et Risk Management (Notebooks 09-12)
   - Phase 4 : Algorithm Framework (Notebooks 13-15)
   - Phase 5-8 : Alternative Data, ML, Deep Learning, AI Avancée (Notebooks 16-27)

3. **Explorer les projets** : Le dossier `projects/` contient des stratégies prêtes à backtester. Copiez un `main.py` dans votre projet QC Lab pour démarrer rapidement.

4. **Lire le README principal** : [`README.md`](README.md) pour la vue d'ensemble complète

5. **Rejoindre la communauté** :
   - [QuantConnect Forum](https://www.quantconnect.com/forum)
   - [GitHub Discussions](https://github.com/QuantConnect/Lean/discussions)

6. **(Optionnel) Configurer MCP QuantConnect** pour automatisation avec Claude Code

---

## Ressources Utiles

- [Documentation QuantConnect](https://www.quantconnect.com/docs)
- [LEAN Engine GitHub](https://github.com/QuantConnect/Lean)
- [Livre "Hands-On AI Trading"](https://www.hands-on-ai-trading.com)
- [CoursIA Main README](../../README.md)

---

**Besoin d'aide ?** Consultez le [TROUBLESHOOTING.md](TROUBLESHOOTING.md) (à venir) ou posez vos questions sur le forum QuantConnect.

**Bon trading algorithmique !** 🚀
