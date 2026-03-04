"""Script to create Lab15 notebook - Kaggle Challenge."""
import json

nb = {
    "cells": [],
    "metadata": {
        "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
        "language_info": {"name": "python", "version": "3.11.0"}
    },
    "nbformat": 4,
    "nbformat_minor": 5
}

cell_id = 0

def md(text):
    global cell_id
    nb["cells"].append({
        "cell_type": "markdown",
        "id": f"cell-{cell_id}",
        "metadata": {},
        "source": text.strip().split('\n')
    })
    cell_id += 1

def code(text):
    global cell_id
    lines = text.strip().split('\n')
    nb["cells"].append({
        "cell_type": "code",
        "execution_count": None,
        "id": f"cell-{cell_id}",
        "metadata": {},
        "outputs": [],
        "source": [l + '\n' for l in lines[:-1]] + ([lines[-1]] if lines else [])
    })
    cell_id += 1

# Lab 15 content
md("""# Lab 15: Kaggle Challenge avec MLE-STAR

## Objectifs

- Appliquer MLE-STAR a une competition Kaggle simulee
- Combiner Web Search + Ablation + Raffinement
- Generer une soumission competitive

## Workflow MLE-STAR Complet

1. [UNDERSTAND] Comprendre la competition
2. [SEARCH] Trouver les modeles SOTA
3. [CODE] Generer le code initial
4. [ABLATION] Identifier les points d'amelioration
5. [REFINE] raffiner iterativement
6. [SUBMIT] Soumettre et analyser""")

md("## 1. Configuration")

code("import sys\nsys.path.insert(0, '..')\n\nimport json\nimport re\nimport numpy as np\nimport pandas as pd\nfrom typing import List, Dict, Optional\nfrom dataclasses import dataclass\nfrom pathlib import Path\n\nfrom config import get_settings\nfrom utils import LLMClient")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 2. Kaggle Competition Simulator")

code("@dataclass\nclass CompetitionInfo:\n    name: str\n    task: str\n    metric: str\n    description: str\n    data_description: str\n\nclass KaggleSimulator:\n    def get_competition_info(self) -> CompetitionInfo:\n        return CompetitionInfo(\n            name='Tabular Playground Series',\n            task='binary classification',\n            metric='AUC-ROC',\n            description='Predict customer churn based on tabular features',\n            data_description='20 features numeriques et categoriques, 10000 exemples'\n        )\n\n    def generate_sample_data(self, n_samples: int = 500) -> pd.DataFrame:\n        np.random.seed(42)\n        return pd.DataFrame({\n            'customer_id': range(n_samples),\n            'age': np.random.randint(18, 80, n_samples),\n            'tenure': np.random.randint(1, 72, n_samples),\n            'monthly_charges': np.random.uniform(20, 150, n_samples).round(2),\n            'total_charges': np.random.uniform(100, 8000, n_samples).round(2),\n            'contract_type': np.random.choice(['Month-to-month', 'One year', 'Two year'], n_samples),\n            'internet_service': np.random.choice(['DSL', 'Fiber', 'No'], n_samples),\n            'target': np.random.randint(0, 2, n_samples)\n        })")

md("## 3. MLE-STAR Agent Complet")

code("class MLEStarAgent:\n    def __init__(self):\n        self.llm = LLMClient()\n        self.competition = None\n        self.data = None\n        self.code = None\n\n    def understand_competition(self, info: CompetitionInfo) -> str:\n        print('[UNDERSTAND] Analyse de la competition...')\n        prompt = f\"\"\"Analyse cette competition Kaggle:\n\nNOM: {info.name}\nTACHE: {info.task}\nMETRIQUE: {info.metric}\n\nResume en 2-3 phrases.\"\"\"\n        response = self.llm.generate(prompt, temperature=0.3)\n        return response\n\n    def search_sota(self, task: str) -> List[str]:\n        print('[SEARCH] Recherche SOTA...')\n        prompt = f\"\"\"Pour la tache '{task}', quels sont les 3 modeles les plus performants?\nDonne juste les noms, un par ligne.\"\"\"\n        response = self.llm.generate(prompt, temperature=0.3)\n        models = re.findall(r'\\d+\\.\\s*(.+)', response)\n        return models[:3] if models else ['RandomForest', 'XGBoost', 'LightGBM']\n\n    def generate_initial_code(self, info: CompetitionInfo, models: List[str]) -> str:\n        print('[CODE] Generation du code initial...')\n        prompt = f\"\"\"Genere un script Python pour cette competition.\nTACHE: {info.task}\nMETRIQUE: {info.metric}\nMODELES: {', '.join(models[:2])}\n\nLe script doit charger les donnees, entrainer un modele et evaluer.\n```python\n[code]\n```\"\"\"\n        response = self.llm.generate(prompt, temperature=0.3)\n        match = re.search(r'```python\\s*(.*?)\\s*```', response, re.DOTALL)\n        return match.group(1).strip() if match else '# Code generation failed'\n\n    def run_pipeline(self, info: CompetitionInfo) -> Dict:\n        print('='*50)\n        print('MLE-STAR PIPELINE')\n        print('='*50)\n        understanding = self.understand_competition(info)\n        models = self.search_sota(info.task)\n        self.code = self.generate_initial_code(info, models)\n        return {'understanding': understanding, 'models': models, 'code': self.code}")

md("## 4. Test du Pipeline")

code("# Initialiser le simulateur\nsimulator = KaggleSimulator()\ninfo = simulator.get_competition_info()\nsample_data = simulator.generate_sample_data(300)\n\nprint(f'Competition: {info.name}')\nprint(f'Data shape: {sample_data.shape}')")

code("# Executer le pipeline MLE-STAR\nagent = MLEStarAgent()\nresult = agent.run_pipeline(info)")

md("## 5. Affichage des Resultats")

code("print('\\\\n' + '='*50)\nprint('COMPREHENSION:')\nprint('='*50)\nprint(result['understanding'][:400])")

code("print('\\\\n' + '='*50)\nprint('MODELES SOTA:')\nprint('='*50)\nfor m in result['models']:\n    print(f'  - {m}')")

code("print('\\\\n' + '='*50)\nprint('CODE GENERE:')\nprint('='*50)\nprint(result['code'][:500] + '...' if len(result['code']) > 500 else result['code'])")

md("""## 6. Resume du Lab

### Workflow MLE-STAR

1. Understand: Analyser la competition
2. Search: Trouver les modeles SOTA
3. Code: Generer une solution initiale
4. Ablation: Identifier les ameliorations
5. Refine: Iterer

### Resultats MLE-Bench

MLE-STAR obtient 63.6% de medailles sur MLE-Bench-Lite.

### Prochaine etape

Lab 16: Data Science Agent avec GCP""")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day6-MLE-Star/Lab15-Kaggle-Challenge.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
