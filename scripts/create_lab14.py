"""Script to create Lab14 notebook - Ablation and Refinement."""
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

# Lab 14 content
md("""# Lab 14: Ablation et Raffinement Cible (MLE-STAR Component)

## Objectifs

- Identifier les blocs de code dans un pipeline ML
- Realiser des etudes d'ablation pour prioriser les ameliorations
- raffiner de maniere ciblee les composants critiques

## Principe de l'Ablation

```
Pipeline ML = [Feature Eng] + [Model] + [Training] + [Ensemble]
                    |
                    v
              Ablation: Tester chaque composant separement
                    |
                    v
              Identifier le plus impactant
                    |
                    v
              Raffiner ce composant
```""")

md("## 1. Configuration")

code("""import sys
sys.path.insert(0, '..')

import json
import re
import numpy as np
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
from enum import Enum

from config import get_settings
from utils import LLMClient""")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 2. Code Block Identification")

code("""@dataclass
class CodeBlock:
    id: str
    name: str
    description: str
    code: str
    importance: float = 0.0

class BlockType(Enum):
    FEATURE_ENGINEERING = "feature_engineering"
    MODEL_SELECTION = "model_selection"
    HYPERPARAMETER_TUNING = "hyperparameter_tuning"
    TRAINING = "training"
    EVALUATION = "evaluation"
    ENSEMBLE = "ensemble" """)

code('''class CodeBlockAnalyzer:
    """Identifie les blocs de code dans un pipeline ML."""

    def __init__(self, llm: LLMClient):
        self.llm = llm

    def identify_blocks(self, code: str) -> List[CodeBlock]:
        """Identifie les blocs logiques dans le code."""
        prompt = f"""Analyse ce code ML et identifie les blocs logiques.

CODE:
```python
{code[:2000]}
```

Identifie 3-5 blocs (feature engineering, model, training, etc.).
Format JSON:
[
  {{"id": "block1", "name": "...", "description": "...", "code": "..."}}]
]

JSON:"""

        response = self.llm.generate(prompt, temperature=0.2)

        try:
            match = re.search(r'\\[.*\\]', response, re.DOTALL)
            if match:
                data = json.loads(match.group(0))
                return [CodeBlock(**b) for b in data]
        except:
            pass
        return []''')

md("## 3. Ablation Study Simulator")

code('''class AblationStudy:
    """Simule des etudes d'ablation pour prioriser les ameliorations."""

    def __init__(self, llm: LLMClient):
        self.llm = llm

    def estimate_importance(self, blocks: List[CodeBlock], task: str) -> List[CodeBlock]:
        """Estime l'importance relative de chaque bloc."""
        blocks_desc = "\\n".join([
            f"- {b.id}: {b.name} - {b.description[:50]}"
            for b in blocks
        ])

        prompt = f"""Estime l'importance de chaque bloc pour la tache: {task}

BLOCS:
{blocks_desc}

Donne un score d'importance de 0.0 a 1.0 pour chaque bloc.
Format JSON:
[
  {{"id": "block1", "importance": 0.9}},
  {{"id": "block2", "importance": 0.6}}
]

JSON:"""

        response = self.llm.generate(prompt, temperature=0.2)

        try:
            match = re.search(r'\\[.*\\]', response, re.DOTALL)
            if match:
                data = json.loads(match.group(0))
                importance_map = {d['id']: d['importance'] for d in data}
                for block in blocks:
                    block.importance = importance_map.get(block.id, 0.5)
        except:
            # Default importance
            for i, block in enumerate(blocks):
                block.importance = 0.8 - i * 0.1

        return sorted(blocks, key=lambda b: b.importance, reverse=True)''')

md("## 4. Targeted Refinement")

code('''class TargetedRefiner:
    """Raffine de maniere ciblee les composants critiques."""

    def __init__(self, llm: LLMClient):
        self.llm = llm

    def refine_block(self, block: CodeBlock, task: str, current_score: float) -> str:
        """Genere une version amelioree d'un bloc."""
        prompt = f"""Ameliore ce bloc de code ML pour la tache: {task}

BLOC: {block.name}
DESCRIPTION: {block.description}
CODE ACTUEL:
```python
{block.code[:1000]}
```

SCORE ACTUEL: {current_score:.3f}

Genere une version amelioree qui pourrait augmenter le score.
Focus sur les optimisations simples et efficaces.

```python
# Code ameliore
```"""

        response = self.llm.generate(prompt, temperature=0.3)
        match = re.search(r'```python\\s*(.*?)\\s*```', response, re.DOTALL)
        return match.group(1).strip() if match else block.code''')

md("## 5. MLE-STAR Ablation Pipeline")

code('''class MLEStarAblation:
    """Pipeline d'ablation complet de MLE-STAR."""

    def __init__(self):
        self.llm = LLMClient()
        self.block_analyzer = CodeBlockAnalyzer(self.llm)
        self.ablation_study = AblationStudy(self.llm)
        self.refiner = TargetedRefiner(self.llm)

    def analyze_and_refine(self, code: str, task: str, current_score: float = 0.5) -> Dict:
        """Analyse le code, identifie les blocs, et suggere des raffinements."""
        print("[ANALYZER] Identification des blocs...")
        blocks = self.block_analyzer.identify_blocks(code)
        print(f"  - {len(blocks)} blocs identifies")

        if not blocks:
            return {'success': False, 'error': 'Impossible d identifier les blocs'}

        print("\\n[ABLATION] Estimation de l'importance...")
        blocks = self.ablation_study.estimate_importance(blocks, task)

        print("  Resultats:")
        for b in blocks[:3]:
            print(f"    - {b.name}: {b.importance:.2f}")

        # Raffiner le bloc le plus important
        top_block = blocks[0]
        print(f"\\n[REFINER] Raffinement de '{top_block.name}'...")
        refined_code = self.refiner.refine_block(top_block, task, current_score)

        return {
            'success': True,
            'blocks': [(b.name, b.importance) for b in blocks],
            'top_block': top_block.name,
            'refined_code': refined_code
        }''')

md("## 6. Test avec un Exemple de Code")

code("""# Exemple de code ML a analyser
sample_code = '''
import pandas as pd
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import cross_val_score

# Feature Engineering
df = pd.read_csv('data.csv')
df['feature_ratio'] = df['feature_a'] / (df['feature_b'] + 1e-6)
df['feature_log'] = np.log1p(df['feature_c'])

X = df.drop('target', axis=1)
y = df['target']

# Model
model = RandomForestClassifier(n_estimators=100, random_state=42)

# Training & Evaluation
scores = cross_val_score(model, X, y, cv=5)
print(f"Accuracy: {scores.mean():.4f}")
'''

print("Code a analyser:")
print(sample_code[:300] + "...")""")

code("""# Test du pipeline d'ablation
pipeline = MLEStarAblation()

result = pipeline.analyze_and_refine(
    code=sample_code,
    task="binary classification tabular",
    current_score=0.75
)

print("\\n" + "="*50)
print("RESULTAT DE L'ABLATION:")
print("="*50)
print(f"\\nBlocs identifies:")
for name, imp in result['blocks']:
    print(f"  - {name}: importance {imp:.2f}")

print(f"\\nBloc prioritaire: {result['top_block']}")""")

md("## 7. Affichage du Code Raffine")

code("""if result['success'] and result.get('refined_code'):
    print("\\n" + "="*50)
    print("CODE RAFFINE:")
    print("="*50)
    print(result['refined_code'][:600] + "..." if len(result['refined_code']) > 600 else result['refined_code'])""")

md("""## 8. Resume du Lab

### Ce que nous avons implemente

1. **CodeBlockAnalyzer**: Identifie les blocs logiques
2. **AblationStudy**: Estime l'importance relative
3. **TargetedRefiner**: Ameliore les composants critiques

### Principe MLE-STAR

L'ablation permet de:
- Ne pas gaspiller d'efforts sur des composants peu impactants
- Focus sur les zones a haut potentiel d'amelioration
- Iterer rapidement sur les changements importants

### Limitations

- L'importance est estimee par le LLM (pas testee reellement)
- Une vraie ablation necessite d'executer le code
- Le raffinement est suggestif, pas garanti

### Prochaine etape

- **Lab 15**: Kaggle Challenge avec MLE-STAR complet""")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day6-MLE-Star/Lab14-Ablation-Refinement.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
