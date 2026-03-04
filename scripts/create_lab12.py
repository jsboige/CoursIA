"""Script to create Lab12 notebook - DS-STAR Workshop."""
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

# Lab 12 content
md("""# Lab 12: DS-STAR Workshop - Analyse Multi-Fichiers

## Objectifs

- Combiner FileAnalyzer + Planner-Coder-Verifier en pipeline complet
- Analyser plusieurs fichiers de donnees de maniere autonome
- Generer un rapport d'analyse structure""")

md("## 1. Configuration")

code("""import sys
sys.path.insert(0, '..')

import os
import json
import re
import pandas as pd
import numpy as np
from typing import Optional, Dict, List, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
from pathlib import Path

from config import get_settings
from utils import LLMClient""")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 2. Imports des Modules DS-STAR")

code("""# Data classes reutilisees
@dataclass
class Plan:
    steps: List[str]
    reasoning: str

@dataclass
class ExecutionResult:
    success: bool
    output: str
    error: Optional[str] = None
    code: Optional[str] = None

@dataclass
class FileMetadata:
    filename: str
    format: str
    size_bytes: int
    num_rows: int = None
    num_columns: int = None
    columns: list = None
    sample_data: list = None

class VerificationStatus(Enum):
    SUCCESS = 'success'
    NEEDS_REFINEMENT = 'needs_refinement'
    FAILED = 'failed'""")

md("## 3. FileAnalyzer Module")

code('''class FileAnalyzer:
    """Analyse automatique de fichiers de donnees."""
    SUPPORTED = {'.csv': 'csv', '.json': 'json', '.xlsx': 'excel'}

    def __init__(self, llm_client=None):
        self.llm = llm_client or LLMClient()

    def analyze_csv(self, path: str) -> FileMetadata:
        df = pd.read_csv(path)
        cols = []
        for c in df.columns:
            info = {'name': c, 'dtype': str(df[c].dtype), 'missing_pct': round(df[c].isna().mean()*100, 2)}
            if df[c].dtype in ['int64', 'float64']:
                info['stats'] = {'min': float(df[c].min()), 'max': float(df[c].max()), 'mean': float(df[c].mean())}
            cols.append(info)
        return FileMetadata(
            filename=Path(path).name, format='csv', size_bytes=os.path.getsize(path),
            num_rows=len(df), num_columns=len(df.columns), columns=cols,
            sample_data=df.head(3).to_dict('records')
        )

    def generate_context(self, meta: FileMetadata) -> str:
        lines = [f"Fichier: {meta.filename}", f"Format: {meta.format}", f"Taille: {meta.size_bytes/1024:.1f} KB"]
        if meta.num_rows:
            lines.append(f"Lignes: {meta.num_rows}, Colonnes: {meta.num_columns}")
        if meta.columns:
            for c in meta.columns[:5]:
                lines.append(f"  - {c['name']} ({c['dtype']})")
        return "\\\\n".join(lines)''')

md("## 4. Planner-Coder-Verifier Modules")

code('''class Planner:
    def __init__(self, llm: LLMClient):
        self.llm = llm

    def create_plan(self, question: str, context: str) -> Plan:
        prompt = f"""Planifie l'analyse pour cette question.

CONTEXTE: {context[:800]}
QUESTION: {question}

Donne 2-3 etapes simples. Format:
REASONING: [raisonnement]
STEPS:
1. [etape 1]
2. [etape 2]"""
        response = self.llm.generate(prompt, temperature=0.3)
        steps, reasoning = [], ""
        in_steps = False
        for line in response.split('\\n'):
            if line.startswith('REASONING:'):
                reasoning = line.replace('REASONING:', '').strip()
            elif line.startswith('STEPS:'):
                in_steps = True
            elif in_steps and re.match(r'^\\d+\\.', line.strip()):
                steps.append(re.sub(r'^\\d+\\.\\s*', '', line.strip()))
        return Plan(steps=steps, reasoning=reasoning)''')

code('''class Coder:
    def __init__(self, llm: LLMClient):
        self.llm = llm

    def generate_code(self, plan: Plan, context: str) -> str:
        steps_text = '\\n'.join(f"{i+1}. {s}" for i, s in enumerate(plan.steps))
        prompt = f"""Genere du code Python pour ce plan.
PLAN: {steps_text}
DataFrame disponible: 'df'. Utilise print() pour les resultats.
```python
[ton code]
```"""
        response = self.llm.generate(prompt, temperature=0.2)
        match = re.search(r'```python\\s*(.*?)\\s*```', response, re.DOTALL)
        return match.group(1).strip() if match else response''')

code('''class Executor:
    def __init__(self, df: pd.DataFrame):
        self.df = df
        self.namespace = {'df': df, 'pd': pd, 'np': np, 'print': print}

    def execute(self, code: str) -> ExecutionResult:
        from io import StringIO
        import sys
        old_stdout = sys.stdout
        sys.stdout = StringIO()
        try:
            exec(code, self.namespace)
            return ExecutionResult(success=True, output=sys.stdout.getvalue(), code=code)
        except Exception as e:
            return ExecutionResult(success=False, output=sys.stdout.getvalue(), error=str(e), code=code)
        finally:
            sys.stdout = old_stdout''')

code('''class Verifier:
    def __init__(self, llm: LLMClient):
        self.llm = llm

    def verify(self, question: str, result: ExecutionResult) -> Tuple[VerificationStatus, str]:
        if not result.success:
            return VerificationStatus.FAILED, f"Erreur: {result.error}"
        prompt = f"""Verifie ce resultat.
QUESTION: {question}
RESULTAT: {result.output[:500]}
Reponds SUCCESS ou NEEDS_REFINEMENT."""
        response = self.llm.generate(prompt, temperature=0.1).upper()
        if 'SUCCESS' in response:
            return VerificationStatus.SUCCESS, "OK"
        return VerificationStatus.NEEDS_REFINEMENT, "A ameliorer"''')

md("## 5. DS-STAR Orchestrator Complet")

code('''class DSStarPipeline:
    """Pipeline DS-STAR complet: Analyze -> Plan -> Code -> Execute -> Verify"""

    def __init__(self, max_iterations: int = 2):
        self.llm = LLMClient()
        self.file_analyzer = FileAnalyzer(self.llm)
        self.planner = Planner(self.llm)
        self.coder = Coder(self.llm)
        self.verifier = Verifier(self.llm)
        self.max_iterations = max_iterations

    def analyze_file(self, file_path: str, question: str) -> Dict:
        # Step 1: Analyze file
        print(f"[FILE ANALYZER] Analyse de {Path(file_path).name}...")
        meta = self.file_analyzer.analyze_csv(file_path)
        context = self.file_analyzer.generate_context(meta)

        # Load data
        df = pd.read_csv(file_path)
        executor = Executor(df)

        # Step 2-5: Iterative loop
        for iteration in range(self.max_iterations):
            print(f"\\n=== ITERATION {iteration + 1} ===")

            print("[PLANNER] Creation du plan...")
            plan = self.planner.create_plan(question, context)
            print(f"Etapes: {len(plan.steps)}")

            print("[CODER] Generation du code...")
            code = self.coder.generate_code(plan, context)

            print("[EXECUTOR] Execution...")
            result = executor.execute(code)

            if not result.success:
                print(f"[ERROR] {result.error}")
                context += f"\\nErreur: {result.error}"
                continue

            print(f"[OUTPUT] {result.output[:150]}...")

            print("[VERIFIER] Verification...")
            status, msg = self.verifier.verify(question, result)
            print(f"[STATUS] {status.value}: {msg}")

            if status == VerificationStatus.SUCCESS:
                return {'success': True, 'output': result.output, 'code': code, 'iterations': iteration + 1}

            context += f"\\nResultat partiel: {result.output[:300]}"

        return {'success': False, 'output': result.output, 'error': 'Max iterations', 'iterations': self.max_iterations}''')

md("## 6. Creation d'un Dataset de Test")

code("""# Dataset de ventes multi-produits
import tempfile
test_dir = tempfile.mkdtemp()

np.random.seed(42)
df = pd.DataFrame({
    'date': pd.date_range('2024-01-01', periods=150, freq='D'),
    'product': np.random.choice(['Widget A', 'Widget B', 'Gadget X'], 150),
    'region': np.random.choice(['Nord', 'Sud', 'Est', 'Ouest'], 150),
    'revenue': np.random.uniform(100, 2000, 150).round(2),
    'units': np.random.randint(1, 50, 150)
})

csv_path = os.path.join(test_dir, 'sales.csv')
df.to_csv(csv_path, index=False)
print(f'Dataset cree: {csv_path}')
print(f'{len(df)} lignes, colonnes: {list(df.columns)}')""")

md("## 7. Test du Pipeline DS-STAR")

code("""# Test avec une question simple
pipeline = DSStarPipeline(max_iterations=1)

question = "Quel produit genere le plus de revenu total?"
result = pipeline.analyze_file(csv_path, question)

print("\\n" + "="*50)
print("RESULTAT FINAL:")
print("="*50)
if result['success']:
    print(result['output'])
else:
    print(f"Statut: {result.get('error', 'Incomplete')}")""")

md("## 8. Test avec Question Complexe")

code("""# Question d'analyse temporelle
question2 = "Montre l'evolution des revenus par mois"
result2 = pipeline.analyze_file(csv_path, question2)

print("\\n" + "="*50)
print("RESULTAT:")
print("="*50)
print(result2.get('output', result2.get('error', 'Pas de resultat'))[:400])""")

md("## 9. Nettoyage")

code("""import shutil
shutil.rmtree(test_dir)
print('Cleanup done')""")

md("""## 10. Resume du Workshop

### Architecture DS-STAR Complete

```
[Fichier] --> [FileAnalyzer] --> Contexte
                                     |
                                     v
                               [Planner] --> Plan
                                     |
                                     v
                               [Coder] --> Code
                                     |
                                     v
                             [Executor] --> Resultat
                                     |
                                     v
                             [Verifier] --> SUCCESS/RETRY
```

### Points cles

1. **FileAnalyzer**: Extrait le contexte structure des fichiers
2. **Boucle iterative**: Permet de corriger et raffiner automatiquement
3. **Verifier**: Assure la qualite des resultats avant de retourner

### Ameliorations possibles

- Support de plus de formats (JSON, Excel, Parquet)
- Caching des metadonnees
- Parallelisation pour multi-fichiers
- Rapport final structure (Markdown/HTML)

### Prochaine etape

- **Lab 13**: MLE-STAR - Recherche web pour modeles SOTA""")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
