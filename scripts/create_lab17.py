"""Script to create Lab17 notebook - Final Project."""
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

# Lab 17 content
md("""# Lab 17: Projet Final - Pipeline DS-STAR Complet

## Objectifs

- Integrer tous les composants: FileAnalyzer, Planner-Coder-Verifier
- Appliquer a un probleme reel de data science
- Generer un rapport d'analyse automatise

## Architecture Complete

Fichiers CSV/JSON --> FileAnalyzer --> Planner --> Coder --> Executor --> Verifier --> Reporter""")

md("## 1. Configuration")

code("import sys\nsys.path.insert(0, '..')\n\nimport os\nimport json\nimport re\nimport pandas as pd\nimport numpy as np\nfrom typing import List, Dict, Optional, Tuple\nfrom dataclasses import dataclass, asdict\nfrom enum import Enum\nfrom pathlib import Path\n\nfrom config import get_settings\nfrom utils import LLMClient")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 2. Data Classes")

code("@dataclass\nclass Plan:\n    steps: List[str]\n    reasoning: str\n\n@dataclass\nclass ExecutionResult:\n    success: bool\n    output: str\n    error: Optional[str] = None\n    code: Optional[str] = None\n\n@dataclass\nclass FileMetadata:\n    filename: str\n    format: str\n    size_bytes: int\n    num_rows: int = None\n    num_columns: int = None\n    columns: list = None\n\nclass VerificationStatus(Enum):\n    SUCCESS = 'success'\n    NEEDS_REFINEMENT = 'needs_refinement'\n    FAILED = 'failed'")

md("## 3. Modules DS-STAR")

code("class FileAnalyzer:\n    SUPPORTED = {'.csv': 'csv', '.json': 'json'}\n\n    def __init__(self, llm=None):\n        self.llm = llm or LLMClient()\n\n    def analyze_csv(self, path: str) -> FileMetadata:\n        df = pd.read_csv(path)\n        cols = [{'name': c, 'dtype': str(df[c].dtype)} for c in df.columns]\n        return FileMetadata(\n            filename=Path(path).name, format='csv', size_bytes=os.path.getsize(path),\n            num_rows=len(df), num_columns=len(df.columns), columns=cols\n        )\n\n    def generate_context(self, meta: FileMetadata) -> str:\n        lines = [f'Fichier: {meta.filename}', f'Lignes: {meta.num_rows}', f'Colonnes: {meta.num_columns}']\n        if meta.columns:\n            lines.append('Colonnes: ' + ', '.join([c['name'] for c in meta.columns[:5]]))\n        return '\\\\n'.join(lines)")

code("class Planner:\n    def __init__(self, llm: LLMClient):\n        self.llm = llm\n\n    def create_plan(self, question: str, context: str) -> Plan:\n        prompt = f'Planifie: {question}\\\\nCONTEXTE: {context[:600]}\\\\nDonne 2-3 etapes. Format: REASONING: [...] STEPS: 1. [...] 2. [...]'\n        response = self.llm.generate(prompt, temperature=0.3)\n        steps, reasoning = [], ''\n        in_steps = False\n        for line in response.split('\\\\n'):\n            if line.startswith('REASONING:'):\n                reasoning = line.replace('REASONING:', '').strip()\n            elif line.startswith('STEPS:'):\n                in_steps = True\n            elif in_steps and re.match(r'^\\\\d+\\\\.', line.strip()):\n                steps.append(re.sub(r'^\\\\d+\\\\.\\\\s*', '', line.strip()))\n        return Plan(steps=steps, reasoning=reasoning)")

code("class Coder:\n    def __init__(self, llm: LLMClient):\n        self.llm = llm\n\n    def generate_code(self, plan: Plan, context: str) -> str:\n        steps_text = '\\\\n'.join(f'{i+1}. {s}' for i, s in enumerate(plan.steps))\n        prompt = f'Code Python pour: {steps_text}\\\\nDataFrame: df. Utilise print(). ```python [code] ```'\n        response = self.llm.generate(prompt, temperature=0.2)\n        match = re.search(r'```python\\\\s*(.*?)\\\\s*```', response, re.DOTALL)\n        return match.group(1).strip() if match else ''")

code("class Executor:\n    def __init__(self, df: pd.DataFrame):\n        self.df = df\n        self.namespace = {'df': df, 'pd': pd, 'np': np, 'print': print}\n\n    def execute(self, code: str) -> ExecutionResult:\n        from io import StringIO\n        import sys\n        old_stdout = sys.stdout\n        sys.stdout = StringIO()\n        try:\n            exec(code, self.namespace)\n            return ExecutionResult(success=True, output=sys.stdout.getvalue(), code=code)\n        except Exception as e:\n            return ExecutionResult(success=False, output=sys.stdout.getvalue(), error=str(e), code=code)\n        finally:\n            sys.stdout = old_stdout")

code("class Verifier:\n    def __init__(self, llm: LLMClient):\n        self.llm = llm\n\n    def verify(self, question: str, result: ExecutionResult) -> Tuple[VerificationStatus, str]:\n        if not result.success:\n            return VerificationStatus.FAILED, f'Erreur: {result.error}'\n        prompt = f'Verifie: {question}\\\\nResultat: {result.output[:400]}\\\\nReponds SUCCESS ou NEEDS_REFINEMENT.'\n        response = self.llm.generate(prompt, temperature=0.1).upper()\n        if 'SUCCESS' in response:\n            return VerificationStatus.SUCCESS, 'OK'\n        return VerificationStatus.NEEDS_REFINEMENT, 'A ameliorer'")

code("class ReportGenerator:\n    def __init__(self, llm: LLMClient):\n        self.llm = llm\n\n    def generate_report(self, question: str, results: List[Dict], metadata: FileMetadata) -> str:\n        prompt = f'Genere un rapport Markdown pour: {question}\\\\nFichier: {metadata.filename} ({metadata.num_rows} lignes)\\\\nResultats: {len(results)} analyses'\n        return self.llm.generate(prompt, temperature=0.3)")

md("## 4. Pipeline Complet")

code("class DSStarPipeline:\n    def __init__(self, max_iterations: int = 2):\n        self.llm = LLMClient()\n        self.file_analyzer = FileAnalyzer(self.llm)\n        self.planner = Planner(self.llm)\n        self.coder = Coder(self.llm)\n        self.verifier = Verifier(self.llm)\n        self.reporter = ReportGenerator(self.llm)\n        self.max_iterations = max_iterations\n\n    def analyze(self, file_path: str, question: str) -> Dict:\n        print('='*50 + '\\\\nDS-STAR PIPELINE\\\\n' + '='*50)\n\n        meta = self.file_analyzer.analyze_csv(file_path)\n        context = self.file_analyzer.generate_context(meta)\n        print(f'[FILE] {meta.filename}: {meta.num_rows} lignes')\n\n        df = pd.read_csv(file_path)\n        executor = Executor(df)\n        results = []\n\n        for i in range(self.max_iterations):\n            print(f'\\\\n=== ITERATION {i+1} ===')\n            plan = self.planner.create_plan(question, context)\n            print(f'[PLANNER] {len(plan.steps)} etapes')\n            code = self.coder.generate_code(plan, context)\n            result = executor.execute(code)\n            print(f'[EXECUTOR] {\"OK\" if result.success else \"ERROR\"}')\n            if result.success:\n                status, msg = self.verifier.verify(question, result)\n                print(f'[VERIFIER] {status.value}')\n                results.append({'output': result.output, 'status': status.value})\n                if status == VerificationStatus.SUCCESS:\n                    break\n                context += f'\\\\nResultat: {result.output[:200]}'\n\n        report = self.reporter.generate_report(question, results, meta)\n        return {'success': len(results) > 0, 'results': results, 'report': report}")

md("## 5. Dataset de Test")

code("import tempfile\ntest_dir = tempfile.mkdtemp()\n\nnp.random.seed(42)\ndf = pd.DataFrame({\n    'date': pd.date_range('2024-01-01', periods=200, freq='D'),\n    'product': np.random.choice(['A', 'B', 'C', 'D'], 200),\n    'region': np.random.choice(['Nord', 'Sud', 'Est', 'Ouest'], 200),\n    'revenue': np.random.uniform(500, 5000, 200).round(2),\n    'units': np.random.randint(5, 100, 200)\n})\n\ncsv_path = os.path.join(test_dir, 'sales.csv')\ndf.to_csv(csv_path, index=False)\nprint(f'Dataset: {csv_path} ({len(df)} lignes)')")

md("## 6. Execution du Pipeline")

code("pipeline = DSStarPipeline(max_iterations=1)\nresult = pipeline.analyze(csv_path, 'Analyse les ventes par region')")

md("## 7. Resultats")

code('print(chr(10) + "="*50 + chr(10) + "RAPPORT" + chr(10) + "="*50)\nprint(result["report"][:800])')

code("""import shutil
shutil.rmtree(test_dir)
print('Done')""")

md("""## 8. Conclusion

### Competences acquises

- Architecture d'agents pour data science
- Boucles iteratives avec raffinement
- Abstraction multi-provider
- Rapports automatises

### Extensions possibles

- Support de plus de formats
- Parallelisation
- Interface web
- Deploiement cloud

Felicitation! Vous avez complete la serie AgenticDataScience.""")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day7-Production/Lab17-Final-Project.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
