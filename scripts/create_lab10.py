"""Script to create Lab10 notebook."""
import json
import os

# Create notebook
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

# Lab content
md("# Lab 10: Data File Analyzer (DS-STAR Component)\n\n## Objectifs\n\n- Implementer le module File Analyzer de DS-STAR\n- Analyser des fichiers heterogenes (CSV, JSON, Markdown, texte)\n- Extraire des metadonnees structurees")

md("## 1. Configuration")

code("import sys\nsys.path.insert(0, '..')\n\nimport os\nimport json\nimport pandas as pd\nimport numpy as np\nfrom pathlib import Path\nfrom dataclasses import dataclass, asdict\n\nfrom config import get_settings\nfrom utils import LLMClient")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 2. FileMetadata DataClass")

code("@dataclass\nclass FileMetadata:\n    filename: str\n    format: str\n    size_bytes: int\n    num_rows: int = None\n    num_columns: int = None\n    columns: list = None\n    statistics: dict = None\n    sample_data: list = None")

md("## 3. FileAnalyzer Class")

code('''class FileAnalyzer:
    SUPPORTED = {'.csv': 'csv', '.json': 'json', '.md': 'markdown', '.txt': 'text'}

    def __init__(self, llm_client=None):
        self.llm = llm_client or LLMClient()

    def detect_format(self, path):
        ext = Path(path).suffix.lower()
        return self.SUPPORTED.get(ext, 'unknown')

    def analyze_csv(self, path):
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
            sample_data=df.head(5).to_dict('records')
        )

    def analyze(self, path):
        fmt = self.detect_format(path)
        if fmt == 'csv':
            return self.analyze_csv(path)
        raise ValueError(f"Format non supporte: {fmt}")

    def generate_summary(self, meta):
        lines = [f"Fichier: {meta.filename}", f"Format: {meta.format}", f"Taille: {meta.size_bytes/1024:.1f} KB"]
        if meta.num_rows:
            lines.append(f"Lignes: {meta.num_rows}, Colonnes: {meta.num_columns}")
        if meta.columns:
            for c in meta.columns[:5]:
                lines.append(f"  - {c['name']} ({c['dtype']}): {c.get('missing_pct', 0)}% manquant")
        return "\\n".join(lines)

    def generate_llm_summary(self, meta, question=None):
        ctx = self.generate_summary(meta)
        if meta.sample_data:
            ctx += f"\\n\\nEchantillon:\\n{json.dumps(meta.sample_data[:2], indent=2, default=str)[:400]}"
        prompt = f"Analyse ce fichier et resume-le:\\n{ctx}\\n{f'Question: {question}' if question else ''}"
        return self.llm.generate(prompt, temperature=0.3)''')

md("## 4. Tests")

code("# Creation fichier test\nimport tempfile\ntest_dir = tempfile.mkdtemp()\n\ndf = pd.DataFrame({\n    'id': range(1, 101),\n    'product': [f'P{i}' for i in range(1, 101)],\n    'category': np.random.choice(['A', 'B', 'C'], 100),\n    'price': np.random.uniform(10, 500, 100).round(2),\n    'qty': np.random.randint(1, 50, 100)\n})\ndf.loc[10:15, 'price'] = np.nan\n\ncsv_path = os.path.join(test_dir, 'products.csv')\ndf.to_csv(csv_path, index=False)\nprint(f'CSV cree: {csv_path}')")

code("# Test analyseur\nanalyzer = FileAnalyzer()\nmeta = analyzer.analyze(csv_path)\nprint(analyzer.generate_summary(meta))")

code("# Colonnes detail\nfor c in meta.columns:\n    print(f\"{c['name']}: {c['dtype']}, {c.get('missing_pct', 0)}% manquant\")\n    if 'stats' in c:\n        print(f\"  -> min={c['stats']['min']:.1f}, max={c['stats']['max']:.1f}, mean={c['stats']['mean']:.1f}\")")

md("## 5. Resume LLM")

code("# Resume intelligent\nsummary = analyzer.generate_llm_summary(meta)\nprint(summary)")

code("# Resume guide\nq = \"Quelles analyses puis-je faire sur ces donnees?\"\nprint(f\"Question: {q}\\n\")\nresult = analyzer.generate_llm_summary(meta, q)\nprint(result)")

md("## 6. Resume du Lab\n\n### Points cles\n\n1. FileAnalyzer: Analyse automatique de fichiers\n2. Metadonnees: Extraction de schemas et stats\n3. Resume LLM: Contextualisation pour le Planner\n\n### Prochaine etape\n\n- Lab 11: Boucle Planner-Coder-Verifier")

code("# Cleanup\nimport shutil\nshutil.rmtree(test_dir)\nprint('Done')")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day5-DS-Star/Lab10-File-Analyzer.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
