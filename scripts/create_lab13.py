"""Script to create Lab13 notebook - Web Search for SOTA Models."""
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

# Lab 13 content
md("""# Lab 13: Web Search pour Modeles SOTA (MLE-STAR Component)

## Objectifs

- Implementer la recherche web pour trouver les modeles SOTA
- Extraire des informations depuis arXiv et autres sources
- Generer du code initial base sur les resultats

## Architecture MLE-STAR

```
Competition Kaggle
       |
       v
[WEB SEARCH] --> Modeles SOTA
       |
       v
[PLANNER] --> Plan ML
       |
       v
[CODER] --> Code Initial
       |
       v
[ABLATION] --> Raffinement
```""")

md("## 1. Configuration")

code("""import sys
sys.path.insert(0, '..')

import json
import re
import requests
from typing import List, Dict, Optional
from dataclasses import dataclass
from datetime import datetime

from config import get_settings
from utils import LLMClient""")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 2. Data Classes")

code("""@dataclass
class SearchResult:
    title: str
    url: str
    snippet: str
    source: str
    date: str = None

@dataclass
class ModelInfo:
    name: str
    paper_url: str
    description: str
    code_url: str = None
    performance: str = None""")

md("## 3. Web Search Module")

code('''class WebSearcher:
    """Recherche web pour trouver des modeles SOTA."""

    def __init__(self):
        self.headers = {'User-Agent': 'Mozilla/5.0 (compatible; DS-Star/1.0)'}

    def search_arxiv(self, query: str, max_results: int = 5) -> List[SearchResult]:
        """Recherche sur arXiv via API."""
        url = f"http://export.arxiv.org/api/query?search_query=all:{query}&max_results={max_results}"
        try:
            response = requests.get(url, headers=self.headers, timeout=10)
            results = []
            # Parse Atom feed
            entries = response.text.split('<entry>')[1:]
            for entry in entries:
                title = re.search(r'<title>(.*?)</title>', entry, re.DOTALL)
                link = re.search(r'<id>(.*?)</id>', entry)
                summary = re.search(r'<summary>(.*?)</summary>', entry, re.DOTALL)
                if title and link:
                    results.append(SearchResult(
                        title=title.group(1).strip().replace('\\n', ' '),
                        url=link.group(1).strip(),
                        snippet=summary.group(1).strip()[:200] if summary else '',
                        source='arxiv'
                    ))
            return results
        except Exception as e:
            print(f"Erreur arXiv: {e}")
            return []

    def search_papers_with_code(self, task: str) -> List[SearchResult]:
        """Simule une recherche sur Papers With Code (API publique)."""
        # Papers With Code a une API publique mais limitee
        # Pour ce lab, on simule avec des resultats types
        mock_results = [
            SearchResult(
                title="State-of-the-Art Image Classification",
                url="https://paperswithcode.com/sota/image-classification-on-imagenet",
                snippet="Vision Transformers achieve 90.5% top-1 accuracy",
                source="paperswithcode"
            ),
            SearchResult(
                title="Object Detection Benchmarks",
                url="https://paperswithcode.com/sota/object-detection-on-coco",
                snippet="YOLOv9 and DINO lead COCO detection",
                source="paperswithcode"
            )
        ]
        return mock_results''')

md("## 4. LLM-Based Model Extractor")

code('''class ModelExtractor:
    """Extrait les informations de modeles depuis les resultats de recherche."""

    def __init__(self, llm: LLMClient):
        self.llm = llm

    def extract_models(self, search_results: List[SearchResult], task: str) -> List[ModelInfo]:
        """Utilise le LLM pour extraire les modeles pertinents."""
        context = "\\n".join([
            f"- {r.title}: {r.snippet} ({r.url})"
            for r in search_results[:5]
        ])

        prompt = f"""Analyse ces resultats de recherche pour la tache: {task}

RESULTATS:
{context}

Extrait les 2-3 modeles les plus pertinents avec leurs informations.
Format JSON:
[
  {{"name": "...", "paper_url": "...", "description": "...", "code_url": "..."}}
]

JSON:"""

        response = self.llm.generate(prompt, temperature=0.2)

        # Extract JSON
        try:
            match = re.search(r'\\[.*\\]', response, re.DOTALL)
            if match:
                data = json.loads(match.group(0))
                return [ModelInfo(**m) for m in data]
        except:
            pass
        return []''')

md("## 5. Code Generator from SOTA")

code('''class SOTACodeGenerator:
    """Genere du code initial base sur les modeles SOTA trouves."""

    def __init__(self, llm: LLMClient):
        self.llm = llm

    def generate_initial_code(self, task: str, models: List[ModelInfo]) -> str:
        """Genere du code de base utilisant les modeles SOTA."""
        models_desc = "\\n".join([
            f"- {m.name}: {m.description}"
            for m in models[:2]
        ])

        prompt = f"""Genere du code Python initial pour cette tache ML.

TACHE: {task}

MODELES SOTA DISPONIBLES:
{models_desc}

Genere un script Python simple et commente qui:
1. Charge les donnees
2. Prepare le modele
3. Entra�ne et evalue

```python
# Ton code ici
```"""

        response = self.llm.generate(prompt, temperature=0.3)
        match = re.search(r'```python\\s*(.*?)\\s*```', response, re.DOTALL)
        return match.group(1).strip() if match else response''')

md("## 6. MLE-STAR Pipeline Partiel")

code('''class MLEStarSearcher:
    """Pipeline de recherche SOTA (partie de MLE-STAR)."""

    def __init__(self):
        self.llm = LLMClient()
        self.web_searcher = WebSearcher()
        self.extractor = ModelExtractor(self.llm)
        self.code_gen = SOTACodeGenerator(self.llm)

    def find_sota_models(self, task: str) -> Dict:
        """Trouve les modeles SOTA pour une tache donnee."""
        print(f"[WEB SEARCH] Recherche pour: {task}")

        # Search arXiv
        print("  - Recherche arXiv...")
        arxiv_results = self.web_searcher.search_arxiv(task)

        # Search Papers With Code (simule)
        print("  - Recherche Papers With Code...")
        pwc_results = self.web_searcher.search_papers_with_code(task)

        all_results = arxiv_results + pwc_results
        print(f"  - {len(all_results)} resultats trouves")

        # Extract models with LLM
        print("[EXTRACTOR] Extraction des modeles...")
        models = self.extractor.extract_models(all_results, task)
        print(f"  - {len(models)} modeles identifies")

        return {
            'task': task,
            'search_results': all_results,
            'models': models
        }

    def generate_baseline_code(self, task: str, models: List[ModelInfo]) -> str:
        """Genere du code de base."""
        print("[CODE GEN] Generation du code initial...")
        code = self.code_gen.generate_initial_code(task, models)
        return code''')

md("## 7. Test du Pipeline")

code("""# Test avec une tache ML typique
searcher = MLEStarSearcher()

task = "image classification imagenet"
result = searcher.find_sota_models(task)

print("\\n" + "="*50)
print("MODELES TROUVES:")
print("="*50)
for m in result['models']:
    print(f"\\n- {m.name}")
    print(f"  Description: {m.description[:80]}...")
    print(f"  Paper: {m.paper_url}")""")

md("## 8. Generation de Code")

code("""# Generer du code initial
if result['models']:
    code = searcher.generate_baseline_code(task, result['models'])
    print("\\n" + "="*50)
    print("CODE GENERE:")
    print("="*50)
    print(code[:800] + "..." if len(code) > 800 else code)""")

md("""## 9. Resume du Lab

### Ce que nous avons implemente

1. **WebSearcher**: Recherche sur arXiv et Papers With Code
2. **ModelExtractor**: Extraction des modeles via LLM
3. **SOTACodeGenerator**: Generation de code initial

### Limitations

- L'API Papers With Code est simulee (rate limiting)
- La recherche web reelle necessite une API (Tavily, Serper)
- Le code genere est un point de depart, pas une solution complete

### Integration MLE-STAR

Dans MLE-STAR complet, ce module est utilise pour:
1. Comprendre la competition Kaggle
2. Trouver les approches SOTA
3. Generer le code initial
4. Puis passer a l'ablation et raffinement

### Prochaine etape

- **Lab 14**: Ablation et Raffinement Cible""")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day6-MLE-Star/Lab13-Web-Search-SOTA.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
