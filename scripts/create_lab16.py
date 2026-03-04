"""Script to create Lab16 notebook - Data Science Agent GCP."""
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

# Lab 16 content
md("""# Lab 16: Data Science Agent avec GCP (BigQuery)

## Objectifs

- Comprendre l'architecture de l'agent Data Science Google
- Explorer NL2SQL et NL2Py pour BigQuery
- Integrer BQML pour le machine learning

## Prerequis

Ce lab necessite un projet GCP avec BigQuery API activee.
Note: Ce lab presente l'architecture theorique.""")

md("## 1. Configuration")

code("import sys\nsys.path.insert(0, '..')\n\nimport json\nimport re\nfrom typing import List, Dict, Optional\nfrom dataclasses import dataclass\n\nfrom config import get_settings\nfrom utils import LLMClient")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 2. NL2SQL Translator")

code("@dataclass\nclass SQLQuery:\n    sql: str\n    explanation: str\n    tables_used: List[str]\n\nclass NL2SQLTranslator:\n    def __init__(self, llm: LLMClient):\n        self.llm = llm\n\n    def translate(self, question: str, schema: Dict) -> SQLQuery:\n        schema_desc = self._format_schema(schema)\n        prompt = f\"\"\"Convertis cette question en SQL BigQuery.\n\nSCHEMA:\n{schema_desc}\n\nQUESTION: {question}\n\nEXPLANATION: [explication]\nSQL:\n```sql\n[requete]\n```\"\"\"\n        response = self.llm.generate(prompt, temperature=0.2)\n        explanation = ''\n        sql = ''\n        if 'EXPLANATION:' in response:\n            match = re.search(r'EXPLANATION:\\s*(.+?)(?=SQL:|$)', response, re.DOTALL)\n            explanation = match.group(1).strip() if match else ''\n        sql_match = re.search(r'```sql\\s*(.*?)\\s*```', response, re.DOTALL)\n        sql = sql_match.group(1).strip() if sql_match else ''\n        return SQLQuery(sql=sql, explanation=explanation, tables_used=[])\n\n    def _format_schema(self, schema: Dict) -> str:\n        return '\\n'.join([f'Table {t}: {cols}' for t, cols in schema.items()])")

md("## 3. NL2Py Translator")

code("@dataclass\nclass PythonCode:\n    code: str\n    explanation: str\n\nclass NL2PyTranslator:\n    def __init__(self, llm: LLMClient):\n        self.llm = llm\n\n    def translate(self, question: str, data_context: str) -> PythonCode:\n        prompt = f\"\"\"Genere du code Python pour: {question}\n\nCONTEXTE: {data_context}\n\nEXPLANATION: [explication]\nCODE:\n```python\n[code]\n```\"\"\"\n        response = self.llm.generate(prompt, temperature=0.2)\n        explanation = ''\n        code = ''\n        if 'EXPLANATION:' in response:\n            match = re.search(r'EXPLANATION:\\s*(.+?)(?=CODE:|$)', response, re.DOTALL)\n            explanation = match.group(1).strip() if match else ''\n        code_match = re.search(r'```python\\s*(.*?)\\s*```', response, re.DOTALL)\n        code = code_match.group(1).strip() if code_match else ''\n        return PythonCode(code=code, explanation=explanation)")

md("## 4. Data Science Agent")

code("class DataScienceAgent:\n    def __init__(self):\n        self.llm = LLMClient()\n        self.nl2sql = NL2SQLTranslator(self.llm)\n        self.nl2py = NL2PyTranslator(self.llm)\n\n    def analyze(self, question: str, schema: Dict, mode: str = 'sql') -> Dict:\n        print(f'[AGENT] Question: {question}')\n        print(f'[AGENT] Mode: {mode}')\n        if mode == 'sql':\n            result = self.nl2sql.translate(question, schema)\n            return {'type': 'sql', 'query': result.sql, 'explanation': result.explanation}\n        elif mode == 'python':\n            data_context = self.nl2sql._format_schema(schema)\n            result = self.nl2py.translate(question, data_context)\n            return {'type': 'python', 'code': result.code, 'explanation': result.explanation}\n        return {'error': 'Mode non supporte'}")

md("## 5. Test avec Schema Simule")

code("schema = {\n    'sales': ['date', 'product', 'region', 'quantity', 'revenue'],\n    'customers': ['customer_id', 'name', 'segment', 'signup_date'],\n    'products': ['product_id', 'name', 'category', 'price']\n}\n\nprint('Schema BigQuery:')\nfor table, cols in schema.items():\n    print(f'  {table}: {cols}')")

code("# Test NL2SQL\nagent = DataScienceAgent()\nquestion = 'Quel est le revenu total par region?'\nresult = agent.analyze(question, schema, mode='sql')\n\nprint('\\\\n' + '='*50)\nprint('RESULTAT NL2SQL:')\nprint('='*50)\nprint(f'Explication: {result.get(\"explanation\", \"N/A\")}')\nprint(f'SQL: {result.get(\"query\", \"N/A\")}')")

code("# Test NL2Py\nquestion2 = 'Calcule la moyenne des revenus par mois'\nresult2 = agent.analyze(question2, schema, mode='python')\n\nprint('\\\\n' + '='*50)\nprint('RESULTAT NL2Py:')\nprint('='*50)\nprint(f'Explication: {result2.get(\"explanation\", \"N/A\")}')\nprint(f'Code: {result2.get(\"code\", \"N/A\")[:300]}...')")

md("""## 6. Resume du Lab

### Architecture Google Data Science Agent

1. NL2SQL: Question naturelle vers BigQuery
2. NL2Py: Question naturelle vers Python
3. BQML: Modeles ML dans BigQuery

### Prochaine etape

Lab 17: Projet Final""")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day7-Production/Lab16-Data-Science-Agent.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
