"""Script to create Lab11 notebook."""
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

# Lab 11 content
md("# Lab 11: Planner-Coder-Verifier Loop (DS-STAR Core)\n\n## Objectifs\n\n- Implementer la boucle iterative Planner-Coder-Verifier de DS-STAR\n- Creer un systeme multi-agents pour l'analyse de donnees\n- Gerer les echecs et raffinements automatiques")

md("## 1. Architecture Planner-Coder-Verifier\n\n```\nQuestion --> [PLANNER] --> Plan\n                      |\n                      v\n                [CODER] --> Code\n                      |\n                      v\n                [EXECUTOR] --> Result\n                      |\n                      v\n                [VERIFIER] --> Success/Retry\n```")

md("## 2. Configuration")

code("import sys\nsys.path.insert(0, '..')\n\nimport json\nimport re\nimport pandas as pd\nimport numpy as np\nfrom typing import Optional, Dict, List, Tuple\nfrom dataclasses import dataclass\nfrom enum import Enum\n\nfrom config import get_settings\nfrom utils import LLMClient")

code("settings = get_settings()\nprint(f'Provider: {settings.active_provider}')")

md("## 3. Data Classes")

code("@dataclass\nclass Plan:\n    steps: List[str]\n    reasoning: str\n\n@dataclass\nclass ExecutionResult:\n    success: bool\n    output: str\n    error: Optional[str] = None\n    code: Optional[str] = None\n\nclass VerificationStatus(Enum):\n    SUCCESS = 'success'\n    NEEDS_REFINEMENT = 'needs_refinement'\n    FAILED = 'failed'")

md("## 4. Planner Agent")

code('''class Planner:
    def __init__(self, llm: LLMClient):
        self.llm = llm

    def create_plan(self, question: str, context: str) -> Plan:
        prompt = f"""Tu es un planificateur d'analyse de donnees.

CONTEXTE DES FICHIERS:
{context}

QUESTION: {question}

Genere un plan d'analyse en 3-5 etapes. Pour chaque etape, decris:
1. L'objectif
2. La methode
3. Le resultat attendu

Format de sortie:
REASONING: [ton raisonnement]
STEPS:
1. [etape 1]
2. [etape 2]
...

Plan:"""

        response = self.llm.generate(prompt, temperature=0.3)

        # Parse response
        steps = []
        reasoning = ""
        lines = response.split('\\n')
        in_steps = False

        for line in lines:
            if line.startswith('REASONING:'):
                reasoning = line.replace('REASONING:', '').strip()
            elif line.startswith('STEPS:'):
                in_steps = True
            elif in_steps and re.match(r'^\\d+\\.', line.strip()):
                steps.append(re.sub(r'^\\d+\\.\\s*', '', line.strip()))

        return Plan(steps=steps, reasoning=reasoning)''')

md("## 5. Coder Agent")

code('''class Coder:
    def __init__(self, llm: LLMClient):
        self.llm = llm

    def generate_code(self, plan: Plan, context: str) -> str:
        steps_text = '\\n'.join(f"{i+1}. {s}" for i, s in enumerate(plan.steps))

        prompt = f"""Tu es un programmeur Python expert. Genere du code pour executer ce plan.

CONTEXTE:
{context}

PLAN:
{steps_text}

Genere UNIQUEMENT du code Python executable entre balises ```python ... ```
Le DataFrame est disponible dans la variable 'df'.
Utilise print() pour afficher les resultats.

Code:"""

        response = self.llm.generate(prompt, temperature=0.2)

        # Extract code
        match = re.search(r'```python\\s*(.*?)\\s*```', response, re.DOTALL)
        if match:
            return match.group(1).strip()
        return response''')

md("## 6. Executor")

code('''class Executor:
    def __init__(self, df: pd.DataFrame):
        self.df = df
        self.namespace = {'df': df, 'pd': pd, 'np': np, 'print': print}

    def execute(self, code: str) -> ExecutionResult:
        import sys
        from io import StringIO

        old_stdout = sys.stdout
        sys.stdout = StringIO()

        try:
            exec(code, self.namespace)
            output = sys.stdout.getvalue()
            return ExecutionResult(success=True, output=output, code=code)
        except Exception as e:
            output = sys.stdout.getvalue()
            return ExecutionResult(success=False, output=output, error=str(e), code=code)
        finally:
            sys.stdout = old_stdout''')

md("## 7. Verifier Agent")

code('''class Verifier:
    def __init__(self, llm: LLMClient):
        self.llm = llm

    def verify(self, question: str, result: ExecutionResult) -> Tuple[VerificationStatus, str]:
        if not result.success:
            return VerificationStatus.FAILED, f"Erreur d'execution: {result.error}"

        prompt = f"""Verifie si ce resultat repond a la question.

QUESTION: {question}

RESULTAT:
{result.output[:1000]}

Reponds par:
- SUCCESS si le resultat est complet et correct
- NEEDS_REFINEMENT si le resultat est partiel mais prometteur
- FAILED si le resultat ne repond pas du tout

Verdict:"""

        response = self.llm.generate(prompt, temperature=0.1).upper()

        if 'SUCCESS' in response:
            return VerificationStatus.SUCCESS, "Resultat valide"
        elif 'REFINEMENT' in response:
            return VerificationStatus.NEEDS_REFINEMENT, "Necessite des ajustements"
        return VerificationStatus.FAILED, "Resultat insuffisant"''')

md("## 8. DS-STAR Orchestrator")

code('''class DSStarAgent:
    def __init__(self, df: pd.DataFrame, max_iterations: int = 3):
        self.llm = LLMClient()
        self.planner = Planner(self.llm)
        self.coder = Coder(self.llm)
        self.executor = Executor(df)
        self.verifier = Verifier(self.llm)
        self.max_iterations = max_iterations

    def analyze(self, question: str, file_context: str = None) -> Dict:
        context = file_context or "DataFrame 'df' disponible"

        for iteration in range(self.max_iterations):
            print(f"\\n=== ITERATION {iteration + 1}/{self.max_iterations} ===")

            # Step 1: Plan
            print("[PLANNER] Creation du plan...")
            plan = self.planner.create_plan(question, context)
            print(f"Etapes: {len(plan.steps)}")

            # Step 2: Generate code
            print("[CODER] Generation du code...")
            code = self.coder.generate_code(plan, context)

            # Step 3: Execute
            print("[EXECUTOR] Execution...")
            result = self.executor.execute(code)

            if not result.success:
                print(f"[ERROR] {result.error}")
                context += f"\\nErreur precedente: {result.error}\\nCorrige le code."
                continue

            print(f"[OUTPUT] {result.output[:200]}...")

            # Step 4: Verify
            print("[VERIFIER] Verification...")
            status, message = self.verifier.verify(question, result)
            print(f"[STATUS] {status.value}: {message}")

            if status == VerificationStatus.SUCCESS:
                return {
                    'success': True,
                    'output': result.output,
                    'code': code,
                    'iterations': iteration + 1
                }

            # Raffinement
            context += f"\\nResultat partiel: {result.output[:500]}\\nAmeliore l'analyse."

        return {
            'success': False,
            'output': result.output if 'result' in dir() else '',
            'error': 'Max iterations atteint',
            'iterations': self.max_iterations
        }''')

md("## 9. Test avec un Dataset")

code("# Dataset de test\nimport tempfile\nimport os\n\ndf = pd.DataFrame({\n    'date': pd.date_range('2024-01-01', periods=200, freq='D'),\n    'product': np.random.choice(['A', 'B', 'C', 'D'], 200),\n    'region': np.random.choice(['Nord', 'Sud', 'Est', 'Ouest'], 200),\n    'revenue': np.random.uniform(100, 5000, 200).round(2),\n    'units': np.random.randint(1, 100, 200)\n})\nprint(f'Dataset: {len(df)} lignes')\ndf.head()")

code("# Test de l'agent DS-STAR avec 1 iteration pour rapidite\nagent = DSStarAgent(df, max_iterations=1)\n\nquestion = \"Quelle est la region avec le plus grand revenu moyen?\"\nresult = agent.analyze(question)\n\nprint(\"\\n\" + \"=\"*50)\nprint(\"RESULTAT FINAL:\")\nprint(\"=\"*50)\nif result['success']:\n    print(result['output'])\nelse:\n    print(f\"Erreur: {result.get('error', 'Inconnu')}\")")

md("## 10. Resume du Lab\n\n### Ce que nous avons implemente\n\n1. **Planner**: Decompose la question en etapes\n2. **Coder**: Genere le code Python\n3. **Executor**: Execute en toute securite\n4. **Verifier**: Valide ou demande raffinement\n\n### Points cles\n\n- La boucle iterative permet de corriger les erreurs\n- Le verifier assure la qualite des resultats\n- Le contexte est enrichi a chaque iteration\n\n### Prochaine etape\n\n- **Lab 12**: Workshop DS-STAR complet avec fichiers reels")

# Save
output = 'MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb'
with open(output, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1)
print(f"Created: {output}")
