# =============================================================================
# Vendored from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file: argumentation_analysis/agents/core/logic/propositional_logic_agent.py
# Upstream commit: ecfd9b9c (SHA cite par l'issue #18392)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA NOTICE: see ./NOTICE-EPITA — section "Argument_Analysis volet texte->PL".
#
# ROLE DANS CoursIA (#18392)
# --------------------------
# Le tronc EPITA definit le pattern "le LLM pilote un raisonneur deterministe" :
#   text_to_belief_set  : le LLM traduit le texte en formules PL ;
#   generate_queries    : le LLM propose les requetes pertinentes ;
#   execute_query       : Tweety decide de l'entaillement (jamais le LLM).
# Ce module vendorise le chemin texte -> PL : les prompts et les filtres qui
# garantissent que TOUTE formule affichee est une sortie LLM validee par le
# parseur Tweety — aucune formule ne vit en dur dans le notebook consommateur.
#
# DELTA DOCUMENTE vs upstream (adaptations, pas des reecritures)
# --------------------------------------------------------------
# 1. Budget LLM : upstream fait DEUX appels pour la traduction
#    (TextToPLDefs puis TextToPLFormulas) + un pour les requetes. L'issue #18392
#    arbitre a DEUX appels au total : les prompts de defs et de formulas sont
#    fusionnes ici en PROMPT_TEXT_TO_PL (une reponse JSON portant les deux cles),
#    PROMPT_GEN_QUERIES reste l'appel de requetes.
# 2. Service LLM injecte : upstream invoque `kernel.invoke` sur des fonctions de
#    plugin Semantic Kernel. Ici le service est INJECTE (un callable
#    `chat(prompt) -> str` fourni par le notebook), le module reste importable
#    et testable sans SK ni cle (cf _config.py : zero secret dans la lib).
# 3. Extraction JSON et filtrage des formules : logique VERBATIM de
#    `_extract_json_block` et `_filter_formulas` (regex + issubset), en
#    fonctions libres.
# 4. La validation syntaxique par Tweety est injectee aussi (`parse_fn`) :
#    `validate_with_parser` separe acceptees / rejetees sans lever, pour que le
#    notebook puisse MONTRER un rejet (l'argument pedagogique de #18392).
# =============================================================================

"""Champ texte -> PL : prompts, extraction JSON, filtres, partition par le parseur.

Le consommateur canonique est la section « Du texte a la formule » de
Argumentation-05-Formal-Verification-Python.ipynb. Le module est volontairement
SK-free : le service de chat et le parseur Tweety sont injectes.
"""

from __future__ import annotations

import json
import re
from typing import Callable, List, Tuple

# --- Prompts (fusion des prompts upstream PROMPT_TEXT_TO_PL_DEFS +
# PROMPT_TEXT_TO_PL_FORMULAS ; marqueurs {{$var}} conserves tels quels) ---

PROMPT_TEXT_TO_PL = """
Vous etes un expert en logique propositionnelle (PL). Votre tache se fait en deux temps sur un texte donne :

**Temps 1 - Propositions atomiques** : identifiez les propositions atomiques (faits de base) du texte.
Les noms des propositions doivent etre concis, en minuscules et en `snake_case` (ex: "socrates_is_mortal").

**Temps 2 - Formules** : traduisez le texte en formules logiques en utilisant EXCLUSIVEMENT les propositions du temps 1.

**Regles strictes :**
*   **Utilisation exclusive** : n'utilisez QUE les propositions que vous avez declarees au temps 1. N'en inventez pas de nouvelles.
*   **Connecteurs** : utilisez `!`, `&&`, `||`, `=>`, `<=>`.
*   **Format** : les formules sont une liste de chaines de caracteres. N'ajoutez PAS de point-virgule a la fin.

**Format de sortie (JSON strict, sans autre texte) :**
```json
{
  "propositions": ["..."],
  "formulas": ["..."]
}
```

**Exemple :**
Texte: "Socrate est un homme. Si un etre est un homme, alors il est mortel."
```json
{
  "propositions": [
    "socrates_is_a_man",
    "socrates_is_mortal"
  ],
  "formulas": [
    "socrates_is_a_man",
    "socrates_is_a_man => socrates_is_mortal"
  ]
}
```

Analysez le texte suivant et produisez l'objet JSON complet.

{{$input}}
"""

PROMPT_GEN_QUERIES = """
Vous etes un expert en logique propositionnelle. Votre tache est de generer des "idees" de requetes pertinentes pour interroger un ensemble de croyances (belief set) donne.

**Contexte fourni :**
1.  **Texte original** : le texte qui motive l'analyse.
2.  **Ensemble de croyances** : les propositions atomiques declarees et les formules traduites.

**Votre tache :**
Generez un objet JSON contenant UNIQUEMENT la cle `query_ideas`.
La valeur de `query_ideas` doit etre une liste de chaines de caracteres, ou chaque chaine est une proposition que vous jugez pertinent de verifier.

**Regles strictes :**
*   **Utilisation exclusive** : n'utilisez QUE les propositions qui existent dans l'ensemble de croyances fourni. N'en inventez pas.
*   **Pertinence** : les idees de requetes doivent chercher a verifier des conclusions ou des faits interessants au regard du texte original.
*   **Format de sortie** : un objet JSON valide, sans aucun texte ou explication supplementaire.

**Exemple :**
```json
{
  "query_ideas": [
    "socrates_is_mortal",
    "socrates_is_a_man"
  ]
}
```

Maintenant, analysez le contexte suivant et genererez les idees de requetes.

**Texte original :**
{{$input}}

**Ensemble de croyances :**
{{$belief_set}}
"""


def render_prompt(template: str, **variables: str) -> str:
    """Substitue les marqueurs `{{$var}}` (syntaxe SK conservee des prompts upstream)."""
    for name, value in variables.items():
        template = template.replace("{{$" + name + "}}", value)
    return template


def extract_json_block(text: str) -> str:
    """Extrait le premier bloc JSON valide de la reponse du LLM.

    Logique verbatim de `_extract_json_block` (upstream) : bloc ```json fenced
    d'abord, sinon braces externes, sinon la chaine telle quelle (le loads
    suivant echouera bruyamment — comportement assume).
    """
    match = re.search(r"```json\s*(\{.*?\})\s*```", text, re.DOTALL)
    if match:
        return match.group(1)

    start_index = text.find("{")
    end_index = text.rfind("}")
    if start_index != -1 and end_index != -1 and end_index > start_index:
        return text[start_index : end_index + 1]

    return text


def filter_formulas(formulas: List[str], declared_propositions) -> List[str]:
    """Filtre les formules pour ne garder que celles qui utilisent des propositions declarees.

    Logique verbatim de `_filter_formulas` (upstream) : une formule dont un
    identifiant n'est pas dans l'ensemble declare est rejetee — le LLM ne peut
    pas introduire de proposition inconnue par le biais d'une formule.
    """
    declared = set(declared_propositions)
    proposition_pattern = re.compile(r"\b[a-zA-Z_][a-zA-Z0-9_]*\b")

    valid_formulas = []
    for formula in formulas:
        used_propositions = set(proposition_pattern.findall(formula))
        if used_propositions.issubset(declared):
            valid_formulas.append(formula)
    return valid_formulas


def parse_translation_response(raw: str) -> Tuple[List[str], List[str]]:
    """Reponse LLM brute -> (propositions, formulas).

    Echoue par ValueError (pas de retour silencieux) : une traduction
    inexploitable doit se VOIR, pas se resoudre en liste vide.
    """
    data = json.loads(extract_json_block(raw))
    propositions = data.get("propositions")
    formulas = data.get("formulas")
    if not isinstance(propositions, list) or not isinstance(formulas, list):
        raise ValueError(
            "Reponse de traduction incomplete (cles attendues : propositions, "
            f"formulas) ; cles vues : {sorted(data) if isinstance(data, dict) else type(data)}"
        )
    return [str(p) for p in propositions], [str(f) for f in formulas]


def parse_query_response(raw: str) -> List[str]:
    """Reponse LLM brute -> liste d'idees de requetes (chaines)."""
    data = json.loads(extract_json_block(raw))
    ideas = data.get("query_ideas", [])
    if not isinstance(ideas, list):
        raise ValueError(f"query_ideas n'est pas une liste : {type(ideas)}")
    return [str(q) for q in ideas if isinstance(q, str)]


def validate_with_parser(
    formulas: List[str], parse_fn: Callable[[str], object]
) -> Tuple[List[str], List[dict]]:
    """Partitionne les formules en (acceptees, rejetees) via le VRAI parseur.

    `parse_fn` est typiquement `parser.parseFormula` (Tweety PlParser) : toute
    exception est capturee et raportee, jamais masquee — le rejet est une
    information pedagogique (#18392 : montrer un echec de traduction), pas une
    panne.
    """
    accepted: List[str] = []
    rejected: List[dict] = []
    for formula in formulas:
        try:
            parse_fn(formula)
            accepted.append(formula)
        except Exception as exc:  # jpype leve des types Java : catch large assumé
            rejected.append({"formula": formula, "error": str(exc).strip()[:160]})
    return accepted, rejected


def belief_set_summary(propositions: List[str], formulas: List[str]) -> str:
    """Corps JSON du belief set tel que presente au prompt de requetes (upstream)."""
    return json.dumps(
        {"propositions": propositions, "formulas": formulas}, indent=2, ensure_ascii=False
    )
