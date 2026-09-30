"""Quantificateurs booleens (QBF) par enumeration naive et acceptabilite
argumentative (strate 6, Epic #4588, grain #17339).

Port pedagogique DECLARE de la distillation-outil EPITA 2025 Argumentation :

* ``argumentation_analysis/agents/core/logic/qbf_native.py`` (466 lignes, ne
  au commit ``0d2ac1b0``, PR EPITA #167 « pure-Python QBF solver +
  argumentation-to-QBF conversion »), enseigne par
  ``docs/coursia_contrib/belief_revision.ipynb`` section 5.

Source mesuree firsthand au clone local ``2025-Epita-Intelligence-Symbolique``
a la tete ``a5ac1a5d`` (2026-09-22). Divergences declarees par rapport a la
source (regle ``organ-first-implementation``) :

1. **L'acceptabilite sceptique consomme l'organe natif** : la source importe
   ``argumentation_analysis.agents.core.logic.dung_native`` (try/except) ;
   le port consomme :func:`ict.argumentation.preferred_extensions` -- ajoutee
   a l'organe par ce meme grain (il n'exposait que la semantique grounded).
   Le mapping noms -> indices d'arguments vit a la frontiere.
2. **Refus uniformise** : la source rend ``accepted=None`` avec une raison
   pour un cadre trop grand cote credule, et laisserait lever une exception
   brute cote sceptique ; le port attrape le ``ValueError`` de l'organe et
   rend la meme forme ``accepted=None`` des deux cotes.
3. **Docstrings en francais** (convention du depot), sans emojis.

Semantiques COPIEES FIDELEMENT (ce sont elles que les gates differentiels des
tests verifient contre la source, litteraux figes) :

* AST booleen : ``Var`` / ``Not`` / ``And`` / ``Or`` / ``Implies`` avec
  ``evaluate(assignment)`` et ``variables()`` ;
* quantificateurs ``ForAll`` / ``Exists`` a blocs de variables, evalues par
  produit cartesien ``itertools.product`` (enumeration naive ASSUMEE : la
  methode est le sujet, l'alternance rendue visible pas a pas) ;
* parseur a precedentences ``! > & > | > =>`` **sans parentheses** (limite
  declaree de la source, conservee et enseignee : le carnet montre le piege
  de lecture) ;
* ``check_qbf`` construit la formule quantifiee en imbriquant depuis la
  matrice avec ``reversed(quantifiers)`` (le premier quantifier de la liste
  est le plus externe) ;
* ``analyze_qbf`` rapporte ``search_space = 2**n`` -- le cout rendu visible ;
* acceptabilite CREDULE : enumeration des sous-ensembles par masques binaires
  croissants, sans conflit + admissible, TEMOIN = premier extension trouvee
  (deterministe : ordre des bits) ; borne ``n <= 15`` ;
* acceptabilite SCEPTIQUE : ``target`` dans TOUTES les extensions preferees.

Conventions de la serie : determinisme complet, CPU pur, stdlib uniquement.
"""

from __future__ import annotations

import itertools
from typing import Any, Dict, List, Optional, Set, Tuple

from .argumentation import DungAF, preferred_extensions

__all__ = [
    "QBFFormula",
    "Var",
    "Not",
    "And",
    "Or",
    "Implies",
    "ForAll",
    "Exists",
    "parse_formula",
    "check_qbf",
    "analyze_qbf",
    "credulous_acceptance_qbf",
    "skeptical_acceptance_qbf",
    "example_simple_validity",
    "example_simple_satisfiability",
    "example_mixed_quantifiers",
    "example_argumentation_acceptance",
]


# --------------------------------------------------------------------------- #
#  AST booleen a quantificateurs                                              #
# --------------------------------------------------------------------------- #


class QBFFormula:
    """Base commune : evaluation sous assignation partielle + variables."""

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        raise NotImplementedError

    def variables(self) -> Set[str]:
        raise NotImplementedError

    def __repr__(self) -> str:
        raise NotImplementedError


class Var(QBFFormula):
    """Une variable propositionnelle, identifiee par son nom (une lettre
    simple pour le parseur : aucun caractere d'operateur dans le nom)."""

    def __init__(self, name: str):
        self.name = name

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        return assignment[self.name]

    def variables(self) -> Set[str]:
        return {self.name}

    def __repr__(self) -> str:
        return self.name


class Not(QBFFormula):
    """Negation unaire."""

    def __init__(self, inner: QBFFormula):
        self.inner = inner

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        return not self.inner.evaluate(assignment)

    def variables(self) -> Set[str]:
        return self.inner.variables()

    def __repr__(self) -> str:
        return f"!({self.inner!r})"


class And(QBFFormula):
    """Conjonction binaire."""

    def __init__(self, left: QBFFormula, right: QBFFormula):
        self.left = left
        self.right = right

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        return self.left.evaluate(assignment) and self.right.evaluate(assignment)

    def variables(self) -> Set[str]:
        return self.left.variables() | self.right.variables()

    def __repr__(self) -> str:
        return f"({self.left!r} & {self.right!r})"


class Or(QBFFormula):
    """Disjonction binaire."""

    def __init__(self, left: QBFFormula, right: QBFFormula):
        self.left = left
        self.right = right

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        return self.left.evaluate(assignment) or self.right.evaluate(assignment)

    def variables(self) -> Set[str]:
        return self.left.variables() | self.right.variables()

    def __repr__(self) -> str:
        return f"({self.left!r} | {self.right!r})"


class Implies(QBFFormula):
    """Implication ``left => right`` (materielle : fausse seulement pour
    Vrai => Faux)."""

    def __init__(self, left: QBFFormula, right: QBFFormula):
        self.left = left
        self.right = right

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        return (not self.left.evaluate(assignment)) or self.right.evaluate(assignment)

    def variables(self) -> Set[str]:
        return self.left.variables() | self.right.variables()

    def __repr__(self) -> str:
        return f"({self.left!r} => {self.right!r})"


class ForAll(QBFFormula):
    """Quantificateur universel sur un bloc de variables : la formule interne
    doit tenir pour TOUTE combinaison de valeurs du bloc."""

    def __init__(self, vars: List[str], formula: QBFFormula):
        self.vars = vars
        self.formula = formula

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        for combo in itertools.product([True, False], repeat=len(self.vars)):
            extended = dict(assignment)
            for var, val in zip(self.vars, combo):
                extended[var] = val
            if not self.formula.evaluate(extended):
                return False
        return True

    def variables(self) -> Set[str]:
        return set(self.vars) | self.formula.variables()

    def __repr__(self) -> str:
        return f"ForAll {self.vars}. ({self.formula!r})"


class Exists(QBFFormula):
    """Quantificateur existentiel sur un bloc de variables : la formule
    interne doit tenir pour AU MOINS une combinaison du bloc."""

    def __init__(self, vars: List[str], formula: QBFFormula):
        self.vars = vars
        self.formula = formula

    def evaluate(self, assignment: Dict[str, bool]) -> bool:
        for combo in itertools.product([True, False], repeat=len(self.vars)):
            extended = dict(assignment)
            for var, val in zip(self.vars, combo):
                extended[var] = val
            if self.formula.evaluate(extended):
                return True
        return False

    def variables(self) -> Set[str]:
        return set(self.vars) | self.formula.variables()

    def __repr__(self) -> str:
        return f"Exists {self.vars}. ({self.formula!r})"


# --------------------------------------------------------------------------- #
#  Parseur a precedentices (limite declaree : pas de parentheses)             #
# --------------------------------------------------------------------------- #


def parse_formula(s: str) -> QBFFormula:
    """Parse une formule propositionnelle en chaine.

    Operateurs : ``!`` (negation), ``&`` (conjonction), ``|`` (disjonction),
    ``=>`` (implication). Precedences ``! > & > | > =>`` (l'implication est
    la plus faible, associative a droite).

    **Limite declaree, heritee de la source** : pas de parentheses. Les
    formules doivent rester simples ; le carnet montre le piege de lecture
    que cette limite fabrique (``a & b | c`` se lit ``(a & b) | c``).
    """
    s = s.strip()
    # Implication : la plus faible, coupee une fois (associative a droite).
    if "=>" in s:
        parts = s.split("=>", 1)
        return Implies(parse_formula(parts[0]), parse_formula(parts[1]))
    # Disjonction.
    if "|" in s:
        parts = s.split("|")
        result = parse_formula(parts[0])
        for p in parts[1:]:
            result = Or(result, parse_formula(p))
        return result
    # Conjonction.
    if "&" in s:
        parts = s.split("&")
        result = parse_formula(parts[0])
        for p in parts[1:]:
            result = And(result, parse_formula(p))
        return result
    # Negation.
    if s.startswith("!"):
        return Not(parse_formula(s[1:]))
    # Variable.
    return Var(s.strip())


# --------------------------------------------------------------------------- #
#  Solveur QBF par enumeration naive                                          #
# --------------------------------------------------------------------------- #


def check_qbf(
    quantifiers: List[Dict[str, Any]],
    formula_str: str,
) -> Tuple[bool, str]:
    """Verifie la validite d'une QBF par enumeration naive.

    Parameters
    ----------
    quantifiers :
        Liste de ``{"type": "forall" | "exists", "vars": ["x", "y"]}``,
        la plus EXTERNE d'abord (l'ordre de la liste est l'ordre de lecture
        de gauche a droite de la formule quantifiee).
    formula_str :
        La matrice propositionnelle (chaine, sans parentheses).

    Retourne ``(est_valide, message)``.
    """
    matrix = parse_formula(formula_str)
    # Imbrication depuis la matrice : le DERNIER quantifier de la liste
    # entoure la matrice, les precedents emballent le tout -- d'ou le
    # reversed, qui fait du premier element la plus grande enveloppe.
    formula = matrix
    for q in reversed(quantifiers):
        q_type = q.get("type", "forall")
        q_vars = q.get("vars", [])
        if q_type == "exists":
            formula = Exists(q_vars, formula)
        else:
            formula = ForAll(q_vars, formula)

    result = formula.evaluate({})
    return result, f"QBF {'VALID' if result else 'INVALID'}: {formula_str}"


def analyze_qbf(
    quantifiers: List[Dict[str, Any]],
    formula_str: str,
) -> Dict[str, Any]:
    """Analyse QBF complete avec statistiques de cout.

    Le champ ``statistics["search_space"] = 2 ** len(variables)`` rend
    visible le prix de l'enumeration naive : c'est le nombre de feuilles
    que parcourt l'evaluation complete dans le pire cas.
    """
    is_valid, message = check_qbf(quantifiers, formula_str)
    all_vars: List[str] = []
    for q in quantifiers:
        all_vars.extend(q.get("vars", []))
    return {
        "formula": formula_str,
        "quantifiers": quantifiers,
        "valid": is_valid,
        "message": message,
        "statistics": {
            "quantifier_count": len(quantifiers),
            "variable_count": len(all_vars),
            "search_space": 2 ** len(all_vars),
            "handler": "ict.qbf",
            "reasoner": "naive_enumeration",
        },
    }


# --------------------------------------------------------------------------- #
#  Acceptabilite argumentative via l'organe Dung                              #
# --------------------------------------------------------------------------- #


def credulous_acceptance_qbf(
    arguments: List[str],
    attacks: List[List[str]],
    target: str,
) -> Dict[str, Any]:
    """L'argument ``target`` est-il CREDULEMENT accepte ?

    Creativement accepte ssi IL EXISTE une extension admissible le contenant
    -- le quantificateur existentiel de la question est matérialisé par
    l'enumeration des sous-ensembles : la recherche d'un temoin EST le
    quantificateur, c'est l'objet de la lecon du carnet.

    Enumeration par masques binaires croissants (2**n), borne ``n <= 15``
    au-dela de laquelle l'organe refuse de mesurer (``accepted=None``).
    Le temoin retourne est le PREMIER trouve : deterministe.
    """
    if target not in arguments:
        return {
            "target": target,
            "accepted": False,
            "reason": f"Argument '{target}' not in framework",
            "method": "credulous_qbf",
        }

    # Index inverse des attaquants (noms -> ensemble d'attaquants).
    attacked_by: Dict[str, Set[str]] = {a: set() for a in arguments}
    for atk in attacks:
        if len(atk) >= 2 and atk[1] in attacked_by:
            attacked_by[atk[1]].add(atk[0])

    n = len(arguments)
    if n > 15:
        return {
            "target": target,
            "accepted": None,
            "reason": f"Framework too large ({n} args) for naive enumeration",
            "method": "credulous_qbf",
        }

    for bits in range(1 << n):
        ext = {arguments[i] for i in range(n) if bits & (1 << i)}
        if target not in ext:
            continue
        # Sans conflit.
        conflict_free = True
        for atk in attacks:
            if len(atk) >= 2 and atk[0] in ext and atk[1] in ext:
                conflict_free = False
                break
        if not conflict_free:
            continue
        # Admissible : tout attaquant exterieur d'un membre est contre-attaque.
        admissible = True
        for member in ext:
            for attacker in attacked_by.get(member, set()):
                if attacker not in ext:
                    counter_attacked = any(
                        a[0] in ext and a[1] == attacker
                        for a in attacks
                        if len(a) >= 2
                    )
                    if not counter_attacked:
                        admissible = False
                        break
            if not admissible:
                break
        if admissible:
            return {
                "target": target,
                "accepted": True,
                "witness_extension": sorted(ext),
                "reason": f"Found admissible extension containing {target}",
                "method": "credulous_qbf",
            }

    return {
        "target": target,
        "accepted": False,
        "reason": f"No admissible extension contains {target}",
        "method": "credulous_qbf",
    }


def skeptical_acceptance_qbf(
    arguments: List[str],
    attacks: List[List[str]],
    target: str,
) -> Dict[str, Any]:
    """L'argument ``target`` est-il SCEPTIQUEMENT accepte ?

    Sceptiquement accepte ssi ``target`` est dans TOUTES les extensions
    preferees -- le quantificateur universel de la question, matérialisé
    par l'enumeration des extensions preferees de l'organe natif
    :func:`ict.argumentation.preferred_extensions`.

    Divergence declaree (voir docstring module) : la source deleguait a
    ``dung_native`` ; le port consomme l'organe de la serie, mapping
    noms -> indices a la frontiere. Refus uniformise : cadre trop grand ->
    ``accepted=None`` avec la raison, cote credule comme cote sceptique.
    """
    if target not in arguments:
        return {
            "target": target,
            "accepted": False,
            "reason": f"Argument '{target}' not in framework",
            "method": "skeptical_qbf",
        }

    index = {name: i for i, name in enumerate(arguments)}
    af = DungAF(
        [index[a] for a in arguments],
        [
            (index[atk[0]], index[atk[1]])
            for atk in attacks
            if len(atk) >= 2 and atk[0] in index and atk[1] in index
        ],
    )
    try:
        preferred = preferred_extensions(af)
    except ValueError as exc:
        return {
            "target": target,
            "accepted": None,
            "reason": str(exc),
            "method": "skeptical_qbf",
        }
    if not preferred:
        return {
            "target": target,
            "accepted": False,
            "reason": "No preferred extensions found",
            "method": "skeptical_qbf",
        }
    inverse = {i: name for name, i in index.items()}
    in_all = all(target in {inverse[i] for i in ext} for ext in preferred)
    return {
        "target": target,
        "accepted": in_all,
        "preferred_extensions": [sorted(inverse[i] for i in ext) for ext in preferred],
        "reason": (
            f"{target} is in ALL {len(preferred)} preferred extensions"
            if in_all
            else f"{target} is NOT in all preferred extensions"
        ),
        "method": "skeptical_qbf",
    }


# --------------------------------------------------------------------------- #
#  Exemples canoniques (references de la source, figes par les tests)         #
# --------------------------------------------------------------------------- #


def example_simple_validity():
    """``forall x. (x | !x)`` -- toujours valide (tautologie)."""
    return analyze_qbf(
        [{"type": "forall", "vars": ["x"]}],
        "x | !x",
    )


def example_simple_satisfiability():
    """``exists x. (x & !x)`` -- jamais satisfiable (contradiction)."""
    return analyze_qbf(
        [{"type": "exists", "vars": ["x"]}],
        "x & !x",
    )


def example_mixed_quantifiers():
    """``forall x. exists y. (x => y)`` -- valide : pour tout x, choisir y=Vrai."""
    return analyze_qbf(
        [
            {"type": "forall", "vars": ["x"]},
            {"type": "exists", "vars": ["y"]},
        ],
        "x => y",
    )


def example_argumentation_acceptance():
    """Acceptabilite credule dans le Nixon diamond."""
    return credulous_acceptance_qbf(
        arguments=["a", "b", "c"],
        attacks=[["a", "b"], ["b", "a"]],
        target="a",
    )
