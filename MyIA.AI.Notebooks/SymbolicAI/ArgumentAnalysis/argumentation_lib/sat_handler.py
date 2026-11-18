"""Enveloppe SAT de l'argumentation propositionnelle (organe manquant).

Pourquoi ce fichier existe
-------------------------
`argumentation_lib/_pl_handler.py` (port verbatim EPITA) **documente** un chemin
SAT pour l'entailment propositionnel et l'appelle effectivement :

    def pl_query_sat(self, knowledge_base_str, query_formula_str) -> bool:
        ...
        handler = self._get_sat_handler()
        return handler.query(normalized_kb, normalized_query, settings.pysat_solver)

    def _get_sat_handler(self):
        from .sat_handler import SATHandler      # <-- ce module

Or `argumentation_lib/sat_handler.py` **n'existait pas** dans l'arbre : le chemin
SAT etait donc du code mort. Consequence mesuree (#23120) : tout appel PL
retombait sur `pl_query_tweety`, c'est-a-dire l'enumeration de modeles du
reasoner Tweety (`SimplePlReasoner.query`), qui marche en 2^n. Sur le contenu
reel produit par le carnet `Argumentation-08b-Executor-Python.ipynb`
(14 phrases en langage naturel -> ~200 "atomes" apres normalisation), cela
donne un `java.lang.OutOfMemoryError: Java heap space` au lieu d'un verdict.

Ce module fournit l'organe natif manquant : l'encodeur Tseitin (PL -> CNF) et
l'entailment par satisfiabilite (base et negation de la requete insolubles).

Deux remedes, tous deux ici
--------------------------
1. **Refus a la frontiere.** Une formule propositionnelle est une suite de
   propositions et d'operateurs. Une phrase en langage naturel n'en est pas
   une : la tokeniser mot a mot (ce que fait `_normalize_formula`) transforme
   une phrase en dizaines d'atomes et l'enumeration en 2^200. Ici, une entree
   non propositionnelle est **refusee** (`PLFormulaError`), jamais atomisee en
   silence. Le refus est le comportement correct : la question mal posee doit
   etre signalee, pas absorbee par un solveur.

2. **Chemin SAT effectif.** L'entailment passe par PySAT (Tseitin -> CNF ->
   solveur), pas par l'enumeration de modeles. Le cout est lineaire en la
   taille de la formule au lieu de 2^n.

Organe natif et reutilisation (regle "organ-first")
---------------------------------------------------
Le moteur de resolution est celui **du depot** :
`MyIA.AI.Notebooks/SymbolicAI/ext_tools/sat_solver.py` expose `solve_sat(clauses,
solver_name)` (meme famille de backends PySAT que ce module utilise :
cadical195 par defaut). Ce module l'invoque via `importlib` (le dossier
`ext_tools/` n'est pas un package) et retombe sur PySAT direct si le fichier
n'est pas resolvable. Aucune seconde implementation de solveur n'est introduite.

Ce que ce module ne fait pas
-----------------------------
Il ne cable pas la phase formelle du carnet 08b : le raccordement du runner
appartient a la PR #23040 (lane `myia-ai-01:CoursIA-2`), qui touche
`_runner.py`, `_pl_reasoner.py` et `_pl_verdict.py`. Ce module est l'organe que
ce raccordement pourra appeler ; il ne modifie aucun de ces fichiers.

Note de provenance : ce module n'est **pas** un port verbatim EPITA (contraire
a `_pl_handler.py`) ; c'est une piece de shim ecrite pour le CoursIA, au meme
titre que `_config.py` ou `_paths.py`.
"""

from __future__ import annotations

import importlib.util
import logging
import os
import re
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

logger = logging.getLogger(__name__)

#: PySAT est-il importable ? C'est le drapeau que `_pl_handler._sat_available`
#: lit pour decider si le chemin SAT peut etre pris. Sans lui,
#: `sat_handler.PYSAT_AVAILABLE` levait `AttributeError`, avalie par le
#: `except` du caller, et le chemin SAT restait du code mort (reserve #23449).
try:
    import pysat  # noqa: F401

    PYSAT_AVAILABLE = True
except Exception:  # pragma: no cover - dependance d'environnement
    PYSAT_AVAILABLE = False

__all__ = [
    "PLFormulaError",
    "PYSAT_AVAILABLE",
    "SATHandler",
    "SATPLEngine",
    "entails",
    "verdict",
    "parse_pl_formula",
]


# ---------------------------------------------------------------------------
# 1. Lexer / parseur propositionnel strict
# ---------------------------------------------------------------------------

#: Operateurs acceptes, du plus prioritaire au moins prioritaire.
_OPERATOR_TOKENS = (
    "<->",
    "<=>",
    "↔",
    "->",
    "=>",
    "→",
    "&&",
    "||",
    "¬",
    "&",
    "|",
    ")",
    "(",
    "!",
    "~",
    "^",
)

#: Mots-cles operateurs (formes textuelles).
_KEYWORD_OPERATORS = {
    "iff": "<->",
    "implies": "->",
    "and": "&&",
    "or": "||",
    "not": "!",
    "xor": "^",
    "true": "true",
    "false": "false",
}

_TOKEN_RE = re.compile(
    r"""
    (?P<space>\s+)
  | (?P<op><->|<=>|↔|->|=>|→|&&|\|\||[&|!~^()¬])
  | (?P<ident>[A-Za-z_][A-Za-z0-9_]*)
    """,
    re.VERBOSE,
)


class PLFormulaError(ValueError):
    """Entree non propositionnelle, ou formule malformee.

    Levée à la frontière : mieux vaut un refus explicite qu'une atomisation
    silencieuse d'une phrase en langage naturel (cf. module docstring).
    """


@dataclass(frozen=True)
class _Atom:
    name: str


@dataclass(frozen=True)
class _Not:
    child: object


@dataclass(frozen=True)
class _BinOp:
    op: str
    left: object
    right: object


@dataclass
class _Token:
    kind: str  # "op" | "ident" | "end"
    value: str
    position: int


def _tokenize(text: str) -> List[_Token]:
    """Tokenise une formule propositionnelle.

    Le texte est balaye integralement : un caractere qui n'appartient ni a un
    operateur ni a un identifiant (ponctuation, accent, apostrophe...) est
    signale, ce qui suffit a rejeter une phrase en langage naturel.
    """
    if not isinstance(text, str):
        raise PLFormulaError(f"Formule non textuelle : {type(text).__name__}")

    tokens: List[_Token] = []
    position = 0
    length = len(text)
    while position < length:
        match = _TOKEN_RE.match(text, position)
        if match is None:
            snippet = text[position : position + 20]
            raise PLFormulaError(
                f"Caractere invalide en position {position} : {snippet!r}. "
                "Une formule propositionnelle n'accepte que des propositions, "
                "des operateurs (& | ! -> <-> ^ et leurs variantes) et des "
                "parentheses."
            )
        position = match.end()
        if match.lastgroup == "space":
            continue
        if match.lastgroup == "op":
            tokens.append(_Token("op", match.group(), match.start()))
        else:
            tokens.append(_Token("ident", match.group(), match.start()))

    tokens.append(_Token("end", "", length))
    return tokens


class _Parser:
    """Analyse descendante recursive sur la precedence logique usuelle."""

    def __init__(self, text: str) -> None:
        self._text = text
        self._tokens = _tokenize(text)
        self._index = 0

    # -- helpers ------------------------------------------------------------

    @property
    def _current(self) -> _Token:
        return self._tokens[self._index]

    def _peek(self) -> _Token:
        return self._tokens[self._index]

    def _advance(self) -> _Token:
        token = self._tokens[self._index]
        self._index += 1
        return token

    def _match_keyword(self, *names: str) -> Optional[str]:
        token = self._peek()
        if token.kind != "ident":
            return None
        lowered = token.value.lower()
        for name in names:
            if lowered == name:
                self._advance()
                return _KEYWORD_OPERATORS[name]
        return None

    def _match_op(self, *values: str) -> Optional[str]:
        token = self._peek()
        if token.kind == "op" and token.value in values:
            self._advance()
            return token.value
        return None

    # -- grammar ------------------------------------------------------------

    def parse(self) -> object:
        if self._current.kind == "end":
            raise PLFormulaError("Formule vide.")
        node = self._parse_biconditional()
        if self._current.kind != "end":
            raise PLFormulaError(
                f"Formule malformee : jeton inattendu {self._current.value!r} "
                f"en position {self._current.position}."
            )
        return node

    def _parse_biconditional(self) -> object:
        node = self._parse_implication()
        while True:
            operator = self._match_op("<->", "<=>", "↔") or self._match_keyword("iff")
            if not operator:
                return node
            right = self._parse_implication()
            node = _BinOp("<->", node, right)

    def _parse_implication(self) -> object:
        node = self._parse_disjunction()
        while True:
            operator = self._match_op("->", "=>", "→") or self._match_keyword("implies")
            if not operator:
                return node
            right = self._parse_disjunction()
            node = _BinOp("->", node, right)

    def _parse_disjunction(self) -> object:
        node = self._parse_conjunction()
        while True:
            operator = self._match_op("||", "|") or self._match_keyword("or")
            if not operator:
                return node
            right = self._parse_conjunction()
            node = _BinOp("|", node, right)

    def _parse_conjunction(self) -> object:
        node = self._parse_exclusive_or()
        while True:
            operator = self._match_op("&&", "&") or self._match_keyword("and")
            if not operator:
                return node
            right = self._parse_exclusive_or()
            node = _BinOp("&", node, right)

    def _parse_exclusive_or(self) -> object:
        node = self._parse_unary()
        while True:
            operator = self._match_op("^") or self._match_keyword("xor")
            if not operator:
                return node
            right = self._parse_unary()
            node = _BinOp("^", node, right)

    def _parse_unary(self) -> object:
        operator = self._match_op("!", "~", "¬") or self._match_keyword("not")
        if operator:
            return _Not(self._parse_unary())
        return self._parse_primary()

    def _parse_primary(self) -> object:
        if self._match_op("("):
            node = self._parse_biconditional()
            if not self._match_op(")"):
                raise PLFormulaError(
                    "Parenthese fermante manquante dans la formule."
                )
            return node

        token = self._advance()
        if token.kind == "ident":
            lowered = token.value.lower()
            if lowered == "true":
                return _Atom("true")
            if lowered == "false":
                return _Atom("false")
            return _Atom(token.value)
        if token.kind == "end":
            raise PLFormulaError("Formule incomplete : operateur sans operande.")
        raise PLFormulaError(
            f"Operateur inattendu {token.value!r} en position {token.position}."
        )


def parse_pl_formula(text: str) -> object:
    """Analyse une formule propositionnelle et renvoie son arbre.

    Lève `PLFormulaError` si l'entree n'est pas une formule propositionnelle
    (phrase en langage naturel, litteral markdown, formule tronquee...).
    """
    return _Parser(text).parse()


# ---------------------------------------------------------------------------
# 2. Encodeur de Tseitin (PL -> CNF)
# ---------------------------------------------------------------------------


@dataclass
class _Encoder:
    """Encodeur de Tseitin : chaque sous-formule recoit une variable.

    Le lien "variable <-> formule" est bilateral : la variable est definie
    comme equivalente a la formule (clauses de definition), ce qui permet
    d'utiliser la variable d'une formule comme litteral dans une clause.

    Cas particulier de l'atome : une proposition `p` est elle-meme une
    variable du probleme CNF ; elle ne recoit **aucune** clause de definition
    (l'imposer, meme a true, reviendrait a fixer la proposition plutot qu'a la
    decrire).
    """

    clauses: List[List[int]] = field(default_factory=list)
    atom_vars: Dict[str, int] = field(default_factory=dict)
    _next_var: int = 1

    def new_var(self) -> int:
        var = self._next_var
        self._next_var += 1
        return var

    def atom_var(self, name: str) -> int:
        if name not in self.atom_vars:
            self.atom_vars[name] = self.new_var()
        return self.atom_vars[name]

    def assert_formula(self, node: object) -> int:
        """Encode une formule et l'**impose** (clause unitaire).

        Une formule de la base de connaissances est une assertion : elle doit
        etre vraie dans tout modele qui satisfait la base. Pour un atome, la
        variable du probleme CNF *est* la proposition : l'imposer revient
        exactement a affirmer la proposition.
        """
        var = self.encode(node)
        self.clauses.append([var])
        return var

    def encode(self, node: object) -> int:
        if isinstance(node, _Atom):
            return self.atom_var(node.name)

        if isinstance(node, _Not):
            child = self.encode(node.child)
            return self.negation(child)

        if isinstance(node, _BinOp):
            left = self.encode(node.left)
            right = self.encode(node.right)
            operator = node.op
            if operator == "&":
                return self.conjunction(left, right)
            if operator == "|":
                return self.disjunction(left, right)
            if operator == "->":
                return self.implication(left, right)
            if operator == "<->":
                # (left -> right) & (right -> left)
                forward = self.implication(left, right)
                backward = self.implication(right, left)
                return self.conjunction(forward, backward)
            if operator == "^":
                # (left & !right) | (!left & right)
                first = self.conjunction(left, self.negation(right))
                second = self.conjunction(self.negation(left), right)
                return self.disjunction(first, second)
            raise PLFormulaError(f"Operateur non encode : {operator!r}")

        raise PLFormulaError(f"Noeud non encode : {node!r}")

    # -- combinateurs CNF (une variable par connecteur, clauses de definition bilaterales) -------

    def negation(self, child: int) -> int:
        """Variable `v` telle que `v <-> !child`."""
        var = self.new_var()
        self.clauses.append([-var, -child])  # v -> !child
        self.clauses.append([child, var])  # !child -> v
        return var

    def conjunction(self, left: int, right: int) -> int:
        """Variable `v` telle que `v <-> (left & right)`."""
        var = self.new_var()
        self.clauses.append([-var, left])  # v -> left
        self.clauses.append([-var, right])  # v -> right
        self.clauses.append([-left, -right, var])  # (left & right) -> v
        return var

    def disjunction(self, left: int, right: int) -> int:
        """Variable `v` telle que `v <-> (left | right)`."""
        var = self.new_var()
        self.clauses.append([-var, left, right])  # v -> (left | right)
        self.clauses.append([-left, var])  # left -> v
        self.clauses.append([-right, var])  # right -> v
        return var

    def implication(self, left: int, right: int) -> int:
        """Variable `v` telle que `v <-> (!left | right)`."""
        var = self.new_var()
        self.clauses.append([-var, -left, right])  # v -> (!left | right)
        # (!left | right) -> v  <=>  (left & !right) -> v : la distribution
        # d'un `&` sous un `|` donne DEUX clauses, pas une (une seule clause
        # `left | !right | v` serait strictement plus faible et briserait
        # l'equivalence v <-> (!left | right)).
        self.clauses.append([left, var])  # left & !right -> v  (1/2)
        self.clauses.append([-right, var])  # left & !right -> v  (2/2)
        return var


# ---------------------------------------------------------------------------
# 3. Moteur de resolution
# ---------------------------------------------------------------------------

#: Chemin relatif de l'organe SAT du depot, depuis ce fichier.
_REPO_SAT_ORGAN = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    os.pardir,
    os.pardir,
    "ext_tools",
    "sat_solver.py",
)


def _load_repo_sat_organ():
    """Charge l'organe SAT du depot (`ext_tools/sat_solver.py`).

    Le dossier `ext_tools/` n'est pas un package : le chargement se fait par
    chemin. Retourne None si le fichier n'est pas resoluble (le module
    retombe alors sur PySAT direct, avec un avertissement).
    """
    path = os.path.normpath(_REPO_SAT_ORGAN)
    if not os.path.isfile(path):
        logger.warning(
            "Organe SAT du depot introuvable (%s) ; repli sur PySAT direct.", path
        )
        return None
    try:
        spec = importlib.util.spec_from_file_location("_coursia_ext_tools_sat", path)
        if spec is None or spec.loader is None:
            return None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        if not getattr(module, "PYSAT_AVAILABLE", False):
            logger.warning("L'organe SAT du depot n'a pas PySAT ; repli direct.")
            return None
        return module
    except Exception as exc:  # pragma: no cover - dependance d'environnement
        logger.warning(
            "Chargement de l'organe SAT du depot impossible (%s) ; repli sur PySAT direct.",
            exc,
        )
        return None


def _solve_with_pysat(clauses: Sequence[Sequence[int]], solver_name: str):
    """Resolution directe via PySAT (repli de l'organe du depot)."""
    from pysat.solvers import Solver

    with Solver(name=solver_name, bootstrap_with=[list(c) for c in clauses]) as solver:
        if solver.solve():
            return True, solver.get_model(), {"solver": solver_name, "status": "SAT"}
        return False, None, {"solver": solver_name, "status": "UNSAT"}


class SATHandler:
    """Entailment propositionnel par satisfiabilite (PySAT / Tseitin).

    API compatible avec l'appel attendu par `_pl_handler.py` :
      - ``solve_formulas(formules, solver_name) -> (is_sat, named_model, stats)``
      - ``query(kb_formulas, query_formula, solver_name) -> bool``
    """

    def __init__(self, default_solver: str = "cadical195") -> None:
        self.default_solver = default_solver
        self._organ = _load_repo_sat_organ()

    # -- bas niveau ---------------------------------------------------------

    def _solve(
        self, clauses: Sequence[Sequence[int]], solver_name: Optional[str]
    ) -> Tuple[bool, Optional[List[int]], dict]:
        name = solver_name or self.default_solver
        if self._organ is not None:
            is_sat, model, stats = self._organ.solve_sat(
                [list(c) for c in clauses], solver_name=name
            )
            return bool(is_sat), model, stats
        return _solve_with_pysat(clauses, name)

    @staticmethod
    def _named_model(
        model: Optional[Iterable[int]], atom_vars: Dict[str, int]
    ) -> Dict[str, bool]:
        """Traduit un modele PySAT en modele nomme (proposition -> booleen)."""
        if model is None:
            return {}
        assignment = {literal for literal in model}
        named: Dict[str, bool] = {}
        for name, var in atom_vars.items():
            named[name] = var in assignment
        return named

    # -- API publique -------------------------------------------------------

    def solve_formulas(
        self,
        formulas: Sequence[str],
        solver_name: Optional[str] = None,
    ) -> Tuple[bool, Optional[Dict[str, bool]], dict]:
        """Satisfiabilite d'une base de connaissances propositionnelle.

        Retourne ``(is_satisfiable, modele_nomme_ou_None, statistiques)``.
        Une formule non propositionnelle leve `PLFormulaError` : la base est
        refusee, jamais degradee.
        """
        encoder = _Encoder()
        formulas = list(formulas)
        for formula in formulas:
            encoder.assert_formula(parse_pl_formula(formula))
        is_sat, model, stats = self._solve(encoder.clauses, solver_name)
        named = self._named_model(model, encoder.atom_vars) if is_sat else None
        stats = dict(stats)
        stats["num_formulas"] = len(formulas)
        stats["num_atoms"] = len(encoder.atom_vars)
        return bool(is_sat), named, stats

    def query(
        self,
        kb_formulas: Sequence[str],
        query_formula: str,
        solver_name: Optional[str] = None,
    ) -> bool:
        """Entailment : la base de connaissances entail-t-elle la requete ?

        La base et la negation de la requete sontposees ensemble ; si cet
        ensemble est insoluble, la requete est entailee.
        """
        encoder = _Encoder()
        for formula in kb_formulas:
            encoder.assert_formula(parse_pl_formula(formula))
        encoder.assert_formula(_Not(parse_pl_formula(query_formula)))

        is_sat, _model, _stats = self._solve(encoder.clauses, solver_name)
        return not is_sat


class SATPLEngine:
    """Moteur propositionnel **drop-in** pour `PLReasonerPlugin` (#23040).

    #23040 (lane `myia-ai-01:CoursIA-2`) introduit une couture propre : le
    plugin `PLReasonerPlugin` porte le *contrat* (format du verdict,
    enregistrement dans le registre) et le *moteur* est injectable via le
    parametre `engine`. Le moteur de reference est `TweetyPLEngine`, dont la
    methode `entails(formulas, query) -> bool` est le point d'appel.

    Cette classe expose **exactement** ce contrat, avec un moteur different :
    l'entailment par satisfiabilite (encodeur de Tseitin + solveur CNF du
    depot `ext_tools/sat_solver.py`).

    Pourquoi un second moteur est utile (mesure #23120) :
      - `SimplePlReasoner` de Tweety **enumere les modeles** : le cout est
        2^n sur un belief set de taille n. C'est la cause mesuree du
        `OutOfMemoryError` du carnet 08b ;
      - l'entailment par satisfiabilite est **lineaire** en la taille de la
        formule (une seule instance de solveur, une seule lecture de
        formule) ;
      - aucune JVM n'est requise : le verdict ne depend pas du classpath
        Tweety.

    Ce moteur ne remplace pas Tweety : il est **injectable** a la demande.
    Le choix de l'un ou l'autre reste une decision de la lane qui cable la
    phase formelle (cf. `argumentation_lib/_runner.py`).
    """

    name = "coursia-sat-pl-engine"

    def __init__(self, default_solver: str = "cadical195") -> None:
        self._handler = SATHandler(default_solver=default_solver)

    def entails(self, formulas: Sequence[str], query: str) -> bool:
        """Vrai si le belief set entail la requete (decide par le solveur).

        Contrat identique a `TweetyPLEngine.entails` : leve `PLFormulaError`
        si une formule du belief set n'est pas propositionnelle (refus
        explicite, jamais d'atomisation silencieuse).
        """
        return self._handler.query(list(formulas), query)


# ---------------------------------------------------------------------------
# 4. Raccourcis de module
# ---------------------------------------------------------------------------


def entails(kb_formulas: Sequence[str], query_formula: str) -> bool:
    """Entailment propositionnel (raccourci fonctionnel)."""
    return SATHandler().query(kb_formulas, query_formula)


def verdict(kb_formulas: Sequence[str], query_formula: str) -> str:
    """Verdict textuel de l'entailment : ``ACCEPTED`` ou ``REJECTED``.

    Les deux chaines sont celles que la chaine de verification du carnet 08b
    recherche (cf. `argumentation_lib/_tweety_bridge.py`).
    """
    return "ACCEPTED" if entails(kb_formulas, query_formula) else "REJECTED"
