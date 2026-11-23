"""Combinateurs S/K/I et systeme de tag de Post -- organe du pli 4 de l'EPIC Origami
Wolfram (#19742, issue #25061).

Outille la brique « representation ultime du calcul » du pli 4 : la logique
combinatoire de Schonfinkel (1920) et Curry (1927-1930), ou deux regles
suffisent -- ``S f g x = f x (g x)`` et ``K x y = x`` (``I x = x`` etant
derivable : ``S K K x = K x (K x) = x``) -- pour representer tout calcul
(Church 1935 : equivalence avec le lambda-calcul ; Turing 1936 : equivalence
avec les machines).

Deux instruments vivent ici :

* **Termes S/K/I** : representation en arbre binaire d'application, reduction
  en ordre normal (gauche-exterieur, qui trouve la forme normale quand elle
  existe -- confluence de Church-Rosser et theoreme de standardisation) ou en
  ordre applicatif (qui peut diverger sur un terme qui en a une), abstraction
  de bracket (lambda -> SKI) et entiers de Church. C'est le banc de
  « la representation abstraite du calcul lui-meme » (Wolfram 2020, section
  *The Abstract Representation of Things*).
* **Systeme de tag de Post (1921)** : chaines sur {0,1}, suppression de
  ``nu`` elements en tete a chaque pas, regles ``0 -> 00``, ``1 -> 1101``
  avec ``nu = 3``. Le probleme de Post -- ce systeme s'arrete-t-il (chaine
  plus courte que ``nu``), cycle-t-il ou croit-il sans borne pour TOUTE
  chaine initiale ? -- est ouvert depuis un siecle. Minsky (1961) a prouve
  que les systemes de tag convenablement construits sont universels ; le cas
  particulier de Post, lui, resiste : c'est la borne empirique
  d'irreductibilite du geste symbolique que le carnet ICT-51 mesure.

**Source primaire** : Wolfram, S. (2020) « Combinators: A Centennial View »,
writings.stephenwolfram.com (sections *The Abstract Representation of Things*,
*Combinators Arrive*, *Lambda Calculus*) ; Wolfram, S. (2021) « After 100
Years, Can We Finally Crack Post's Problem of Tag? » (systeme 00/1101,
``nu = 3``, blocs inatteignables). Reception critique : Curry, Hindley &
Seldin (1972) ; Cardone & Hindley (2006/2009) ; Bimbo (2009, SEP) ; Klop,
van Oostrom & van Raamsdonk (1993) -- references relevees dans la copie
archivee de Wolfram (2021), « A Bibliography of Combinators » (arXiv
2106.11729). Aucune publication n'entre dans le depot.

**Provenance dans le depot** : organe neuf du pli 4 (issue #25061), meme
forme que ``ict.wolfram_step`` (pli 2, PR #22201/#22214) : le moteur vit
dans le package ``ict/``, le carnet ICT-51 le consomme sans reimplementer.

**Cadrage epistemologique** : l'organer ne *prouve* pas la confluence (le
pli 4 grain B la confie a l'organe formel Lean -- relations de Mathlib --,
a nommer avant toute reimplementation, cf. regle organ-first) ; il fournit
l'instrument empirique : ordres de reduction aleatoires convergeant vers la
meme forme normale, sensibilite a la strategie (``K I omega`` diverge en
ordre applicatif et termine en ordre normal), croissance des traces du tag
de Post. La these wolframienne -- combinateurs comme « premiere
representation purement abstraite de la computation elle-meme » -- se
confronte au carnet a la reception historique (Hindley, Cardone), pas
seulement en recit.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple, Union

__all__ = [
    "Var",
    "App",
    "S",
    "K",
    "I",
    "parse_ski",
    "to_str",
    "reduce_once",
    "is_normal_form",
    "reduce_term",
    "random_reduce",
    "bracket_abstraction",
    "lam",
    "church",
    "church_to_int",
    "OMEGA",
    "tag_step",
    "tag_evolve",
    "POST_RULES",
    "POST_NU",
    "first_missing_blocks",
]

# ---------------------------------------------------------------------------
# Representation des termes
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Var:
    """Variable libre (affichage seulement : les combinateurs clos n'en ont pas)."""

    name: str


@dataclass(frozen=True)
class App:
    """Application : ``func`` applique a ``arg`` (association a gauche)."""

    func: "Term"
    arg: "Term"


Term = Union[Var, App]

S = Var("S")
K = Var("K")
I = Var("I")

# Le terme omega : S I I (S I I) se reduit en lui-meme -- divergence pure.
OMEGA = App(App(App(S, I), I), App(App(S, I), I))

# Composition et echange, decomposes en S/K (le docstring de parse_ski les
# promet) : B f g x = f (g x) et C f x y = f y x. Les decompositions sont
# les formes closes standard en S/K, verifiees par les tests dedies.
B = App(App(S, App(K, S)), K)
C = App(App(S, App(App(S, App(K, B)), S)), App(K, K))


def parse_ski(text: str) -> Term:
    """Parse une chaine d'applications ``"S K K x"`` (association a gauche).

    Les jetons reconnus : ``S``, ``K``, ``I``, ``B``, ``C`` (combinateurs
    usuels decomposes en S/K), et tout autre identifiant devient une
    :class:`Var` libre. Les parentheses groupent.
    """
    tokens = text.replace("(", " ( ").replace(")", " ) ").split()
    pos = 0

    def parse_expr() -> Term:
        nonlocal pos
        atoms: List[Term] = []
        while pos < len(tokens):
            tok = tokens[pos]
            if tok == "(":
                pos += 1
                atoms.append(parse_expr())
            elif tok == ")":
                break
            else:
                atoms.append(_atom(tok))
            pos += 1
        if not atoms:
            raise ValueError("terme vide")
        term = atoms[0]
        for nxt in atoms[1:]:
            term = App(term, nxt)
        return term

    # analyse principale : parenthese ouvrante = groupe
    def parse_top() -> Term:
        nonlocal pos
        atoms: List[Term] = []
        while pos < len(tokens):
            tok = tokens[pos]
            if tok == "(":
                pos += 1
                atoms.append(parse_expr())
            elif tok == ")":
                raise ValueError("parenthese fermante inattendue")
            else:
                atoms.append(_atom(tok))
            pos += 1
        if not atoms:
            raise ValueError("terme vide")
        term = atoms[0]
        for nxt in atoms[1:]:
            term = App(term, nxt)
        return term

    return parse_top()


def _atom(tok: str) -> Term:
    """Mappe un jeton a son terme ; ``B`` et ``C`` se decomposent en S/K."""
    if tok == "S":
        return S
    if tok == "K":
        return K
    if tok == "I":
        return I
    if tok == "B":
        return B
    if tok == "C":
        return C
    return Var(tok)


def to_str(term: Term) -> str:
    """Affichage parenthese minimal : l'application associe a gauche.

    Seul l'argument de droite prend des parentheses quand il est lui-meme une
    application (``f x (g x)``) ; le foncteur de gauche n'en prend jamais
    (``App(App(f, x), y)`` s'ecrit ``f x y``).
    """
    if isinstance(term, Var):
        return term.name
    left = to_str(term.func)
    right = to_str(term.arg)
    if isinstance(term.arg, App):
        right = "(" + right + ")"
    return f"{left} {right}"


# ---------------------------------------------------------------------------
# Reduction
# ---------------------------------------------------------------------------


def _match_S(term: Term) -> Optional[Tuple[Term, Term, Term]]:
    """S f g x -> renvoie (f, g, x) si le terme est de cette forme reduite."""
    if (
        isinstance(term, App)
        and isinstance(term.func, App)
        and isinstance(term.func.func, App)
        and term.func.func.func == S
    ):
        return term.func.func.arg, term.func.arg, term.arg
    return None


def _match_K(term: Term) -> Optional[Tuple[Term, Term]]:
    if (
        isinstance(term, App)
        and isinstance(term.func, App)
        and term.func.func == K
    ):
        return term.func.arg, term.arg
    return None


def _match_I(term: Term) -> Optional[Term]:
    if isinstance(term, App) and term.func == I:
        return term.arg
    return None


def _redexes(term: Term) -> List[Tuple[Term, ...]]:
    """Decrit le redex racine du terme, s'il existe."""
    m = _match_S(term)
    if m is not None:
        return [("S",) + m]
    m = _match_K(term)
    if m is not None:
        return [("K",) + m]
    m = _match_I(term)
    if m is not None:
        return [("I", m)]
    return []


def is_normal_form(term: Term) -> bool:
    """Vrai si aucun sous-terme n'est un redex S/K/I."""
    return _leftmost_redex(term) is None


def _leftmost_redex(
    term: Term, innermost: bool = False
) -> Optional[Tuple[Term, Tuple[str, int, int]]]:
    """Trouve le redex le plus a gauche (exterieur par defaut, interieur si
    ``innermost``) et renvoie (chemin-en-tuple, (regle, i, j)).

    Implementation simple : reconstruction recursive du terme remplace.
    Renvoie None si le terme est en forme normale.
    """
    redex = _redexes(term)
    if redex and not innermost:
        rule = redex[0][0]
        return term, (rule, 0, 0)
    # descendre dans les sous-termes (gauche d'abord)
    if isinstance(term, App):
        sub = _leftmost_redex(term.func, innermost)
        if sub is not None:
            return sub
        sub = _leftmost_redex(term.arg, innermost)
        if sub is not None:
            return sub
    if redex and innermost:
        rule = redex[0][0]
        return term, (rule, 0, 0)
    return None


def _apply_redex(term: Term) -> Optional[Term]:
    """Un pas de reduction au redex racine ; None si la racine n'est pas un redex."""
    m = _match_S(term)
    if m is not None:
        f, g, x = m
        return App(App(f, x), App(g, x))
    m = _match_K(term)
    if m is not None:
        return m[0]
    m = _match_I(term)
    if m is not None:
        return m
    return None


def reduce_once(term: Term, order: str = "normal") -> Optional[Term]:
    """Un pas de reduction.

    * ``order='normal'`` : redex le plus a gauche, l'exterieur d'abord
      (trouve la forme normale quand elle existe).
    * ``order='applicative'`` : l'interieur d'abord (evalue les arguments ;
      peut diverger sur un terme qui a une forme normale).

    Renvoie le terme reduit, ou ``None`` si deja en forme normale.
    """
    if order not in ("normal", "applicative"):
        raise ValueError("order doit valoir 'normal' ou 'applicative'")
    innermost = order == "applicative"

    def step(t: Term) -> Optional[Term]:
        if not innermost:
            red = _apply_redex(t)
            if red is not None:
                return red
        if isinstance(t, App):
            f = step(t.func)
            if f is not None:
                return App(f, t.arg)
            a = step(t.arg)
            if a is not None:
                return App(t.func, a)
        if innermost:
            return _apply_redex(t)
        return None

    return step(term)


def reduce_term(
    term: Term,
    order: str = "normal",
    max_steps: int = 10000,
    trace: bool = False,
) -> Tuple[Optional[Term], int, Optional[List[Term]]]:
    """Reduit jusqu'a la forme normale ou ``max_steps``.

    Renvoie ``(forme_normale_ou_None, nb_pas, trace_optionnelle)`` ;
    ``None`` en premiere position = divergence (borne atteinte).
    """
    steps = 0
    tr = [term] if trace else None
    current = term
    while steps < max_steps:
        nxt = reduce_once(current, order)
        if nxt is None:
            return current, steps, tr
        current = nxt
        steps += 1
        if tr is not None:
            tr.append(current)
    return None, steps, tr


def random_reduce(
    term: Term, rng, max_steps: int = 10000
) -> Tuple[Optional[Term], int]:
    """Reduction en ordre aleatoire (n'importe quel redex, uniformement).

    Instrument du constat empirique de Church-Rosser : des ordres differents
    convergent vers la meme forme normale (unicite), seuls le nombre de pas
    et l'existence d'un chemin divergent varient.
    """
    steps = 0
    current = term
    while steps < max_steps:
        redexes = _all_redex_paths(current)
        if not redexes:
            return current, steps
        chosen = rng.choice(redexes)
        current = _replace_path(current, chosen)
        steps += 1
    return None, steps


def _all_redex_paths(term: Term, path: Tuple[int, ...] = ()) -> List[Tuple[int, ...]]:
    """Chemins (0=func, 1=arg) de tous les redex du terme."""
    paths: List[Tuple[int, ...]] = []
    if _redexes(term):
        paths.append(path)
    if isinstance(term, App):
        paths.extend(_all_redex_paths(term.func, path + (0,)))
        paths.extend(_all_redex_paths(term.arg, path + (1,)))
    return paths


def _replace_path(term: Term, path: Sequence[int]) -> Term:
    """Reduit le redex situe a ``path`` (construit par ``_all_redex_paths``)."""
    if not path:
        red = _apply_redex(term)
        if red is None:
            raise ValueError("pas de redex a la racine")
        return red
    head, rest = path[0], path[1:]
    if not isinstance(term, App):
        raise ValueError("chemin invalide")
    if head == 0:
        return App(_replace_path(term.func, rest), term.arg)
    return App(term.func, _replace_path(term.arg, rest))


# ---------------------------------------------------------------------------
# Abstraction de bracket : lambda -> SKI
# ---------------------------------------------------------------------------


def lam(var: str, body: Term) -> Term:
    """Traduit ``\\var. body`` en combinateurs S/K/I (abstraction de bracket).

    Schema classique : ``[x.x] = I`` ; ``[x.c] = K c`` (c sans x) ;
    ``[x.(M N)] = S [x.M] [x.N]`` -- avec les deux optimisations de Curry
    quand une composante ne depend pas de x ( ``S (K m) n -> B m n`` n'est
    PAS appliquee : l'organe garde la traduction pure, la croissance du
    terme est justement l'objet de la mesure du carnet).
    """
    return _abstract(var, body)


def _free_vars(term: Term) -> set:
    if isinstance(term, Var):
        return {term.name}
    return _free_vars(term.func) | _free_vars(term.arg)


def _abstract(x: str, term: Term) -> Term:
    fv = _free_vars(term)
    if x not in fv:
        return App(K, term)
    if isinstance(term, Var) and term.name == x:
        return I
    if isinstance(term, App):
        return App(App(S, _abstract(x, term.func)), _abstract(x, term.arg))
    raise ValueError("terme non abstrait de variable libre inattendue")


# ---------------------------------------------------------------------------
# Entiers de Church
# ---------------------------------------------------------------------------


def church(n: int) -> Term:
    """Entier de Church ``n`` en S/K pur : ``\\f x. f^n x`` via bracket."""
    f, x = Var("f"), Var("x")
    body: Term = x
    for _ in range(n):
        body = App(f, body)
    return _abstract("f", _abstract("x", body))


def church_to_int(term: Term, max_steps: int = 100000) -> Optional[int]:
    """Reconvertit un entier de Church en int en l'appliquant au successeur.

    Application concrete du terme abstrait : ``term (+1) 0`` en ordre normal.
    Renvoie None si la reduction diverge ou ne donne pas un entier.
    """
    # application concrete : term applique aux variables libres f et x,
    # la forme normale f (f (... x)) se compte directement
    applied = App(App(term, Var("f")), Var("x"))
    nf, steps, _ = reduce_term(applied, "normal", max_steps)
    if nf is None:
        return None
    return _count_applications(nf)


def _count_applications(term: Term) -> Optional[int]:
    """Compte ``f (f (... x))`` ; renvoie None si la forme n'est pas celle-la."""
    count = 0
    current = term
    while isinstance(current, App) and current.func == Var("f"):
        count += 1
        current = current.arg
    if current == Var("x"):
        return count
    return None


# ---------------------------------------------------------------------------
# Systeme de tag de Post
# ---------------------------------------------------------------------------

#: Regles du systeme de Post (1921) : alphabet {0, 1}, 0 -> 00, 1 -> 1101.
POST_RULES: Dict[str, str] = {"0": "00", "1": "1101"}

#: Nombre d'elements supprimes en tete a chaque pas (nu de Post).
POST_NU: int = 3


def tag_step(string: Sequence[str], rules: Dict[str, str] = POST_RULES, nu: int = POST_NU) -> Optional[List[str]]:
    """Un pas du systeme de tag : supprimer ``nu`` elements en tete, puis
    ajouter en queue le bloc associe au premier element supprime.

    Renvoie ``None`` si le pas n'est pas applicable (chaine plus courte que
    ``nu`` : le systeme est arrete) ou si le premier element supprime n'a pas
    de regle.
    """
    if len(string) < nu:
        return None
    dropped = string[0]
    if dropped not in rules:
        return None
    return list(string[nu:]) + list(rules[dropped])


def tag_evolve(
    string: Sequence[str],
    rules: Dict[str, str] = POST_RULES,
    nu: int = POST_NU,
    max_steps: int = 100000,
) -> Tuple[List[List[str]], str]:
    """Evolution complete : renvoie (trace, verdict).

    Verdicts : ``'halted'`` (chaine < nu), ``'cycle'`` (etat deja vu),
    ``'unbounded'`` (borne de pas atteinte -- ni arret ni cycle constates).
    """
    trace: List[List[str]] = [list(string)]
    seen: Dict[str, int] = {"".join(string): 0}
    current = list(string)
    for step in range(1, max_steps + 1):
        nxt = tag_step(current, rules, nu)
        if nxt is None:
            return trace, "halted"
        key = "".join(nxt)
        if key in seen:
            trace.append(nxt)
            return trace, "cycle"
        seen[key] = step
        current = nxt
        trace.append(nxt)
    return trace, "unbounded"


def first_missing_blocks(trace: Sequence[Sequence[str]], width: int = 4) -> List[str]:
    """Blocs de ``width`` elements qui n'apparaissent JAMAIS dans la trace.

    Instrument du fait mesure par Wolfram (2021, section *The Space of
    Possible States*) : une fois la chaine entierement composee de blocs
    ajoutes (``00`` et ``1101``), ``1111`` est inatteignable -- aucun bloc ne
    porte quatre ``1`` consecutifs et aucun ne se termine par deux ``1``,
    donc aucune jonction ne peut les produire.

    La portee est la **trace observee**, pas le systeme entier : une graine
    arbitraire peut deja porter un ``11`` que la queue d'un bloc vient
    completer (``10011`` donne ``111101`` des le premier pas). Sur les 496
    graines de longueur 4 a 8, 121 atteignent ``1111``.
    """
    seen: set = set()
    for state in trace:
        s = "".join(state)
        for i in range(max(0, len(s) - width + 1)):
            seen.add(s[i : i + width])
    alphabet = sorted({ch for st in trace for ch in st})
    import itertools

    missing = [
        "".join(t)
        for t in itertools.product(alphabet, repeat=width)
        if "".join(t) not in seen
    ]
    return missing
