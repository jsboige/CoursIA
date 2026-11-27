"""path_profile -- variables du chemin de resolution d'une grille (#27214).

Instrument de mesure du protocole scelle
``docs/research/sudoku-frontiere-inference-pre-enregistrement.md`` (section 4).
Le protocole a ete commite avant ce module ; en cas d'ecart entre les deux, le
protocole fait foi et ce module est en defaut.

Ce module ne resout rien par lui-meme. Il rejoue la politique de
``inference_trace.InferenceSolver`` -- a chaque pas, la premiere regle de
``RULE_ORDER`` qui trouve un pas, dans son ordre de balayage -- en gardant
l'etat qui precede chaque pas, et il en deduit les variables de chemin. Le
rejou est compare a ``solve()`` a chaque appel : toute divergence leve
``ReplayDivergence``, jamais une valeur silencieusement fausse.

Un seul oracle (protocole §7.6) : ``dlx_certificates`` n'intervient ici que par
``verify_trace``, qui controle chaque pas contre la solution unique. Aucune
etape d'inference n'en sort.

Micro-choix d'execution. Le protocole ne les fixe pas ; ils le sont ici, avant
le pilote, et ne changent plus ensuite :

- a1 -- rang d'un pas : indice (a partir de 1) de sa regle dans ``RULE_ORDER``
  du solveur rejoue. Il suit donc ``R`` : une regle ajoutee par un lot decale
  les rangs qui la suivent, et toute mesure nomme le commit.
- a2 -- ``support_last`` d'une regle dont les premisses ne nomment pas les
  cases : les cases portant la valeur sont recomptees sur l'etat qui precede le
  pas, dans les unites que citent les premisses (le bloc de ``pointing_pair``,
  la ligne ou la colonne de ``locked_claiming``, les lignes de ``x_wing``).
- a3 -- ``tangle`` : nombre cyclomatique du graphe d'exclusion (protocole
  §4.3, revision v2), sur un graphe simple -- deux candidats partagent au
  plus un lien ; un etat sans candidat n'en a pas et rend ``None``.
- a4 -- une regle inconnue de ce module n'arrete pas le profil : le pas est
  profile (rang, eliminations, etats) et seul son support vaut ``None``.

Usage (pilote du protocole §9) :

    python path_profile.py ../Puzzles/Sudoku_gen_facile.txt
    python path_profile.py ../Puzzles/*.txt --json profils.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from statistics import median
from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple

_SCRIPTS = Path(__file__).resolve().parent
_SUDOKU = _SCRIPTS.parent
for _p in (str(_SUDOKU), str(_SCRIPTS)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from dlx_certificates import solve_certificate  # noqa: E402
from inference_trace import InferenceSolver, Step, Trace, verify_trace  # noqa: E402


# ---------------------------------------------------------------------------
# Etat : les candidats de chacune des 81 cases
# ---------------------------------------------------------------------------

State = Tuple[FrozenSet[int], ...]


def state_of(cands: Sequence[Sequence[int]]) -> State:
    """Etat immuable a partir de ``InferenceSolver.cands``."""
    return tuple(frozenset(cands[r][c]) for r in range(9) for c in range(9))


def _units() -> List[List[Tuple[int, int]]]:
    """Les 27 unites : 9 lignes, 9 colonnes, 9 blocs."""
    units: List[List[Tuple[int, int]]] = []
    units += [[(r, c) for c in range(9)] for r in range(9)]
    units += [[(r, c) for r in range(9)] for c in range(9)]
    units += [[(3 * br + i, 3 * bc + j) for i in range(3) for j in range(3)]
              for br in range(3) for bc in range(3)]
    return units


UNITS = _units()


# ---------------------------------------------------------------------------
# tangle (protocole §4.3)
# ---------------------------------------------------------------------------


Node = Tuple[int, int, int]


def exclusion_graph(state: State) -> Optional[Tuple[int, int, int]]:
    """``(N, E, C)`` du graphe d'exclusion d'un etat : noeuds, liens distincts,
    composantes connexes. ``None`` si l'etat n'a aucun candidat.

    Le graphe a pour noeuds les candidats ``(case, chiffre)`` et pour liens
    les couples qui s'excluent : deux chiffres d'une meme case, ou un meme
    chiffre en deux cases d'une meme unite. Il est simple : deux cases d'une
    meme ligne et d'un meme bloc, par exemple, ont un seul lien pour un
    chiffre donne, bien qu'elles partagent deux unites.
    """
    nodes: List[Node] = []
    for idx, cands in enumerate(state):
        r, c = divmod(idx, 9)
        for v in sorted(cands):
            nodes.append((r, c, v))
    if not nodes:
        return None

    links: Set[Tuple[Node, Node]] = set()

    def link(a: Node, b: Node) -> None:
        links.add((a, b) if a < b else (b, a))

    # Cas : deux chiffres d'une meme case.
    for idx, cands in enumerate(state):
        r, c = divmod(idx, 9)
        vs = sorted(cands)
        for i in range(len(vs)):
            for v in vs[i + 1:]:
                link((r, c, vs[i]), (r, c, v))

    # Unites : un meme chiffre en deux cases d'une meme unite.
    for unit in UNITS:
        for v in range(1, 10):
            spots = [(r, c, v) for (r, c) in unit if v in state[r * 9 + c]]
            for i in range(len(spots)):
                for node in spots[i + 1:]:
                    link(spots[i], node)

    parent = {n: n for n in nodes}

    def find(x: Node) -> Node:
        root = x
        while parent[root] != root:
            root = parent[root]
        while parent[x] != root:
            parent[x], x = root, parent[x]
        return root

    for a, b in links:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    return len(nodes), len(links), len({find(n) for n in nodes})


def tangle(state: State) -> Optional[float]:
    """Nombre cyclomatique du graphe d'exclusion, ``E - N + C``, divise par
    ``N`` (protocole §4.3, revision v2). ``None`` si l'etat n'a aucun candidat.

    Le nombre cyclomatique compte les cycles lineairement independants du
    graphe : il vaut 0 sur une foret et croit avec l'enchevetrement des
    exclusions. La revision v1 mesurait la part de la plus grande composante
    connexe ; elle valait 1 sur chaque etat du pilote (protocole §10.7).
    """
    counts = exclusion_graph(state)
    if counts is None:
        return None
    n_nodes, n_links, n_components = counts
    return (n_links - n_nodes + n_components) / n_nodes


# ---------------------------------------------------------------------------
# support (protocole §4.1) : cases citees par les premisses
# ---------------------------------------------------------------------------

_CELL_RE = re.compile(r"\((\d),(\d)\)")
_POINTING_RE = re.compile(r"^valeur (\d) alignee dans le bloc \((\d),(\d)\)$")
_CLAIMING_RE = re.compile(r"^valeur (\d) de la (ligne|colonne) (\d) confinee au bloc "
                          r"\((\d),(\d)\)$")
_FISH_RE = re.compile(r"^valeur (\d) : lignes ([\d,]+) partagent colonnes \[([\d,\s]+)\]$")

# Regles dont les premisses citent les cases du pas, sans recomptage d'unite.
# Les ailes du lot 4 (#27533) en relevent : pivot et deux pinces y sont nommes,
# au format ``(ligne,colonne)``.
_PREMISE_CELLS = frozenset({
    "naked_single", "hidden_single", "naked_pair", "naked_triple", "naked_quad",
    "hidden_pair", "hidden_triple", "hidden_quad",
    "xy_wing", "xyz_wing",
})


def _measured(count: int) -> Optional[int]:
    """Un recomptage nul n'est pas une mesure : l'etat contredit les premisses."""
    return count if count > 0 else None


def support(rule: str, premises: str, before: State) -> Optional[int]:
    """Nombre de cases sur lesquelles porte un pas (micro-choix a2).

    ``None`` quand le module ne connait pas la regle, quand les premisses ne
    sont plus au format attendu, ou quand le recomptage trouve zero case --
    jamais ``0``, qui se confondrait avec une mesure.
    """
    if rule in _PREMISE_CELLS:
        return _measured(len(set(_CELL_RE.findall(premises))))

    m = _POINTING_RE.match(premises)
    if m and rule == "pointing_pair":
        v, br, bc = int(m.group(1)), int(m.group(2)), int(m.group(3))
        return _measured(sum(1 for i in range(3) for j in range(3)
                             if v in before[(3 * br + i) * 9 + (3 * bc + j)]))

    m = _CLAIMING_RE.match(premises)
    if m and rule == "locked_claiming":
        v, unit_type, idx = int(m.group(1)), m.group(2), int(m.group(3))
        return _measured(sum(1 for other in range(9)
                             if v in before[(idx * 9 + other) if unit_type == "ligne"
                                            else (other * 9 + idx)]))

    m = _FISH_RE.match(premises)
    if m and rule == "x_wing":
        v = int(m.group(1))
        rows = [int(t) for t in m.group(2).split(",")]
        return _measured(sum(1 for r in rows for c in range(9)
                             if v in before[r * 9 + c]))

    return None


# ---------------------------------------------------------------------------
# Rejou de la politique
# ---------------------------------------------------------------------------


class ReplayDivergence(RuntimeError):
    """Le rejou ne reproduit pas ``solve()`` : le profil serait faux."""


@dataclass(frozen=True)
class Pas:
    """Un pas rejoue : sa regle, l'etat qui le precede, l'etape rendue."""

    rule: str
    before: State
    step: Step


@dataclass
class Replay:
    """Le chemin rejoue d'une grille."""

    trace: Trace
    steps: List[Pas] = field(default_factory=list)
    final: State = ()
    final_grid: str = ""


def replay(solver: InferenceSolver, max_steps: int = 10000) -> Replay:
    """Rejoue la politique de ``solver`` sur son etat courant, sans recherche."""
    steps: List[Pas] = []
    stalled = False
    while not solver.is_solved() and len(steps) < max_steps:
        before = state_of(solver.cands)
        found: Optional[Step] = None
        rule = ""
        for rule in solver.RULE_ORDER:
            found = getattr(solver, "_" + rule)()
            if found is not None:
                break
        if found is None:
            stalled = True
            break
        found.index = len(steps)
        steps.append(Pas(rule, before, found))

    trace = Trace(puzzle=solver.puzzle, steps=[p.step for p in steps],
                  solved=solver.is_solved(), stalled=stalled)
    grid = "".join(str(solver.grid[r][c]) for r in range(9) for c in range(9))
    return Replay(trace=trace, steps=steps, final=state_of(solver.cands),
                  final_grid=grid)


def _check_equivalence(replay_result: Replay, puzzle: str) -> None:
    """Le rejou doit produire exactement le chemin de ``solve()``."""
    ref = InferenceSolver(puzzle).solve()
    got = replay_result.trace
    same = (got.solved == ref.solved and got.stalled == ref.stalled
            and [s.rule for s in got.steps] == [s.rule for s in ref.steps]
            and [s.grid_after for s in got.steps] == [s.grid_after for s in ref.steps]
            and [s.eliminations for s in got.steps] == [s.eliminations for s in ref.steps])
    if not same:
        raise ReplayDivergence(
            f"le rejou diverge de solve() sur {puzzle} : "
            f"{len(got.steps)} pas rejoues contre {len(ref.steps)}, "
            f"resolu={got.solved}/{ref.solved}, arrete={got.stalled}/{ref.stalled}")


# ---------------------------------------------------------------------------
# Profil d'une grille
# ---------------------------------------------------------------------------


@dataclass
class Profile:
    """Variables de chemin d'une grille (protocole §4).

    Les champs de §4.1 ne sont renseignes que pour une grille resolue, ceux de
    §4.2 que pour un arret : une variable non definie vaut ``None``.
    """

    puzzle: str
    solved: bool
    trace_accepted: bool
    n_steps: int
    r_max: Optional[int] = None
    pos_r_max: Optional[float] = None
    rank_last: Optional[int] = None
    support_last: Optional[int] = None
    elim_last: Optional[int] = None
    collapse: Optional[int] = None
    tangle_last: Optional[float] = None
    steps_stall: Optional[int] = None
    rank_hist: Optional[Dict[int, int]] = None
    empty_stall: Optional[int] = None
    cands_stall: Optional[int] = None
    tangle_stall: Optional[float] = None

    def to_dict(self) -> Dict:
        out = dict(self.__dict__)
        if out["rank_hist"] is not None:
            out["rank_hist"] = {str(k): v for k, v in sorted(out["rank_hist"].items())}
        return out


def profile_grid(puzzle: str, check_equivalence: bool = True) -> Profile:
    """Profil complet d'une grille, trace verifiee par l'oracle."""
    replayed = replay(InferenceSolver(puzzle))
    if check_equivalence:
        _check_equivalence(replayed, puzzle)

    trace = replayed.trace
    rank_of = {rule: i + 1 for i, rule in enumerate(InferenceSolver.RULE_ORDER)}
    ranks = [rank_of[p.rule] for p in replayed.steps]
    verdict = verify_trace(trace)
    prof = Profile(puzzle=trace.puzzle, solved=trace.solved,
                   trace_accepted=verdict.accepted, n_steps=len(trace.steps))

    if trace.solved:
        prof.r_max = max(ranks) if ranks else None
        if len(ranks) > 1 and prof.r_max is not None:
            prof.pos_r_max = ranks.index(prof.r_max) / (len(ranks) - 1)
        # Geste final : le dernier pas de rang >= 3 (un singleton est de rang 1 ou 2).
        idx_last = next((i for i in range(len(ranks) - 1, -1, -1) if ranks[i] >= 3), None)
        if idx_last is not None:
            pas = replayed.steps[idx_last]
            prof.rank_last = ranks[idx_last]
            prof.support_last = support(pas.rule, pas.step.premises, pas.before)
            prof.elim_last = len(pas.step.eliminations)
            prof.collapse = len(ranks) - 1 - idx_last
            prof.tangle_last = tangle(pas.before)
    else:
        prof.steps_stall = len(ranks)
        prof.rank_hist = dict(sorted(Counter(ranks).items()))
        prof.empty_stall = replayed.final_grid.count("0")
        prof.cands_stall = sum(len(c) for c in replayed.final)
        prof.tangle_stall = tangle(replayed.final)
    return prof


# ---------------------------------------------------------------------------
# Corpus
# ---------------------------------------------------------------------------


@dataclass
class CorpusReport:
    """Profil d'un corpus et comptes d'exclusion (protocole §7.5)."""

    path: str
    sha256: str
    n_grilles: int = 0
    n_lignes_ignorees: int = 0
    n_doublons: int = 0
    n_sans_solution_unique: int = 0
    n_resolues: int = 0
    n_arrets: int = 0
    n_traces_refusees: int = 0
    n_sans_geste: int = 0
    medians_solved: Dict[str, Optional[float]] = field(default_factory=dict)
    n_defined_solved: Dict[str, int] = field(default_factory=dict)
    medians_stall: Dict[str, Optional[float]] = field(default_factory=dict)
    n_defined_stall: Dict[str, int] = field(default_factory=dict)
    rank_hist_stall: Dict[int, int] = field(default_factory=dict)
    profiles: List[Profile] = field(default_factory=list)

    @property
    def coverage(self) -> float:
        return self.n_resolues / self.n_grilles if self.n_grilles else 0.0

    def to_dict(self) -> Dict:
        return {
            "path": self.path,
            "sha256": self.sha256,
            "n_grilles": self.n_grilles,
            "n_lignes_ignorees": self.n_lignes_ignorees,
            "n_doublons": self.n_doublons,
            "n_sans_solution_unique": self.n_sans_solution_unique,
            "n_resolues": self.n_resolues,
            "n_arrets": self.n_arrets,
            "n_traces_refusees": self.n_traces_refusees,
            "n_sans_geste": self.n_sans_geste,
            "coverage": self.coverage,
            "medians_solved": self.medians_solved,
            "n_defined_solved": self.n_defined_solved,
            "medians_stall": self.medians_stall,
            "n_defined_stall": self.n_defined_stall,
            "rank_hist_stall": {str(k): v for k, v in sorted(self.rank_hist_stall.items())},
            "profiles": [p.to_dict() for p in self.profiles],
        }


def has_unique_solution(puzzle: str) -> bool:
    """Unicite de la solution, etablie par l'oracle exact (protocole §7.6).

    C'est le seul usage du solveur exact hors ``verify_trace`` : il dit si la
    grille est eligible, il ne dit rien du chemin.
    """
    cert = solve_certificate(puzzle, find_all=True, limit=2)
    return cert is not None and cert.solutions_found == 1


def load_puzzles(path: Path) -> Tuple[List[str], int]:
    """Grilles d'un fichier : une par ligne de 81 caracteres ``[0-9.]``.

    Les lignes vides ou d'un autre format sont comptees et ignorees (protocole
    §7.5) ; un doublon exact n'est conserve qu'une fois, et compte.
    """
    puzzles: List[str] = []
    skipped = 0
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or not re.fullmatch(r"[0-9.]{81}", line):
            skipped += 1
            continue
        puzzles.append(line)
    return puzzles, skipped


def fingerprint(raw: bytes) -> str:
    """Empreinte canonique d'un corpus : ``sha256`` des octets, fins de ligne en LF.

    Le meme corpus arrive en CRLF sur un checkout Windows
    (``core.autocrlf=true``) et en LF sur Linux ; sur les octets lus tels
    quels, un meme commit donnait deux ``report.json`` et une empreinte qui
    n'etait ni celle du blob ni une forme declaree (#28619). Seule la suite
    CRLF est reduite : un retour chariot isole dans une ligne appartient au
    corpus. ``load_puzzles`` lit les memes grilles dans les deux formes.
    """
    return hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest()


def profile_corpus(path: Path) -> CorpusReport:
    """Profil de chaque grille d'un fichier, avec les comptes de §7.5.

    Une grille sans solution unique est ecartee par l'oracle et comptee ; une
    trace refusee par ``verify_trace`` est comptee, et son profil publie tel
    quel, marque ``trace_accepted=False``. L'empreinte du corpus est celle de
    ``fingerprint``.
    """
    raw, skipped = load_puzzles(path)
    report = CorpusReport(path=path.name,
                          sha256=fingerprint(path.read_bytes()),
                          n_lignes_ignorees=skipped)
    seen = set()
    for puzzle in raw:
        key = puzzle.replace(".", "0")
        if key in seen:
            report.n_doublons += 1
            continue
        seen.add(key)
        if not has_unique_solution(puzzle):
            report.n_sans_solution_unique += 1
            continue
        report.profiles.append(profile_grid(puzzle))
    report.n_grilles = len(report.profiles)

    solved = [p for p in report.profiles if p.solved]
    stalled = [p for p in report.profiles if not p.solved]
    report.n_resolues = len(solved)
    report.n_arrets = len(stalled)
    report.n_traces_refusees = sum(1 for p in report.profiles if not p.trace_accepted)
    report.n_sans_geste = sum(1 for p in solved if p.rank_last is None)

    def medians(group: List[Profile], names: Sequence[str],
                target: Dict[str, Optional[float]], counts: Dict[str, int]) -> None:
        for name in names:
            vals = [getattr(p, name) for p in group if getattr(p, name) is not None]
            counts[name] = len(vals)
            target[name] = float(median(vals)) if vals else None

    medians(solved, ("n_steps", "r_max", "pos_r_max", "rank_last", "support_last",
                     "elim_last", "collapse", "tangle_last"),
            report.medians_solved, report.n_defined_solved)
    medians(stalled, ("steps_stall", "empty_stall", "cands_stall", "tangle_stall"),
            report.medians_stall, report.n_defined_stall)

    hist: Counter = Counter()
    for p in stalled:
        hist.update(p.rank_hist or {})
    report.rank_hist_stall = dict(sorted(hist.items()))
    return report


# ---------------------------------------------------------------------------
# Ligne de commande
# ---------------------------------------------------------------------------


def _fmt(value: Optional[float], digits: int = 3) -> str:
    if value is None:
        return "-"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return str(value)


def format_report(report: CorpusReport) -> str:
    """Resume texte d'un corpus (ASCII, pour une console cp1252)."""
    lines = [
        f"== {report.path}  sha256={report.sha256[:16]}",
        f"grilles={report.n_grilles} ignorees={report.n_lignes_ignorees} "
        f"doublons={report.n_doublons} "
        f"sans_solution_unique={report.n_sans_solution_unique} "
        f"resolues={report.n_resolues} "
        f"arrets={report.n_arrets} couverture={report.coverage:.3f} "
        f"traces_refusees={report.n_traces_refusees} sans_geste={report.n_sans_geste}",
    ]
    solved = {k: (v, report.n_defined_solved.get(k, 0))
              for k, v in report.medians_solved.items()}
    lines.append("resolues (mediane, n): " + "  ".join(
        f"{k}={_fmt(v)}({n})" for k, (v, n) in solved.items()))
    stalled = {k: (v, report.n_defined_stall.get(k, 0))
               for k, v in report.medians_stall.items()}
    lines.append("arrets (mediane, n): " + "  ".join(
        f"{k}={_fmt(v)}({n})" for k, (v, n) in stalled.items()))
    if report.rank_hist_stall:
        hist = "  ".join(f"r{k}={v}" for k, v in report.rank_hist_stall.items())
        lines.append("rangs des pas avant arret: " + hist)
    return "\n".join(lines)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Variables du chemin de resolution d'un corpus de grilles "
                    "(protocole #27214).")
    parser.add_argument("corpus", nargs="+", type=Path,
                        help="fichier de grilles, 81 caracteres [0-9.] par ligne")
    parser.add_argument("--json", type=Path, default=None,
                        help="ecrire le rapport complet (profils par grille)")
    args = parser.parse_args(argv)

    reports = []
    for path in args.corpus:
        if not path.is_file():
            print(f"fichier introuvable : {path}", file=sys.stderr)
            return 2
        report = profile_corpus(path)
        reports.append(report)
        print(format_report(report))

    if args.json is not None:
        payload = {"corpora": [r.to_dict() for r in reports]}
        args.json.write_text(json.dumps(payload, indent=1, ensure_ascii=False),
                             encoding="utf-8")
        print(f"rapport ecrit : {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
