"""Rendu de diagrammes de noeuds 2D a partir d'un PD-code — Python pur (numpy + matplotlib).

Contexte (issue #21908) : la serie KNOTS doit afficher de vrais diagrammes de noeuds
(projection plane + passages par-dessus/par-dessous). Le moteur de rendu natif de la
pile SnapPy/Spherogram n'est PAS portable : ``spherogram.links.draw.run_draw`` lance un
sous-processus POSIX (``draw`` + ``mpost`` + ``epstopdf``), absent de Windows et de la CI,
et Spherogram 2.4.1 n'embarque aucune fonction de tracé Python (zero reference a
matplotlib dans le paquet — verifie firsthand, 2026-10-21, issue #21908).

Ce module implement l'option 3 de l'issue : la **topologie** (croisements, sur/sous)
reste portee par le PD-code calcule par SnapPy ; seule la **projection plane** est
reconstruite ici, en Python pur deterministe :

1. le PD-code definit un systeme de rotation (ordre cyclique des 4 demi-aretes a
   chaque croisement) — les faces de la projection s'en deduisent par permutation ;
2. la caracteristique d'Euler ``V - E + F`` valide que le systeme est planaire (= 2
   pour un diagramme connexe) — un PD-code incoherent est refuse explicitement ;
3. les croisements sont places par un **plongement de Tutte** (face externe egale au
   plus grand cycle simple, sommets externes sur un cercle, interieurs barycentriques) ;
4. chaque arete est tracee en arc de Bezier quadratique, avec ecartement des aretes
   paralleles (digones) du cote du centroide — un diagramme reduit a 3 croisements
   (trèfle) est le multigraphe 2K3, non tracable en segments droits ;
5. le passage sur/sous est rendu par un **halo blanc** redessine sur le brin superieur
   au voisinage de chaque croisement (matplotlib ``patheffects.withStroke``) ;
6. une verification geometrique **numerique** compte les intersections de la figure
   hors croisements declares : un dessin valide rend ``geometric_crossings == 0``.

Conventions PD-code (Knot Atlas / SnapPy, verifiees contre ``spherogram.Link`` 2.4.1) :
un croisement ``X[a, b, c, d]`` liste ses aretes dans l'ordre trigonometrique, ``a`` etant
l'arete entrante du brin inferieur. Le brin inferieur relie donc les positions 0 et 2,
le brin superieur les positions 1 et 3. La position globale du dessin peut etre
l'image miroir du diagramme d'origine (isotopie sure, orientation non garantie).

Limites documentees :
- les kinks de Reidemeister I (une arete dont les deux extremites sont le meme
  croisement) ne sont pas supportes — lever le kink d'abord (``Link.simplify()``) ;
- les diagrammes scinds (plusieurs composantes) sont places cote a cote, sans
  garantie d'esthetique.

CLI (inspection manuelle) :

    python scripts/notebook_tools/knot_diagram.py --list-pd
    python scripts/notebook_tools/knot_diagram.py --name 3_1 --out trefoil.png
    python scripts/notebook_tools/knot_diagram.py --pd-json "[[5,2,0,3],[3,0,4,1],[1,4,2,5]]" --out t.png

Part of #21908
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Sequence, Tuple

import numpy as np

Edge = int
Dart = Tuple[int, int]  # (index de croisement, position 0-3 dans le quadruplet)

# PD-codes de reference, mesures via spherogram 2.4.1 (Link(name).PD_code(), 2026-10-22).
# 3_1 / 4_1 / K11n34 sont les trois noeuds de la section 6.1 de KNOTS-02 ;
# 5_2 sert de temoin supplementaire (5 croisements, 2 sommets interieurs).
EXAMPLE_PD: Dict[str, List[Tuple[int, int, int, int]]] = {
    "3_1": [(5, 2, 0, 3), (3, 0, 4, 1), (1, 4, 2, 5)],
    "4_1": [(7, 4, 0, 5), (3, 0, 4, 1), (1, 7, 2, 6), (5, 3, 6, 2)],
    "5_2": [(4, 0, 5, 9), (0, 6, 1, 5), (8, 2, 9, 1), (2, 8, 3, 7), (6, 4, 7, 3)],
    "K11n34": [
        (2, 0, 3, 21), (0, 6, 1, 5), (6, 2, 7, 1), (10, 3, 11, 4), (4, 11, 5, 12),
        (7, 15, 8, 14), (19, 8, 20, 9), (9, 16, 10, 17), (17, 12, 18, 13),
        (13, 18, 14, 19), (15, 21, 16, 20),
    ],
}

UNDER_POSITIONS: Tuple[int, int] = (0, 2)
OVER_POSITIONS: Tuple[int, int] = (1, 3)


class PDCodeError(ValueError):
    """PD-code incoherent : arete absente/double, kink de Reidemeister I, ou systeme de rotation non planaire."""


# ---------------------------------------------------------------------------
# Etape 1-2 : systeme de rotation et faces de la projection
# ---------------------------------------------------------------------------

def edge_occurrences(pd: Sequence[Sequence[int]]) -> Dict[Edge, Tuple[Dart, Dart]]:
    """Cartographie chaque etiquette d'arete vers ses deux darts (croisement, position).

    Un PD-code valide liste chaque arete exactement deux fois : une fois a chacune de
    ses extremites.
    """
    occ: Dict[Edge, List[Dart]] = {}
    for ci, quad in enumerate(pd):
        if len(quad) != 4:
            raise PDCodeError(f"croisement {ci}: un PD-code liste 4 aretes, recu {len(quad)}")
        for k, e in enumerate(quad):
            occ.setdefault(int(e), []).append((ci, k))
    out: Dict[Edge, Tuple[Dart, Dart]] = {}
    for e, lst in occ.items():
        if len(lst) != 2:
            raise PDCodeError(f"arete {e}: presente {len(lst)} fois (attendu: 2)")
        d0, d1 = lst
        if d0[0] == d1[0]:
            raise PDCodeError(
                f"arete {e}: kink de Reidemeister I (les deux extremites sont le "
                f"croisement {d0[0]}) — non supporte, faire Link.simplify() d'abord"
            )
        out[e] = (d0, d1)
    return out


def pd_faces(pd: Sequence[Sequence[int]]) -> Tuple[List[List[Dart]], Dict[Edge, Tuple[Dart, Dart]]]:
    """Faces de la projection par parcours de la permutation ``alpha o sigma``.

    ``sigma`` tourne d'un cran dans l'ordre trigonometrique a chaque croisement
(l'ordre du quadruplet PD), ``alpha`` saute a l'autre extremite de l'arete. Les
    cycles de la composition parcourent les bords de faces de la projection.
    """
    occ = edge_occurrences(pd)
    alpha: Dict[Dart, Dart] = {}
    for d0, d1 in occ.values():
        alpha[d0], alpha[d1] = d1, d0

    def phi(d: Dart) -> Dart:
        return alpha[(d[0], (d[1] + 1) % 4)]

    darts = [(ci, k) for ci in range(len(pd)) for k in range(4)]
    faces: List[List[Dart]] = []
    seen = set()
    for d in darts:
        if d in seen:
            continue
        face: List[Dart] = []
        cur = d
        while cur not in seen:
            seen.add(cur)
            face.append(cur)
            cur = phi(cur)
        faces.append(face)
    return faces, occ


def _connected_components(n_vertices: int, occ: Dict[Edge, Tuple[Dart, Dart]]) -> List[List[int]]:
    adj: Dict[int, List[int]] = {v: [] for v in range(n_vertices)}
    for d0, d1 in occ.values():
        adj[d0[0]].append(d1[0])
        adj[d1[0]].append(d0[0])
    comps: List[List[int]] = []
    seen = set()
    for v in range(n_vertices):
        if v in seen:
            continue
        comp, stack = [], [v]
        seen.add(v)
        while stack:
            u = stack.pop()
            comp.append(u)
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        comps.append(sorted(comp))
    return comps


def check_euler(pd: Sequence[Sequence[int]]) -> List[List[int]]:
    """Valide la planarite du systeme de rotation et retourne les composantes.

    Pour un diagramme a C composantes connexes : ``V - E + F = 1 + C``. Un PD-code
    dont les quadruplets ne decrivent pas une projection plane est refuse ici,
    avant tout calcul de layout.
    """
    faces, occ = pd_faces(pd)
    components = _connected_components(len(pd), occ)
    chi = len(pd) - len(occ) + len(faces)
    if chi != 1 + len(components):
        raise PDCodeError(
            f"systeme de rotation non planaire: chi={chi}, attendu {1 + len(components)} "
            f"(V={len(pd)}, E={len(occ)}, F={len(faces)}, composantes={len(components)})"
        )
    return components


# ---------------------------------------------------------------------------
# Etape 3 : plongement de Tutte (positions des croisements)
# ---------------------------------------------------------------------------

def _tutte_component(
    pd: Sequence[Sequence[int]],
    occ: Dict[Edge, Tuple[Dart, Dart]],
    faces: List[List[Dart]],
    component: List[int],
) -> np.ndarray:
    """Positions des croisements d'une composante par plongement de Tutte.

    Face externe = le plus grand cycle simple (sans croisement repete) de la
    composante, place sur le cercle unite ; les croisements interieurs resolvent le
    systeme barycentrique du multigraphe (aretes paralleles incluses, multiplicites
    dans la matrice).
    """
    comp_set = set(component)
    simple = [
        f for f in faces
        if {c for c, _ in f} <= comp_set and len({c for c, _ in f}) == len(f)
    ]
    if not simple:
        raise PDCodeError("aucune face a cycle simple: PD-code non tracable")
    outer_face = max(simple, key=len)
    outer_vertices = [c for c, _ in outer_face]

    pos = np.zeros((len(pd), 2))
    m = len(outer_vertices)
    for i, v in enumerate(outer_vertices):
        # parcours de la face externe dans le sens horaire vu de l'exterieur
        ang = -2.0 * np.pi * i / m
        pos[v] = (np.cos(ang), np.sin(ang))

    interior = [v for v in component if v not in set(outer_vertices)]
    if not interior:
        return pos

    A = np.zeros((len(pd), len(pd)))
    for d0, d1 in occ.values():
        u, v = d0[0], d1[0]
        if u in comp_set and v in comp_set:
            A[u, v] += 1
            A[v, u] += 1

    idx = {v: i for i, v in enumerate(interior)}
    L = np.zeros((len(interior), len(interior)))
    b = np.zeros((len(interior), 2))
    for v in interior:
        i = idx[v]
        deg = A[v].sum()
        L[i, i] = deg
        for w in range(len(pd)):
            if A[v, w] == 0:
                continue
            if w in idx:
                L[i, idx[w]] -= A[v, w]
            else:
                b[i] += A[v, w] * pos[w]
    try:
        sol = np.linalg.solve(L, b)
    except np.linalg.LinAlgError as exc:  # pragma: no cover - garde defensive
        raise PDCodeError("systeme barycentrique singulier: composante sans face externe") from exc
    for v, i in idx.items():
        pos[v] = sol[i]
    return pos


def layout_crossings(pd: Sequence[Sequence[int]]) -> np.ndarray:
    """Positions 2D des croisements (plongement de Tutte, deterministe).

    Les composantes multiples sont placees successivement le long de l'axe x,
    chaque composante dans son propre disque unite.
    """
    faces, occ = pd_faces(pd)
    components = check_euler(pd)
    pos = np.zeros((len(pd), 2))
    offset = 0.0
    for comp in components:
        p = _tutte_component(pd, occ, faces, comp)
        sub = p[comp]
        sub = sub - sub.mean(axis=0)  # recentrage dans le disque unite
        radius = float(np.max(np.linalg.norm(sub, axis=1))) if len(comp) else 0.0
        pos[comp] = sub + np.array([offset + radius, 0.0])
        offset += 2.0 * radius + 0.6
    if not np.all(np.isfinite(pos)):
        raise PDCodeError("layout non fini numeriquement")
    if len({tuple(np.round(p, 9)) for p in pos}) != len(pos):
        raise PDCodeError("deux croisements confondus: layout degenere")
    return pos


# ---------------------------------------------------------------------------
# Etape 4 : arcs de Bezier par arete
# ---------------------------------------------------------------------------

def edge_control_points(
    pos: np.ndarray,
    occ: Dict[Edge, Tuple[Dart, Dart]],
    curve: float = 0.10,
    pair_gap: float = 0.16,
) -> Dict[Edge, np.ndarray]:
    """Point de controle Bezier de chaque arete.

    Chaque arete recoit une courbure douce uniforme (``curve``) pour briser les
    colinearites exactes du Tutte, et les aretes paralleles d'un meme couple de
    croisements sont ecartees de ``pair_gap`` par rang, du cote du centroide — un
    multigraphe comme 2K3 (ombre du trefle) n'a pas de trace droit valide.
    """
    centroid = pos.mean(axis=0)
    groups: Dict[Tuple[int, int], List[Edge]] = {}
    for e, (d0, d1) in occ.items():
        groups.setdefault(tuple(sorted((d0[0], d1[0]))), []).append(e)

    ctrl: Dict[Edge, np.ndarray] = {}
    for pair, edges in groups.items():
        u, v = pair
        p0, p1 = pos[u], pos[v]
        if np.allclose(p0, p1, atol=1e-9):
            raise PDCodeError(f"aretes de {u}-{v}: croisements confondus")
        mid = (p0 + p1) / 2
        d = p1 - p0
        nrm = np.array([-d[1], d[0]])
        n = float(np.linalg.norm(nrm))
        nrm = nrm / n
        length = n
        toward = centroid - mid
        sign = 1.0 if float(np.dot(nrm, toward)) >= 0.0 else -1.0
        for rank, e in enumerate(sorted(edges)):
            off = sign * (rank * pair_gap + curve) * length
            ctrl[e] = mid + nrm * off
    return ctrl


def bezier(p0: np.ndarray, c: np.ndarray, p1: np.ndarray, samples: int = 60) -> np.ndarray:
    """Polyline d'echantillonnage d'un arc de Bezier quadratique (samples points)."""
    t = np.linspace(0.0, 1.0, samples)[:, None]
    return (1 - t) ** 2 * p0 + 2 * (1 - t) * t * c + t**2 * p1


def _prefix_by_length(pts: np.ndarray, fraction: float) -> np.ndarray:
    """Prefixe de la polyline couvrant ``fraction`` de sa longueur d'arc."""
    seglen = np.linalg.norm(np.diff(pts, axis=0), axis=1)
    total = float(seglen.sum())
    if total <= 0:
        return pts
    target = fraction * total
    cum = np.cumsum(seglen)
    k = int(np.searchsorted(cum, target))
    return pts[: min(k + 1, len(pts))]


# ---------------------------------------------------------------------------
# Etape 6 : verification geometrique
# ---------------------------------------------------------------------------

def segments_intersect(p1: np.ndarray, p2: np.ndarray, p3: np.ndarray, p4: np.ndarray) -> bool:
    """Intersection propre de deux segments (les contacts d'extremite et collinearites ne comptent pas).

    Le test ``d1*d2 < 0`` et ``d3*d4 < 0`` ne compte que les croisements d'interieur :
    deux arcs se rejoignant a un croisement declare ne doivent pas etre comptes comme
    intersection parasite.
    """
    def cross(o, a, b):
        return float((a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]))
    d1, d2 = cross(p3, p4, p1), cross(p3, p4, p2)
    d3, d4 = cross(p1, p2, p3), cross(p1, p2, p4)
    return (d1 * d2 < 0) and (d3 * d4 < 0)


def geometric_crossing_count(
    curves: Dict[Edge, np.ndarray],
    occ: Dict[Edge, Tuple[Dart, Dart]],
) -> int:
    """Intersections geometriques hors croisements declares du diagramme.

    Un dessin valide rend 0 : les seuls contacts d'arcs sont les croisements du
    PD-code, ou partagent deja un croisement commun (exclues du comptage).
    """
    edges = sorted(curves)
    # aretes partageant un croisement: ecartees systematiquement
    share_vertex = set()
    for i in range(len(edges)):
        for j in range(i + 1, len(edges)):
            (a0, _), (a1, _) = occ[edges[i]]
            (b0, _), (b1, _) = occ[edges[j]]
            if {a0, a1} & {b0, b1}:
                share_vertex.add((i, j))
    total = 0
    for i in range(len(edges)):
        a = curves[edges[i]]
        for j in range(i + 1, len(edges)):
            if (i, j) in share_vertex:
                continue
            b = curves[edges[j]]
            for k in range(len(a) - 1):
                for l in range(len(b) - 1):
                    if segments_intersect(a[k], a[k + 1], b[l], b[l + 1]):
                        total += 1
    return total


# ---------------------------------------------------------------------------
# Assemblage : diagramme complet
# ---------------------------------------------------------------------------

@dataclass
class CrossingInfo:
    """Un croisement : positions (dans le quadruplet PD) du brin sous et du brin sur."""
    index: int
    under: Tuple[Edge, Edge]
    over: Tuple[Edge, Edge]


@dataclass
class KnotDiagram:
    """Diagramme reconstruit: positions, arcs, structure sur/sous, validite geometrique."""
    pd: List[Tuple[int, int, int, int]]
    positions: np.ndarray
    faces: List[List[Dart]]
    occurrences: Dict[Edge, Tuple[Dart, Dart]]
    control_points: Dict[Edge, np.ndarray]
    curves: Dict[Edge, np.ndarray]
    crossings: List[CrossingInfo] = field(default_factory=list)
    geometric_crossings: int = -1

    @property
    def crossing_count(self) -> int:
        return len(self.pd)

    @property
    def is_valid_projection(self) -> bool:
        return self.geometric_crossings == 0


def build_diagram(
    pd: Sequence[Sequence[int]],
    samples: int = 60,
    curve: float = 0.10,
    pair_gap: float = 0.16,
) -> KnotDiagram:
    """Construit le diagramme complet d'un PD-code (layout + arcs + verification)."""
    faces, occ = pd_faces(pd)
    check_euler(pd)
    pos = layout_crossings(pd)
    ctrl = edge_control_points(pos, occ, curve=curve, pair_gap=pair_gap)
    curves = {e: bezier(pos[d0[0]], ctrl[e], pos[d1[0]], samples) for e, (d0, d1) in occ.items()}
    crossings = [
        CrossingInfo(
            index=ci,
            under=(quad[UNDER_POSITIONS[0]], quad[UNDER_POSITIONS[1]]),
            over=(quad[OVER_POSITIONS[0]], quad[OVER_POSITIONS[1]]),
        )
        for ci, quad in enumerate(pd)
    ]
    return KnotDiagram(
        pd=[tuple(q) for q in pd],  # type: ignore[arg-type]
        positions=pos,
        faces=faces,
        occurrences=occ,
        control_points=ctrl,
        curves=curves,
        crossings=crossings,
        geometric_crossings=geometric_crossing_count(curves, occ),
    )


# ---------------------------------------------------------------------------
# Etape 5 : rendu matplotlib (import differe — le layout marche sans matplotlib)
# ---------------------------------------------------------------------------

def draw_diagram(
    diagram: KnotDiagram,
    ax=None,
    color: str = "#1f3b73",
    linewidth: float = 2.2,
    overhang: float = 0.45,
    zorder_base: int = 2,
    zorder_over: int = 3,
):
    """Trace le diagramme sur un Axes matplotlib et retourne l'Axes.

    Le brin superieur est redessine pres de chaque croisement avec un halo blanc
    (``patheffects.withStroke``) qui interrompt visuellement le brin inferieur :
    c'est le rendu du passage par-dessus/par-dessous. ``overhang`` est la fraction
    de longueur d'arc couverte par le halo de part et d'autre du croisement.
    """
    import matplotlib.patheffects as pe
    import matplotlib.pyplot as plt

    if ax is None:
        _, ax = plt.subplots()
    occ = diagram.occurrences
    for e in sorted(diagram.curves):
        pts = diagram.curves[e]
        ax.plot(pts[:, 0], pts[:, 1], color=color, lw=linewidth,
                solid_capstyle="round", zorder=zorder_base)
    halo = [pe.withStroke(linewidth=linewidth + 4.8, foreground="white")]
    for ci, quad in enumerate(diagram.pd):
        for k in OVER_POSITIONS:
            e = quad[k]
            pts = diagram.curves[e]
            d0, _ = occ[e]
            if d0 != (ci, k):  # orienter la polyline depuis ce croisement
                pts = pts[::-1]
            head = _prefix_by_length(pts, overhang)
            ax.plot(head[:, 0], head[:, 1], color=color, lw=linewidth,
                    solid_capstyle="round", zorder=zorder_over,
                    path_effects=halo)
    ax.set_aspect("equal")
    ax.axis("off")
    return ax


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--name", choices=sorted(EXAMPLE_PD), help="PD-code de reference integre")
    group.add_argument("--pd-json", help="PD-code en JSON, ex. '[[5,2,0,3],[3,0,4,1],[1,4,2,5]]'")
    group.add_argument("--list-pd", action="store_true", help="liste les PD-codes de reference")
    parser.add_argument("--out", help="PNG de sortie (requiert matplotlib)")
    parser.add_argument("--check-only", action="store_true", help="pas de PNG, juste la validation")
    args = parser.parse_args(argv)

    if args.list_pd:
        for name, pd in sorted(EXAMPLE_PD.items()):
            print(f"{name}: {list(pd)}")
        return 0
    pd = EXAMPLE_PD[args.name] if args.name else [tuple(q) for q in json.loads(args.pd_json)]
    diagram = build_diagram(pd)
    print(f"croisements={diagram.crossing_count} faces={len(diagram.faces)} "
          f"intersections_geometriques={diagram.geometric_crossings} "
          f"projection_valide={diagram.is_valid_projection}")
    if not args.check_only and args.out:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        fig, ax = plt.subplots(figsize=(6, 6))
        draw_diagram(diagram, ax=ax)
        ax.set_title(f"{args.name or 'PD'} — {diagram.crossing_count} croisements")
        fig.tight_layout()
        fig.savefig(args.out, dpi=110, facecolor="white")
        plt.close(fig)
        print(f"PNG: {args.out}")
    return 0 if diagram.is_valid_projection else 1


if __name__ == "__main__":
    sys.exit(main())
