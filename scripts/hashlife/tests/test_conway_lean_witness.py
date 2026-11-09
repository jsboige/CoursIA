"""Cross-witness Python/Lean pour la perplexite structurelle (issue #20205).

Contre-temoin independant du module Lean `Conway.Life.Perplexity` : ce test
reimplemente de zero (sans importer `k_trajectory.py`) le comptage LZ76 par
phrases sur le bitstream exact du temoin decide dans le lake, et verifie
l'egalite avec la constante decidee par le noyau Lean.

Important : le glider utilise ici est celui du lake
(`Conway.Life.glider = [(0,0),(1,0),(1,2),(2,0),(2,1)]`, deplacement (1,-1),
periode 4), PAS la base `glider_at` de `k_trajectory.py` — deux encodages
differents du meme motif. Le bitstream et le compte ne sont comparables
qu'a coordonnees identiques.

Semantique mise en miroir (phraseLenAt / countFromGo cote Lean) :
- phrase en position i = longueur minimale k telle que bits[i:i+k] ne soit
  PAS un facteur contigu de bits[:i+k-1] ;
- cap : si tous les k <= reste satisfont l'occurrence, la phrase prend tout
  le reste (garde `phraseGo_guard` cote Lean).
"""
from __future__ import annotations

import pytest

# Constante decidee par le noyau Lean (theorem witness_glider_lz76,
# Conway/Life/Perplexity.lean). Toute divergence ici = bug de l'une des
# deux implementations, a trier avant tout merge.
LEAN_WITNESS_K = 13

# Conway.Life.glider (lake), pas k_trajectory.glider_at.
GLIDER: list[tuple[int, int]] = [(0, 0), (1, 0), (1, 2), (2, 0), (2, 1)]

BOX_N = 8
WINDOW_W = 4


def step(cells: list[tuple[int, int]]) -> list[tuple[int, int]]:
    """Une etape B3/S23 (memes regles que Conway.Life.step)."""
    s = set(cells)
    cand = set(s)
    for (x, y) in s:
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                if dx or dy:
                    cand.add((x + dx, y + dy))
    out = set()
    for p in cand:
        n = sum(
            1
            for dx in (-1, 0, 1)
            for dy in (-1, 0, 1)
            if (dx or dy) and (p[0] + dx, p[1] + dy) in s
        )
        if p in s:
            if n in (2, 3):
                out.add(p)
        elif n == 3:
            out.add(p)
    return sorted(out)


def evolve(g: list[tuple[int, int]], t: int) -> list[tuple[int, int]]:
    for _ in range(t):
        g = step(g)
    return g


def encode_box(grid: list[tuple[int, int]], n: int = BOX_N) -> list[int]:
    """Boite n*n serialee en row-major (mirror de Conway.Life.encodeBox)."""
    s = set(grid)
    return [1 if (i, j) in s else 0 for i in range(n) for j in range(n)]


def occurs(v: list[int], h: list[int]) -> bool:
    """Facteur contigu (mirror de Conway.Life.occursIn, v non vide)."""
    m = len(v)
    return any(h[a : a + m] == v for a in range(len(h) - m + 1))


def lz76_count_bits(bits: list[int]) -> int:
    """Comptage LZ76 par phrases (mirror de Conway.Life.lz76Count)."""
    n = len(bits)
    i = 0
    c = 0
    while i < n:
        k = 1
        while i + k <= n and occurs(bits[i : i + k], bits[: i + k - 1]):
            k += 1
        phr = k if i + k <= n else n - i
        c += 1
        i += phr
    return c


def serialize_window(g0: list[tuple[int, int]], w: int = WINDOW_W,
                     n: int = BOX_N) -> list[int]:
    """Fenetre seriale (mirror de serializeI sur window W k=0)."""
    out: list[int] = []
    for t in range(w):
        out += encode_box(evolve(g0, t), n)
    return out


def test_glider_window_lz76_witness() -> None:
    """Le compte Python sur le bitstream glider == la constante Lean decidee."""
    bits = serialize_window(GLIDER)
    assert len(bits) == WINDOW_W * BOX_N * BOX_N
    assert lz76_count_bits(bits) == LEAN_WITNESS_K


def test_lz76_reference_strings() -> None:
    """Valeurs de reference calculees a la main (memes cas que la preuve
    Lean de sous-additivite forte)."""
    assert lz76_count_bits([1, 1]) == 2
    assert lz76_count_bits([1, 0, 1]) == 3
    # tout-zero : premiere phrase 1, puis chaque zero est deja vu
    assert lz76_count_bits([0] * 8) == 2
    # alphabet alterne : prefixe negatif pousse la premiere longue phrase
    assert lz76_count_bits([1, 0, 1, 0, 1]) == 3


@pytest.mark.parametrize(
    "u,v",
    [
        ([1, 1], [1]),
        ([1, 0], [1]),
        ([1, 0, 1], [1, 0, 1]),
        ([0, 0, 1, 0], [1, 0, 0, 1, 0]),
        (serialize_window(GLIDER, 2), serialize_window(GLIDER, 2)[::-1]),
    ],
)
def test_subadditivity_smoke(u: list[int], v: list[int]) -> None:
    """Fumee de la sous-additivite forte prouvee dans le lake
    (lz76Count_append : sans constante +1 — le chevauchant est absorbe)."""
    assert lz76_count_bits(u + v) <= lz76_count_bits(u) + lz76_count_bits(v)


def test_complement_invariance_smoke() -> None:
    """Fumee de l'invariance par complement d'alphabet (lz76Count_map_not)."""
    bits = serialize_window(GLIDER)
    flipped = [1 - b for b in bits]
    assert lz76_count_bits(flipped) == lz76_count_bits(bits)


def test_glider_trajectory_is_a_spaceship() -> None:
    """Le glider du lake est de periode 4, deplacement (1, -1) —
    mirror de Conway.Life.glider_spaceship."""
    g4 = evolve(GLIDER, 4)
    shifted = sorted((x + 1, y - 1) for (x, y) in GLIDER)
    assert g4 == shifted
    # periode exacte : aucune des generations 1..3 ne reproduit le motif
    for t in range(1, 4):
        assert evolve(GLIDER, t) != sorted(GLIDER)
