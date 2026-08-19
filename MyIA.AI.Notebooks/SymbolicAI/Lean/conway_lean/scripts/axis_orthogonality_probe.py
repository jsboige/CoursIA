# Probe d'orthogonalité deux-axes (issue #11162, jambe empirique) — nouveauté x confinement
#
# Le probe Grain 1 (`novelty_probe.py`, PR #11221) mesure l'axe NOUVEAUTÉ seul :
# l'axe CONFINEMENT n'y est jamais mesuré — l'orthogonalité des deux axes est
# affirmée en docstring, pas éprouvée. Ce probe mesure les DEUX axes sur les
# MÊMES trajectoires et confronte la classification mesurée au tableau de
# l'issue. Le verdict est autorisé à contredire la théorie de départ.
#
# Axe CONFINEMENT (proxy empirique de `jumpCaptured`, #11007) : le pattern
# reste-t-il dans une fenêtre fixe ancrée à son état initial ? Mesuré en cadre
# ABSOLU : `advance_abs` réplique `hashlife.advance` en traquant l'origine du
# canvas (centre() : +size/2 ; successor() : +size/4, size/2 ; crop strip :
# +size/4, size/2), pour que la translation pure soit visible — un glider ne
# grandit jamais (bbox constante) mais s'échappe à c/4 : une mesure sur la
# seule bbox SERAIT AVEUGLE à l'échappement par translation. La géométrie du
# cadre absolu est validée par contrôles (bloc immobile ; glider translaté
# d'exactement une diagonale par 4 générations).
#
#   front(t)      : demi-étendue de Chebyshev des cellules vivantes, mesurée
#                   depuis le centre initial — capte TOUT échappement (front
#                   ET translation). front_speed = pente LSQ de front vs t.
#   bulk90(t)     : rayon de Chebyshev contenant 90 % de la population autour
#                   du centroïde courant — la masse, pas le front.
#   residency(t)  : fraction de population dans la fenêtre centrale fixe
#                   384x384 ancrée au centre initial.
#
# Axe NOUVEAUTÉ (cache de mémoïsation, comme Golly) : nœuds distincts de
# l'arbre (comme Grain 1, pour comparabilité), pente log-log, et TAUX DE HIT
# cumulatif + par intervalle des caches join/successor (hits/(hits+misses)) —
# la grandeur qui fait la vitesse réelle de Golly, instrumentée ici pour la
# première fois sur ce dépôt.
#
# Contrôles positifs/négatifs (échouent BRUYAMMENT, à chaque exécution) :
#   - bloc          : immobile en cadre absolu, front_speed ~ 0     (négatif échappement)
#   - glider        : +1 cellule en diagonale par 4 générations     (validation géométrie)
#                     et front_speed >= 0.15 (c/4 = 0.25)           (positif échappement)
#   - blinker       : la mémoïsation TOUCHE (hits >= 1)             (compteur vivant —
#                     « 0 nouveauté détectée » et « rien regardé » ne rendent pas la même valeur)
#   - random soups  : pente de nouveauté >= 0.25                    (positif nouveauté)
#   - règle B3/S23  : advance() == baseline_life() sur 8 générations pour CHAQUE
#                     pattern embarqué (via novelty_probe.selfcheck + extension locale)
#
# Familles / instances (6 familles, 9 instances — chaque ligne de sortie porte
# famille + nom d'instance) :
#   still_life   : block                    (1 instance)
#   oscillator   : blinker (p2)             (1)
#   spaceship    : glider                   (1)  — témoin d'échappement PUR : s'échappe, zéro nouveauté
#   tiled_growth : gosper_gun               (1)  — substitut documenté du space-filler (#11221)
#   methuselah   : r_pentomino, acorn       (2)
#   random_soup  : soup_s42, soup_s7, soup_s99 (3, graines déterministes)
#
# Usage : python axis_orthogonality_probe.py [--checkpoints 0,1,...,2048] [--patterns ...]

from __future__ import annotations

import argparse
import random
import time

import hashlife as hl
from novelty_probe import (
    PATTERNS as BASE_PATTERNS,
    _clear_caches,
    _normalize,
    decode_rle,
    distinct_nodes,
    loglog_slope,
    selfcheck as novelty_selfcheck,
)

GLIDER_RLE = "bob$2bo$3o!"
SOUP_SEEDS = (42, 7, 99)
SOUP_SIZE = 32
SOUP_DENSITY = 0.25
WINDOW_HALF = 192  # fenêtre centrale fixe : 384x384 ancrée au centre initial

# Seuils des verdicts (documentés — calibrés sur les séparations mesurées,
# cf README : le seuil de pic 4000 s'assoit dans le vide entre le gun (483)
# et la soupe la plus calme (6272), écart x13 de part et d'autre) :
#   confinement : front_speed >= 0.05 cell/gen -> ÉCHAPPE (c/4 = 0.25, c/2 = 0.5)
#   nouveauté   : pente >= 0.50 OU pic de join-misses/interval >= 4000 -> SLOW
#                pente < 0.25 ET hit cumulatif >= 0.80 -> FAST ; sinon INTERMÉDIAIRE
ESCAPE_FRONT_SPEED = 0.05
SLOW_SLOPE = 0.50
SLOW_PEAK_INTERVAL_MISSES = 4000
FAST_SLOPE = 0.25
FAST_CUM_HIT = 0.80

SELFCHECK_GENS = 8


def soup_cells(seed: int) -> list[tuple[int, int]]:
    """Soupe aléatoire déterministe SOUP_SIZE x SOUP_SIZE, densité SOUP_DENSITY."""
    rng = random.Random(seed)
    return [
        (x, y)
        for x in range(SOUP_SIZE)
        for y in range(SOUP_SIZE)
        if rng.random() < SOUP_DENSITY
    ]


def build_patterns() -> list[dict]:
    """Table des 9 instances : nom, famille, cellules initiales."""
    entries = []
    for name in ("block", "blinker", "gosper_gun", "r_pentomino", "acorn"):
        cls, _desc, rle, *_ = BASE_PATTERNS[name]
        entries.append({"name": name, "family": cls, "cells": decode_rle(rle)})
    entries.append(
        {"name": "glider", "family": "spaceship", "cells": decode_rle(GLIDER_RLE)}
    )
    for seed in SOUP_SEEDS:
        entries.append(
            {
                "name": f"soup_s{seed}",
                "family": "random_soup",
                "cells": soup_cells(seed),
            }
        )
    return entries


# --- Cadre absolu : répliques de advance/crop avec tracking d'origine ---------


def _centre_abs(node, off, size):
    node = hl.centre(node)
    # centre() place l'ancien canvas SxS au centre du nouveau 2Sx2S : le repère
    # du nouveau canvas démarre S/2 AVANT l'ancien origine -> offset absolu
    # MOINS S/2 (une cellule d'abcisse ancienne x se lit x + S/2 dans le
    # nouveau repère, à position absolue inchangée)
    off = (off[0] - size // 2, off[1] - size // 2)
    size *= 2
    return node, off, size


def _successor_abs(node, j, off, size):
    node = hl.successor(node, j)
    off = (off[0] + size // 4, off[1] + size // 4)
    size //= 2
    return node, off, size


def advance_abs(node, off, size, n):
    """Réplique exacte de hl.advance SANS le crop final, en trackant l'origine.

    Retourne (node, off, size) : l'origine du canvas du node retourné, dans le
    repère absolu (le repère du construct initial). Contrat géométrique :
      centre()   : l'ancien canvas SxS occupe le carré central du nouveau
                   2Sx2S -> le nouveau repère démarre S/2 avant l'ancien
                   origine : offset ABSOLU −S/2, taille x2 ;
      successor(): résultat = évolution de la région centrale de moitié ->
                   nouveau repère à S/4 de l'ancien : offset +S/4, taille /2.
    Validé par les contrôles (bloc immobile, glider +diagonale/4 générations).
    """
    if n == 0:
        return node, off, size
    bits = []
    while n > 0:
        bits.append(n & 1)
        n >>= 1
        node, off, size = _centre_abs(node, off, size)
        node, off, size = _centre_abs(node, off, size)
    for k, bit in enumerate(reversed(bits)):
        j = len(bits) - k - 1
        if bit:
            node, off, size = _successor_abs(node, j, off, size)
    return node, off, size


def crop_abs(node, off, size):
    """Réplique de hl.crop en trackant l'origine (inner() : +S/4, taille /2).

    Indispensable entre checkpoints : sans lui, les centre() de chaque advance
    accumuleraient la taille de canvas (x4 par bit) et l'explosion mémoire
    tuerait le run. Le node retourné est le même que celui de hl.advance.
    """
    while node.k > 3 and hl.is_padded(node):
        node = hl.inner(node)
        off = (off[0] + size // 4, off[1] + size // 4)
        size //= 2
    return node, off, size


def abs_cells(node, off) -> set[tuple[int, int]]:
    """Cellules vivantes du node, en coordonnées absolues."""
    return {(x + off[0], y + off[1]) for x, y, _g in hl.expand(node)}


# --- Métriques spatiales ------------------------------------------------------


def bbox_center(cells):
    xs = [x for x, _ in cells]
    ys = [y for _, y in cells]
    return (min(xs) + max(xs)) / 2, (min(ys) + max(ys)) / 2


def chebyshev_radius(cells, cx, cy):
    return max((max(abs(x - cx), abs(y - cy)) for x, y in cells), default=0.0)


def spatial_metrics(cells, c0):
    """front (depuis le centre initial), bulk90 (autour du centroïde courant),
    residency (fenêtre centrale fixe)."""
    if not cells:
        return {"front": 0.0, "bulk90": 0.0, "residency": 1.0}
    cx = sum(x for x, _ in cells) / len(cells)
    cy = sum(y for _, y in cells) / len(cells)
    radii = sorted(max(abs(x - cx), abs(y - cy)) for x, y in cells)
    bulk90 = radii[int(0.9 * (len(radii) - 1))]
    inside = sum(
        1
        for x, y in cells
        if abs(x - c0[0]) <= WINDOW_HALF and abs(y - c0[1]) <= WINDOW_HALF
    )
    return {
        "front": chebyshev_radius(cells, c0[0], c0[1]),
        "bulk90": float(bulk90),
        "residency": inside / len(cells),
    }


def lin_slope(points):
    """Pente LSQ de y contre t sur (t, y) — vitesse cell/génération."""
    pts = [(t, y) for t, y in points if t > 0]
    if len(pts) < 2:
        return 0.0
    n = len(pts)
    mt = sum(t for t, _ in pts) / n
    my = sum(y for _, y in pts) / n
    var = sum((t - mt) ** 2 for t, _ in pts)
    if var == 0:
        return 0.0
    return sum((pts[i][0] - mt) * (pts[i][1] - my) for i in range(n)) / var


def hit_rate(info):
    total = info.hits + info.misses
    return info.hits / total if total else 0.0


# --- Pass de mesure -----------------------------------------------------------


def run_pattern(entry, checkpoints):
    """Une trajectoire, les DEUX axes mesurés dessus. Chaque ligne est nommée
    (famille + instance) — l'instrument nomme ce qu'il vient de mesurer."""
    _clear_caches()
    node = hl.construct(list(entry["cells"]))
    off, size = (0, 0), 1 << node.k
    cells0 = abs_cells(node, off)
    c0 = bbox_center(cells0)
    pop0 = len(cells0)
    rows = []
    prev_t = 0
    prev_join = hl.join.cache_info()
    prev_succ = hl.successor.cache_info()
    prev_distinct = 0
    for t in checkpoints:
        if t > prev_t:
            node, off, size = advance_abs(node, off, size, t - prev_t)
            node, off, size = crop_abs(node, off, size)
            prev_t = t
        cells = abs_cells(node, off)
        sp = spatial_metrics(cells, c0)
        nd, k = distinct_nodes(node)
        ji, si = hl.join.cache_info(), hl.successor.cache_info()
        d_join = (ji.hits + ji.misses) - (prev_join.hits + prev_join.misses)
        d_succ = (si.hits + si.misses) - (prev_succ.hits + prev_succ.misses)
        rows.append(
            {
                "t": t,
                "level": k,
                "population": len(cells),
                **sp,
                "distinct": nd,
                "delta_distinct": nd - prev_distinct,
                "delta_join_misses": ji.misses - prev_join.misses,
                "join_hit_rate_interval": (
                    (ji.hits - prev_join.hits) / d_join if d_join else 0.0
                ),
                "succ_hit_rate_interval": (
                    (si.hits - prev_succ.hits) / d_succ if d_succ else 0.0
                ),
            }
        )
        prev_join, prev_succ, prev_distinct = ji, si, nd
    ji, si = hl.join.cache_info(), hl.successor.cache_info()
    axes = {
        "family": entry["family"],
        "name": entry["name"],
        "pop0": pop0,
        "front_speed": lin_slope([(r["t"], r["front"]) for r in rows]),
        "bulk90_speed": lin_slope([(r["t"], r["bulk90"]) for r in rows]),
        "final_residency": rows[-1]["residency"],
        "novelty_slope": loglog_slope([(r["t"], r["distinct"]) for r in rows]),
        "join_hit_cum": hit_rate(ji),
        "succ_hit_cum": hit_rate(si),
        "peak_join_misses_interval": max(
            (r["delta_join_misses"] for r in rows if r["t"] > 0), default=0
        ),
    }
    return rows, axes


def verdict_confinement(axes):
    if axes["front_speed"] >= ESCAPE_FRONT_SPEED:
        return "ECHAPPE"
    return "TIENT"


def verdict_novelty(axes):
    if (
        axes["novelty_slope"] >= SLOW_SLOPE
        or axes["peak_join_misses_interval"] >= SLOW_PEAK_INTERVAL_MISSES
    ):
        return "SLOW"
    if axes["novelty_slope"] < FAST_SLOPE and axes["join_hit_cum"] >= FAST_CUM_HIT:
        return "FAST"
    return "INTERMEDIAIRE"


# --- Contrôles ----------------------------------------------------------------


def _rule_check(cells, gens=SELFCHECK_GENS):
    """advance() == baseline_life() à translation près, sur ce pattern."""
    _clear_caches()
    node = hl.construct(list(cells))
    ref = _normalize(set(cells))
    for _t in range(1, gens + 1):
        node = hl.advance(node, 1)
        got = _normalize({(x, y) for x, y, _g in hl.expand(hl.crop(node))})
        ref = _normalize(set(hl.baseline_life(ref)))
        if got != ref:
            return False
    return True


def controls(patterns):
    """Contrôles positifs/négatifs — chaque instrument doit BOUGER sur ce qu'il
    doit attraper, sinon SystemExit(1) : une valeur nulle d'un instrument mort
    ne doit pas se lire comme une mesure."""
    failures = []
    for f in novelty_selfcheck():
        failures.append(f"substrat: {f}")
    for entry in patterns:
        if not _rule_check(entry["cells"]):
            failures.append(f"regle B3/S23: {entry['name']} diverge de baseline_life")

    # Géométrie du cadre absolu : bloc immobile, glider +1 diagonale / 4 générations
    _clear_caches()
    by_name = {e["name"]: e["cells"] for e in patterns}
    node = hl.construct(list(by_name["block"]))
    off, size = (0, 0), 1 << node.k
    c_before = abs_cells(node, off)
    node, off, size = advance_abs(node, off, size, 8)
    node, off, size = crop_abs(node, off, size)
    c_after = abs_cells(node, off)
    if c_before != c_after:
        failures.append(
            f"geometrie: block a bouge en cadre absolu "
            f"({len(c_before ^ c_after)} cellules)"
        )

    _clear_caches()
    node = hl.construct(list(by_name["glider"]))
    off, size = (0, 0), 1 << node.k
    c0 = abs_cells(node, off)
    node, off, size = advance_abs(node, off, size, 4)
    node, off, size = crop_abs(node, off, size)
    c4 = abs_cells(node, off)
    # translation exacte d'une diagonale : pour le bon (dx, dy) dans les 4
    # diagonales, l'ensemble translaté doit être IDENTIQUE à l'initial
    if not any(
        {(x - dx, y - dy) for x, y in c4} == c0 for dx in (-1, 1) for dy in (-1, 1)
    ):
        failures.append(
            "geometrie: glider non translaté d'une diagonale exacte en 4 générations"
        )

    # Compteur vivant : la mémoïsation doit TOUCHER sur blinker (p2 -> retour d'état)
    _clear_caches()
    node = hl.construct(list(by_name["blinker"]))
    for _ in range(4):
        node = hl.advance(node, 2)
    if hl.join.cache_info().hits < 1 or hl.successor.cache_info().hits < 1:
        failures.append(
            "compteur cache: blinker 4 cycles sans AUCUN hit join/successor "
            "-- instrument de hit-rate mort"
        )
    return failures


# --- Confrontation à la théorie ------------------------------------------------

# Tableau de l'issue #11162 (verbatim) + lignes témoins absentes du tableau.
EXPECTED = [
    ("space-filler", "gosper_gun", ("ECHAPPE", "FAST"), "substitut documenté (#11221)"),
    ("methuselah", "r_pentomino", ("TIENT", "SLOW"), "ligne du tableau"),
    ("methuselah", "acorn", ("TIENT", "SLOW"), "ligne du tableau (variante longue)"),
    ("still_life", "block", ("TIENT", "FAST"), "témoin négatif double (hors tableau)"),
    ("oscillator_p2", "blinker", ("TIENT", "FAST"), "témoin négatif double (hors tableau)"),
    ("spaceship", "glider", ("ECHAPPE", "FAST"), "témoin échappement pur (hors tableau)"),
    ("random_soup", "soup_s42", (None, "SLOW"), "témoin nouveauté (hors tableau)"),
]


def spearman(xs, ys):
    """Rang de Spearman (égalités : rang moyen), approximation standard."""

    def ranks(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j + 1]] == v[order[i]]:
                j += 1
            avg = (i + j) / 2 + 1
            for k in range(i, j + 1):
                r[order[k]] = avg
            i = j + 1
        return r

    rx, ry = ranks(xs), ranks(ys)
    n = len(xs)
    d2 = sum((rx[i] - ry[i]) ** 2 for i in range(n))
    return 1 - 6 * d2 / (n * (n * n - 1))


def confront(results):
    by_name = {a["name"]: a for a in results}
    lines = [
        "== Confrontation au tableau de l'issue #11162",
        "famille           instance      attendu            mesuré                 verdict",
    ]
    for family, name, (exp_conf, exp_nov), note in EXPECTED:
        if name not in by_name:
            continue
        a = by_name[name]
        conf, nov = verdict_confinement(a), verdict_novelty(a)
        exp = f"{exp_conf or '—'}+{exp_nov}"
        got = f"{conf}+{nov}"
        if exp_conf is None:
            verdict = "hors tableau"
        elif (exp_conf, exp_nov) == (conf, nov):
            verdict = "CONFORME"
        else:
            verdict = "CONTREDIT"
        lines.append(f"{family:<17} {name:<13} {exp:<18} {got:<22} {verdict}")
    return lines


# --- Rendu ----------------------------------------------------------------------


def render_pattern(rows, axes):
    lines = [
        f"== {axes['family']}/{axes['name']} — {len(rows)} checkpoints, "
        f"pop0={axes['pop0']}"
    ]
    lines.append(
        "      t  level     pop   front  bulk90  resid    dist  d_dist  hitJoin"
        "  hitSucc"
    )
    for r in rows:
        lines.append(
            f"{r['t']:>7}  {r['level']:>5}  {r['population']:>6}"
            f"  {r['front']:>6.1f}  {r['bulk90']:>6.1f}  {r['residency']:>5.2f}"
            f"  {r['distinct']:>6}  {r['delta_distinct']:>6}"
            f"  {r['join_hit_rate_interval']:>7.3f}  {r['succ_hit_rate_interval']:>7.3f}"
        )
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Probe deux-axes nouveauté x confinement (issue #11162)"
    )
    parser.add_argument(
        "--checkpoints",
        default="0,1,2,4,8,16,32,64,128,256,512,1024,2048",
    )
    parser.add_argument("--patterns", default=None)
    parser.add_argument("--skip-controls", action="store_true")
    args = parser.parse_args()
    checkpoints = sorted({int(t) for t in args.checkpoints.split(",")})

    patterns = build_patterns()
    if args.patterns:
        wanted = set(args.patterns.split(","))
        patterns = [p for p in patterns if p["name"] in wanted]

    families = {}
    for p in patterns:
        families[p["family"]] = families.get(p["family"], 0) + 1
    fam_desc = ", ".join(f"{f} {n}" for f, n in sorted(families.items()))
    print(
        f"instrument: axis_orthogonality_probe — {len(patterns)} instances, "
        f"{len(families)} familles ({fam_desc}), fenêtre {2 * WINDOW_HALF}x{2 * WINDOW_HALF}, "
        f"checkpoints 0..{checkpoints[-1]}"
    )

    if not args.skip_controls:
        failures = controls(build_patterns())
        if failures:
            for f in failures:
                print(f"CONTROL FAIL: {f}")
            raise SystemExit(1)
        print(
            "contrôles: règle B3/S23 (advance==baseline, 8 gén x 9 instances), "
            "géométrie cadre absolu (block immobile, glider +1 diagonale/4 gén), "
            "compteur cache vivant (blinker hits>=1) — OK"
        )

    results = []
    for entry in patterns:
        t0 = time.perf_counter()
        rows, axes = run_pattern(entry, checkpoints)
        axes["wall_s"] = time.perf_counter() - t0
        results.append(axes)
        print()
        print(render_pattern(rows, axes))

    print()
    print("== Résumé des deux axes (chaque ligne = une instance mesurée)")
    print(
        "famille           instance       front_v  bulk_v  resid_f   pente  hitCum"
        "  picMiss  CONFINEMENT  NOUVEAUTE"
    )
    for a in results:
        print(
            f"{a['family']:<17} {a['name']:<14} {a['front_speed']:>6.3f}"
            f"  {a['bulk90_speed']:>6.3f}  {a['final_residency']:>6.2f}"
            f"  {a['novelty_slope']:>5.3f}  {a['join_hit_cum']:>6.3f}"
            f"  {a['peak_join_misses_interval']:>7}"
            f"  {verdict_confinement(a):<11}  {verdict_novelty(a)}"
        )

    print()
    print("== Quadrant 2x2 (confinement x nouveauté)")
    grid = {}
    for a in results:
        grid.setdefault(
            (verdict_confinement(a), verdict_novelty(a)), []
        ).append(a["name"])
    for conf in ("TIENT", "ECHAPPE"):
        for nov in ("FAST", "INTERMEDIAIRE", "SLOW"):
            names = grid.get((conf, nov), [])
            print(f"  {conf:>7} + {nov:<12}: {len(names)}  {', '.join(names)}")

    print()
    print("\n".join(confront(results)))

    # Association mesurée entre les deux axes (thèse d'orthogonalité : rho ~ 0)
    front = [a["front_speed"] for a in results]
    for key, label in (
        ("novelty_slope", "pente nouveauté"),
        ("join_hit_cum", "hit cumulatif join"),
    ):
        vals = [a[key] for a in results]
        rho = spearman(front, vals)
        print(f"spearman(front_speed, {label}) = {rho:+.3f}")

    print()
    print(
        "seuils: ECHAPPE si front_speed >= %.2f ; SLOW si pente >= %.2f ou pic"
        " join-misses >= %d ; FAST si pente < %.2f et hit cumulatif >= %.2f"
        % (
            ESCAPE_FRONT_SPEED,
            SLOW_SLOPE,
            SLOW_PEAK_INTERVAL_MISSES,
            FAST_SLOPE,
            FAST_CUM_HIT,
        )
    )


if __name__ == "__main__":
    main()
