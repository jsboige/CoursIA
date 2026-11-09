# Novelty probe — mesure empirique de l'axe « nouveauté » de l'issue #11162
#
# L'axe confinement (jumpCaptured, #11007) dit si une trajectoire reste dans
# la fenêtre centrale ; l'axe NOUVEAUTÉ dit si l'arbre de macrocells produit
# des nœuds distincts le long de la trajectoire — la quantité qui fait que
# Golly est rapide (cache de mémoïsation touche) ou lente (tout est neuf).
# Les deux axes sont orthogonaux : un space-filler échappe la boîte à vitesse
# lumière mais répète ses tuiles (rapide) ; un methuselah reste borné longtemps
# mais invente des structures à toutes les échelles (lent).
#
# Instrument : le hashlife Python de référence (`hashlife.py`) mémoïse `join`
# et `successor` via `lru_cache`. Un MISS de `join` = un nœud d'arbre JAMAIS VU
# (les sous-arbres structurellement identiques sont le même objet Python).
# La nouveauté par intervalle = Δ(misses) entre deux checkpoints ; le nombre
# de nœuds distincts de l'arbre courant = parcours du quadtree en collectant
# les id() (chaque nœud partagé compté une fois).
#
# Le self-check valide le substrat AVANT toute mesure : advance() (hashlife)
# contre baseline_life() (règle naïve) sur les 8 premières générations de
# chaque pattern — un instrument se valide par les formes qu'il doit attraper.
#
# Patterns embarqués (définitions canoniques) :
#   block        — still life (classe stable)
#   blinker      — oscillateur p2 (classe périodique)
#   gosper_gun   — croissance non bornée à tuiles répétées (gliders identiques)
#                  — remplaçant documenté du space-filler : le RLE du
#                  space-filler n'est pas sourçable (LifeWiki 403 sur les deux
#                  canaux) et écrire ~150 coordonnées de mémoire invaliderait
#                  le probe en silence ; le gun démontre le même point
#                  théorique : croissance non bornée + motifs répétés
#                  => nouveauté sous-linéaire.
#   r_pentomino  — methuselah (1103 générations de chaos, se stabilise en
#                  débris + gliders) — la transition chaos → stabilité doit
#                  être VISIBLE dans la courbe de nouveauté.
#   acorn        — methuselah long (5206 générations).
#
# Usage : python novelty_probe.py [--checkpoints 0,1,2,4,...,2048]

from __future__ import annotations

import argparse
import time

import hashlife as hl


def decode_rle(rle: str) -> list[tuple[int, int]]:
    """Décode un RLE Life (B3/S23 implicite) en liste de cellules (x, y).

    Les patterns sont embarqués en RLE canonique plutôt qu'en coordonnées
    transcrites : une transcription de mémoire a invalidé silencieusement la
    première version du gun (36 cellules fausses d'une unité — invisible au
    self-check, qui valide la règle, pas l'identité du pattern).
    """
    cells: list[tuple[int, int]] = []
    x = y = 0
    count = ""
    for ch in rle:
        if ch.isdigit():
            count += ch
        elif ch == "b":
            x += int(count) if count else 1
            count = ""
        elif ch == "o":
            n = int(count) if count else 1
            cells.extend((x + i, y) for i in range(n))
            x += n
            count = ""
        elif ch == "$":
            y += int(count) if count else 1
            x = 0
            count = ""
        elif ch == "!":
            break
    return cells


# Patterns canoniques (RLE) : nom -> (classe, description, RLE)
# Vérification d'identité attendue : (population_initiale, période_oscillation,
# croissance_par_période) — un pattern décodé qui ne satisfait pas sa propre
# définition fait échouer le probe avant toute mesure.
PATTERNS: dict[str, tuple[str, str, str, int, int, int]] = {
    "block": (
        "still_life",
        "still life 2x2, stable a toute generation",
        "2o$2o!",
        4, 1, 0,
    ),
    "blinker": (
        "oscillator_p2",
        "oscillateur de periode 2",
        "3o!",
        3, 2, 0,
    ),
    "gosper_gun": (
        "tiled_growth",
        "Gosper glider gun : croissance non bornee, un glider (5 cellules) "
        "par periode de 30 generations",
        "24bo$22bobo$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o"
        "$2o8bo3bob2o4bobo$10bo5bo7bo$11bo3bo$12b2o!",
        36, 30, 5,
    ),
    "r_pentomino": (
        "methuselah",
        "R-pentomino : 5 cellules, 1103 generations de chaos",
        "b2o$2o$bo!",
        5, 0, 0,
    ),
    "acorn": (
        "methuselah",
        "acorn : 7 cellules, 5206 generations",
        "bo$3bo$2o2b3o!",
        7, 0, 0,
    ),
}

SELFCHECK_GENS = 8


def _clear_caches() -> None:
    """Réinitialise les caches de mémoïsation entre patterns.

    Sans cela, un pattern mesuré après un autre bénéficierait de ses nœuds
    déjà construits et le compte de misses n' mesurerait que lui.
    """
    hl.join.cache_clear()
    hl.successor.cache_clear()
    hl.get_zero.cache_clear()


def _population(points: set[tuple[int, int]]) -> int:
    return len(points)


def _normalize(points: set[tuple[int, int]]) -> set[tuple[int, int]]:
    """Recentre un ensemble de cellules sur le coin (0,0) de sa bounding box.

    hashlife (crop/expand) et baseline_life ne partagent pas le même repère
    d'origine : la comparaison exacte est à TRANSLATION près (aucune rotation
    ni réflexion n'est introduite par l'un ou l'autre).
    """
    min_x = min(x for x, _ in points)
    min_y = min(y for _, y in points)
    return {(x - min_x, y - min_y) for x, y in points}


def selfcheck() -> list[str]:
    """Valide substrat ET identité des patterns avant toute mesure.

    Deux étages :
    1. IDENTITÉ — chaque pattern décodé satisfait sa définition : population
       initiale attendue, et pour les patterns périodiques / à croissance,
       pop(t+période) − pop(t) = croissance exactement. C'est ce check qui
       attrape une transcription fabriquée (la v1 du gun : 36 cellules fausses,
       population 21 à t=64 — un soup mort, pas un gun).
    2. RÈGLE — advance() (hashlife) contre baseline_life (règle naïve) sur 8
       générations, ensembles exacts à translation près.
    """
    failures: list[str] = []
    for name, (_cls, _desc, rle, pop0, period, growth) in PATTERNS.items():
        cells = decode_rle(rle)
        _clear_caches()
        node = hl.construct(list(cells))
        if node.n != pop0:
            failures.append(f"{name}: population initiale {node.n} != attendue {pop0}")
            continue
        if period > 0:
            for t_base in (2 * period, 3 * period):
                p1 = hl.advance(hl.construct(list(cells)), t_base).n
                p2 = hl.advance(hl.construct(list(cells)), t_base + period).n
                if p2 - p1 != growth:
                    failures.append(
                        f"{name}: croissance par periode {p2 - p1} != attendue {growth} "
                        f"(pop {t_base}={p1}, pop {t_base + period}={p2})"
                    )
        ref = _normalize(set(cells))
        for t in range(1, SELFCHECK_GENS + 1):
            node = hl.advance(node, 1)
            got = _normalize({(x, y) for x, y, _ in hl.expand(hl.crop(node))})
            ref = _normalize(set(hl.baseline_life(ref)))
            if got != ref:
                failures.append(
                    f"{name}: generation {t} diverge "
                    f"(hashlife {len(got)} cellules, baseline {len(ref)})"
                )
                break
    return failures


def distinct_nodes(node: hl.Node) -> tuple[int, int]:
    """Nombre de nœuds distincts (hors partage) de l'arbre, et niveau racine.

    Chaque sous-arbre structurellement identique est le même objet Python
    (mémoïsation de join) : collecter les id() compte chaque nœud distinct
    une seule fois — la quantité « nœuds distincts de l'arbre de macrocells »
    de l'issue #11162.
    """
    seen: set[int] = set()
    stack = [node]
    while stack:
        n = stack.pop()
        if id(n) in seen:
            continue
        seen.add(id(n))
        if n.k > 0:
            stack.extend([n.a, n.b, n.c, n.d])
    return len(seen), node.k


def loglog_slope(points: list[tuple[int, int]]) -> float:
    """Pente des moindres carrés de log2(y) contre log2(x) (x, y > 0)."""
    pts = [(x, y) for x, y in points if x > 0 and y > 0]
    if len(pts) < 2:
        return 0.0
    import math

    xs = [math.log2(x) for x, _ in pts]
    ys = [math.log2(y) for _, y in pts]
    n = len(xs)
    mx = sum(xs) / n
    my = sum(ys) / n
    var = sum((x - mx) ** 2 for x in xs)
    if var == 0:
        return 0.0
    return sum((xs[i] - mx) * (ys[i] - my) for i in range(n)) / var


def probe(name: str, checkpoints: list[int]) -> dict:
    """Mesure la nouveauté d'un pattern aux checkpoints donnés.

    Rend par checkpoint : génération t, niveau k de la racine, nœuds distincts
    de l'arbre, Δ nœuds nouveaux depuis le checkpoint précédent (nouveauté de
    l'intervalle), Δ misses de join/successor, population, temps mur de
    l'intervalle.
    """
    _cls, _desc, rle, _pop0, _period, _growth = PATTERNS[name]
    cells = decode_rle(rle)
    _clear_caches()
    node = hl.construct(list(cells))
    rows: list[dict] = []
    prev_distinct = 0
    prev_join_misses = 0
    prev_succ_misses = 0
    prev_t = 0
    for t in checkpoints:
        t0 = time.perf_counter()
        if t > prev_t:
            node = hl.advance(node, t - prev_t)
            prev_t = t
        wall_ms = (time.perf_counter() - t0) * 1000.0
        nd, k = distinct_nodes(node)
        jm = hl.join.cache_info().misses
        sm = hl.successor.cache_info().misses
        rows.append(
            {
                "t": t,
                "level": k,
                "distinct": nd,
                "delta_distinct": nd - prev_distinct,
                "delta_join_misses": jm - prev_join_misses,
                "delta_succ_misses": sm - prev_succ_misses,
                "population": node.n,
                "wall_ms": wall_ms,
            }
        )
        prev_distinct, prev_join_misses, prev_succ_misses = nd, jm, sm
    slope = loglog_slope([(r["t"], r["distinct"]) for r in rows])
    return {"name": name, "class": _cls, "rows": rows, "slope": slope}


def render(result: dict) -> str:
    """Table lisible d'un résultat de probe + verdict qualitatif."""
    name, cls, rows, slope = (
        result["name"], result["class"], result["rows"], result["slope"]
    )
    lines = [
        f"== {name} ({cls}) — pente log2(distinct)/log2(t) = {slope:.3f}",
        "      t  level  distinct   d_new  d_join  d_succ  pop      ms",
    ]
    for r in rows:
        lines.append(
            f"{r['t']:>7}  {r['level']:>5}  {r['distinct']:>8}"
            f"  {r['delta_distinct']:>6}  {r['delta_join_misses']:>6}"
            f"  {r['delta_succ_misses']:>6}  {r['population']:>4}"
            f"  {r['wall_ms']:>6.1f}"
        )
    if slope < 0.25:
        verdict = "SUBLINEAIRE — arbre stable, cache-friendly (axe FAST)"
    elif slope < 0.5:
        verdict = "MODEREE — croissance arborescente partielle"
    else:
        verdict = "PERSISTANTE — structures neuves continues (axe SLOW)"
    lines.append(f"   verdict: {verdict}")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Probe de nouveauté hashlife (issue #11162, axe efficacité)"
    )
    parser.add_argument(
        "--checkpoints",
        default="0,1,2,4,8,16,32,64,128,256,512,1024,2048",
        help="liste des générations auxquelles mesurer (défaut : puissances de 2)",
    )
    parser.add_argument(
        "--patterns",
        default=",".join(PATTERNS),
        help="patterns à mesurer (défaut : tous)",
    )
    args = parser.parse_args()
    checkpoints = sorted({int(t) for t in args.checkpoints.split(",")})

    failures = selfcheck()
    if failures:
        for f in failures:
            print(f"SELF-CHECK FAIL: {f}")
        raise SystemExit(1)
    print(f"self-check: advance() == baseline_life() sur {SELFCHECK_GENS} "
          f"generations x {len(PATTERNS)} patterns — OK")

    results = []
    for name in args.patterns.split(","):
        if name not in PATTERNS:
            raise SystemExit(f"pattern inconnu: {name}")
        res = probe(name, checkpoints)
        results.append(res)
        print()
        print(render(res))

    print()
    print("== Table fast/slow (résumé)")
    print("classe            pattern        pente   verdict")
    for res in results:
        v = (
            "FAST"
            if res["slope"] < 0.25
            else "intermediaire"
            if res["slope"] < 0.5
            else "SLOW"
        )
        print(
            f"{res['class']:<16}  {res['name']:<14}  {res['slope']:>5.3f}   {v}"
        )


if __name__ == "__main__":
    main()
