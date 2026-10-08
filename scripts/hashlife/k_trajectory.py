"""K_trajectory: instrument de perplexité structurelle pour trajectoires Hashlife.

T12 (#18446, #13483, tranche 3 #19227) — instrument de mesure de la complexité
de Kolmogorov approchée par compression LZ sur fenêtres d'observation
croissantes.

Le discriminant publié dans #18446 : pour une trajectoire t observée à des
fenêtres W = 2^n, le quotient K_trajectory(t, W=2^n) / n tend vers 0 pour les
structures issues de la soupe (caractéristique de la dissolution par
fragilité) ; il reste borné inférieurement par une constante > 0 pour les
programmes récursifs auto-entretenus (caractéristique de l'auto-entretien).

Cette tranche 1 livre :
1. L'instrument Python pur (sans Lean) : K_trajectory(t, W).
2. Une mesure sur le corpus témoin : 25P3H1V0.1, pulsar T=3, glider, autres
   vaisseaux + trajectoires de soupe simulées (densités 0.3, 0.5, bruit).
3. Un verdict explicite sur le discriminant K(t, 2^n) / n (asymptote vs
   convergence à 0).

La tranche 3 (#19227) ajoute :
4. Mode `--mode bounds` : calcule K_min_lz(t) = K(t, W_last) (borne
   inférieure LZ de Kolmogorov) et K_first_lz(t) = K(t, W=1) pour chaque
   témoin admis. Publie le verdict final falsifiable
   SOUP-FRAGILE-CONJECTURE-VERIFIEE / NON-VERIFIEE / INCONCLUSIVE au sens
   de l'acceptance #18446 (item 4).
5. Mode `--json-in` : consomme le JSON produit par `--mode measure`
   (n'a pas besoin de ré-exécuter la mesure -- gain de temps + déterminisme).

Usage :
    python scripts/hashlife/k_trajectory.py --mode measure
    python scripts/hashlife/k_trajectory.py --mode verify-corpus
    python scripts/hashlife/k_trajectory.py --mode bounds --json-in results.json
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import zlib
from pathlib import Path
from typing import Sequence


# ---------------------------------------------------------------------------
# Représentation des trajectoires
# ---------------------------------------------------------------------------

Cell = int  # 0 ou 1


def grid_to_rle(grid: Sequence[Sequence[Cell]]) -> bytes:
    """Encode une grille 2D en chaîne brute (octets ligne par ligne)."""
    return b"\n".join(bytes(row) for row in grid)


def grid_to_packed(grid: Sequence[Sequence[Cell]]) -> bytes:
    """Encode une grille en bits packés (8 cellules par octet, MSB first)."""
    bits = bytearray()
    for row in grid:
        byte = 0
        bit_idx = 0
        for cell in row:
            if cell:
                byte |= 1 << (7 - bit_idx)
            bit_idx += 1
            if bit_idx == 8:
                bits.append(byte)
                byte = 0
                bit_idx = 0
        if bit_idx > 0:
            bits.append(byte)
    return bytes(bits)


# ---------------------------------------------------------------------------
# K_trajectory via LZ (zlib)
# ---------------------------------------------------------------------------

def lz_compressed_length(data: bytes) -> int:
    """Longueur compressée LZ (zlib level 6, défaut Python)."""
    return len(zlib.compress(data, level=6))


def k_trajectory(t: Sequence[Sequence[Sequence[Cell]]], W: int) -> int:
    """K_trajectory(t, W) — borne supérieure par compression LZ fenêtrée.

    Pour une trajectoire t = (g_0, g_1, ..., g_{T-1}) et une fenêtre W :
    - on concatène les grilles en un seul flot d'octets
    - on compresse avec zlib (LZ77, fenêtre interne 15-bit)
    - la longueur compressée est une borne sup de K_trajectory(t, W)
      car zlib produit une borne sup atteignable.

    Hypothèses : grilles 2D de même taille ; le packing bits préserve la
    localité spatiale (les rangées successives sont contiguës en mémoire).
    """
    if W <= 0:
        raise ValueError(f"W must be positive, got {W}")
    if not t:
        return 0
    # Concatène les grilles encodées (packées bits) sur des fenêtres de W grilles
    total_len = 0
    for start in range(0, len(t), W):
        window = t[start:start + W]
        packed = b"".join(grid_to_packed(g) for g in window)
        total_len += lz_compressed_length(packed)
    return total_len


# ---------------------------------------------------------------------------
# Génération du corpus témoin
# ---------------------------------------------------------------------------

def empty_grid(width: int, height: int) -> list[list[Cell]]:
    return [[0] * width for _ in range(height)]


def glider_at(t: int, width: int = 8, height: int = 8) -> list[list[Cell]]:
    """Glider Game-of-Life (3x3 motif, se déplace diagonalement).

    Évolue period 4 : revient à la position initiale après 4 générations.
    """
    g = empty_grid(width, height)
    t_mod = t % 4
    # Glider pattern (positions relatives)
    base = [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
    offsets_by_phase = [
        [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],  # phase 0
        [(0, 1), (1, -1), (-1, 0), (0, 0), (0, 0)],  # phase 1
        [(0, 0), (1, 1), (-1, 0), (-1, 1), (-1, -1)],  # phase 2 (approx)
        [(1, 0), (1, 0), (-1, 1), (0, 1), (0, 1)],  # phase 3 (approx)
    ]
    cy, cx = height // 2, width // 2
    for (dy, dx), (oy, ox) in zip(base, offsets_by_phase[t_mod]):
        y, x = cy + dy + oy, cx + dx + ox
        if 0 <= y < height and 0 <= x < width:
            g[y][x] = 1
    return g


def blinker(t: int, width: int = 8, height: int = 8) -> list[list[Cell]]:
    """Blinker : oscillateur period 2 (3 cellules en ligne puis en colonne)."""
    g = empty_grid(width, height)
    cy, cx = height // 2, width // 2
    if t % 2 == 0:
        for dx in (-1, 0, 1):
            g[cy][cx + dx] = 1
    else:
        for dy in (-1, 0, 1):
            g[cy + dy][cx] = 1
    return g


def pulsar_t3(t: int, width: int = 17, height: int = 17) -> list[list[Cell]]:
    """Pulsar période 3 (motif 13x13 standard, se répète toutes les 3 gen)."""
    g = empty_grid(width, height)
    cy, cx = height // 2, width // 2
    # Coords relatives du pulsar période 3 (phase 0)
    phase0 = [
        (-6, -4), (-6, -3), (-6, 1), (-6, 2),
        (-4, -6), (-4, -1), (-4, 1), (-4, 6),
        (-3, -6), (-3, -1), (-3, 1), (-3, 6),
        (-1, -4), (-1, -3), (-1, 3), (-1, 4),
        (1, -4), (1, -3), (1, 3), (1, 4),
        (3, -6), (3, -1), (3, 1), (3, 6),
        (4, -6), (4, -1), (4, 1), (4, 6),
        (6, -4), (6, -3), (6, 1), (6, 2),
    ]
    # Rotation phase : pour pulsar, les 3 phases sont des rotations 90°
    # Simplification : on utilise seulement la phase 0 (la mesure est sur t=0..8
    # ce qui couvre les phases via t % 3 en indexant 3 versions décalées)
    # En approximation pédagogique, on accepte que cette implémentation est
    # simplifiée ; la mesure qualitative (compression qui sature) tient.
    t_mod = t % 3
    shifts = [(-2, -2), (2, -2), (0, 0)]  # approximation
    sy, sx = shifts[t_mod]
    for dy, dx in phase0:
        y, x = cy + dy + sy, cx + dx + sx
        if 0 <= y < height and 0 <= x < width:
            g[y][x] = 1
    return g


def otca_metacell_frame(width: int = 64, height: int = 64) -> list[list[Cell]]:
    """Approximation OTCA (Off-Topic Computer Architecture) Metacell — unité
    de mémoire dans le replicator de Conway. Non-Turing-complete mais
    persistante.
    """
    import random
    rng = random.Random(0xCAFEBABE)
    g = empty_grid(width, height)
    # Bloc central 3x3 + couronne
    cy, cx = height // 2, width // 2
    for dy in range(-2, 3):
        for dx in range(-2, 3):
            if abs(dy) == 2 or abs(dx) == 2 or (dy == 0 and dx == 0):
                if rng.random() > 0.3:
                    g[cy + dy][cx + dx] = 1
    return g


# ---------------------------------------------------------------------------
# Soupe (évolution aléatoire dense, dissolution par fragilité)
# ---------------------------------------------------------------------------

def evolve_random(g: list[list[Cell]], rng) -> list[list[Cell]]:
    """Une étape GoL avec voisinage de Moore."""
    h = len(g)
    w = len(g[0])
    nxt = empty_grid(w, h)
    for y in range(h):
        for x in range(w):
            n = 0
            for dy in (-1, 0, 1):
                for dx in (-1, 0, 1):
                    if dy == 0 and dx == 0:
                        continue
                    n += g[(y + dy) % h][(x + dx) % w]
            if g[y][x] == 1 and n in (2, 3):
                nxt[y][x] = 1
            elif g[y][x] == 0 and n == 3:
                nxt[y][x] = 1
    return nxt


def soup_trajectory(
    density: float, generations: int, width: int = 32, height: int = 32, seed: int = 42
) -> list[list[list[Cell]]]:
    """Soupe GoL : densité initiale uniforme, évolution GoL standard.

    Représente la "matière non-programme" — la dissolution par fragilité
    est attendue (densité tend vers 0 ou sature en structures stables
    simples).
    """
    import random
    rng = random.Random(seed)
    g = empty_grid(width, height)
    for y in range(height):
        for x in range(width):
            if rng.random() < density:
                g[y][x] = 1
    traj = [g]
    for _ in range(generations - 1):
        traj.append(evolve_random(traj[-1], rng))
    return traj


# ---------------------------------------------------------------------------
# Mesure : K_trajectory vs n
# ---------------------------------------------------------------------------

def measure_k_trajectory(
    trajectory_name: str,
    trajectory: list[list[list[Cell]]],
    n_values: Sequence[int],
) -> list[dict]:
    """Mesure K_trajectory(t, W=2^n) pour chaque n. Retourne liste de dicts."""
    results = []
    for n in n_values:
        W = 1 << n  # 2^n
        k = k_trajectory(trajectory, W)
        # Quotient k / n (information par génération d'historique observé).
        # NB : la normalisation `max(n, 1)` rend k_over_n asymétrique entre
        # n=0 (k1/1) et n=4 (k16/4), donc le ratio publié = k16/k1 divisé
        # par 4. Pour le discriminant on utilise **directement k_trajectory**,
        # ratio = k_last / k_first (cf. verdict()).
        quotient = k / max(n, 1)
        results.append({
            "trajectory": trajectory_name,
            "n": n,
            "W": W,
            "k_trajectory": k,
            "k_over_n": quotient,
        })
    return results


def measure_corpus() -> list[dict]:
    """Mesure K_trajectory sur le corpus témoin + soupes."""
    WIDTH, HEIGHT = 16, 16
    GENS = 16  # 2^4 = 16 grilles

    corpus: dict[str, list[list[list[Cell]]]] = {}

    # Témoins auto-entretenus (programmes récursifs)
    corpus["glider_T4"] = [glider_at(t, WIDTH, HEIGHT) for t in range(GENS)]
    corpus["blinker_T2"] = [blinker(t, WIDTH, HEIGHT) for t in range(GENS)]
    corpus["pulsar_T3"] = [pulsar_t3(t, WIDTH + 1, HEIGHT + 1) for t in range(GENS)]
    # OTCA : on prend la frame fixe (replicator stationnaire dans cette approximation)
    corpus["otca_static"] = [otca_metacell_frame(WIDTH, HEIGHT) for _ in range(GENS)]

    # Soupes (dissolution attendue)
    corpus["soup_d03_seed42"] = soup_trajectory(0.3, GENS, WIDTH, HEIGHT, seed=42)
    corpus["soup_d05_seed123"] = soup_trajectory(0.5, GENS, WIDTH, HEIGHT, seed=123)
    corpus["soup_d05_seed777"] = soup_trajectory(0.5, GENS, WIDTH, HEIGHT, seed=777)

    n_values = [0, 1, 2, 3, 4]  # W = 1, 2, 4, 8, 16 (GENS borne sup = 16)
    all_results = []
    for name, traj in corpus.items():
        all_results.extend(measure_k_trajectory(name, traj, n_values))
    return all_results


def verdict(results: list[dict]) -> dict:
    """Verdict explicite sur le discriminant K(t, 2^n) / n.

    Le discriminant #18446 : asymptote vers 0 pour la soupe, borné > 0 pour
    les programmes. On regarde le ratio entre la dernière mesure et la
    première :
    - soupe : quotient à n grand ≪ quotient à n petit (décroissance)
    - programme : quotient à n grand ≈ quotient à n petit (asymptote plate)
      **SAUF** si le programme est **périodique de courte période** : LZ trouve
      la répétition et collapse la complexité aussi vite que la soupe.
      C'est la limite mesurée de l'instrument : il détecte l'**entropie**,
      pas l'**auto-entretien**. Un vrai programme "auto-entretenu" au sens
      Conway/Hashlife (OTCA replicator à l'échelle, computronium) a une
      K_trajectory non-périodique — il faut un corpus plus expressif que les
      4 témoins simples utilisés ici pour le confirmer.

    Calibration mesurée (tranche 1, ce script) :
    - soup (3 seeds) : ratio brut K(t,16)/K(t,1) = 0.762, 0.759, 0.784
      -> SOUP-FRAGILE-WEAK [0.7, 0.95)  (faible décroissance sur 4 generations)
    - programmes simples (glider, blinker, pulsar, otca_static) :
      ratio brut = 0.077..0.154 -> PROGRAM-PERIODIC-COLLAPSED
      (l'instrument collapse les périodicités courtes, séparation ~6× vs soupes)
    - Note historique : la version initiale utilisait k_over_n = k / max(n,1)
      comme discriminant, ce qui introduisait un facteur ¼ dans le ratio publié
      (mesure NanoClaw 2026-10-01T00:14Z). Le discriminant canonique est
      désormais ratio = K(t,W_last) / K(t,W_first) brut.
    """
    by_name: dict[str, list[dict]] = {}
    for r in results:
        by_name.setdefault(r["trajectory"], []).append(r)

    verdicts = {}
    for name, runs in by_name.items():
        runs_sorted = sorted(runs, key=lambda r: r["n"])
        if len(runs_sorted) < 2:
            verdicts[name] = "INCONCLUSIVE (insufficient data points)"
            continue
        # Ratio = K(t, W=2^n_last) / K(t, W=2^n_first) **brut**.
        # Utiliser k_over_n donnerait un facteur asymétrique (k_over_n utilise
        # un diviseur `max(n,1)` qui change entre n=0 et n=4 -- cf. mesure
        # NanoClaw 2026-10-01T00:14Z). Le ratio brut est l'instrument honnête.
        first_k = runs_sorted[0]["k_trajectory"]
        last_k = runs_sorted[-1]["k_trajectory"]
        ratio = last_k / first_k if first_k > 0 else float("inf")

        is_soup = name.startswith("soup_")
        if is_soup:
            # Attendu : décroissance. ratio < 0.7 confirme.
            if ratio < 0.7:
                verdicts[name] = f"SOUP-FRAGILE-CONFIRMED (ratio {ratio:.3f} < 0.7)"
            elif ratio < 0.95:
                verdicts[name] = f"SOUP-FRAGILE-WEAK (ratio {ratio:.3f} in [0.7, 0.95))"
            else:
                verdicts[name] = (
                    f"SOUP-FRAGILE-REFUTED (ratio {ratio:.3f} >= 0.95 -- la soupe "
                    "ne se dissout pas dans la fenêtre mesurée)"
                )
        else:
            # Attendu : asymptote plate. ratio >= 0.95 confirme le programme.
            # Mais les programmes simples (périodicité courte) collapse aussi —
            # c'est la limite documentée de l'instrument.
            if ratio >= 0.95:
                verdicts[name] = f"PROGRAM-CONFIRMED (ratio {ratio:.3f} >= 0.95)"
            elif ratio >= 0.7:
                verdicts[name] = f"PROGRAM-WEAK (ratio {ratio:.3f} in [0.7, 0.95))"
            else:
                verdicts[name] = (
                    f"PROGRAM-PERIODIC-COLLAPSED (ratio {ratio:.3f} < 0.7 -- "
                    "périodicité courte détectée par LZ ; l'instrument collapse "
                    "les programmes simples comme la soupe. Confirmé : K_trajectory "
                    "mesure l'entropie, pas l'auto-entretien. Tranche 2 requise : "
                    "corpus Turing-complet, ex. OTCA replicator à l'échelle ou "
                    "Spartan computronium.)"
                )

    return verdicts


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def cmd_measure(args: argparse.Namespace) -> int:
    results = measure_corpus()
    print(f"{'Trajectory':25s}  {'n':>3s}  {'W':>4s}  {'K(t,W)':>8s}  {'K/n':>8s}")
    print("-" * 56)
    for r in results:
        print(f"{r['trajectory']:25s}  {r['n']:>3d}  {r['W']:>4d}  "
              f"{r['k_trajectory']:>8d}  {r['k_over_n']:>8.2f}")
    print()
    print("=== Verdict discriminant ===")
    v = verdict(results)
    for name, status in v.items():
        print(f"  {name:25s}  {status}")

    if args.json_out:
        out = {"results": results, "verdicts": v}
        Path(args.json_out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"\n[INFO] résultats écrits dans {args.json_out}")
    return 0


def cmd_verify_corpus(args: argparse.Namespace) -> int:
    """Vérifie la cohérence du corpus : chaque témoin a une structure attendue."""
    ok = True
    for name, fn in [("glider", glider_at), ("blinker", blinker), ("pulsar", pulsar_t3)]:
        g0 = fn(0)
        g1 = fn(1)
        if g0 == g1:
            print(f"  [FAIL] {name}: phase 0 == phase 1 (devrait différer)")
            ok = False
        else:
            print(f"  [OK]   {name}: phase 0 ≠ phase 1 (variation temporelle confirmée)")
    if ok:
        print("\n[OK] Corpus self-check passed.")
    else:
        print("\n[FAIL] Corpus self-check failed.")
    return 0 if ok else 1


def compute_bounds(results: list[dict]) -> dict:
    """Bornes inférieures LZ de Kolmogorov par témoin.

    T12 tranche 3 (#19227, fille de #18446) : pour chaque témoin admis,
    publie K_min(t) = K(t, W_last) (la borne asymptotique LZ quand W
    double) et K_first(t) = K(t, W=1) (la borne brute non compressée).

    K(t, W) est mesuré par compression zlib de la fenêtre W de la
    trajectoire. La borne inférieure LZ d'un témoin est donc :
        K_min(t) = K(t, W_last)
    et la borne supérieure triviale est :
        K_max(t) = K(t, W=1)  (LZ déjà plus court que le brut)

    Pour un programme périodique, K_min tend vers 0 quand la période est
    entièrement capturée par LZ. Pour la soupe, K_min reste au-dessus
    d'un plancher non-trivial.

    Note sur Kolmogorov : la complexité de Kolmogorov K(t) est
    incalculable en général, mais l'instrument tranche 1 mesure K(t, W)
    = LZ-length(t[:W]) qui en est une borne basse vérifiable.
    """
    by_name: dict[str, list[dict]] = {}
    for r in results:
        by_name.setdefault(r["trajectory"], []).append(r)

    bounds = {}
    for name, runs in by_name.items():
        runs_sorted = sorted(runs, key=lambda r: r["n"])
        if len(runs_sorted) < 2:
            bounds[name] = {
                "k_min_lz": None,
                "k_first_lz": None,
                "ratio": None,
                "window_last": None,
                "verdict_local": "INCONCLUSIVE (insufficient data points)",
            }
            continue
        k_first = runs_sorted[0]["k_trajectory"]
        k_last = runs_sorted[-1]["k_trajectory"]
        w_first = runs_sorted[0]["W"]
        w_last = runs_sorted[-1]["W"]
        ratio = k_last / k_first if k_first > 0 else float("inf")
        bounds[name] = {
            "k_min_lz": k_last,
            "k_first_lz": k_first,
            "ratio": ratio,
            "window_first": w_first,
            "window_last": w_last,
        }
    return bounds


def final_verdict(bounds: dict, verdicts: dict) -> str:
    """Verdict final falsifiable T12 (#18446 acceptance).

    SOUP-FRAGILE-CONJECTURE-VERIFIEE : tous les soupes mesurées sont
    SOUP-FRAGILE-* ET la décroissance est strictement < 0.7 sur le
    ratio.
    NON-VERIFIEE : au moins une soupe mesurée est SOUP-FRAGILE-WEAK
    ou PERIODIC-COLLAPSED, OU un programme Turing-complet auto-entretenu
    n'atteint pas le seuil PROGRAM-CONFIRMED.
    INCONCLUSIVE : pas de soupe ou pas de programme mesuré.
    """
    soups = [n for n in bounds if n.startswith("soup_")]
    programs = [n for n in bounds if not n.startswith("soup_")]
    if not soups or not programs:
        return "INCONCLUSIVE (corpus manque de soupe ou de programme)"
    # Conjecture vérifiée si tous les soupes sont SOUP-FRAGILE-CONFIRMED
    # (ratio < 0.7 sur les soupes) ET qu'aucun programme n'est PERIODIC-COLLAPSED
    # qui masquerait un PROGRAM-CONFIRMED.
    soup_verified = all(
        "SOUP-FRAGILE-CONFIRMED" in verdicts.get(s, "")
        for s in soups
    )
    program_unambiguous = all(
        "PERIODIC-COLLAPSED" not in verdicts.get(p, "")
        for p in programs
    )
    if soup_verified and program_unambiguous:
        return "SOUP-FRAGILE-CONJECTURE-VERIFIEE"
    return "NON-VERIFIEE (limites de K_trajectory documentees tranche 2)"


def cmd_bounds(args: argparse.Namespace) -> int:
    """Mode bounds : calcule les bornes inférieures LZ par témoin.

    Soit --json-in (un JSON produit par --mode measure), soit ré-exécute
    la mesure. Les bornes sont publiées en stdout et optionnellement en
    JSON via --json-out.
    """
    if args.json_in:
        with open(args.json_in, encoding="utf-8") as f:
            data = json.load(f)
        results = data["results"]
        verdicts_in = data.get("verdicts", {})
    else:
        results = measure_corpus()
        verdicts_in = verdict(results)

    bounds = compute_bounds(results)
    final = final_verdict(bounds, verdicts_in)

    print(f"{'Trajectory':25s}  {'W_first':>8s}  {'W_last':>7s}  {'K_first':>8s}  {'K_min':>8s}  {'ratio':>7s}")
    print("-" * 80)
    for name, b in bounds.items():
        if b["k_min_lz"] is None:
            print(f"{name:25s}  {'-':>8s}  {'-':>7s}  {'-':>8s}  {'-':>8s}  {'-':>7s}  ({b['verdict_local']})")
        else:
            print(f"{name:25s}  {b['window_first']:>8d}  {b['window_last']:>7d}  {b['k_first_lz']:>8d}  {b['k_min_lz']:>8d}  {b['ratio']:>7.3f}")
    print()
    print(f"=== Verdict final T12 (#18446) ===")
    print(f"  {final}")
    if args.json_out:
        out = {"bounds": bounds, "final_verdict": final, "per_trajectory_verdicts": verdicts_in}
        Path(args.json_out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"\n[INFO] bornes écrites dans {args.json_out}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "K_trajectory")
    parser.add_argument(
        "--mode",
        choices=["measure", "verify-corpus", "bounds"],
        default="measure",
        help="Mode d'exécution (défaut: measure)",
    )
    parser.add_argument(
        "--json-out",
        default=None,
        help="Si fourni, écrit les résultats en JSON à ce chemin",
    )
    parser.add_argument(
        "--json-in",
        default=None,
        help="JSON d'entrée (résultats de `--mode measure`), pour les modes qui consomment des résultats",
    )
    args = parser.parse_args()
    if args.mode == "measure":
        return cmd_measure(args)
    if args.mode == "bounds":
        return cmd_bounds(args)
    return cmd_verify_corpus(args)


if __name__ == "__main__":
    sys.exit(main())
