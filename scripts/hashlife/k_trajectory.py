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

Tranche Origami pli 3 (#19742, EPIC Origami Wolfram) ajoute :
6. Mode `--mode wolfram` : mesure K_trajectory sur les automates 1-D de
   Wolfram (Rule 30 chaotique, Rule 110 Turing-complet). Génère la
   trajectoire via `ict.wolfram_step.wolfram_trajectory` (organe pli 2
   PR #19793) ; convertit chaque état 1-D en ligne 1×N compatible avec
   `grid_to_packed` ; mesure le discriminant cross-dimension 1-D / 2-D.
   Hypothèse initiale (invalidée par la mesure, cf. WOLFRAM-VERDICT.md) :
   Rule 30 ~ fragile-LZ, Rule 110 ~ incompressible. Mesure à n_cells >= 512 :
   l'instrument discrimine les deux règles, mais dans le sens INVERSÉ —
   le chaos (Rule 30) est incompressible, la structure Turing-complète
   (Rule 110) est compressible. À n_cells = 64 l'instrument est saturé par
   le cadrage zlib (~11 octets/fenêtre vs 8 octets d'état) : toute
   discrimination y est un artefact.

Tranche Origami pli 4 (#19766, EPIC Origami Wolfram) ajoute :
7. Mode `--mode wolfram-4classes` : mesure K_trajectory sur les 4 classes
   canoniques de Wolframe (0/I, 4/II, 30/III, 110/IV). Même organe, même
   plancher de mesure concluante (n_cells >= 512, cf. WOLFRAM_MIN_N_CELLS) :
   sous ce seuil, `wolfram_class_verdict` rend SATURATED et le verdict
   cross-classes est INCONCLUSIVE. Cf. WOLFRAM-VERDICT-CROSS-CLASSES.md.

Usage :
    python scripts/hashlife/k_trajectory.py --mode measure
    python scripts/hashlife/k_trajectory.py --mode verify-corpus
    python scripts/hashlife/k_trajectory.py --mode bounds --json-in results.json
    python scripts/hashlife/k_trajectory.py --mode wolfram --rule 30 --n-cells 1024
    python scripts/hashlife/k_trajectory.py --mode wolfram --all
    python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 1024
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


# ---------------------------------------------------------------------------
# Mode Wolfram (Origami pli 3, EPIC #19742 / PR pli 2 #19793)
# ---------------------------------------------------------------------------


def wolfram_trajectory_to_grid(traj: Sequence[Sequence[Cell]]) -> list[list[list[Cell]]]:
    """Convertit une trajectoire 1-D Wolframe en liste de grilles 1×N.

    Chaque état (vecteur 1-D de cellules) devient une grille 1×N : une
    seule ligne, N colonnes. Cette forme est compatible avec
    `grid_to_packed` (packing bits, 8 cellules/octet, MSB first).

    Hypothèse : `traj[i]` est une séquence de Cell (= 0 ou 1), de longueur
    fixe N pour tous les i. Si N n'est pas multiple de 8, le dernier
    octet est complété par des zéros (cf. `grid_to_packed`).
    """
    return [[list(state)] for state in traj]


def measure_wolfram_trajectory(
    rule: int,
    n_cells: int,
    n_steps: int,
    seed: int,
    n_values: Sequence[int],
) -> list[dict]:
    """Mesure K_trajectory sur la trajectoire Wolframe d'une règle.

    Génère la trajectoire via `ict.wolfram_step.wolfram_trajectory`,
    convertit en grilles 1×N, et mesure K(t, W=2^n) pour chaque n dans
    `n_values`.

    NB : la trajectoire 1-D est "naturellement" compatible avec l'instrument
    LZ fenêtré (les états successifs sont contigus en mémoire après
    packing). Pas de réimplémentation de la mesure -- seul l'organe
    `ict.wolfram_step` est invoqué.
    """
    try:
        from ict.wolfram_step import wolfram_trajectory  # pli 2 PR #19793
    except ImportError as e:
        raise RuntimeError(
            "ict.wolfram_step introuvable. L'organe (PR #19793) doit être "
            "présent dans MyIA.AI.Notebooks/IIT/ICT-Series/ict/wolfram_step.py "
            f"et ce dossier doit être dans sys.path. Erreur: {e}"
        )

    traj_1d = wolfram_trajectory(
        rule=rule, n_cells=n_cells, n_steps=n_steps, seed=seed, record_densities=False
    )
    traj_grid = wolfram_trajectory_to_grid(traj_1d)
    rows = measure_k_trajectory(f"wolfram_R{rule}_n{n_cells}_seed{seed}", traj_grid, n_values)
    # Metadonnees de cadrage pour un verdict sans artefact zlib : taille brute
    # packee de la trajectoire et n_cells. Le verdict classe sur la fraction
    # de compression K/raw (insensible au plancher de cadrage ~11 octets par
    # fenetre), pas sur le ratio brut (cf. wolfram_verdict).
    raw_packed_bytes = n_steps * ((n_cells + 7) // 8)
    for r in rows:
        r["n_cells"] = n_cells
        r["raw_packed_bytes"] = raw_packed_bytes
    return rows


def measure_wolfram_corpus(n_cells: int = 1024, n_steps: int | None = None, seed: int = 33) -> list[dict]:
    """Mesure K_trajectory sur le corpus Wolframe (Rule 30 + Rule 110).

    Règles canoniques :
    - Rule 30 (classe III, chaotique) -- mesuré INCOMPRESSIBLE à n >= 512 :
      le chaos porte une entropie proche du maximum, aucune fenêtre ne
      compresse (le collapse LZ de la soupe 2-D ne transfère pas au 1-D).
    - Rule 110 (classe IV, Turing-complet) -- mesuré STRUCTURED-COMPRESSIBLE :
      son fond périodique + particules sont réguliers, donc LZ-compressibles.
      L'instrument mesure la régularité, pas la Turing-complétude.

    Paramètres :
    - n_cells=1024 : taille canonique de la mesure committée
      (wolfram_results.json). Plancher documenté : 512 -- en dessous,
      chaque état packé tient sous le plancher de cadrage zlib (~11 octets
      par fenêtre) et Rule 30 / Rule 110 mesurent identiques à l'octet
      près (zone saturée, verdict SATURATED).
    - n_steps : nombre d'états ; par défaut aligné sur n_cells par
      cmd_wolfram (fenêtre max W=64).
    - seed=33 : reproductibilité (cf. PR #19793).
    """
    n_values = [0, 1, 2, 3, 4, 5, 6]  # W = 1, 2, 4, 8, 16, 32, 64 (borne n_steps)
    if n_steps is None:
        n_steps = n_cells
    all_results = []
    for rule in (30, 110):
        all_results.extend(
            measure_wolfram_trajectory(
                rule=rule, n_cells=n_cells, n_steps=n_steps, seed=seed, n_values=n_values
            )
        )
    return all_results


def wolfram_verdict(results: list[dict]) -> dict:
    """Verdict cross-règles pour les trajectoires Wolframe, hors zone de saturation.

    Le classement s'appuie sur la **fraction de compression** à la fenêtre max :

        frac = K(t, W_last) / raw_packed_bytes

    où raw_packed_bytes = n_steps * ceil(n_cells / 8) (métadonnée posée par
    `measure_wolfram_trajectory`). Cette grandeur est insensible au plancher
    de cadrage zlib (~11 octets par fenêtre : en-tête + bloc stocké), contrairement
    au ratio brut K(W_last)/K(W_first) qui, pour un contenu incompressible,
    vaut mécaniquement (c + 11/W_last) / (c + 11) avec c = ceil(n_cells/8) --
    une constante de cadrage, pas un signal (mesuré : Rule 30 à n=1024 rend
    ratio 0.922 = exactement cette arithmétique, K(W=1)/état = 139.00 = 128+11).

    Zone de saturation : à n_cells = 64, chaque état packé ne porte que 8 octets,
    sous le plancher de cadrage zlib ; Rule 30 et Rule 110 y mesurent identiques
    à l'octet près (1026 -> 523 toutes les deux, cf. JSON n=64 historique).
    Tout verdict de discrimination fabriqué à cette taille est un artefact.
    Plancher documenté : n_cells >= 512 (64 octets d'état vs 11 de cadrage).

    Classification à n_cells >= 512 (frac à W_last) :
    - frac >= 0.98 : INCOMPRESSIBLE -- chaque fenêtre au plafond d'entropie.
    - frac <= 0.70 : COMPRESSIBLE -- structure régulière trouvée par LZ.
    - sinon : WEAK.
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
        first_k = runs_sorted[0]["k_trajectory"]
        last_k = runs_sorted[-1]["k_trajectory"]
        ratio = last_k / first_k if first_k > 0 else float("inf")
        n_cells = runs_sorted[0].get("n_cells")
        raw = runs_sorted[0].get("raw_packed_bytes")

        if not n_cells or not raw:
            verdicts[name] = f"INCONCLUSIVE (metadonnees de cadrage absentes, ratio {ratio:.3f})"
            continue
        content_bytes = (n_cells + 7) // 8
        if n_cells < 512:
            verdicts[name] = (
                f"WOLFRAM-SATURATED (n_cells={n_cells} : {content_bytes} octets/etat sous le "
                f"plancher de cadrage zlib ~11 octets/fenetre ; Rule 30 et Rule 110 y sont "
                f"identiques a l'octet pres, ratio {ratio:.3f} non concluant ; n_cells >= 512 requis)"
            )
            continue
        frac = last_k / raw

        if "R30" in name:
            if frac >= 0.98:
                verdicts[name] = (
                    f"WOLFRAM-CHAOTIC-INCOMPRESSIBLE (frac {frac:.3f} >= 0.98 -- le chaos "
                    "classe III porte une entropie proche du maximum : aucune fenetre ne "
                    "compresse ; le collapse LZ observe sur la soupe 2-D ne transfere pas au 1-D)"
                )
            elif frac <= 0.70:
                verdicts[name] = f"WOLFRAM-CHAOTIC-COMPRESSIBLE (frac {frac:.3f} <= 0.70 -- collapse LZ du chaos, discriminant soupe)"
            else:
                verdicts[name] = f"WOLFRAM-WEAK (frac {frac:.3f} in (0.70, 0.98))"
        elif "R110" in name:
            if frac <= 0.70:
                verdicts[name] = (
                    f"WOLFRAM-TURING-STRUCTURED-COMPRESSIBLE (frac {frac:.3f} <= 0.70 -- la "
                    "structure emergente de Rule 110 (fond periodique + particules) est "
                    "reguliere, donc LZ-compressible ; l'instrument mesure la regularite, "
                    "pas la Turing-completude)"
                )
            elif frac >= 0.98:
                verdicts[name] = f"WOLFRAM-TURING-INCOMPRESSIBLE (frac {frac:.3f} >= 0.98 -- auto-entretien LZ-confirme)"
            else:
                verdicts[name] = f"WOLFRAM-WEAK (frac {frac:.3f} in (0.70, 0.98))"
        else:
            verdicts[name] = f"INCONCLUSIVE (regle inconnue, frac {frac:.3f})"

    return verdicts


def wolfram_cross_verdict(wv: dict) -> str:
    """Verdict final cross-règles Wolframe.

    Hypothèse d'origine (transfert du discriminant soupe 2-D au 1-D) :
    CONFIRMED = Rule 30 CHAOTIC-COMPRESSIBLE + Rule 110 TURING-INCOMPRESSIBLE.

    Mesure à n_cells >= 512 (seed 33) : la discrimination entre les deux règles
    est RÉELLE, mais la direction est INVERSÉE -- Rule 30 (chaos) incompressible,
    Rule 110 (Turing-complet) compressible -- d'où REFUTED. Une mesure en zone
    saturée (n_cells < 512) rend INCONCLUSIVE : l'instrument n'y voit que son
    propre cadrage.
    """
    r30_keys = [n for n in wv if "R30" in n]
    r110_keys = [n for n in wv if "R110" in n]
    r30_compressible = any("CHAOTIC-COMPRESSIBLE" in wv[k] for k in r30_keys)
    r110_incompressible = any("TURING-INCOMPRESSIBLE" in wv[k] for k in r110_keys)
    r30_incompressible = any("CHAOTIC-INCOMPRESSIBLE" in wv[k] for k in r30_keys)
    r110_compressible = any("STRUCTURED-COMPRESSIBLE" in wv[k] for k in r110_keys)
    saturated = any("SATURATED" in wv[k] for k in r30_keys + r110_keys)

    if saturated:
        return "WOLFRAM-CROSS-DIMENSION-INCONCLUSIVE"
    if r30_compressible and r110_incompressible:
        return "WOLFRAM-CROSS-DIMENSION-CONFIRMED"
    if r30_incompressible and r110_compressible:
        return "WOLFRAM-CROSS-DIMENSION-REFUTED"
    if r30_compressible or r110_incompressible:
        return "WOLFRAM-CROSS-DIMENSION-PARTIAL"
    return "WOLFRAM-CROSS-DIMENSION-INCONCLUSIVE"


def cmd_wolfram(args: argparse.Namespace) -> int:
    """Mode wolfram : mesure K_trajectory sur automates 1-D Wolframe.

    Soit `--rule <int> --n-cells <int>` (mesure d'une règle unique), soit
    `--all` (Rule 30 + Rule 110 par défaut).
    """
    n_values = [0, 1, 2, 3, 4, 5, 6]
    if args.all:
        results = measure_wolfram_corpus(
            n_cells=args.n_cells, n_steps=args.n_cells, seed=args.seed
        )
    else:
        results = measure_wolfram_trajectory(
            rule=args.rule,
            n_cells=args.n_cells,
            n_steps=args.n_cells,
            seed=args.seed,
            n_values=n_values,
        )

    print(f"{'Trajectory':35s}  {'n':>3s}  {'W':>4s}  {'K(t,W)':>8s}  {'K/n':>8s}")
    print("-" * 70)
    for r in results:
        print(
            f"{r['trajectory']:35s}  {r['n']:>3d}  {r['W']:>4d}  "
            f"{r['k_trajectory']:>8d}  {r['k_over_n']:>8.2f}"
        )
    print()
    print("=== Verdict Wolframe par regle ===")
    wv = wolfram_verdict(results)
    for name, status in wv.items():
        print(f"  {name:35s}  {status}")
    print()
    final = wolfram_cross_verdict(wv)
    print(f"=== Verdict final cross-regles ===")
    print(f"  {final}")

    if args.json_out:
        out = {
            "results": results,
            "per_rule_verdicts": wv,
            "cross_verdict": final,
            "n_cells": args.n_cells,
            "n_steps": args.n_cells,
            "seed": args.seed,
        }
        Path(args.json_out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"\n[INFO] resultats ecrits dans {args.json_out}")
    return 0


"""Extension pli 4 cross-classes pour k_trajectory.py -- a inserer apres wolfram_cross_verdict()."""

# ---------------- Pli 4 : cross-classes 4 regles ----------------


# Seuils partages avec wolfram_verdict()
_FRAGILE = 0.7
_ENTRENED = 0.95

# Plancher de mesure concluante pour l'automate 1-D : sous n_cells = 512, la
# fenetre packee reste sous le plancher de cadrage zlib, toutes les regles
# rendent la meme constante et la classification ne mesure plus le contenu.
# Mesure 2026-10-09 : a n_cells = 64, R30 et R110 rendent un ratio identique
# de 0.510 (K(W=1) = 1026, K(W=64) = 523 = 512 + 11).
WOLFRAM_MIN_N_CELLS = 512


WOLFRAM_CLASS_MAP = {
    0: ("I", "uniforme"),
    4: ("II", "periodique"),
    30: ("III", "chaotique"),
    110: ("IV", "Turing-complet"),
}


def measure_wolfram_4classes(
    n_cells: int = 64, n_steps: int = 64, seed: int = 33
) -> list[dict]:
    """Mesure K_trajectory sur les 4 classes canoniques de Wolframe.

    Regles : 0 (I, uniforme), 4 (II, periodique), 30 (III, chaotique),
    110 (IV, Turing-complet). Le verdict attendu :

    - I/II (R0/R4) : COLLAPSED (LZ capture la structure simple).
    - III/IV (R30/R110) : WEAK-COLLAPSE ou ENTROPIE PARTIELLE.

    Si la discrimination fine III vs IV emerge (ratio R30 != ratio R110
    au-dela du bruit), c'est un resultat falsifiable positif. Sinon, le
    discriminant K_trajectory est confirme comme insuffisant pour
    discriminer Turing vs chaos 1-D (cf. WOLFRAM-VERDICT-CROSS-CLASSES.md).
    """
    n_values = [0, 1, 2, 3, 4, 5, 6]  # W = 1, 2, 4, 8, 16, 32, 64
    all_results = []
    for rule in (0, 4, 30, 110):
        all_results.extend(
            measure_wolfram_trajectory(
                rule=rule,
                n_cells=n_cells,
                n_steps=n_steps,
                seed=seed,
                n_values=n_values,
            )
        )
    return all_results


def wolfram_class_verdict(results: list[dict]) -> dict:
    """Verdict par regle, calibre pour les 4 classes Wolframe.

    Pour chaque regle, calcule le ratio K(t, W_last) / K(t, W_first) et
    classifie en utilisant les conventions de WOLFRAM :

    - WOLFRAM-COLLAPSED : ratio < _FRAGILE (LZ collapse : I/II attendu).
    - WOLFRAM-WEAK-COLLAPSE : _FRAGILE <= ratio < _ENTRENED
      (entropie partielle, III/IV attendu).
    - WOLFRAM-ENTRENED : ratio >= _ENTRENED
      (LZ ne collapse pas, entropie maximale).

    Cas particuliers :
    - Si rule in {0, 4} et verdict WOLFRAM-ENTRENED : VERDICT-REFUTED
      (les classes I/II doivent collapse ; non-collapse contredit la
      classification Wolframe).
    - Si rule in {30, 110} et verdict WOLFRAM-COLLAPSED : VERDICT-REFUTED
      (les classes III/IV ne doivent pas collapse ; ce serait un signal
      qu'on n'instrumente pas correctement le regime attendu).
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
        first_k = runs_sorted[0]["k_trajectory"]
        last_k = runs_sorted[-1]["k_trajectory"]
        ratio = last_k / first_k if first_k > 0 else float("inf")

        # Identifier la regle depuis le nom (format: wolfram_R<N>_n<NC>_seed<S>)
        try:
            rule = int(name.split("_R")[1].split("_")[0])
        except (IndexError, ValueError):
            verdicts[name] = f"INCONCLUSIVE (parse fail, ratio {ratio:.3f})"
            continue

        try:
            n_cells = int(name.split("_n")[1].split("_")[0])
        except (IndexError, ValueError):
            n_cells = None

        if n_cells is not None and n_cells < WOLFRAM_MIN_N_CELLS:
            verdicts[name] = (
                f"WOLFRAM-SATURATED (n_cells={n_cells} < {WOLFRAM_MIN_N_CELLS} : "
                f"la fenetre packee est sous le plancher de cadrage zlib, "
                f"ratio {ratio:.3f} mesure le cadrage, pas le contenu)"
            )
            continue

        klass = WOLFRAM_CLASS_MAP.get(rule)
        if klass is None:
            verdicts[name] = f"INCONCLUSIVE (regle {rule} hors 4 classes, ratio {ratio:.3f})"
            continue

        klass_label, klass_name = klass
        if ratio < _FRAGILE:
            raw = f"WOLFRAM-COLLAPSED (ratio {ratio:.3f} < {_FRAGILE})"
        elif ratio < _ENTRENED:
            raw = f"WOLFRAM-WEAK-COLLAPSE (ratio {ratio:.3f} in [{_FRAGILE},{_ENTRENED}))"
        else:
            raw = f"WOLFRAM-ENTRENED (ratio {ratio:.3f} >= {_ENTRENED})"

        # Calibrer par classe
        if klass_label in ("I", "II"):
            if ratio < _ENTRENED:
                verdicts[name] = f"CLASS-{klass_label}-CONFIRMED ({raw})"
            else:
                verdicts[name] = (
                    f"CLASS-{klass_label}-REFUTED ({raw} -- "
                    f"{klass_name} doit collapse sous LZ)"
                )
        else:  # III, IV
            if ratio >= _FRAGILE:
                verdicts[name] = f"CLASS-{klass_label}-CONFIRMED ({raw})"
            else:
                verdicts[name] = (
                    f"CLASS-{klass_label}-REFUTED ({raw} -- "
                    f"{klass_name} doit avoir entropie partielle)"
                )

    return verdicts


def wolfram_4classes_cross_verdict(cv: dict) -> str:
    """Verdict final sur les 4 classes Wolframe vs K_trajectory.

    Renvoie un verdict falsifiable en fonction du pattern observe :

    - ALL-EXPECTED : I/II collapse, III/IV WEAK-COLLAPSE ou ENTREPRED.
      C'est le resultat attendu selon la classification Wolframe 2002.

    - I/II-INVERSE : I ou II reste WEAK ou ENTREPRED alors qu'il devrait
      collapse. Le discriminant detecte une entropie dans une trajectoire
      qui n'en a pas -- faux positif.

    - III/IV-INVERSE : III ou IV collapse alors qu'il devrait garder de
      l'entropie. Faux negatif -- le K_trajectory manque l'information
      structurelle.

    - PARTIAL : une ou plusieurs classes confirment, une ou plusieurs
      contredisent. Resultat mixte.

    - INDETERMINATE : donnees insuffisantes (donnees manquantes ou
      ratio bruite).
    """
    saturated = [n for n, v in cv.items() if "SATURATED" in v]
    if saturated and len(saturated) == len(cv):
        return (
            f"WOLFRAM-4CLASSES-SATURATED ({len(saturated)}/{len(cv)} classes sous "
            f"le plancher de cadrage zlib -- aucune classification n'y est concluante)"
        )

    confirmed = []
    refuted = []
    for name, verdict_str in cv.items():
        if "CONFIRMED" in verdict_str:
            confirmed.append(name)
        elif "REFUTED" in verdict_str:
            refuted.append(name)
        # INCONCLUSIVE et SATURATED ignores

    if not confirmed and not refuted:
        return "WOLFRAM-4CLASSES-INDETERMINATE (donnees insuffisantes)"
    if not refuted:
        return f"WOLFRAM-4CLASSES-ALL-EXPECTED ({len(confirmed)}/{len(cv)} classes confirment)"

    refuted_classes = set()
    for n in refuted:
        try:
            rule = int(n.split("_R")[1].split("_")[0])
            klass = WOLFRAM_CLASS_MAP.get(rule, ("?",))[0]
            refuted_classes.add(klass)
        except (IndexError, ValueError):
            pass

    if refuted_classes.issubset({"I", "II"}):
        return f"WOLFRAM-4CLASSES-I/II-INVERSE ({len(refuted)}/{len(cv)} contredisent -- faux positif sur structure simple)"
    if refuted_classes.issubset({"III", "IV"}):
        return f"WOLFRAM-4CLASSES-III/IV-INVERSE ({len(refuted)}/{len(cv)} contredisent -- faux negatif sur entropie)"
    return f"WOLFRAM-4CLASSES-PARTIAL ({len(confirmed)} confirm / {len(refuted)} refute)"


def cmd_wolfram_4classes(args: argparse.Namespace) -> int:
    """Mode wolfram-4classes : mesure K_trajectory sur les 4 classes Wolframe.

    Mesure R0 (I), R4 (II), R30 (III), R110 (IV) et produit un verdict
    par classe + un verdict cross-classes falsifiable.

    Usage :
        python scripts/hashlife/k_trajectory.py --mode wolfram-4classes \\
            --n-cells 64 --n-steps 64 --seed 33
    """
    n_values = [0, 1, 2, 3, 4, 5, 6]
    results = measure_wolfram_4classes(
        n_cells=args.n_cells, n_steps=args.n_cells, seed=args.seed
    )

    # Affichage par regle
    print(f"{'Trajectory':35s}  {'Class':>5s}  {'n':>3s}  {'W':>4s}  {'K(t,W)':>8s}  {'K/n':>8s}")
    print("-" * 90)
    by_rule: dict[int, list[dict]] = {}
    for r in results:
        try:
            rule = int(r["trajectory"].split("_R")[1].split("_")[0])
            by_rule.setdefault(rule, []).append(r)
        except (IndexError, ValueError):
            pass
    for rule in (0, 4, 30, 110):
        runs = sorted(by_rule.get(rule, []), key=lambda r: r["n"])
        klass_label = WOLFRAM_CLASS_MAP.get(rule, ("?",))[0]
        for run in runs:
            print(
                f"{run['trajectory']:35s}  {klass_label:>5s}  {run['n']:>3d}  "
                f"{run['W']:>4d}  {run['k_trajectory']:>8d}  {run['k_over_n']:>8.2f}"
            )

    # Verdicts
    print()
    print("=== Verdict Wolframe par regle ===")
    cv = wolfram_class_verdict(results)
    for name, status in cv.items():
        print(f"  {name:35s}  {status}")
    print()
    final = wolfram_4classes_cross_verdict(cv)
    print(f"=== Verdict final cross-classes ===")
    print(f"  {final}")

    # Sortie JSON
    if args.json_out:
        out = {
            "results": results,
            "per_class_verdicts": cv,
            "cross_classes_verdict": final,
            "n_cells": args.n_cells,
            "n_steps": args.n_cells,
            "seed": args.seed,
            "rules": (0, 4, 30, 110),
            "class_map": {str(k): v for k, v in WOLFRAM_CLASS_MAP.items()},
        }
        Path(args.json_out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"\n[INFO] resultats ecrits dans {args.json_out}")
    return 0


# ---------------- Pli 7 : Kolmogorov structure function ----------------


# Plancher de mesure concluante : sous n_cells = 512, la fenetre packee
# (W+1 etats) reste trop courte pour que zlib distingue contenu et cadrage,
# et R30 / R110 rendent la meme constante. Mesure 2026-10-09 : a n_cells = 64
# les deux regles rendent KSF = 8.000 (= n_cells / 8 octets, plancher exact).
WOLFRAM_KSF_MIN_N_CELLS = 512

# Landmarks asymptotiques (KSF mesuree a grand contexte), en BITS par cellule
WOLFRAM_KSF_LANDMARKS = {
    0: ("I", "uniforme", 0.0),
    4: ("II", "periodique", 0.0),
    30: ("III", "chaotique", 0.85),
    110: ("IV", "Turing-complet", 0.20),
}


def pack_states_1d(states: Sequence[Sequence[Cell]]) -> bytes:
    """Pack une liste d'etats 1-D Wolframe en bytes (MSB first par cellule).

    Chaque etat est une sequence de 0/1 de longueur n_cells ; packe en
    l'octet au bit le plus significatif (MSB-first), 8 cellules par octet.
    Padding MSB=0 sur le dernier octet si n_cells n'est pas multiple de 8.
    """
    if not states:
        return b""
    n_cells = len(states[0])
    bits = []
    for s in states:
        bits.extend(int(b) for b in s)
    out = bytearray()
    for i in range(0, len(bits), 8):
        chunk = bits[i:i + 8]
        byte = 0
        for j, b in enumerate(chunk):
            byte |= (int(b) & 1) << (7 - j)
        out.append(byte)
    return bytes(out)


def ksf_trajectory(
    rule: int,
    n_cells: int = 64,
    n_steps: int = 64,
    seed: int = 33,
    context_sizes: Sequence[int] = (1, 2, 4, 8, 16, 32),
) -> list[dict]:
    """Mesure la Kolmogorov structure function (KSF) d'une trajectoire Wolframe.

    Pour chaque taille de contexte W' dans `context_sizes`, calcule
    K(W_t | W_{t-W'+1..t}) = len(LZ(pack_states([W_t-W'+1..t+1]))) -
    len(LZ(pack_states([W_t-W'+1..t]))), moyenne sur tous les pas t >= W'.

    Les valeurs rendues sont en **octets** ; l'echelle comparable aux
    landmarks est `ksf_bits_per_cell` = ksf_mean * 8 / n_cells.

    Une trajectoire **aleatoire** (entropie maximale) a ksf_mean -> n_cells/8
    octets, soit 1.0 bit par cellule (le contexte n'aide pas, le pas suivant
    a entropie totale). Une trajectoire **structuree** tend vers 0 bit par
    cellule (le contexte suffit a determiner le pas suivant).

    Differenciation R30 (chaotique) vs R110 (Turing-complet) :
    - R30 est statistiquement uniforme -> KSF reste elevee, contexte n'aide
      pas.
    - R110 a des structures (gliders, reactions) -> KSF decroit quand le
      contexte capture une partie du "programme". Discrimination falsifiable.

    Reference : Vereshchagin & Vitanyi (2004) IEEE Trans. Info. Theory 50(12).
    """
    try:
        from ict.wolfram_step import wolfram_trajectory  # pli 2 PR #19793
    except ImportError as e:
        raise RuntimeError(
            "ict.wolfram_step introuvable. L'organe (PR #19793) doit etre "
            "present dans MyIA.AI.Notebooks/IIT/ICT-Series/ict/wolfram_step.py "
            f"et ce dossier doit etre dans sys.path. Erreur: {e}"
        )

    traj_1d = wolfram_trajectory(
        rule=rule, n_cells=n_cells, n_steps=n_steps, seed=seed, record_densities=False
    )
    # traj_1d : Sequence[Sequence[Cell]] = liste d'etats successifs

    if len(traj_1d) < max(context_sizes) + 1:
        raise ValueError(
            f"n_steps={n_steps} insuffisant pour context_sizes={list(context_sizes)}. "
            f"Il faut au moins max(context_sizes) + 1 = {max(context_sizes) + 1} etats."
        )

    results = []
    for W in context_sizes:
        ksf_values: list[int] = []
        k_ctx_values: list[int] = []
        for t in range(W, len(traj_1d)):
            ctx_states = traj_1d[t - W:t]
            cur_state = traj_1d[t]
            ctx_bytes = pack_states_1d(ctx_states)
            ctx_plus_cur_bytes = pack_states_1d(ctx_states + [cur_state])
            k_ctx = lz_compressed_length(ctx_bytes)
            k_full = lz_compressed_length(ctx_plus_cur_bytes)
            # K(W_t | context) = K(ctx || W_t) - K(ctx)
            ksf = k_full - k_ctx
            ksf_values.append(ksf)
            k_ctx_values.append(k_ctx)

        if ksf_values:
            ksf_mean = sum(ksf_values) / len(ksf_values)
            ksf_min = min(ksf_values)
            ksf_max = max(ksf_values)
            k_ctx_mean = sum(k_ctx_values) / len(k_ctx_values)
        else:
            ksf_mean = ksf_min = ksf_max = k_ctx_mean = 0.0

        results.append({
            "trajectory": f"wolfram_R{rule}_n{n_cells}_seed{seed}",
            "rule": rule,
            "n_cells": n_cells,
            "W_context": W,
            "ksf_mean": round(ksf_mean, 4),
            "ksf_min": ksf_min,
            "ksf_max": ksf_max,
            # ksf_mean est en OCTETS ; les landmarks sont en BITS par cellule.
            # Sans cette normalisation, R30 (incompressible) rend ksf_mean =
            # n_cells/8, lu a tort comme des bits -- facteur 8.
            "ksf_bits_per_cell": round(ksf_mean * 8.0 / n_cells, 4),
            "k_context_mean": round(k_ctx_mean, 4),
            "n_measurements": len(ksf_values),
        })

    return results


def measure_wolfram_ksf(
    n_cells: int = 64,
    n_steps: int = 64,
    seed: int = 33,
) -> list[dict]:
    """Mesure KSF sur les 4 classes canoniques Wolframe (R0, R4, R30, R110).

    4 regles x 6 context_sizes = 24 mesures (une par paire regle/contexte).
    Permet la discrimination fine III/IV via comparaison KSF(W=32).
    """
    context_sizes = (1, 2, 4, 8, 16, 32)
    all_results = []
    for rule in (0, 4, 30, 110):
        all_results.extend(
            ksf_trajectory(
                rule=rule, n_cells=n_cells, n_steps=n_steps, seed=seed,
                context_sizes=context_sizes,
            )
        )
    return all_results


def wolfram_ksf_verdict(results: list[dict]) -> dict:
    """Verdict par regle : la KSF asymptotique (W=32) est-elle conforme au landmark ?

    Pour chaque regle, extrait la mesure au plus grand contexte (W=32) et
    la compare au landmark canonique (cf. WOLFRAM_KSF_LANDMARKS). Si la
    mesure observee s'ecarte significativement du landmark, REFUTE ;
    sinon CONFIRME.

    La comparaison se fait sur ksf_bits_per_cell (bits par cellule), la
    seule echelle commensurable aux landmarks ci-dessous.

    Hypothese de discrimination R30 vs R110 (a falsifier ou confirmer) :
    - R30 KSF(W=32) ~ 0.85 (chaos, contexte n'aide pas).
    - R110 KSF(W=32) ~ 0.20 (Turing-complet, contexte capture gliders).

    Sous n_cells < WOLFRAM_KSF_MIN_N_CELLS, la mesure est declaree
    `WOLFRAM-SATURATED` : la fenetre packee est sous le plancher de cadrage
    zlib et les deux regles rendent la meme constante.
    """
    verdicts = {}
    by_rule: dict[int, list[dict]] = {}
    for r in results:
        by_rule.setdefault(r["rule"], []).append(r)

    for rule, runs in by_rule.items():
        landmark = WOLFRAM_KSF_LANDMARKS.get(rule)
        if landmark is None:
            verdicts[f"KSF_R{rule}"] = f"INCONCLUSIVE (regle {rule} hors 4 classes)"
            continue
        klass, klass_name, expected_ksf = landmark
        runs_sorted = sorted(runs, key=lambda r: r["W_context"])
        max_run = runs_sorted[-1]
        n_cells = max_run["n_cells"]
        if n_cells < WOLFRAM_KSF_MIN_N_CELLS:
            verdicts[f"KSF_R{rule}"] = (
                f"WOLFRAM-SATURATED (n_cells={n_cells} < "
                f"{WOLFRAM_KSF_MIN_N_CELLS} : la fenetre packee est sous le "
                f"plancher de cadrage zlib, KSF mesure le cadrage, pas le contenu)"
            )
            continue
        # Comparaison sur l'echelle normalisee (bits par cellule), seule
        # comparable aux landmarks : ksf_mean est en octets.
        observed_ksf = max_run["ksf_bits_per_cell"]
        delta = abs(observed_ksf - expected_ksf)
        # Tolerance : 0.20 bit/cellule (fenetre pour bruit statistique)
        if delta < 0.20:
            verdicts[f"KSF_R{rule}"] = (
                f"CLASS-{klass}-CONFIRMED (KSF(W={max_run['W_context']}) = "
                f"{observed_ksf:.3f} ~= landmark {expected_ksf:.3f}, delta {delta:.3f})"
            )
        else:
            verdicts[f"KSF_R{rule}"] = (
                f"CLASS-{klass}-DEVIATION (KSF(W={max_run['W_context']}) = "
                f"{observed_ksf:.3f} eloigne du landmark {expected_ksf:.3f}, "
                f"delta {delta:.3f})"
            )

    return verdicts


def wolfram_ksf_discrimination_verdict(verdicts: dict, results: list[dict]) -> str:
    """Verdict final : KSF discrimine-t-elle R30 de R110 ?

    Compare les KSF(W=32) observees de R30 et R110. Si elles sont
    significativement differentes (delta > 0.10), KSF DISCRIMINE
    Turing vs chaos 1-D (vs pli 4 LZ qui ne discriminait pas).

    Si elles sont similaires (delta < 0.10), KSF ne discrimine pas non
    plus -- extension du constat pli 4 que les complexites de trajectoire
    1-D sont insuffisantes pour Turing vs chaos.
    """
    by_rule: dict[int, dict] = {}
    for r in results:
        if r["W_context"] == 32:
            by_rule[r["rule"]] = r

    r30 = by_rule.get(30)
    r110 = by_rule.get(110)
    if r30 is None or r110 is None:
        return "WOLFRAM-KSF-INDETERMINATE (donnees R30/R110 W=32 manquantes)"

    n_cells = r30["n_cells"]
    if n_cells < WOLFRAM_KSF_MIN_N_CELLS:
        return (
            f"WOLFRAM-KSF-SATURATED (n_cells={n_cells} < "
            f"{WOLFRAM_KSF_MIN_N_CELLS} : les deux regles rendent la meme "
            f"constante de cadrage, toute (non)discrimination y est un artefact)"
        )

    ksf_30 = r30["ksf_bits_per_cell"]
    ksf_110 = r110["ksf_bits_per_cell"]
    delta = abs(ksf_30 - ksf_110)

    if delta >= 0.10:
        return (
            f"WOLFRAM-KSF-DISCRIMINANT (R30 KSF(W=32)={ksf_30:.3f} bits/cellule, "
            f"R110 KSF(W=32)={ksf_110:.3f} bits/cellule, delta={delta:.3f} >= 0.10)"
        )
    return (
        f"WOLFRAM-KSF-NONDISCRIMINANT (R30 KSF(W=32)={ksf_30:.3f} bits/cellule, "
        f"R110 KSF(W=32)={ksf_110:.3f} bits/cellule, delta={delta:.3f} < 0.10)"
    )


def cmd_wolfram_ksf(args: argparse.Namespace) -> int:
    """Mode wolfram-ksf : mesure KSF sur les 4 classes Wolframe.

    Usage :
        python scripts/hashlife/k_trajectory.py --mode wolfram-ksf \\
            --n-cells 64 --n-steps 64 --seed 33
    """
    results = measure_wolfram_ksf(
        n_cells=args.n_cells, n_steps=args.n_steps, seed=args.seed,
    )

    # Affichage par regle
    print(f"{'Trajectory':35s}  {'Class':>5s}  {'W_ctx':>5s}  {'KSF_octets':>10s}  {'KSF_b/cell':>10s}  {'K_ctx':>8s}  {'n_meas':>7s}")
    print("-" * 105)
    by_rule: dict[int, list[dict]] = {}
    for r in results:
        by_rule.setdefault(r["rule"], []).append(r)
    for rule in (0, 4, 30, 110):
        runs = sorted(by_rule.get(rule, []), key=lambda r: r["W_context"])
        klass_label = WOLFRAM_KSF_LANDMARKS.get(rule, ("?",))[0]
        for run in runs:
            print(
                f"{run['trajectory']:35s}  {klass_label:>5s}  {run['W_context']:>5d}  "
                f"{run['ksf_mean']:>10.4f}  {run['ksf_bits_per_cell']:>10.4f}  "
                f"{run['k_context_mean']:>8.2f}  {run['n_measurements']:>7d}"
            )

    # Verdicts
    print()
    print("=== Verdict KSF par regle ===")
    verdicts = wolfram_ksf_verdict(results)
    for name, status in verdicts.items():
        print(f"  {name:15s}  {status}")

    # Verdict discrimination
    final = wolfram_ksf_discrimination_verdict(verdicts, results)
    print()
    print("=== Verdict final discrimination R30 vs R110 ===")
    print(f"  {final}")

    # Sortie JSON
    if args.json_out:
        out = {
            "results": results,
            "per_class_verdicts": verdicts,
            "discrimination_verdict": final,
            "n_cells": args.n_cells,
            "n_steps": args.n_steps,
            "seed": args.seed,
            "rules": (0, 4, 30, 110),
            "ksf_landmarks": {
                str(k): {"klass": v[0], "name": v[1], "expected_ksf": v[2]}
                for k, v in WOLFRAM_KSF_LANDMARKS.items()
            },
        }
        Path(args.json_out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"\n[INFO] resultats ecrits dans {args.json_out}")
    return 0


# ---------------- Pli 8 : Block decomposition (Zenil 2013) ----------------


# Landmarks asymptotiques (variance d'entropie par bloc a grand W).
# Justification par classe Wolframe (Wolfram 2002 ch. 7, Cook 2004 R110) :
# - I  (uniforme, R0)     : entropie = 0, std = 0 (constance)
# - II (periodique, R4)   : entropie ~ 0, std ~ 0 (periode capture tout)
# - III (chaotique, R30)  : entropie ~ 1.0, std ~ 0.0 (chaos uniforme, blocs
#                            similaires a toutes les positions)
# - IV (Turing, R110)     : entropie ~ 1.0 (pareil), std eleve (bimodalite :
#                            gliders a entropie basse, reactions a entropie
#                            elevee, structures invisibles au chaos)
# Landmarks de complexite LZ76 normalisee par bloc (moyenne, ecart-type), au
# plus grand block_length W=32. Recalibres pour l'instrument corrige -- les
# valeurs de l'ancienne version portaient sur l'entropie de Shannon, qui est
# invariante a l'arrangement et ne pouvait donc pas discriminer.
#
# Calibration : centre multi-seed (0/1/7/33/42/99) a n_cells = 256 ; la
# verification hors echantillon se fait a n = 512 et n = 1024 (cf.
# WOLFRAM-VERDICT-BLOCKS.md).
#
# Lecture : R0 et R4 sont quasi-incompressibles par bloc (peu de facteurs LZ76,
# trajectoire reguliere) ; R30 est homogene et maximal (chaos partout, std ~ 0) ;
# R110 est **heterogene** -- fond periodique + gliders -- donc plus compressible
# en moyenne que R30 et surtout **dispersee** (std >> 0). C'est cette dispersion
# qui separe III de IV.
WOLFRAM_BLOCK_LANDMARKS = {
    0: ("I", "uniforme", 0.01, 0.02),
    4: ("II", "periodique", 0.04, 0.02),
    30: ("III", "chaotique", 1.03, 0.01),
    110: ("IV", "structure", 0.67, 0.13),
}

# Puissance minimale du test : un ecart-type sur moins de 4 blocs ne mesure rien.
# A n_steps = 64 et W = 32 il n'y a que 2 blocs -- c'est la zone ou l'ancienne
# version publiait un verdict de non-discrimination.
WOLFRAM_BLOCKS_MIN_N_BLOCKS = 4


def shannon_entropy_bits(bitstring: Sequence[Cell]) -> float:
    """Entropie de Shannon (base 2) d'un sequence de bits 0/1.

    H = -p0 * log2(p0) - p1 * log2(p1) avec p0 + p1 = 1.
    Conventions H = 0 si tous les bits sont egaux (p=0 ou p=1).

    ATTENTION -- cette grandeur est **invariante a l'arrangement** : elle ne
    depend que du nombre de 1, jamais de leur position. Mesure 2026-10-09 :
    `H('0101...01') == H(sequence desordonnee equilibree) == 1.0`. Elle ne
    peut donc pas distinguer une trajectoire periodique d'une trajectoire
    chaotique des lors que les deux sont equilibrees.

    Ce n'est PAS la statistique de la block decomposition de Zenil 2013
    (qui agrege une approximation de K(bloc)). Conservee ici pour la
    tracabilite des mesures anterieures ; le verdict utilise
    `block_complexity_distribution` (LZ76 normalise), qui est sensible a
    l'arrangement.
    """
    if not bitstring:
        return 0.0
    n = len(bitstring)
    n_ones = sum(int(b) & 1 for b in bitstring)
    p1 = n_ones / n
    p0 = 1.0 - p1
    if p0 == 0.0 or p1 == 0.0:
        return 0.0
    return -(p0 * math.log2(p0) + p1 * math.log2(p1))


def block_decompose_trajectory(
    traj_1d: Sequence[Sequence[Cell]],
    block_length: int,
) -> list[Sequence[Cell]]:
    """Decompose une trajectoire 1-D Wolframe en blocs non-chevauchants.

    Pour chaque pas d'index i dans [0, n_steps), avec `block_length` etant
    la taille du bloc (en nombre d'etats consecutifs), extrait le bloc
    traj_1d[i : i + block_length] (taille block_length x n_cells).

    Retourne une liste de blocs, chacun etant une concatenation des
    `block_length` etats successifs en une sequence lineaire de bits.

    Hypothese : n_steps >= block_length.
    """
    if block_length <= 0:
        raise ValueError(f"block_length must be positive, got {block_length}")
    n_steps = len(traj_1d)
    if n_steps < block_length:
        return []

    blocks: list[Sequence[Cell]] = []
    for i in range(0, n_steps - block_length + 1, block_length):
        block_states = traj_1d[i:i + block_length]
        # Concatener en une sequence lineaire de bits
        flat: list[Cell] = []
        for state in block_states:
            flat.extend(int(b) & 1 for b in state)
        blocks.append(flat)
    return blocks


def block_entropy_distribution(
    traj_1d: Sequence[Sequence[Cell]],
    block_length: int,
) -> dict:
    """Distribution d'entropie Shannon (base 2) par bloc.

    Pour une longueur de bloc W, decompose la trajectoire en
    n_steps/w blocs non-chevauchants, calcule l'entropie de Shannon (base
    2) du bitstream concatene de chaque bloc, et retourne les statistiques
    agregees (moyenne, std, min, max, mediane).

    Pour R0 (classe I) : tous les blocs identiques, entropie = 0, std = 0.
    Pour R30 (classe III) : tous les blocs similaires, entropie ~ 1, std
    proche de 0 (chaos = entropie maximale partout).
    Pour R110 (classe IV) : blocs heterogenes, entropie ~ 1 en moyenne mais
    std elevee (structures invisibles au chaos).

    Reference : Zenil, Soler-Toscano, Kiani (2013) arXiv:1304.5813.
    """
    blocks = block_decompose_trajectory(traj_1d, block_length)
    if not blocks:
        return {
            "block_length": block_length,
            "n_blocks": 0,
            "mean": 0.0,
            "std": 0.0,
            "min": 0.0,
            "max": 0.0,
            "median": 0.0,
        }

    entropies = [shannon_entropy_bits(b) for b in blocks]
    n = len(entropies)
    mean = sum(entropies) / n
    var = sum((e - mean) ** 2 for e in entropies) / n
    std = math.sqrt(var)
    sorted_e = sorted(entropies)
    median = sorted_e[n // 2] if n % 2 == 1 else (
        sorted_e[n // 2 - 1] + sorted_e[n // 2]
    ) / 2.0

    return {
        "block_length": block_length,
        "n_blocks": n,
        "mean": round(mean, 4),
        "std": round(std, 4),
        "min": round(min(entropies), 4),
        "max": round(max(entropies), 4),
        "median": round(median, 4),
    }


def lz76_factor_count(bitstring: str) -> int:
    """Nombre de facteurs distincts de la factorisation de Lempel-Ziv 76.

    Parcourt la chaine de gauche a droite et compte le nombre de phrases
    (facteurs) nouvelles. C'est un **comptage entier** : aucun compresseur
    n'est invoque, donc aucune constante de cadrage ne s'y ajoute (contraste
    avec `lz_compressed_length`, dont le plancher zlib fausse les petites
    fenetres -- cf. plis 4 et 7).

    Sensible a l'arrangement : une chaine periodique se factorise en peu de
    phrases, une chaine chaotique en beaucoup.

    Port pli 8 (correctif #19836, statistique de verdict de la block
    decomposition) -- recopie byte-identique pour que la rebase de la pile
    Origami se resolve sans conflit de contenu.
    """
    n = len(bitstring)
    i = 0
    count = 0
    while i < n:
        k = 1
        while i + k <= n and bitstring[i:i + k] in bitstring[:i + k - 1]:
            k += 1
        count += 1
        i += k
    return count


def normalized_lz76_complexity(bitstring: str) -> float:
    """Complexite LZ76 normalisee : c(n) * log2(n) / n.

    Estimateur standard de la complexite de Kolmogorov par factorisation LZ76
    (Ziv & Lempel 1978 ; Li & Vitanyi 2019 ch. 6). Vaut ~1.0 pour une chaine
    aleatoire et tend vers 0 pour une chaine periodique.

    Peut depasser 1.0 de quelques centiemes sur les chaines courtes (le
    facteur log2(n) n'est asymptotiquement exact) : c'est une propriete connue
    de l'estimateur, pas une erreur.

    Port pli 8 (correctif #19836) -- recopie byte-identique.
    """
    n = len(bitstring)
    if n <= 1:
        return 0.0
    return lz76_factor_count(bitstring) * math.log2(n) / n


def _bits_to_str(bits: Sequence[Cell]) -> str:
    """Convertit une sequence de cellules 0/1 en chaine '0'/'1'.

    Necessaire car `in` sur une liste teste l'appartenance d'un ELEMENT, pas
    d'une sous-sequence : une recherche de facteur LZ sur une liste de ints
    rendrait toujours faux et degenererait en c(n) = n.

    Port pli 8 (correctif #19836) -- recopie byte-identique.
    """
    return "".join("1" if (int(b) & 1) else "0" for b in bits)


def block_complexity_distribution(
    traj_1d: Sequence[Sequence[Cell]],
    block_length: int,
) -> dict:
    """Distribution de complexite LZ76 normalisee par bloc.

    Meme decoupage que `block_entropy_distribution` (blocs non-chevauchants de
    `block_length` etats consecutifs, chacun aplati en un bitstream), mais la
    statistique par bloc est la complexite LZ76 normalisee -- une
    approximation de K(bloc), donc **sensible a l'arrangement**, la ou
    l'entropie de Shannon ne l'est pas.

    Reference : Zenil, Soler-Toscano, Kiani (2013) arXiv:1304.5813 (block
    decomposition, ou la complexite du bloc est K(bloc)) ; Li & Vitanyi (2019)
    ch. 6 (estimateur LZ76).

    Port pli 8 (correctif #19836) -- recopie byte-identique.
    """
    blocks = block_decompose_trajectory(traj_1d, block_length)
    if not blocks:
        return {
            "block_length": block_length,
            "n_blocks": 0,
            "mean": 0.0,
            "std": 0.0,
            "min": 0.0,
            "max": 0.0,
            "median": 0.0,
        }

    values = [normalized_lz76_complexity(_bits_to_str(b)) for b in blocks]
    n = len(values)
    mean = sum(values) / n
    var = sum((v - mean) ** 2 for v in values) / n
    std = math.sqrt(var)
    sorted_v = sorted(values)
    median = sorted_v[n // 2] if n % 2 == 1 else (
        sorted_v[n // 2 - 1] + sorted_v[n // 2]
    ) / 2.0

    return {
        "block_length": block_length,
        "n_blocks": n,
        "mean": round(mean, 4),
        "std": round(std, 4),
        "min": round(min(values), 4),
        "max": round(max(values), 4),
        "median": round(median, 4),
    }


def measure_wolfram_blocks(
    n_cells: int = 256,
    n_steps: int = 256,
    seed: int = 33,
    block_lengths: Sequence[int] = (1, 2, 4, 8, 16, 32),
) -> list[dict]:
    """Mesure la distribution de complexite par bloc pour les 4 classes Wolframe.

    Pour chaque regle (R0, R4, R30, R110) et chaque longueur de bloc W dans
    `block_lengths`, calcule deux distributions sur les blocs non-chevauchants
    de la trajectoire :

    - `entropy_*` : entropie de Shannon par bloc -- **invariante a
      l'arrangement**, conservee pour la tracabilite ;
    - `complexity_*` : complexite LZ76 normalisee par bloc -- approximation
      de K(bloc), **sensible a l'arrangement**. C'est celle que le verdict
      utilise.

    4 regles x 6 block_lengths = 24 mesures. Discrimine R30 de R110 par la
    **dispersion** de la complexite par bloc : R30 (chaos homogene) a
    std ~ 0, R110 (structure : fond periodique + gliders) a std nettement
    positive.

    Echelle : la mesure canonique est prise a `n_cells = 256`. La statistique
    LZ76 est un comptage entier -- elle n'a pas le plancher de cadrage d'un
    compresseur, donc contrairement aux plis 4 et 7 elle reste valide aux
    petites fenetres ; c'est le **nombre de blocs** (`n_steps / W`) qui borne
    la puissance du test, d'ou n=256 plutot que n=64.

    Reference : Zenil, Soler-Toscano, Kiani (2013) arXiv:1304.5813.
    """
    try:
        from ict.wolfram_step import wolfram_trajectory  # pli 2 PR #19793
    except ImportError as e:
        raise RuntimeError(
            "ict.wolfram_step introuvable. L'organe (PR #19793) doit etre "
            "present dans MyIA.AI.Notebooks/IIT/ICT-Series/ict/wolfram_step.py "
            "et ce dossier doit etre dans sys.path. Erreur: {e}"
        )

    all_results = []
    for rule in (0, 4, 30, 110):
        traj_1d = wolfram_trajectory(
            rule=rule, n_cells=n_cells, n_steps=n_steps, seed=seed,
            record_densities=False,
        )
        for W in block_lengths:
            ent = block_entropy_distribution(traj_1d, W)
            cpx = block_complexity_distribution(traj_1d, W)
            all_results.append({
                "trajectory": f"wolfram_R{rule}_n{n_cells}_seed{seed}",
                "rule": rule,
                "block_length": W,
                "entropy_mean": ent["mean"],
                "entropy_std": ent["std"],
                "entropy_min": ent["min"],
                "entropy_max": ent["max"],
                "entropy_median": ent["median"],
                "complexity_mean": cpx["mean"],
                "complexity_std": cpx["std"],
                "complexity_min": cpx["min"],
                "complexity_max": cpx["max"],
                "complexity_median": cpx["median"],
                "n_blocks": cpx["n_blocks"],
            })
    return all_results


def wolfram_blocks_verdict(results: list[dict]) -> dict:
    """Verdict par regle : la complexite par bloc est-elle conforme au landmark ?

    Pour chaque regle, extrait la mesure au plus grand block_length et compare
    `complexity_mean` / `complexity_std` au landmark (WOLFRAM_BLOCK_LANDMARKS).
    Sous `WOLFRAM_BLOCKS_MIN_N_BLOCKS`, aucune comparaison n'est concluante.

    Hypothese discriminante R30 vs R110 :
    - R30 complexity_std ~ 0.01 (chaos homogene)
    - R110 complexity_std >= 0.08 (heterogeneite structurelle)
    """
    verdicts = {}
    by_rule: dict[int, list[dict]] = {}
    for r in results:
        by_rule.setdefault(r["rule"], []).append(r)

    for rule, runs in by_rule.items():
        landmark = WOLFRAM_BLOCK_LANDMARKS.get(rule)
        if landmark is None:
            verdicts[f"BLOCKS_R{rule}"] = (
                f"INCONCLUSIVE (regle {rule} hors 4 classes)"
            )
            continue
        klass, klass_name, expected_mean, expected_std = landmark
        runs_sorted = sorted(runs, key=lambda r: r["block_length"])
        max_run = runs_sorted[-1]

        if max_run["n_blocks"] < WOLFRAM_BLOCKS_MIN_N_BLOCKS:
            verdicts[f"BLOCKS_R{rule}"] = (
                f"WOLFRAM-BLOCKS-UNDERPOWERED (n_blocks={max_run['n_blocks']} < "
                f"{WOLFRAM_BLOCKS_MIN_N_BLOCKS} : un ecart-type sur si peu de "
                f"blocs ne mesure pas la dispersion)"
            )
            continue

        observed_mean = max_run["complexity_mean"]
        observed_std = max_run["complexity_std"]
        mean_delta = abs(observed_mean - expected_mean)
        std_delta = abs(observed_std - expected_std)
        if mean_delta < 0.15 and std_delta < 0.10:
            verdicts[f"BLOCKS_R{rule}"] = (
                f"CLASS-{klass}-CONFIRMED (mean={observed_mean:.3f} "
                f"~= {expected_mean:.3f}, std={observed_std:.3f} "
                f"~= {expected_std:.3f})"
            )
        else:
            verdicts[f"BLOCKS_R{rule}"] = (
                f"CLASS-{klass}-DEVIATION (mean={observed_mean:.3f} vs "
                f"landmark {expected_mean:.3f} delta={mean_delta:.3f}; "
                f"std={observed_std:.3f} vs landmark {expected_std:.3f} "
                f"delta={std_delta:.3f})"
            )

    return verdicts


def wolfram_blocks_discrimination_verdict(
    verdicts: dict, results: list[dict]
) -> str:
    """Verdict final : la block decomposition discrimine-t-elle R30 de R110 ?

    Compare les dispersions de complexite par bloc de R30 et R110 au plus grand
    block_length (W=32). Si `std(R110) - std(R30) >= 0.05`, **DISCRIMINANT** :
    l'heterogeneite structurelle de R110 (fond periodique + gliders) se lit dans
    la dispersion des blocs, la ou le chaos de R30 est homogene.

    Le seuil est celui de l'ancienne version : il n'a pas ete deplace pour faire
    passer le resultat. Ce qui a change est l'instrument -- la statistique par
    bloc est desormais sensible a l'arrangement, donc le seuil mesure enfin
    quelque chose.
    """
    by_rule: dict[int, dict] = {}
    for r in results:
        if r["block_length"] == 32:
            by_rule[r["rule"]] = r

    r30 = by_rule.get(30)
    r110 = by_rule.get(110)
    if r30 is None or r110 is None:
        return "WOLFRAM-BLOCKS-INDETERMINATE (donnees R30/R110 W=32 manquantes)"

    if (r30["n_blocks"] < WOLFRAM_BLOCKS_MIN_N_BLOCKS
            or r110["n_blocks"] < WOLFRAM_BLOCKS_MIN_N_BLOCKS):
        return (
            f"WOLFRAM-BLOCKS-UNDERPOWERED (n_blocks={r30['n_blocks']} pour W=32, "
            f"minimum {WOLFRAM_BLOCKS_MIN_N_BLOCKS} : augmenter n_steps)"
        )

    std_30 = r30["complexity_std"]
    std_110 = r110["complexity_std"]
    mean_30 = r30["complexity_mean"]
    mean_110 = r110["complexity_mean"]
    delta_std = std_110 - std_30

    if delta_std >= 0.05:
        return (
            f"WOLFRAM-BLOCKS-DISCRIMINANT (R30 mean/std={mean_30:.3f}/{std_30:.3f}, "
            f"R110 mean/std={mean_110:.3f}/{std_110:.3f}, "
            f"delta_std={delta_std:.3f} >= 0.05)"
        )
    return (
        f"WOLFRAM-BLOCKS-NONDISCRIMINANT (R30 mean/std={mean_30:.3f}/{std_30:.3f}, "
        f"R110 mean/std={mean_110:.3f}/{std_110:.3f}, "
        f"delta_std={delta_std:.3f} < 0.05)"
    )


def cmd_wolfram_blocks(args: argparse.Namespace) -> int:
    """Mode wolfram-blocks : mesure block decomposition sur les 4 classes.

    Usage :
        python scripts/hashlife/k_trajectory.py --mode wolfram-blocks \\
            --n-cells 256 --n-steps 256 --seed 33
    """
    results = measure_wolfram_blocks(
        n_cells=args.n_cells,
        n_steps=args.n_steps,
        seed=args.seed,
    )

    # Affichage par regle -- colonnes = complexite LZ76 normalisee par bloc
    print(f"{'Trajectory':35s}  {'Class':>5s}  {'W_blk':>5s}  {'Mean':>6s}  "
          f"{'Std':>6s}  {'Min':>5s}  {'Max':>5s}  {'Median':>6s}  {'n_blk':>5s}")
    print("-" * 100)
    by_rule: dict[int, list[dict]] = {}
    for r in results:
        by_rule.setdefault(r["rule"], []).append(r)
    for rule in (0, 4, 30, 110):
        runs = sorted(by_rule.get(rule, []), key=lambda r: r["block_length"])
        klass_label = WOLFRAM_BLOCK_LANDMARKS.get(rule, ("?",))[0]
        for run in runs:
            print(
                f"{run['trajectory']:35s}  {klass_label:>5s}  "
                f"{run['block_length']:>5d}  {run['complexity_mean']:>6.3f}  "
                f"{run['complexity_std']:>6.3f}  {run['complexity_min']:>5.2f}  "
                f"{run['complexity_max']:>5.2f}  {run['complexity_median']:>6.3f}  "
                f"{run['n_blocks']:>5d}"
            )

    # Verdicts
    print()
    print("=== Verdict block decomposition par regle ===")
    verdicts = wolfram_blocks_verdict(results)
    for name, status in verdicts.items():
        print(f"  {name:15s}  {status}")

    # Verdict discrimination
    final = wolfram_blocks_discrimination_verdict(verdicts, results)
    print()
    print("=== Verdict final discrimination R30 vs R110 ===")
    print(f"  {final}")

    # Sortie JSON
    if args.json_out:
        out = {
            "results": results,
            "per_class_verdicts": verdicts,
            "discrimination_verdict": final,
            "n_cells": args.n_cells,
            "n_steps": args.n_steps,
            "seed": args.seed,
            "rules": (0, 4, 30, 110),
            "blocks_landmarks": {
                str(k): {
                    "klass": v[0],
                    "name": v[1],
                    "expected_mean": v[2],
                    "expected_std": v[3],
                }
                for k, v in WOLFRAM_BLOCK_LANDMARKS.items()
            },
        }
        Path(args.json_out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"\n[INFO] resultats ecrits dans {args.json_out}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "K_trajectory")
    parser.add_argument(
        "--mode",
        choices=["measure", "verify-corpus", "bounds", "wolfram", "wolfram-4classes", "wolfram-ksf", "wolfram-blocks", "wolfram-seed-test"],
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
    parser.add_argument(
        "--rule",
        type=int,
        default=30,
        help="Mode wolfram : regle Wolframe (canoniques : 30, 110). Defaut: 30",
    )
    parser.add_argument(
        "--n-cells",
        type=int,
        default=1024,
        help=(
            "Mode wolfram : nombre de cellules de l'automate 1-D. Plancher de mesure "
            "concluante : 512 (en dessous, cadrage zlib dominant, verdict SATURATED). "
            "Mode wolfram-blocks : 256 est l'echelle canonique (sous 256, W=32 "
            "ne laisse que 2 blocs et le verdict rend UNDERPOWERED). "
            "Mode wolfram-seed-test : 512 minimum (WOLFRAM_SEED_MIN_N_CELLS) -- "
            "sous ce plancher la mesure est SATUREE et --json-out est refuse. "
            "Defaut: 1024"
        ),
    )
    parser.add_argument(
        "--n-steps",
        type=int,
        default=64,
        help="Mode wolfram : nombre de pas de simulation. Defaut: 64",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=33,
        help="Mode wolfram : seed du pattern initial. Defaut: 33",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Mode wolfram : mesurer Rule 30 + Rule 110 (defaut = regle unique)",
    )
    parser.add_argument(
        "--seed-presets",
        nargs="+",
        default=None,
        help="Mode wolfram-seed-test : liste des presets a tester (defaut : single-cell, wolfram-0001000, wolfram-defect, random-dense)",
    )
    args = parser.parse_args()
    if args.mode == "measure":
        return cmd_measure(args)
    if args.mode == "bounds":
        return cmd_bounds(args)
    if args.mode == "wolfram":
        return cmd_wolfram(args)
    if args.mode == "wolfram-4classes":
        return cmd_wolfram_4classes(args)
    if args.mode == "wolfram-ksf":
        return cmd_wolfram_ksf(args)
    if args.mode == "wolfram-blocks":
        return cmd_wolfram_blocks(args)
    if args.mode == "wolfram-seed-test":
        return cmd_wolfram_seed_test(args)
    return cmd_verify_corpus(args)


# ---------------------------------------------------------------------------
# Pli 9 Origami Wolfram : seed specialise + 3 complexites
# ---------------------------------------------------------------------------

# Presets d'etat initial pour tester la discrimination des complexites 1-D
# sous differentes conditions de seed. L'enjeu est de separer la discrimination
# reelle (R30 vs R110) du facteur confondant du seed single-cell utilise dans
# plis 4/7/8.
#
# Reference du seed canonique R110 : Wolfram 2002 ch. 7, §7-9 ; Cook 2004
# (preuve d'universalite de Rule 110). Le seed "0001000 repeat" (background
# periodique avec un defaut local) est la condition qui demontre la
# Turing-completude de R110 dans le livre de Wolfram.

WOLFRAM_SEED_PRESETS = {
    # baseline : une seule cellule allumee au centre, n_cells cellules autour
    # a zero. C'est le seed par defaut des plis 4/7/8 (c.110, c.111, c.112).
    "single-cell": "0001000".replace("1", "1").replace("0", "0"),

    # seed canonique Wolfram 2002 ch. 7 : pattern "0001000" repete sur toute
    # la largeur, avec un defaut local (cellule centrale forcee a 0)
    # qui declenche la propagation de gliders.
    "wolfram-0001000": "0001000" * 8,  # 64 cellules

    # seed canonique "defaut local" : pattern periodique avec UNE cellule
    # cassee au centre (forcee a 0 dans un fond de 1). Wolfram 2002 utilise
    # ce defaut pour declencher l'evolution visible.
    "wolfram-defect": ("0001000" * 8)[:63] + "1",  # 64 cellules

    # controle R30 : pattern dense aleatoire, doit rester nondiscriminant
    # quel que soit le seed (R30 est statistiquement uniforme).
    "random-dense": "10110011" * 8,  # 64 cellules
}

# Plancher d'echelle du test de seed (pli 9) : sous n_cells = 512, la fenetre
# packee KSF (W+1 etats) reste sous le plancher de cadrage zlib et R30 / R110
# rendent la meme constante -- mesure pli 7 (correctif #19826, 2026-10-09) :
# a n_cells = 64 les deux regles rendent KSF = 8.000 = n_cells/8 octets.
# Toute discrimination publiee sous ce plancher est un artefact de saturation,
# pas un resultat : le verdict la declare SATUREE et le CLI refuse d'y ecrire
# un JSON de resultats.
WOLFRAM_SEED_MIN_N_CELLS = 512

# Plancher absolu du verdict de discrimination. Un delta absolu inferieur a
# ce plancher est NONDISCRIMINANT quelle que soit la valeur du ratio
# normalise. Contre-mesure d'un artefact mesure (reserve c.6078963240,
# 2026-10-09) : random-dense a n=512 porte un ratio LZ de 0.307 pour un delta
# absolu de 0.027 -- normaliser par max(abs(v30), abs(v110)) sans plancher
# absolu fabrique un DISCRIMINANT sur du bruit quand les deux valeurs sont
# proches de zero. Les unites de mesure des trois instruments (ratio LZ, KSF
# en bits/cellule, std LZ76 normalisee) sont toutes dans [0, ~1.3], un seul
# plancher commun est commensurable. Valeur = seuil WEAK existant (0.05), le
# seuil qui etait deja dans le code avant ce correctif ; les deltas mesures a
# n=512 sont >= 0.19 (cas reels) et <= 0.03 (bruit), le plancher n'a pas ete
# choisi pour faire passer un cas limite.
WOLFRAM_SEED_ABS_DELTA_FLOOR = 0.05


def wolfram_seed_preset(name: str, n_cells: int) -> list[Cell]:
    """Retourne l'etat initial (1-D) du preset `name`, de taille `n_cells`.

    Le pattern source (chaine de 0/1) est tronque ou repete pour atteindre
    exactement `n_cells` cellules. Si le pattern source est trop court, on
    le repete ; s'il est trop long, on le tronque au centre.

    Conventions :
    - Tous les presets definis dans WOLFRAM_SEED_PRESETS sont des chaines
      de 0/1 de longueur divisible par 7 (motif "0001000") ou 8 ("10110011").
    - "single-cell" est un cas special : une seule cellule allumee au centre,
      le reste a zero. Implementé directement (pas via la chaine).
    """
    if name not in WOLFRAM_SEED_PRESETS:
        raise ValueError(
            f"Preset inconnu: {name}. Choices: {list(WOLFRAM_SEED_PRESETS.keys())}"
        )
    if name == "single-cell":
        state = [0] * n_cells
        state[n_cells // 2] = 1
        return state
    src = WOLFRAM_SEED_PRESETS[name]
    if len(src) == n_cells:
        return [int(c) for c in src]
    # Repeter le pattern jusqu'a atteindre n_cells, puis tronquer.
    out: list[Cell] = []
    while len(out) < n_cells:
        out.extend(int(c) for c in src)
    return out[:n_cells]


def wolfram_trajectory_from_state(
    init_state: Sequence[Cell], rule: int, n_steps: int
) -> list[list[Cell]]:
    """Trajectoire 1-D a partir d'un etat initial explicite.

    Wrapper local sur l'organe `ict.wolfram_step.wolfram_step` qui prend un
    etat initial explicite (au lieu d'un seed aleatoire). Retourne une liste
    d'etats 1-D successifs, chaque etat etant une liste de 0/1 de longueur
    n_cells = len(init_state).

    Convention de sortie : liste de listes Python (pas numpy), pour rester
    compatible avec k_trajectory.py pur-Python. La conversion vers numpy est
    faite en interne par wolfram_step.
    """
    try:
        from ict.wolfram_step import wolfram_step  # pli 2 PR #19793
    except ImportError as e:
        raise RuntimeError(
            "ict.wolfram_step introuvable. L'organe (PR #19793) doit etre "
            "present dans MyIA.AI.Notebooks/IIT/ICT-Series/ict/wolfram_step.py "
            f"et ce dossier doit etre dans sys.path. Erreur: {e}"
        )

    import numpy as np

    state = np.asarray(list(init_state), dtype=int)
    states: list[list[Cell]] = [state.tolist()]
    for _ in range(n_steps - 1):
        state = wolfram_step(state, rule)
        states.append(state.tolist())
    return states


def _traj_states_to_grid(traj_states: list[list[Cell]]) -> list[list[list[Cell]]]:
    """Convertit une trajectoire 1-D (liste d'etats) en liste de grilles 1xN.

    Chaque etat devient une grille a une seule ligne, N colonnes. Format
    compatible avec `grid_to_packed` et `measure_k_trajectory`.

    C'est le meme format que `wolfram_trajectory_to_grid` mais accepte des
    etats en listes Python au lieu de np.ndarray.
    """
    return [[list(state)] for state in traj_states]


def measure_seed_instrument_landscape(
    rules: Sequence[int] = (0, 4, 30, 110),
    presets: Sequence[str] = ("single-cell", "wolfram-0001000", "wolfram-defect", "random-dense"),
    n_cells: int = 64,
    n_steps: int = 64,
    instruments: Sequence[str] = ("lz", "ksf", "blocks"),
    context_sizes: Sequence[int] = (1, 2, 4, 8, 16, 32),
    block_sizes: Sequence[int] = (1, 2, 4, 8, 16, 32),
) -> list[dict]:
    """Mesure les 3 complexites (LZ, KSF, blocks) sur un paysage de seeds.

    Produit `len(rules) * len(presets)` runs, chacun mesure par
    `len(instruments)` complexites. Chaque entree du resultat a les cles :
    - rule (int), preset (str), n_cells (int), n_steps (int)
    - instrument (str) : 'lz' | 'ksf' | 'blocks'
    - Pour 'lz' : lz_W, lz_k_over_n, k_last, k_first, k_last_over_first
    - Pour 'ksf' : ksf_W (octets par contexte, trace), ksf_W_bits_per_cell,
      ksf_last_bits_per_cell (valeur de verdict, bits/cellule au plus grand
      contexte -- port pli 7)
    - Pour 'blocks' : blocks_W (entropie Shannon pour trace + complexite
      LZ76 normalisee par bloc -- port pli 8), blocks_lz76_mean_at_Wmax,
      blocks_lz76_std_at_Wmax (valeur de verdict)
    - summary (str) : phrase d'une ligne resume la mesure.

    Instruments portes des correctifs des plis freres (reserve c.6078963240,
    2026-10-09) :
    - KSF en bits par cellule (correctif pli 7, #19826) -- ksf_mean en octets
      vs reperes en bits/cellule = facteur 8 ;
    - complexite LZ76 normalisee par bloc (correctif pli 8, #19836) --
      l'entropie de Shannon est invariante a l'arrangement et ne peut pas
      separer une trajectoire periodique d'une trajectoire chaotique.

    Echelle : sous `WOLFRAM_SEED_MIN_N_CELLS`, la mesure tourne (diagnostic)
    mais `seed_discrimination_verdict` la declare SATUREE et le CLI refuse
    d'ecrire le JSON de resultats.
    """
    rows: list[dict] = []
    for rule in rules:
        for preset in presets:
            init_state = wolfram_seed_preset(preset, n_cells)
            traj_states = wolfram_trajectory_from_state(init_state, rule, n_steps)
            traj_grid = _traj_states_to_grid(traj_states)
            for instrument in instruments:
                row: dict = {
                    "rule": rule,
                    "preset": preset,
                    "n_cells": n_cells,
                    "n_steps": n_steps,
                    "instrument": instrument,
                }
                if instrument == "lz":
                    # LZ fenetre : K_trajectory sur la trajectoire 1-D
                    # Reutilise la fonction existante measure_k_trajectory.
                    lz_results = measure_k_trajectory(
                        f"wolfram_R{rule}_preset_{preset}", traj_grid, n_values=context_sizes
                    )
                    # lz_results : liste de {n, W, k_trajectory, k_over_n}
                    row["lz_W"] = {str(r["W"]): r["k_trajectory"] for r in lz_results}
                    row["lz_k_over_n"] = {
                        str(r["W"]): r["k_over_n"] for r in lz_results
                    }
                    last_w = max(int(r["W"]) for r in lz_results)
                    last_r = next(r for r in lz_results if int(r["W"]) == last_w)
                    first_r = min(lz_results, key=lambda r: int(r["W"]))
                    row["k_last"] = last_r["k_trajectory"]
                    row["k_first"] = first_r["k_trajectory"]
                    row["k_last_over_first"] = (
                        row["k_last"] / row["k_first"] if row["k_first"] > 0 else 0.0
                    )
                    row["summary"] = (
                        f"LZ K_last={row['k_last']} K_first={row['k_first']} "
                        f"ratio={row['k_last_over_first']:.3f}"
                    )
                elif instrument == "ksf":
                    # KSF : Kolmogorov structure function, calculee directement
                    # sur traj_states (generee depuis le preset explicite).
                    # On ne passe PAS par ksf_trajectory car celui-ci regenere
                    # sa propre trajectoire avec un seed random.
                    ksf_values_per_W: dict[int, list[int]] = {}
                    for W in context_sizes:
                        ksf_values_per_W[W] = []
                        for t in range(W, len(traj_states)):
                            ctx_states = traj_states[t - W:t]
                            cur_state = traj_states[t]
                            ctx_bytes = pack_states_1d(ctx_states)
                            ctx_plus_cur_bytes = pack_states_1d(ctx_states + [cur_state])
                            k_ctx = lz_compressed_length(ctx_bytes)
                            k_full = lz_compressed_length(ctx_plus_cur_bytes)
                            # K(W_t | context) = K(ctx || W_t) - K(ctx)
                            ksf_values_per_W[W].append(k_full - k_ctx)
                    ksf_W_means = {
                        W: (sum(vs) / len(vs) if vs else 0.0)
                        for W, vs in ksf_values_per_W.items()
                    }
                    # Port pli 7 (correctif #19826) : ksf_mean est en OCTETS,
                    # les seuils et reperes sont en BITS par cellule (facteur
                    # 8). La valeur de verdict est ksf_bits_per_cell au plus
                    # grand contexte -- la seule unite commensurable.
                    ksf_W_bits_per_cell = {
                        W: mean_bytes * 8.0 / n_cells
                        for W, mean_bytes in ksf_W_means.items()
                    }
                    row["ksf_W"] = {str(W): v for W, v in ksf_W_means.items()}
                    row["ksf_W_bits_per_cell"] = {
                        str(W): round(v, 4) for W, v in ksf_W_bits_per_cell.items()
                    }
                    last_w = max(ksf_W_means.keys())
                    first_w = min(ksf_W_means.keys())
                    row["ksf_last"] = ksf_W_means[last_w]  # octets (trace)
                    row["ksf_first"] = ksf_W_means[first_w]  # octets (trace)
                    row["ksf_last_minus_first"] = row["ksf_last"] - row["ksf_first"]
                    row["ksf_last_bits_per_cell"] = round(
                        ksf_W_bits_per_cell[last_w], 4
                    )
                    row["summary"] = (
                        f"KSF W={last_w}: {row['ksf_last_bits_per_cell']:.3f} "
                        f"bits/cellule ({row['ksf_last']:.3f} octets)"
                    )
                elif instrument == "blocks":
                    # Block decomposition -- port pli 8 (correctif #19836) :
                    # la statistique de verdict est la complexite LZ76
                    # normalisee par bloc (sensible a l'arrangement), pas
                    # l'entropie de Shannon (invariante a l'arrangement :
                    # H('0101..01') == H(desordre equilibre)). L'entropie
                    # reste mesuree pour tracabilite.
                    block_stats: list[dict] = []
                    for W in block_sizes:
                        ent = block_entropy_distribution(traj_states, W)
                        cpx = block_complexity_distribution(traj_states, W)
                        block_stats.append({
                            "W": W,
                            "entropy_mean": ent["mean"],
                            "entropy_std": ent["std"],
                            "complexity_mean": cpx["mean"],  # LZ76 normalisee
                            "complexity_std": cpx["std"],  # LZ76 normalisee
                            "n_blocks": cpx["n_blocks"],
                        })
                    row["blocks_W"] = block_stats
                    last_w = max(b["W"] for b in block_stats)
                    last_b = next(b for b in block_stats if b["W"] == last_w)
                    # Mesures de verdict : mean/std de la complexite LZ76 au
                    # plus grand W. Les anciennes cles blocks_*_at_W32
                    # portaient l'entropie de Shannon -- remplacees, pas
                    # re-remplies, pour ne pas laisser deux sens sous un nom.
                    row["blocks_lz76_mean_at_Wmax"] = last_b["complexity_mean"]
                    row["blocks_lz76_std_at_Wmax"] = last_b["complexity_std"]
                    row["summary"] = (
                        f"Blocks LZ76 mean@W{last_w}={last_b['complexity_mean']:.3f} "
                        f"std@W{last_w}={last_b['complexity_std']:.3f} "
                        f"(n_blocks={last_b['n_blocks']})"
                    )
                else:
                    raise ValueError(f"Instrument inconnu: {instrument}")
                rows.append(row)
    return rows


def seed_discrimination_verdict(landscape: list[dict]) -> dict:
    """Verdict de discrimination R30 vs R110 sur le paysage de seeds.

    Compare, pour chaque instrument et chaque preset, la mesure R30 vs R110.
    Renvoie :
    - per_instrument : dict[str, dict[str, verdict]] -- verdict par preset
    - global : verdict agrege sur tous les presets
    - discriminative_presets : nombre de presets ou R30 != R110 significatif
    - total_presets : nombre total de presets testes
    - measurements : valeurs brutes (v30, v110, delta absolu, ratio) par
      cellule -- le verdict est falsifiable sans relancer la mesure.

    Verdict par preset et par instrument :
    - 'DISCRIMINANT' : R30 et R110 nettement differents (ratio > 0.20 ET
      delta absolu >= WOLFRAM_SEED_ABS_DELTA_FLOOR)
    - 'WEAK-DISCRIMINANT' : difference existe mais petite (ratio > 0.05 et
      delta absolu >= plancher)
    - 'NONDISCRIMINANT' : R30 et R110 indistinguables -- y compris quand le
      ratio normalise est eleve mais le delta absolu est sous le plancher
      (deux valeurs proches de zero : le ratio y fabrique du bruit)
    - 'SATURATED' : n_cells < WOLFRAM_SEED_MIN_N_CELLS -- la mesure est un
      artefact de cadrage, aucun verdict publiable n'en sort
    - 'INCOMPLETE' : paire R30/R110 manquante dans le paysage

    Garde d'echelle (reserve c.6078963240) : a n_cells = 64, le verdict
    publie par la version initiale etait un artefact de saturation zlib, pas
    une mesure de discrimination.
    """
    if not landscape:
        return {
            "per_instrument": {},
            "global": "EMPTY",
            "discriminative_presets": 0,
            "total_presets": 0,
            "measurements": {},
        }

    presets = sorted({r["preset"] for r in landscape})
    instruments = sorted({r["instrument"] for r in landscape})

    # Garde d'echelle : sous WOLFRAM_SEED_MIN_N_CELLS, la fenetre packee KSF
    # est sous le plancher de cadrage zlib et R30 / R110 rendent la meme
    # constante -- toute discrimination y est un artefact (cf. pli 7).
    n_cells_seen = {r.get("n_cells", 0) for r in landscape}
    n_cells = max(n_cells_seen) if n_cells_seen else 0
    if n_cells < WOLFRAM_SEED_MIN_N_CELLS:
        return {
            "per_instrument": {
                instr: {p: "SATURATED" for p in presets}
                for instr in instruments
            },
            "global": (
                f"WOLFRAM-SEED-SATURATED (n_cells={n_cells} < "
                f"{WOLFRAM_SEED_MIN_N_CELLS} : la fenetre packee est sous le "
                f"plancher de cadrage zlib, R30 et R110 y rendent la meme "
                f"constante -- toute discrimination publiee a cette echelle "
                f"est un artefact)"
            ),
            "discriminative_presets": 0,
            "total_presets": len(presets) * len(instruments),
            "measurements": {},
        }

    # Par (instrument, preset), comparer R30 et R110.
    # Pour LZ : k_last_over_first (ratio, sans unite).
    # Pour KSF : ksf_last_bits_per_cell (bits/cellule -- port pli 7).
    # Pour blocks : blocks_lz76_std_at_Wmax (std LZ76 normalisee -- port pli 8).
    def measure_value(row: dict) -> float:
        if row["instrument"] == "lz":
            return row["k_last_over_first"]
        if row["instrument"] == "ksf":
            return row["ksf_last_bits_per_cell"]
        if row["instrument"] == "blocks":
            return row["blocks_lz76_std_at_Wmax"]
        return 0.0

    per_instrument: dict[str, dict[str, str]] = {}
    measurements: dict[str, dict[str, dict]] = {}
    discriminative_count = 0
    for instrument in instruments:
        per_instrument[instrument] = {}
        measurements[instrument] = {}
        for preset in presets:
            r30 = next(
                (
                    r
                    for r in landscape
                    if r["instrument"] == instrument
                    and r["preset"] == preset
                    and r["rule"] == 30
                ),
                None,
            )
            r110 = next(
                (
                    r
                    for r in landscape
                    if r["instrument"] == instrument
                    and r["preset"] == preset
                    and r["rule"] == 110
                ),
                None,
            )
            if r30 is None or r110 is None:
                per_instrument[instrument][preset] = "INCOMPLETE"
                continue
            v30 = measure_value(r30)
            v110 = measure_value(r110)
            abs_delta = abs(v30 - v110)
            denom = max(abs(v30), abs(v110), 1e-9)
            ratio = abs_delta / denom
            measurements[instrument][preset] = {
                "v30": round(v30, 4),
                "v110": round(v110, 4),
                "abs_delta": round(abs_delta, 4),
                "ratio": round(ratio, 4),
            }
            if v30 == 0 and v110 == 0:
                per_instrument[instrument][preset] = "NONDISCRIMINANT"
                continue
            # Plancher absolu AVANT le ratio : un delta absolu sous le
            # plancher est du bruit, quelle que soit la valeur du ratio
            # normalise (qui explose quand les deux valeurs sont proches de
            # zero). Sans ce plancher, la normalisation par le max fabrique
            # un DISCRIMINANT sur du bruit (reserve c.6078963240).
            if abs_delta < WOLFRAM_SEED_ABS_DELTA_FLOOR:
                per_instrument[instrument][preset] = "NONDISCRIMINANT"
                continue
            if ratio > 0.20:
                verdict = "DISCRIMINANT"
            elif ratio > 0.05:
                verdict = "WEAK-DISCRIMINANT"
            else:
                verdict = "NONDISCRIMINANT"
            per_instrument[instrument][preset] = verdict
            if verdict == "DISCRIMINANT":
                discriminative_count += 1

    # Verdict global : un seul preset discriminant sur les 3 instruments ?
    n_total = len(presets) * len(instruments)
    if discriminative_count == 0:
        global_verdict = "NONDISCRIMINANT_CONFIRME"
    elif discriminative_count == n_total:
        global_verdict = "DISCRIMINANT_FORT"
    else:
        global_verdict = "DISCRIMINANT_FAIBLE"

    return {
        "per_instrument": per_instrument,
        "global": global_verdict,
        "discriminative_presets": discriminative_count,
        "total_presets": n_total,
        "measurements": measurements,
    }


def cmd_wolfram_seed_test(args: argparse.Namespace) -> int:
    """Mode wolfram-seed-test : paysage de seeds × 3 complexites × 4 regles.

    Teste la discrimination R30 vs R110 sous differentes conditions de seed,
    avec les instruments corriges des plis freres (KSF en bits/cellule,
    blocks en complexite LZ76 normalisee). Echelle canonique : n=512
    (WOLFRAM_SEED_MIN_N_CELLS) -- sous ce plancher la mesure est SATUREE et
    le JSON de resultats est refuse.

    Usage :
        python scripts/hashlife/k_trajectory.py --mode wolfram-seed-test \\
            --n-cells 512 --n-steps 512 \\
            --json-out scripts/hashlife/wolfram_seed_test_results.json
    """
    rules = (0, 4, 30, 110)
    presets = tuple(args.seed_presets) if args.seed_presets else (
        "single-cell", "wolfram-0001000", "wolfram-defect", "random-dense"
    )
    instruments = ("lz", "ksf", "blocks")

    print(f"== Wolframe seed test == n_cells={args.n_cells} n_steps={args.n_steps}")
    print(f"  Regles : {rules}")
    print(f"  Presets : {presets}")
    print(f"  Instruments : {instruments}")
    if args.n_cells < WOLFRAM_SEED_MIN_N_CELLS:
        print(
            f"[WARN] n_cells={args.n_cells} < WOLFRAM_SEED_MIN_N_CELLS="
            f"{WOLFRAM_SEED_MIN_N_CELLS} : mesure SATUREE (plancher de cadrage "
            f"zlib), le verdict sera WOLFRAM-SEED-SATURATED."
        )
        if args.json_out:
            print(
                "[ERROR] --json-out refuse sous le plancher d'echelle : on ne "
                "publie pas un artefact de saturation. Relancer avec --n-cells "
                f">= {WOLFRAM_SEED_MIN_N_CELLS}."
            )
            return 1
    print()

    landscape = measure_seed_instrument_landscape(
        rules=rules,
        presets=presets,
        n_cells=args.n_cells,
        n_steps=args.n_steps,
        instruments=instruments,
    )

    # Affichage par preset
    for preset in presets:
        print(f"--- preset = {preset} ---")
        for rule in rules:
            print(f"  Rule {rule:3d} (class {WOLFRAM_BLOCK_LANDMARKS.get(rule, ('?',))[0]})")
            for instrument in instruments:
                row = next(
                    (
                        r
                        for r in landscape
                        if r["preset"] == preset
                        and r["rule"] == rule
                        and r["instrument"] == instrument
                    ),
                    None,
                )
                if row:
                    print(f"    [{instrument:6s}] {row['summary']}")
        print()

    # Verdict
    print("=== Verdict discrimination R30 vs R110 (par preset x instrument) ===")
    verdict = seed_discrimination_verdict(landscape)
    for instrument, verdicts in verdict["per_instrument"].items():
        print(f"  {instrument}:")
        for preset, v in verdicts.items():
            print(f"    {preset:25s}  {v}")
    print()
    print(f"=== Verdict global ===")
    print(f"  {verdict['global']} ({verdict['discriminative_presets']}/{verdict['total_presets']} cellules discriminantes)")

    if args.json_out:
        out = {
            "landscape": landscape,
            "verdict": verdict,
            "n_cells": args.n_cells,
            "n_steps": args.n_steps,
            "rules": list(rules),
            "presets": list(presets),
            "instruments": list(instruments),
        }
        Path(args.json_out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"\n[INFO] resultats ecrits dans {args.json_out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
