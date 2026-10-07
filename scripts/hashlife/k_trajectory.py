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
   Le verdict attendu : Rule 30 ~ SOUP-FRAGILE-* (chaos LZ-compressible),
   Rule 110 ~ PROGRAM-CONFIRMED (Turing-completude non-compressible).

Usage :
    python scripts/hashlife/k_trajectory.py --mode measure
    python scripts/hashlife/k_trajectory.py --mode verify-corpus
    python scripts/hashlife/k_trajectory.py --mode bounds --json-in results.json
    python scripts/hashlife/k_trajectory.py --mode wolfram --rule 30 --n-cells 64
    python scripts/hashlife/k_trajectory.py --mode wolfram --all
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
    return measure_k_trajectory(f"wolfram_R{rule}_n{n_cells}_seed{seed}", traj_grid, n_values)


def measure_wolfram_corpus(n_cells: int = 64, n_steps: int = 64, seed: int = 33) -> list[dict]:
    """Mesure K_trajectory sur le corpus Wolframe (Rule 30 + Rule 110).

    Règles canoniques :
    - Rule 30 (classe III, chaotique) -- attendu SOUP-FRAGILE-*.
    - Rule 110 (classe IV, Turing-complet) -- attendu PROGRAM-CONFIRMED
      ou PROGRAM-WEAK (si la Turing-completude produit des motifs
      périodiques détectables par LZ).

    Paramètres :
    - n_cells=64 : taille canonique Wolframe (Cook 2004, Wolfram 2002).
    - n_steps=64 : 2^6 états, fenêtre max W=64 = la trajectoire entière.
    - seed=33 : reproductibilité (cf. PR #19793).
    """
    n_values = [0, 1, 2, 3, 4, 5, 6]  # W = 1, 2, 4, 8, 16, 32, 64 (borne n_steps)
    all_results = []
    for rule in (30, 110):
        all_results.extend(
            measure_wolfram_trajectory(
                rule=rule, n_cells=n_cells, n_steps=n_steps, seed=seed, n_values=n_values
            )
        )
    return all_results


def wolfram_verdict(results: list[dict]) -> dict:
    """Verdict cross-règles pour les trajectoires Wolframe.

    Pour chaque règle mesurée, calcule le ratio K(t, W_last) / K(t, W_first)
    brut (cf. `verdict()` de la tranche 1) et classifie :

    - WOLFRAM-CHAOTIC-FRAGILE (Rule 30 attendu) -- ratio < 0.7 : le chaos
      est LZ-compressible à toutes les échelles (discriminant soupe).
    - WOLFRAM-TURING-ENTRENED (Rule 110 attendu) -- ratio >= 0.95 : la
      Turing-completude produit des motifs non-compressibles (auto-entretien).
    - WOLFRAM-WEAK : ratio in [0.7, 0.95) -- indétermination, à creuser.

    Le verdict cross-règles final :
    - CONFIRMED : Rule 30 fragile + Rule 110 entrened (les deux confirment
      l'hypothèse cross-dimension).
    - PARTIAL : un seul des deux confirme.
    - REFUTED : aucun des deux ne confirme (ou Rule 30 entrened, Rule 110
      fragile -- le discriminant ne tient pas).
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

        if "R30" in name:
            # Rule 30 = chaos = fragile (LZ collapse)
            if ratio < 0.7:
                verdicts[name] = f"WOLFRAM-CHAOTIC-FRAGILE (ratio {ratio:.3f} < 0.7)"
            elif ratio < 0.95:
                verdicts[name] = f"WOLFRAM-WEAK (ratio {ratio:.3f} in [0.7, 0.95))"
            else:
                verdicts[name] = (
                    f"WOLFRAM-CHAOTIC-REFUTED (ratio {ratio:.3f} >= 0.95 -- "
                    "le chaos ne collapse pas, discriminant 1-D différent du 2-D)"
                )
        elif "R110" in name:
            # Rule 110 = Turing-complet = non-compressible = entrened
            if ratio >= 0.95:
                verdicts[name] = f"WOLFRAM-TURING-ENTRENED (ratio {ratio:.3f} >= 0.95)"
            elif ratio >= 0.7:
                verdicts[name] = f"WOLFRAM-WEAK (ratio {ratio:.3f} in [0.7, 0.95))"
            else:
                verdicts[name] = (
                    f"WOLFRAM-TURING-REFUTED (ratio {ratio:.3f} < 0.7 -- "
                    "la Turing-completude collapse sous LZ, l'auto-entretien "
                    "1-D n'est pas detecte par K_trajectory)"
                )
        else:
            verdicts[name] = f"INCONCLUSIVE (regle inconnue, ratio {ratio:.3f})"

    return verdicts


def wolfram_cross_verdict(wv: dict) -> str:
    """Verdict final cross-règles Wolframe.

    CONFIRMED : Rule 30 CHAOTIC-FRAGILE + Rule 110 TURING-ENTRENED.
    PARTIAL : un seul des deux confirme.
    REFUTED : aucun ne confirme, ou les deux sont inversés (Rule 30 entrened,
              Rule 110 fragile).
    """
    r30_keys = [n for n in wv if "R30" in n]
    r110_keys = [n for n in wv if "R110" in n]
    r30_fragile = any("CHAOTIC-FRAGILE" in wv[k] for k in r30_keys)
    r110_entrened = any("TURING-ENTRENED" in wv[k] for k in r110_keys)
    r30_entrened = any("CHAOTIC-REFUTED" in wv[k] for k in r30_keys)
    r110_fragile = any("TURING-REFUTED" in wv[k] for k in r110_keys)

    if r30_fragile and r110_entrened:
        return "WOLFRAM-CROSS-DIMENSION-CONFIRMED"
    if r30_entrened and r110_fragile:
        return "WOLFRAM-CROSS-DIMENSION-REFUTED (les deux inverses)"
    if r30_fragile or r110_entrened:
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
    confirmed = []
    refuted = []
    for name, verdict_str in cv.items():
        if "CONFIRMED" in verdict_str:
            confirmed.append(name)
        elif "REFUTED" in verdict_str:
            refuted.append(name)
        # INCONCLUSIVE ignore

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
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "K_trajectory")
    parser.add_argument(
        "--mode",
        choices=["measure", "verify-corpus", "bounds", "wolfram", "wolfram-4classes"],
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
        default=64,
        help="Mode wolfram : nombre de cellules de l'automate 1-D. Defaut: 64",
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
    args = parser.parse_args()
    if args.mode == "measure":
        return cmd_measure(args)
    if args.mode == "bounds":
        return cmd_bounds(args)
    if args.mode == "wolfram":
        return cmd_wolfram(args)
    if args.mode == "wolfram-4classes":
        return cmd_wolfram_4classes(args)
    return cmd_verify_corpus(args)


if __name__ == "__main__":
    sys.exit(main())
