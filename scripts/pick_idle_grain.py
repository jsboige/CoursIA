#!/usr/bin/env python3
"""Tirage aleatoire pondere d'une poignee de grains dans le pool d'issues ouvertes.

Pourquoi cet organe existe
--------------------------
`gh issue list` plafonne a 30 resultats par defaut, tries par recence. Avec un
pool de 140 issues dont 89 creees dans les 7 derniers jours, un worker qui
scanne le pool ne voit **rien de plus vieux que ~6 jours** -- il repioche
mecaniquement dans ce que le coordinateur vient de creer, ce qui referme la
boucle de monoculture que `.claude/rules/variation-protocol.md` cherche a
ouvrir. Le picker defait la troncature par construction (`--limit 300`, une
seule requete) et rend la selection *aleatoire ponderee* au lieu de
*recente-d'abord*.

Il **ne decide pas**. Il tire une poignee de candidats et laisse a l'agent le
choix final selon les criteres de variete de sa lane courante (G-VAR-1/2/3).

Trois urnes, parce que le pool n'est pas homogene
-------------------------------------------------
- **grains**    : issues unitaires, directement executables.
- **umbrella**  : EPIC / conteneurs. Le tirage rend l'EPIC ; l'agent pioche ou
                  cree un sous-grain dedans. C'est la que vit le DEEP/CONTENU
                  ancien -- une urne unique ne le montrerait jamais.
- **delivered** : issues portant `candidate-delivered` (livrees par une PR
                  mergee mais jamais fermees). Les offrir a chaque tirage est
                  ce qui fait *refluer* le compte sans batch-close aveugle :
                  l'agent verifie firsthand (G.9) puis ferme avec preuve, ou
                  retire le label en disant pourquoi.

Usage
-----
    python scripts/pick_idle_grain.py --lane myia-po-2026:CoursIA
    python scripts/pick_idle_grain.py --lane myia-po-2023:CoursIA-2 --prev-genre guard
    python scripts/pick_idle_grain.py --lane <l> --reroll 1        # nouveau tirage
    python scripts/pick_idle_grain.py --lane <l> --check-claims    # + verif claims
    python scripts/pick_idle_grain.py --lane <l> --json            # sortie machine

Le tirage est **deterministe par (lane, heure UTC, reroll)** : deux lanes
tirent des candidats differents a la meme minute, et une meme lane qui relance
dans l'heure retrouve son tirage (idempotent, pas de thrash). `--reroll N`
decale la graine quand aucun candidat ne convient.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import random
import re
import subprocess
import sys

REPO = "jsboige/CoursIA"

# Enumeration CLOSE de variation-protocol.md, partitionnee CONTENU / META.
CONTENU = {
    "lean", "qc", "training", "genai",
    "notebook-python", "notebook-dotnet", "research-code",
}
META = {"guard", "tooling", "ledger", "docs", "readme", "test", "refactor"}

# Inference de genre : (regex sur titre+labels, genre). Premiere qui matche.
# Volontairement grossier -- le genre infere est une *aide au tri*, pas un
# verdict : l'agent pose le vrai tag Grain: lui-meme.
GENRE_RULES: list[tuple[str, str]] = [
    (r"\.lean\b|\blean[-_ ]|\blake\b|sorry|mathlib|grothendieck|knot|hashlife|tao\b", "lean"),
    (r"quantconnect|\bqc[-_ (]|backtest|quantbook|lean-cli|sharpe", "qc"),
    (r"training|post[- ]?training|\bppo\b|fine[- ]?tun|checkpoint|walk[- ]?forward", "training"),
    (r"genai|comfyui|diffusion|audiobook|\btts\b|whisper|acestep|voice|image gener", "genai"),
    (r"\.ipynb|notebook", "notebook-python"),
    (r"c#|csharp|\.net|dotnet|roslyn|aspire|nuget|semantickernel", "notebook-dotnet"),
    (r"z3|solveur|solver|automat|opensp|tweety|pymc|infer\.net|prover", "research-code"),
    (r"workflow|\bci\b|gate\b|guard|gitleaks|check-|advisory", "guard"),
    (r"script|tooling|organe|cli\b|papermill|render_envs", "tooling"),
    (r"readme", "readme"),
    (r"\bdocs?\b|documentation|resync doc|cadrage", "docs"),
    (r"\btests?\b|pytest|vitest", "test"),
    (r"ledger|registre|inventaire|catalog", "ledger"),
    (r"refactor|consolidation|migration", "refactor"),
]

NOW = dt.datetime.now(dt.timezone.utc)


def infer_genre(title: str, labels: list[str]) -> str:
    hay = (title + " " + " ".join(labels)).lower()
    for pattern, genre in GENRE_RULES:
        if re.search(pattern, hay):
            return genre
    return "docs"


def age_days(created: str) -> int:
    created_dt = dt.datetime.fromisoformat(created.replace("Z", "+00:00"))
    return max(0, (NOW - created_dt).days)


def fetch_pool() -> list[dict]:
    """Une seule requete, limite haute -- c'est ce qui defait la troncature."""
    out = subprocess.run(
        ["gh", "issue", "list", "--repo", REPO, "--state", "open", "--limit", "300",
         "--json", "number,title,labels,createdAt,updatedAt"],
        capture_output=True, text=True, encoding="utf-8", check=True,
    ).stdout
    raw = json.loads(out)
    pool = []
    for it in raw:
        labels = [lb["name"] for lb in it.get("labels", [])]
        title = it["title"]
        is_umbrella = "EPIC" in labels or title.upper().lstrip("[").startswith("EPIC")
        pool.append({
            "number": it["number"],
            "title": title,
            "labels": labels,
            "age": age_days(it["createdAt"]),
            "genre": infer_genre(title, labels),
            "klass": (
                "delivered" if "candidate-delivered" in labels
                else "umbrella" if is_umbrella
                else "grain"
            ),
        })
    return pool


def weight(item: dict, prev_genre: str | None) -> float:
    """Trois facteurs, tous doux, tous explicables en une ligne.

    Trop de ponderation reproduirait une monoculture avec des etapes en plus :
    on se limite a ce que les gates du variation-protocol demandent deja.
    """
    # Anciennete : sert "faire refluer doucement" -- la traine est la ou le
    # compte s'accumule. 6 mois pesent ~4x une issue de la semaine.
    w = 1.0 + math.log2(1.0 + item["age"] / 7.0)
    # G-VAR-3 au tirage plutot qu'en HOLD a posteriori.
    if prev_genre and item["genre"] == prev_genre:
        w *= 0.25
    # G-VAR-1 : le plancher exige DEEP/MED **et** CONTENU.
    if item["genre"] in CONTENU:
        w *= 2.0
    return w


def draw(items: list[dict], n: int, rng: random.Random, prev_genre: str | None) -> list[dict]:
    """Tirage pondere sans remise (Efraimidis-Spirakis : cle = u^(1/w))."""
    if not items:
        return []
    keyed = []
    for it in items:
        w = weight(it, prev_genre)
        u = rng.random() or 1e-12
        keyed.append((u ** (1.0 / w), w, it))
    keyed.sort(key=lambda t: t[0], reverse=True)
    picked = []
    for _, w, it in keyed[:n]:
        it = dict(it)
        it["weight"] = round(w, 2)
        picked.append(it)
    return picked


def check_claims(numbers: list[int]) -> dict[int, str]:
    """Verif claims sur les seuls candidats tires (N appels, pas 140)."""
    verdicts = {}
    for n in numbers:
        try:
            r = subprocess.run(
                [sys.executable, "scripts/check_lane_claim.py", str(n)],
                capture_output=True, text=True, encoding="utf-8", timeout=60,
            )
            head = (r.stdout or r.stderr or "").strip().splitlines()
            verdicts[n] = head[0][:60] if head else f"exit={r.returncode}"
        except Exception as exc:  # noqa: BLE001 - diagnostic best-effort
            verdicts[n] = f"(check indisponible: {type(exc).__name__})"
    return verdicts


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lane", required=True, help="machine:workspace, ex. myia-po-2026:CoursIA")
    ap.add_argument("--prev-genre", default=None,
                    help="genre du grain precedent de la lane (penalise ce genre au tirage)")
    ap.add_argument("--grains", type=int, default=4, help="candidats urne 'grain' (defaut 4)")
    ap.add_argument("--umbrellas", type=int, default=2, help="candidats urne 'umbrella' (defaut 2)")
    ap.add_argument("--delivered", type=int, default=2, help="candidats urne 'delivered' (defaut 2)")
    ap.add_argument("--reroll", type=int, default=0, help="decale la graine pour un nouveau tirage")
    ap.add_argument("--check-claims", action="store_true", help="verifie les claims sur les tires")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    args = ap.parse_args()

    pool = fetch_pool()
    by_class = {k: [it for it in pool if it["klass"] == k]
                for k in ("grain", "umbrella", "delivered")}

    # Graine : (lane, heure UTC, reroll). Lanes differentes -> tirages
    # differents ; meme lane dans l'heure -> tirage identique (idempotent).
    stamp = NOW.strftime("%Y-%m-%dT%H")
    seed_src = f"{args.lane}|{stamp}|{args.reroll}"
    seed = int(hashlib.sha256(seed_src.encode()).hexdigest()[:16], 16)
    rng = random.Random(seed)

    picks = (
        draw(by_class["grain"], args.grains, rng, args.prev_genre)
        + draw(by_class["umbrella"], args.umbrellas, rng, args.prev_genre)
        + draw(by_class["delivered"], args.delivered, rng, None)
    )

    claims = check_claims([p["number"] for p in picks]) if args.check_claims else {}

    if args.json:
        print(json.dumps({
            "lane": args.lane, "seed_src": seed_src,
            "pool": {k: len(v) for k, v in by_class.items()},
            "picks": picks, "claims": {str(k): v for k, v in claims.items()},
        }, ensure_ascii=False, indent=2))
        return 0

    print(f"Pool ouvert : {len(pool)} issues  "
          f"= {len(by_class['grain'])} grains "
          f"+ {len(by_class['umbrella'])} umbrella "
          f"+ {len(by_class['delivered'])} candidate-delivered")
    print(f"Lane {args.lane} | graine {stamp}"
          + (f" | reroll {args.reroll}" if args.reroll else "")
          + (f" | genre precedent penalise : {args.prev_genre}" if args.prev_genre else ""))
    print()
    header = f"{'urne':<10} {'issue':<8} {'age':>5}  {'genre':<16} {'p':>5}  titre"
    print(header)
    print("-" * len(header))
    for p in picks:
        mark = "*" if p["genre"] in CONTENU else " "
        print(f"{p['klass']:<10} #{p['number']:<7} {p['age']:>4}j  "
              f"{p['genre']:<15}{mark} {p['weight']:>5}  {p['title'][:62]}")
        if p["number"] in claims:
            print(f"{'':>10} {'':>8} {'':>5}  claim: {claims[p['number']]}")
    print()
    print("* = genre CONTENU (seul un genre CONTENU en DEEP/MED tient le plancher G-VAR-1).")
    print("umbrella  -> pioche ou cree un SOUS-grain dedans, ne claim pas l'EPIC entier.")
    print("delivered -> verifie firsthand que la PR livrante satisfait l'acceptance :")
    print("             si oui `gh issue close`, sinon retire le label en disant pourquoi.")
    print("Avant d'EDITER : python scripts/check_lane_claim.py <N>  (lane-claim-protocol).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
