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

Regime : voie normale, pas filet de secours (mandat user 2026-08-20)
--------------------------------------------------------------------
Ce tirage est le **premier geste de chaque cycle**, pas le recours d'une lane
en panne de grain. Un steering nomme par le coordinateur reste possible -- il
devient l'**exception**, et doit lui-meme etre equilibre entre familles et
genres. La raison est mecanique : tant que la selection par defaut restait
"ce que je vois", elle restait "ce qui est recent", et les sujets conduits a
leur terme etaient toujours ceux du moment.

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
    "notebook-python", "notebook-dotnet", "notebook-lean", "slides",
    "research-code",
}
META = {"guard", "tooling", "ledger", "docs", "readme", "test", "refactor"}

# Inference de genre : (regex sur titre+labels, genre). Premiere qui matche.
# Volontairement grossier -- le genre infere est une *aide au tri*, pas un
# verdict : l'agent pose le vrai tag Grain: lui-meme.
GENRE_RULES: list[tuple[str, str]] = [
    # AVANT la regle `lean` generique : un notebook a kernel Lean est du
    # travail de NOTEBOOK (materiel pedagogique), pas du travail de lake.
    # L'ordre compte -- la regle generique ci-dessous matcherait "notebook
    # Lean" en premier et le genre notebook-lean serait inatteignable.
    # `[.]ipynb` == `\.ipynb` sans backslash a transporter.
    (r"(?=.*(?:notebook|[.]ipynb|companion))(?=.*lean)", "notebook-lean"),
    (r"\.lean\b|\blean[-_ ]|\blake\b|sorry|mathlib|grothendieck|knot|hashlife|tao\b", "lean"),
    (r"quantconnect|\bqc[-_ (]|backtest|quantbook|lean-cli|sharpe", "qc"),
    (r"training|post[- ]?training|\bppo\b|fine[- ]?tun|checkpoint|walk[- ]?forward", "training"),
    (r"genai|comfyui|diffusion|audiobook|\btts\b|whisper|acestep|voice|image gener", "genai"),
    (r"\.ipynb|notebook", "notebook-python"),
    (r"slidev|\bslides?\b|deck\b", "slides"),
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
            "idle": age_days(it["updatedAt"]),
            "updated_at": it["updatedAt"],
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
    # Delaissement : jours depuis la DERNIERE activite, distinct de l'age de
    # creation (mesure du 2026-08-20 sur les 140 ouvertes : pearson r = 0.334,
    # donc pas redondant). 91/140 avaient bouge dans les 24 h -- le bruit du
    # moment ; les 12 plus inactives comptaient 9 EPICs. C'est cette population
    # que le tirage doit atteindre : un EPIC intouche depuis 53 j pese ~2.4x un
    # sujet du jour, assez pour remonter, trop peu pour devenir la seule veine.
    w *= 1.0 + math.log2(1.0 + item["idle"] / 14.0)
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


def _summarize_claim(out: str, returncode: int) -> str:
    """Reduit la sortie de ``check_lane_claim.py`` a un verdict d'une ligne.

    La sortie melange une phrase humaine (uniquement quand c'est bloque) puis
    un objet JSON. Prendre la premiere ligne telle quelle affichait ``{`` des
    que le grain etait libre -- soit exactement le cas ou le tirage a besoin
    d'un verdict lisible. On lit donc le JSON, qui porte les deux cas.
    """
    brace = out.find("{")
    if brace != -1:
        # ``raw_decode`` et pas ``loads`` : la sortie porte une phrase humaine
        # APRES l'objet (``CLEAR: no other lane claims #N.``), et ``loads``
        # echoue sur ce suffixe -- c'est ce qui laissait passer un ``{``.
        try:
            data, _ = json.JSONDecoder().raw_decode(out[brace:])
        except json.JSONDecodeError:
            data = None
        if isinstance(data, dict):
            blocking = data.get("blocking_lanes") or []
            if blocking:
                return "BLOQUE par " + ", ".join(blocking)
            if data.get("my_active_claim"):
                return "deja claim par cette lane"
            stale = data.get("stale_claims") or []
            if stale:
                return f"libre (claim perime : {', '.join(map(str, stale))})"
            return "libre"
    first = out.strip().splitlines()
    if first:
        return first[0][:60]
    return f"exit={returncode}"


def check_claims(numbers: list[int], lane: str) -> dict[int, str]:
    """Verif claims sur les seuls candidats tires (N appels, pas 140).

    ``--lane`` est **requis** par ``check_lane_claim.py`` : sans lui, l'appel
    sort en erreur d'usage et chaque candidat affichait ``usage: ...`` a la
    place de son verdict -- un check qui ne peut pas rougir, donc pas un check.
    """
    verdicts = {}
    for n in numbers:
        try:
            r = subprocess.run(
                [sys.executable, "scripts/check_lane_claim.py",
                 "--lane", lane, str(n)],
                capture_output=True, text=True, encoding="utf-8", timeout=60,
            )
            verdicts[n] = _summarize_claim(r.stdout or r.stderr or "",
                                           r.returncode)
        except Exception as exc:  # noqa: BLE001 - diagnostic best-effort
            verdicts[n] = f"(check indisponible: {type(exc).__name__})"
    return verdicts


def recent_delivery(picks: list[dict]) -> dict[int, str]:
    """Annote les candidats tires dont une PR mergee les reference plus
    recemment que la derniere mise a jour de l'issue.

    #12174 : le label ``candidate-delivered`` est pose par un workflow
    ``schedule:`` quotidien, dans une flotte qui merge plusieurs PRs par heure
    -- au tirage de 16:47Z, #12014 etait classee ``grain`` alors que #12077
    (mergee 16:19Z) avait deja livre 3 de ses 4 items. Le body d'une issue est
    date de sa redaction et un claim ne dit rien d'une livraison : la
    recherche de PRs mergees est la troisieme surface de grounding, et ce
    geste doit vivre dans l'outil qui propose le grain, pas dans la discipline
    de qui le lit. Une requete par candidat tire, jamais un balayage du pool.

    L'annotation **n'ecarte pas** le candidat (parite avec la doctrine
    ``candidate-delivered`` : signale, ne ferme pas) : elle change ce qu'on
    en dit, pas s'il est pris.
    """
    notes: dict[int, str] = {}
    for p in picks:
        n = p["number"]
        try:
            out = subprocess.run(
                ["gh", "pr", "list", "--repo", REPO, "--state", "merged",
                 "--limit", "20", "--search", f"{n} in:title,body",
                 "--json", "number,mergedAt"],
                capture_output=True, text=True, encoding="utf-8", check=True,
                timeout=30,
            ).stdout
            prs = json.loads(out)
        except Exception as exc:  # noqa: BLE001 - diagnostic best-effort
            notes[n] = f"(recherche livraison indisponible: {type(exc).__name__})"
            continue
        if not prs:
            continue
        latest = max(prs, key=lambda pr: pr.get("mergedAt") or "")
        merged = latest.get("mergedAt") or ""
        # Fusion plus recente que la derniere activite de l'issue = le corps
        # visible est potentiellement periéme par rapport au reel. Une fusion
        # ANTERIEURE a updatedAt est deja digeree par le body (ou les
        # commentaires) : pas d'annotation, sinon le signal noie.
        if merged and merged > p.get("updated_at", ""):
            extra = f" (+{len(prs) - 1} autres)" if len(prs) > 1 else ""
            notes[n] = (f"LIVRAISON RECENTE : #{latest['number']} mergee {merged}{extra} "
                        f"(issue non mise a jour depuis {p.get('updated_at', '?')}) "
                        f"-> confronter le body au reel AVANT de dispatcher")
    return notes


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

    claims = check_claims([p["number"] for p in picks], args.lane) if args.check_claims else {}
    delivery = recent_delivery(picks)

    if args.json:
        print(json.dumps({
            "lane": args.lane, "seed_src": seed_src,
            "pool": {k: len(v) for k, v in by_class.items()},
            "picks": picks, "claims": {str(k): v for k, v in claims.items()},
            "recent_delivery": {str(k): v for k, v in delivery.items()},
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
    header = (f"{'urne':<10} {'issue':<8} {'age':>5} {'inact':>6}  "
              f"{'genre':<16} {'p':>5}  titre")
    print(header)
    print("-" * len(header))
    for p in picks:
        mark = "*" if p["genre"] in CONTENU else " "
        print(f"{p['klass']:<10} #{p['number']:<7} {p['age']:>4}j {p['idle']:>5}j  "
              f"{p['genre']:<15}{mark} {p['weight']:>5}  {p['title'][:62]}")
        if p["number"] in claims:
            print(f"{'':>10} {'':>8} {'':>5} {'':>6}  claim: {claims[p['number']]}")
        if p["number"] in delivery:
            note = delivery[p["number"]]
            head, sep, tail = note.partition("-> ")
            print(f"{'':>10} {'':>8} {'':>5} {'':>6}  {head.strip()}")
            if tail:
                print(f"{'':>10} {'':>8} {'':>5} {'':>6}  -> {tail}")
    print()
    print("* = genre CONTENU (seul un genre CONTENU en DEEP/MED tient le plancher G-VAR-1).")
    print("inact = jours depuis la derniere activite. Une inactivite haute est le")
    print("        signe d'un sujet delaisse devant ceux du moment : c'est ce que")
    print("        le tirage remonte, et ce que la lane est attendue de conduire.")
    print("umbrella  -> pioche ou cree un SOUS-grain dedans, ne claim pas l'EPIC entier.")
    print("delivered -> verifie firsthand que la PR livrante satisfait l'acceptance :")
    print("             si oui `gh issue close`, sinon retire le label en disant pourquoi.")
    print("Avant d'EDITER : python scripts/check_lane_claim.py --lane <machine:workspace> <N>")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
