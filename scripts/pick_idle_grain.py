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

Reparer son rouge AVANT de piocher (mandat user 2026-08-22)
------------------------------------------------------------
Le picker **refuse de tirer** (sortie 2, aucun candidat rendu) tant que la
lane porte une PR bloquee ouverte depuis plus de 24 h. La reparation d'une PR
rouge n'appartient qu'a sa lane : le coordinateur ne peut ni rebaser ni
corriger a sa place, donc une lane qui pioche du neuf en laissant son rouge
derriere elle fabrique un residu que personne d'autre ne peut resorber.
"Bloquee" se lit sur le champ GraphQL `isRequired` -- ce que la protection de
branche exige vraiment -- et non sur "au moins un check rouge", qui rougissait
52 PRs sur 55 le 2026-08-22 en comptant les advisories. Voir `red_backlog`.

Usage
-----
    python scripts/pick_idle_grain.py --lane myia-po-2026:CoursIA
    python scripts/pick_idle_grain.py --lane myia-po-2023:CoursIA-2 --prev-genre guard
    python scripts/pick_idle_grain.py --lane <l> --reroll 1        # nouveau tirage
    python scripts/pick_idle_grain.py --lane <l> --check-claims    # + verif claims
    python scripts/pick_idle_grain.py --lane <l> --json            # sortie machine
    python scripts/pick_idle_grain.py --lane <l> --ignore-red      # rouge non reparable
                                                                   # par cette lane, ECRIT sur la PR

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

# Lecteur PARTAGE du tag `Grain:` (#9485). C'est la SEULE ancre qui rattache
# une PR a une lane : mesure du 2026-08-22 sur les 55 PRs ouvertes -- 50 sont
# poussees sous le compte `jsboige`, l'auteur GitHub ne porte donc aucune
# information de lane. Reutiliser l'extracteur plutot qu'en ecrire un
# troisieme : deux lecteurs divergents avaient deja rendu 38 % d'une journee
# de merges invisibles au cap G-VAR-2.
from grain_tag import parse_grain_tag  # noqa: E402

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
    """Annote les candidats tires qu'une autre PR couvre deja -- ouverte ou mergee.

    #12174 : le label ``candidate-delivered`` est pose par un workflow
    ``schedule:`` quotidien, dans une flotte qui merge plusieurs PRs par heure
    -- au tirage de 16:47Z, #12014 etait classee ``grain`` alors que #12077
    (mergee 16:19Z) avait deja livre 3 de ses 4 items. Le body d'une issue est
    date de sa redaction et un claim ne dit rien d'une livraison : la
    recherche de PRs est la troisieme surface de grounding, et ce geste doit
    vivre dans l'outil qui propose le grain, pas dans la discipline de qui le
    lit. Une requete par candidat tire, jamais un balayage du pool.

    #12504 (rapporte par myia-po-2023:CoursIA, 2026-08-24) : ne regarder que
    les PRs **mergees** laissait un angle mort plus couteux que celui qu'on
    fermait. Une issue couverte par une PR encore **OUVERTE** ne porte aucune
    trace de livraison -- ni label, ni body a jour, ni fusion a trouver -- et
    ressort donc en tete d'urne comme un grain frais. Le tirage a place #12504
    en tete (p=2.0) alors que #12519 la couvrait depuis des heures ; la lane
    qui l'a prise a pose un claim **void**. Les deux etats se lisent dans la
    **meme** requete (``--state all``), l'invariant "une requete par candidat"
    est donc preserve.

    Priorite du signal : une PR ouverte l'emporte sur une fusion recente. Une
    fusion dit "c'est peut-etre deja fait" ; une PR ouverte dit "quelqu'un y
    est en ce moment, ton claim sera void". Une PR **fermee sans fusion** ne
    dit rien et est ignoree explicitement.

    L'annotation **n'ecarte pas** le candidat (parite avec la doctrine
    ``candidate-delivered`` : signale, ne ferme pas) : elle change ce qu'on
    en dit, pas s'il est pris. Le verrou cross-lane reste
    ``check_lane_claim.py``, que ``--check-claims`` interroge separement.
    """
    notes: dict[int, str] = {}
    for p in picks:
        n = p["number"]
        try:
            out = subprocess.run(
                ["gh", "pr", "list", "--repo", REPO, "--state", "all",
                 "--limit", "20", "--search", f"{n} in:title,body",
                 "--json", "number,state,isDraft,mergedAt"],
                capture_output=True, text=True, encoding="utf-8", check=True,
                timeout=30,
            ).stdout
            prs = json.loads(out)
        except Exception as exc:  # noqa: BLE001 - diagnostic best-effort
            notes[n] = f"(recherche PR indisponible: {type(exc).__name__})"
            continue
        if not prs:
            continue

        # Une PR fermee-sans-fusion n'atteste de rien : on l'ecarte ici plutot
        # que de la laisser peser dans les deux partitions ci-dessous.
        opened = [pr for pr in prs if pr.get("state") == "OPEN"]
        merged = [pr for pr in prs if pr.get("state") == "MERGED"]

        if opened:
            first = min(opened, key=lambda pr: pr["number"])
            others = [pr["number"] for pr in opened if pr["number"] != first["number"]]
            extra = f" (+{len(others)} autre(s) : " + ", ".join(
                f"#{x}" for x in others) + ")" if others else ""
            draft = " [draft]" if first.get("isDraft") else ""
            notes[n] = (f"TRAVAIL EN COURS : PR #{first['number']}{draft} OUVERTE "
                        f"couvre cette issue{extra} "
                        f"-> claim probablement VOID ; lire "
                        f"`gh pr view {first['number']}` AVANT de claimer")
            continue

        if not merged:
            continue
        latest = max(merged, key=lambda pr: pr.get("mergedAt") or "")
        when = latest.get("mergedAt") or ""
        # Fusion plus recente que la derniere activite de l'issue = le corps
        # visible est potentiellement perime par rapport au reel. Une fusion
        # ANTERIEURE a updatedAt est deja digeree par le body (ou les
        # commentaires) : pas d'annotation, sinon le signal noie.
        if when and when > p.get("updated_at", ""):
            extra = f" (+{len(merged) - 1} autres)" if len(merged) > 1 else ""
            notes[n] = (f"LIVRAISON RECENTE : #{latest['number']} mergee {when}{extra} "
                        f"(issue non mise a jour depuis {p.get('updated_at', '?')}) "
                        f"-> confronter le body au reel AVANT de dispatcher")
    return notes


# --- garde "reparer son rouge d'abord" (mandat user 2026-08-22) ------------
#
# Pourquoi ce garde vit DANS le picker et pas dans une consigne
# -------------------------------------------------------------
# Le residu de PRs anciennes ne vient pas d'un debit de merge insuffisant
# (65 PRs mergees le 2026-08-22, 100 la veille) : il vient de ce qu'une lane
# qui se reveille pioche un grain NEUF au lieu de reparer le rouge qu'elle a
# laisse. La reparation d'une PR rouge appartient a sa lane -- le coordinateur
# ne peut ni rebaser ni corriger a sa place -- donc tant que la lane ne
# revient pas dessus, la PR reste ouverte indefiniment pendant que les PRs du
# jour, elles, mergent. Une consigne de plus ne changerait rien : le picker
# est le point de passage de la selection, c'est donc lui qui doit refuser.
#
# Ce qui compte comme "rouge" -- et ce qui n'en est PAS
# -----------------------------------------------------
# Mesure du 2026-08-22 sur les 55 PRs ouvertes : la definition naive
# "au moins un check en echec" rougissait **52 PRs sur 55**, un garde qui
# refuse tout a tout le monde et se fait contourner le jour meme. La cause
# est que la flotte fait tourner des checks ADVISORY (`... advisory`,
# `fast-lane (ombre)`, `Degraded-mode confessions`) dont l'echec n'empeche
# aucun merge. Le discriminant retenu n'est pas un motif de nom -- fragile,
# et il faudrait le maintenir a chaque nouvel advisory -- mais le champ
# GraphQL `isRequired(pullRequestNumber:)`, qui dit ce que la protection de
# branche exige VRAIMENT. Avec lui : 47 PRs bloquees au lieu de 52, les 4
# ecartees ne l'etant QUE sur des advisories. Si la protection change, le
# garde suit sans edition.
#
# Trois causes bloquantes, toutes reparables par la lane :
#   1. un check REQUIS en echec        -> corriger la substance, ou relancer
#   2. `mergeable: CONFLICTING`        -> rebaser
#   3. un CHANGES_REQUESTED non leve   -> repondre / corriger
#
# L'horloge est l'AGE DE LA PR (`createdAt`), pas la date du dernier echec :
# un timestamp de check se remet a zero a chaque push, ce qui rendrait le
# garde evitable par un commit vide. L'age d'ouverture ne se falsifie pas, et
# il vise exactement la population que le user a pointee -- "les vieilles de
# plus de 12 h" qui trainent pendant que les neuves passent.

RED_HOURS_DEFAULT = 24

# CANCELLED / SKIPPED / NEUTRAL sont volontairement absents : un run annule
# par `concurrency` n'est pas un echec, et le confondre avec un rouge est le
# faux positif qui rend un garde de cascade inutilisable.
CHECK_FAILED = {"FAILURE", "TIMED_OUT", "ACTION_REQUIRED", "STARTUP_FAILURE", "ERROR"}

_PR_STATE_FRAGMENT = """
  p%(n)d: pullRequest(number:%(n)d) {
    number mergeable
    reviews(last:40) { nodes { state submittedAt author { login } } }
    commits(last:1) { nodes { commit { statusCheckRollup { contexts(first:100) { nodes {
      ... on CheckRun      { name    conclusion completedAt startedAt isRequired(pullRequestNumber:%(n)d) }
      ... on StatusContext { context state       createdAt              isRequired(pullRequestNumber:%(n)d) }
    } } } } } }
  }
"""


def _hours_since(iso: str) -> float:
    return (NOW - dt.datetime.fromisoformat(iso.replace("Z", "+00:00"))).total_seconds() / 3600.0


def fetch_open_prs() -> list[dict]:
    """Toutes les PRs ouvertes, avec le corps (pour y lire le tag de lane)."""
    out = subprocess.run(
        ["gh", "pr", "list", "--repo", REPO, "--state", "open", "--limit", "300",
         "--json", "number,title,body,createdAt,isDraft"],
        capture_output=True, text=True, encoding="utf-8", check=True, timeout=120,
    ).stdout
    return json.loads(out)


def fetch_pr_states(numbers: list[int]) -> dict[int, dict]:
    """Etat de merge + checks (avec `isRequired`) + reviews, par lots de 8.

    Une seule requete par lot : le garde n'interroge que les PRs DE LA LANE
    (typiquement 2 a 11), jamais les 55 ouvertes.
    """
    states: dict[int, dict] = {}
    for i in range(0, len(numbers), 8):
        chunk = numbers[i:i + 8]
        query = ('query { repository(owner:"jsboige", name:"CoursIA") {'
                 + "".join(_PR_STATE_FRAGMENT % {"n": n} for n in chunk) + "} }")
        try:
            raw = subprocess.run(
                ["gh", "api", "graphql", "-f", "query=" + query],
                capture_output=True, text=True, encoding="utf-8", check=True, timeout=90,
            ).stdout
            repo = json.loads(raw)["data"]["repository"]
        except Exception:  # noqa: BLE001 - diagnostic best-effort
            continue
        for value in repo.values():
            if value:
                states[value["number"]] = value
    return states


def _ctx_stamp(ctx: dict) -> str:
    """Horodatage comparable d'un contexte. Chaine vide si le run n'a rien rendu."""
    return ctx.get("completedAt") or ctx.get("createdAt") or ctx.get("startedAt") or ""


def drop_superseded(contexts: list[dict]) -> list[dict]:
    """Retire les echecs PERIMES : un rouge anterieur au dernier vert du meme nom.

    Le discriminant est TEMPOREL, jamais nominal, et les deux erreurs symetriques
    sont documentees : dedupliquer par nom seul masque un rouge vivant emis par un
    workflow jumeau (#11894), ne pas dedupliquer du tout en fabrique de faux
    (#12054, 9 rouges pour 0 reel). La regle qui tranche les deux : un echec
    ANTERIEUR au dernier non-echec du meme nom est de l'histoire ; un echec
    CONTEMPORAIN ou posterieur est un jumeau vivant, on le garde.

    Mesure du 2026-08-22 sur #11916 : `Require genre diversity vs prev:` porte un
    FAILURE du 20/08 et un SUCCESS du 22/08 sur le meme head. Sans ce filtre le
    garde renvoyait la lane reparer un check deja vert.
    """
    newest_ok: dict[str, str] = {}
    for ctx in contexts:
        verdict = (ctx.get("conclusion") or ctx.get("state") or "").upper()
        if verdict in CHECK_FAILED:
            continue
        name = ctx.get("name") or ctx.get("context") or "?"
        stamp = _ctx_stamp(ctx)
        if stamp > newest_ok.get(name, ""):
            newest_ok[name] = stamp
    kept = []
    for ctx in contexts:
        verdict = (ctx.get("conclusion") or ctx.get("state") or "").upper()
        name = ctx.get("name") or ctx.get("context") or "?"
        if verdict in CHECK_FAILED and _ctx_stamp(ctx) < newest_ok.get(name, ""):
            continue  # rouge anterieur au dernier vert du meme nom : perime
        kept.append(ctx)
    return kept


def blocking_causes(state: dict) -> list[str]:
    """Causes qui empechent VRAIMENT le merge, formulees en geste de reparation.

    `mergeStateStatus: BLOCKED` n'est deliberement PAS une cause : il vaut
    aussi pour "en attente de review", que la lane ne peut pas lever -- c'est
    au coordinateur de merger. Verifie firsthand sur #12108 le 2026-08-22 :
    BLOCKED, MERGEABLE, zero check en echec. L'accuser aurait renvoye la lane
    reparer une PR qui n'a rien a reparer.
    """
    causes: list[str] = []
    advisory: list[str] = []
    commits = state.get("commits", {}).get("nodes") or []
    rollup = (commits[0]["commit"].get("statusCheckRollup") if commits else None) or {}
    for ctx in drop_superseded((rollup.get("contexts", {}) or {}).get("nodes") or []):
        name = ctx.get("name") or ctx.get("context") or "?"
        verdict = (ctx.get("conclusion") or ctx.get("state") or "").upper()
        if verdict not in CHECK_FAILED:
            continue
        if ctx.get("isRequired"):
            cause = f"check requis en echec : {name}"
            if cause not in causes:
                causes.append(cause)
        elif name not in advisory:
            advisory.append(name)
    if state.get("mergeable") == "CONFLICTING":
        causes.append("conflits avec main -> rebaser")
    latest: dict[str, dict] = {}
    for review in (state.get("reviews", {}) or {}).get("nodes") or []:
        if review["state"] in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
            latest[review["author"]["login"]] = review
    for login, review in latest.items():
        if review["state"] == "CHANGES_REQUESTED":
            causes.append(f"CHANGES_REQUESTED non leve ({login})")
    if causes and advisory:
        causes.append("(diagnostic, non bloquant : " + ", ".join(advisory[:3]) + ")")
    return causes


def red_backlog(lane: str, threshold_hours: float) -> dict:
    """PRs de la lane, bloquees et ouvertes depuis plus de `threshold_hours`.

    Rend aussi `unattributed_blocked` : les PRs bloquees dont le tag `Grain:`
    est illisible. Elles ne peuvent bloquer AUCUNE lane -- c'est la bonne
    arithmetique (deviner une lane serait pire) -- mais les taire donnerait a
    croire que le garde couvre tout l'ouvert. Il ne le couvre pas : leur tag
    manquant est lui-meme le defaut a corriger.
    """
    try:
        prs = fetch_open_prs()
    except Exception as exc:  # noqa: BLE001 - le garde ne doit jamais bloquer sur une panne reseau
        return {"unavailable": f"{type(exc).__name__}", "red": [], "unattributed_blocked": []}

    mine, others = [], []
    for pr in prs:
        if pr.get("isDraft"):
            continue
        age = _hours_since(pr["createdAt"])
        if age < threshold_hours:
            continue
        tag = parse_grain_tag(pr.get("body") or "")
        pr_lane = tag.get("lane") if tag else None
        (mine if pr_lane == lane else others).append(pr)

    states = fetch_pr_states([pr["number"] for pr in mine])
    red = []
    for pr in mine:
        state = states.get(pr["number"])
        if state is None:
            continue
        causes = blocking_causes(state)
        if causes:
            red.append({"number": pr["number"], "title": pr["title"],
                        "age_hours": round(_hours_since(pr["createdAt"])),
                        "causes": causes})
    red.sort(key=lambda r: -r["age_hours"])

    untagged = [pr for pr in others if parse_grain_tag(pr.get("body") or "") is None]
    untagged_states = fetch_pr_states([pr["number"] for pr in untagged]) if untagged else {}
    unattributed = [
        {"number": pr["number"], "title": pr["title"],
         "age_hours": round(_hours_since(pr["createdAt"]))}
        for pr in untagged
        if untagged_states.get(pr["number"]) and blocking_causes(untagged_states[pr["number"]])
    ]
    # Les NUMEROS, pas un compte : le coordinateur est le seul a pouvoir les
    # reprendre (cf skill coordinate, phase 3.5), et un compte ne se traite pas.
    return {"red": red, "unattributed_blocked": unattributed}


def print_red_refusal(lane: str, backlog: dict, threshold_hours: float) -> None:
    red = backlog["red"]
    print(f"REFUS DE TIRAGE -- lane {lane} porte {len(red)} PR(s) bloquee(s) "
          f"ouverte(s) depuis plus de {threshold_hours:g} h.")
    print()
    print("Reparer son propre rouge est la PREMIERE tache du cycle, avant tout")
    print("grain neuf : la PR ne peut etre reparee que par sa lane, le")
    print("coordinateur ne peut ni rebaser ni corriger a sa place.")
    print()
    for item in red:
        print(f"  #{item['number']}  ouverte depuis {item['age_hours']} h  -- {item['title'][:66]}")
        for cause in item["causes"]:
            print(f"       {cause}")
    print()
    print("Trois gestes, dans cet ordre -- le premier repare souvent seul :")
    print("  1. `gh pr update-branch <N>` : rejoue les checks sur une tete fraiche.")
    print("     Un rouge peut dater d'AVANT la correction du garde qui l'a produit")
    print("     (mesure du 2026-08-21 : 5 PRs sur 9 n'avaient rien a corriger).")
    print("     Dater le garde -- `git log -- <script>` -- avant de conclure.")
    print("  2. conflits : rebaser sur origin/main, `--force-with-lease` si la lane")
    print("     est seule sur la branche.")
    print("  3. corriger la substance, pousser, et REPONDRE au CHANGES_REQUESTED")
    print("     par ecrit : un push muet ne leve aucune remarque.")
    print()
    if backlog.get("unattributed_blocked"):
        numbers = ", ".join(f"#{u['number']}" for u in backlog["unattributed_blocked"])
        print(f"Portee : {len(backlog['unattributed_blocked'])} autre(s) PR(s) bloquee(s) ({numbers})")
        print("n'ont pas de tag")
        print("`Grain:` lisible et ne sont donc imputables a aucune lane -- ce garde ne")
        print("les voit pas. Leur tag manquant est lui-meme le defaut a corriger.")
        print()
    print("Si un rouge n'est PAS reparable par cette lane (garde casse sur main,")
    print("dependance d'une autre PR), l'ECRIRE en commentaire sur la PR concernee,")
    print("puis relancer avec --ignore-red. L'echappatoire se justifie par ecrit,")
    print("elle ne se prend pas en silence.")


def main() -> int:
    # Console Windows cp1252 : un titre d'issue portant un caractere hors table
    # (fleche U+2192 etc.) fait crasher le print en UnicodeEncodeError et perd
    # le tirage entier. UTF-8 + replace : le titre s'affiche degrades, le
    # tirage vit.
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8", errors="replace")
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
    ap.add_argument("--red-hours", type=float, default=RED_HOURS_DEFAULT,
                    help=f"seuil du garde 'reparer son rouge d'abord' (defaut {RED_HOURS_DEFAULT} h)")
    ap.add_argument("--ignore-red", action="store_true",
                    help="passer outre le garde -- exige une justification ECRITE sur la PR concernee")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    args = ap.parse_args()

    # Garde "reparer son rouge d'abord" : AVANT le tirage, sinon le grain neuf
    # est deja sous les yeux quand le refus arrive, et c'est lui qui gagne.
    backlog = red_backlog(args.lane, args.red_hours)
    if backlog["red"] and not args.ignore_red:
        if args.json:
            print(json.dumps({"lane": args.lane, "refus": "rouge-a-reparer",
                              "red_hours": args.red_hours, **backlog},
                             ensure_ascii=False, indent=2))
        else:
            print_red_refusal(args.lane, backlog, args.red_hours)
        return 2
    if backlog.get("unavailable") and not args.json:
        print(f"(garde rouge indisponible : {backlog['unavailable']} -- tirage rendu sans verification)")
        print()

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
            "red_backlog": backlog,
        }, ensure_ascii=False, indent=2))
        return 0

    print(f"Pool ouvert : {len(pool)} issues  "
          f"= {len(by_class['grain'])} grains "
          f"+ {len(by_class['umbrella'])} umbrella "
          f"+ {len(by_class['delivered'])} candidate-delivered")
    if backlog["red"]:
        numbers = ", ".join(f"#{r['number']}" for r in backlog["red"])
        print(f"!! --ignore-red : {len(backlog['red'])} PR(s) bloquee(s) de cette lane restent "
              f"a reparer ({numbers}).")
        print("   La justification doit etre ECRITE sur chacune, pas seulement invoquee ici.")
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
