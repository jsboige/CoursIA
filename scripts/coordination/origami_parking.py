#!/usr/bin/env python3
"""Organe(belt) : parquer les EPICs Origami dont le pli suivant n'est pas deplie (#24373).

**Constat (mesure du 2026-11-03, coordinateur ai-01).** Le tapis
(`pick_idle_grain.py --belt`) resservait sans fin des EPICs Origami dont
**tous les plis materialises sont termines** et dont le **pli suivant n'est
pas deplie**. Le depliage est reserve au coordinateur ; aucune lane worker ne
peut le lever. La lane qui tire l'EPIC posait donc un `[RELEASED]` et le cycle
etait perdu : 34 `[RELEASED]` sur #19309 (31 depuis le 27/10), 7 sur #20404.

Depuis #21721, un `[RELEASED]` rend l'item a la flotte : c'est voulu pour une
barriere qu'une autre lane peut lever (GPU, vision). Le depliage d'un pli n'est
levable par **aucune** lane worker. L'EPIC revenait donc en tete de tapis.

**Ce que fait cet organe.**

1. Il RECONNAIT la barriere : un EPIC Origami dont tous les plis materialises
   sont termines (fermes, ou livres par une PR mergee) et dont le pli suivant
   n'est pas annonce.
2. Il **PARQUE** l'EPIC : il n'est plus servi aux lanes worker. Il ressort au
   premier signe de depliage (un pli suivant annonce, ou une sous-issue de
   ce pli).
3. Il **REND VISIBLE** au coordinateur ce qui attend son geste, dans une
   rubrique dediee du tableau `belt_queues.py board` -- « Origami en attente
   de depliage ».

Le parcage ne decide rien sur le veto user sur les nouveaux carnets : il rend
visible un geste qui attend le coordinateur, au lieu de le faire payer aux
lanes.

**Deux lectures, et pourquoi celle-ci.**

*Un pli est « termine » quand il est FERME **ou** LIVRE* (une PR mergee le
cite). Le Coordinateur a lui-meme designe #20404 comme controle POSITIF : ses
plis 2 (#21701) et 3 (#23742) sont encore OUVERTS, mais livres (PRs #21795 et
#23745 mergees). La lecture « tous les plis sont fermes » ne parquerait donc
pas son propre controle positif ; la lecture « termines » (ferme ou livre) est
la seule sous laquelle il tient. Les deux etats sont mesures et affiches.

*Les plis materialises sont les sous-issues de l'EPIC* (`Part of #N`), pas les
commentaires. Les commentaires servent a deux choses : dire quels plis ont ete
annonces (le signe de depliage qui fait resortir l'EPIC) et tracer l'historique.
Un commentaire de lane qui **mentionne l'absence** du marqueur (« aucun
`[PLI 4 DEPLIE]` du coordinateur ») n'est PAS une declaration de depliage :
l'absence du marqueur est justement ce qui maintient le parcage. La negation
est donc lue, et ecartee.

**Geste fail-OPEN.** Une mesure absente ne parque jamais rien : le parcage
n'est active que sur un ETAT MESURE (plis connus, etat de chaque pli connu).
Un EPIC dont on ignore la lecture reste servi -- c'est le sens de la regle
« defaut de mesure n'est pas negligence ».

Usage :

    python scripts/coordination/origami_parking.py --json     # etat mesure
    python scripts/coordination/origami_parking.py --epic 19309 --json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

REPO = "jsboige/CoursIA"

# Duree de validite du cache d'etat (secondes). Le tapis tourne toutes les
# 30 min : un cache d'une heure laisse passer un depliage sans le voir, un
# cache de 15 min le voit dans le cycle suivant.
PARKING_TTL_SECONDS = 1800

# ---------------------------------------------------------------------------
# Couche PURE -- aucune requete reseau. Testable seule.
# ---------------------------------------------------------------------------

_ORIGAMI_RE = re.compile(r"origami", re.I)

# Un pli est designe par son numero : « pli 3 », « Pli 2 », « pli 0/6 ».
_PLI_RE = re.compile(r"\bpli\s*(\d+)", re.I)

# Parent nomme en corps : la convention `Part of #N` (git-workflow.md).
_PARENT_BODY_RE = re.compile(r"(?i)\bpart of #(\d+)")

# Une DECLARATION de depliage : le pli N ... un verbe qui dit que le pli
# s'ouvre. « pli 2 deploie », « pli 3 materialise », « pli 1 ouvert ».
_UNFOLD_VERB = (r"d[ée]pli[ée]|depli[ée]|d[ée]ploy[ée]|mat[ée]rialis[ée]"
                 r"|cr[ée]ée|ouverte?")
_PLI_DECL_RE = re.compile(r"\bpli\s*(\d+)\b[^\n]{0,80}?(?:" + _UNFOLD_VERB + r")",
                          re.I)

# Une mention NEGEE ne declare rien. « aucun [PLI 4 DEPLIE] », « le pli 4
# n'est pas deplie », « le pli 5 reste verrouille », « le pli 3 ne se deplie
# pas » : quatre formes mesurees dans le fil de #19309 et #18205, ou le
# parcage DOIT tenir.
_NEGATION_RE = re.compile(
    r"aucun|aucune|jamais"
    r"|pas\s+de\b"
    r"|pas\s+(?:encore\s+)?(?:d[ée]pli[ée]|depli[ée]|mat[ée]rialis[ée])"
    r"|n['’]est\s+pas\s+(?:d[ée]pli[ée]|depli[ée])"
    r"|ne\s+se\s+(?:d[ée]pli[ée]|depli[ée]|mat[ée]rialis[ée]|d[ée]ploy[ée])"
    r"|non\s+(?:d[ée]pli[ée]|depli[ée]|d[ée]ploy[ée]|mat[ée]rialis[ée]|couvert[ea]s?)"
    r"|partiellement\s+couvert[ea]?"
    r"|toujours\s+absent"
    r"|verrouill[ée]s?"
    r"|sans\s+(?:marqueur|pli|d[ée]pli[ée]ge)",
    re.I)

# Fenetre de contexte lue autour d'une mention, pour y chercher la negation.
_NEGATION_WINDOW_BEFORE = 60

# En-tete de main rendue : le commentaire RECITE la barriere, il ne la leve
# pas.
_RELEASED_HEADER_RE = re.compile(r"^\s*\[RELEASED\]", re.I)


def is_origami_epic(item: dict) -> bool:
    """Cet item est-il un EPIC au format Origami ?

    Deux conditions, toutes deux dans le TITRE :

    * le titre mentionne « origami » -- une EPIC qui en parle dans son corps
      sans etre un EPIC Origami (#13906 : « Les body d'Epic ne sont jamais
      reecrits ») ne passe pas ;
    * le titre ne declare AUCUN numero de pli -- un pli porte son numero
      (« [Epic Origami #19742 - Pli 2] », « [Origami pli 1] »), et un pli
      n'est pas un EPIC.
    """
    title = item.get("title") or ""
    if not _ORIGAMI_RE.search(title):
        return False
    return declared_pli(title) is None


def parent_refs(item: dict) -> set[int]:
    """Parents nommes en corps : `Part of #N`.

    Miroir de `pick_idle_grain.parent_refs` pour la seule surface `Part of`.
    L'organe ne doit pas importer le picker (12 k lignes, et le picker
    importe l'organe) : la regle est donc dupliquee, et un test verifie que
    les deux formes coincident sur un corpus reel.
    """
    refs = {int(m) for m in _PARENT_BODY_RE.findall(item.get("body") or "")}
    refs.discard(item.get("number"))
    return refs


def declared_pli(text: str) -> int | None:
    """Numero de pli declare par un texte (titre ou corps)."""
    m = _PLI_RE.search(text or "")
    return int(m.group(1)) if m else None


def fold_pli(child: dict) -> int | None:
    """Numero de pli d'une sous-issue : le titre d'abord, le corps ensuite.

    Le corps n'est lu que dans ses trois premieres lignes : une sous-issue
    peut citer un pli plus loin (« le pli 4 sera traite ailleurs ») sans etre
    elle-meme un pli.
    """
    pli = declared_pli(child.get("title") or "")
    if pli is not None:
        return pli
    body = child.get("body") or ""
    head = "\n".join(body.splitlines()[:3])
    return declared_pli(head)


def is_fold_of(child: dict, epic_number: int) -> bool:
    """Cette sous-issue est-elle un PLI de l'EPIC ?

    Deux conditions : elle nomme l'EPIC (`Part of #N`) et elle declare un
    numero de pli. Une sous-issue qui ne fait que CITER l'EPIC (une issue de
    consolidation qui la mentionne) ne declare pas de pli : elle n'est pas un
    pli.
    """
    if child.get("number") == epic_number:
        return False
    if epic_number not in parent_refs(child):
        return False
    return fold_pli(child) is not None


def unfolded_declarations(comments: list[dict]) -> list[dict]:
    """Les declarations de depliage, lues dans les commentaires d'un EPIC.

    Rend une liste de dicts `{pli, at, text}`. Deux formes de mention ne
    declarent rien :

    * une mention **NEGEE** (« aucun `[PLI 4 DEPLIE]` du coordinateur », « le
      pli 4 n'est pas deplie ») : elle dit que le pli n'est pas deplie, ce qui
      maintient le parcage au lieu de le lever ;
    * un commentaire de **[RELEASED]** : une lane qui rend la main RECITE le
      marqueur qu'elle n'a pas trouve (« Pli 4 par `[PLI 4 DEPLIE]` »). C'est
      la forme mesuree sur #19309 : sans ce filtre, 6 commentaires de lanes
      feraient croire a un depliage du pli 4.
    """
    out: list[dict] = []
    for comment in comments or []:
        body = comment.get("body") or ""
        if not body:
            continue
        first = next((ln for ln in body.splitlines() if ln.strip()), "")
        if _RELEASED_HEADER_RE.match(first):
            continue
        for m in _PLI_DECL_RE.finditer(body):
            start = max(0, m.start() - _NEGATION_WINDOW_BEFORE)
            context = body[start:m.end()]
            if _NEGATION_RE.search(context):
                continue
            out.append({"pli": int(m.group(1)),
                        "at": comment.get("createdAt"),
                        "text": m.group(0)[:120]})
    return out


def parking_verdict(epic: dict,
                    folds: list[dict],
                    declarations: list[dict]) -> dict:
    """Verdict de parcage d'un EPIC Origami.

    `folds` : liste de dicts `{number, pli, state, delivered}` -- `state` vaut
    `OPEN` ou `CLOSED`, `delivered` dit si une PR mergee cite le pli.
    `declarations` : sortie de `unfolded_declarations`.

    Regles, dans l'ordre :

    1. un pli OUVERT et non livre est du travail actionnable : l'EPIC reste
       servi (c'est un grain, pas une barriere) ;
    2. aucun pli connu : mesure absente, on ne parque pas (fail-OPEN) ;
    3. un pli ANNONCE au-dela du dernier pli materialise : le pli suivant est
       ouvert, l'EPIC doit etre servi pour qu'une lane le porte ;
    4. sinon : tous les plis materialises sont termines et le pli suivant
       n'est pas annonce -> l'EPIC est PARQUE, en attente du depliage.
    """
    number = epic.get("number")
    open_undelivered = [f for f in folds
                         if f.get("state") == "OPEN" and not f.get("delivered")]
    if open_undelivered:
        plis = sorted({f.get("pli") for f in open_undelivered
                       if f.get("pli") is not None})
        return {"parked": False, "measured": True, "epic": number,
                "reason": f"PLI {plis} ouvert et non livre -- grain actionnable",
                "open_folds": [{"number": f.get("number"), "pli": f.get("pli")}
                                for f in open_undelivered]}

    plis = [f.get("pli") for f in folds if f.get("pli") is not None]
    if not plis:
        return {"parked": False, "measured": False, "epic": number,
                "reason": "aucun pli materialise connu -- mesure absente, "
                          "rien n'est parque"}
    last_pli = max(plis)
    announced = [d.get("pli") for d in declarations if d.get("pli") is not None]
    if announced and max(announced) > last_pli:
        return {"parked": False, "measured": True, "epic": number,
                "reason": f"pli {max(announced)} annonce mais non materialise "
                          f"-- le depliage est en cours",
                "next_pli": last_pli + 1}
    return {"parked": True, "measured": True, "epic": number,
            "reason": f"tous les plis materialises sont termines "
                      f"(dernier pli {last_pli}) et le pli {last_pli + 1} "
                      f"n'est pas annonce -- depliage reserve au coordinateur",
            "next_pli": last_pli + 1,
            "folds": [{"number": f.get("number"), "pli": f.get("pli"),
                       "state": f.get("state"), "delivered": bool(f.get("delivered"))}
                      for f in folds]}


# ---------------------------------------------------------------------------
# Couche MESURE -- reseau. Islee de la couche pure.
# ---------------------------------------------------------------------------

def _gh(*args: str) -> str | None:
    try:
        out = subprocess.run(["gh", *args], capture_output=True, text=True,
                             encoding="utf-8", timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if out.returncode != 0:
        return None
    return out.stdout


def origami_epic_numbers(pool: list[dict]) -> list[int]:
    """EPICs Origami du pool (titre « origami », sans numero de pli)."""
    out = []
    for item in pool:
        if not is_origami_epic(item):
            continue
        out.append(int(item["number"]))
    return sorted(out)


def _search_issues(query: str, pages: int = 3) -> list[dict]:
    """Recherche d'issues, paginee, via l'API REST.

    `gh api` avec `-f` passe par POST : la methode GET doit etre explicite,
    sinon l'endpoint de recherche repond 404.
    """
    items: list[dict] = []
    for page in range(1, pages + 1):
        raw = _gh("api", "--method", "GET", "search/issues",
                  "-f", f"q={query}", "-f", "per_page=100", "-f", f"page={page}")
        if raw is None:
            break
        try:
            payload = json.loads(raw)
        except json.JSONDecodeError:
            break
        batch = payload.get("items") or []
        items.extend(batch)
        if len(batch) < 100:
            break
    return items


def fetch_children(epic_numbers: list[int]) -> dict[int, list[dict]]:
    """Sous-issues `Part of #N` de chaque EPIC, avec leur etat.

    Une RECHERCHE par expression composee -- mais l'API de recherche refuse
    une requete de plus de 256 caracteres (422 mesure : 15 clauses en font
    274). Les clauses sont donc **decoupees** en paquets de 6, et chaque
    paquet est pagine.

    Le resultat est sur-large (l'index GitHub rend aussi les issues qui
    citent l'EPIC, et les PRs, qui sont aussi des issues) -- le tri en plis
    est fait par `is_fold_of`, cote appelant.
    """
    by_parent: dict[int, list[dict]] = {n: [] for n in epic_numbers}
    if not epic_numbers:
        return by_parent
    chunks: list[list[int]] = []
    current: list[int] = []
    for n in epic_numbers:
        current.append(n)
        if len(current) >= 6:
            chunks.append(current)
            current = []
    if current:
        chunks.append(current)
    seen: set[tuple[int, int]] = set()
    for chunk in chunks:
        clauses = " OR ".join(f'"Part of #{n}"' for n in chunk)
        query = f"repo:{REPO} ({clauses})"
        for it in _search_issues(query):
            if it.get("pull_request"):
                continue  # une PR cite l'EPIC, ce n'est pas un pli
            number = int(it["number"])
            for parent in parent_refs(it):
                if parent in by_parent and (parent, number) not in seen:
                    seen.add((parent, number))
                    by_parent[parent].append({
                        "number": number,
                        "title": it.get("title") or "",
                        "body": it.get("body") or "",
                        "state": it.get("state") or "OPEN",
                    })
    return by_parent


def fetch_comments(numbers: list[int]) -> dict[int, list[dict]]:
    """Commentaires des EPICs -- UN appel GraphQL (alias par issue).

    Le repli unitaire (`gh issue view`) sert quand le GraphQL tombe : plus
    lent, mais l'organe ne perd pas sa mesure.
    """
    if not numbers:
        return {}
    parts = []
    for i, n in enumerate(numbers):
        parts.append(
            f'i{i}: issue(number:{n}) {{ comments(first:100) '
            f'{{ nodes {{ createdAt body }} }} }}')
    query = "query { repository(owner:\"jsboige\", name:\"CoursIA\") { " \
            + " ".join(parts) + " } }"
    raw = _gh("api", "graphql", "-f", f"query={query}")
    if raw is not None:
        try:
            data = json.loads(raw).get("data") or {}
            repo = data.get("repository") or {}
            out = {}
            for i, n in enumerate(numbers):
                node = repo.get(f"i{i}") or {}
                out[n] = (node.get("comments") or {}).get("nodes") or []
            return out
        except json.JSONDecodeError:
            pass
    out = {}
    for n in numbers:
        raw = _gh("issue", "view", str(n), "--repo", REPO, "--json", "comments")
        try:
            out[n] = (json.loads(raw or "{}").get("comments") or [])
        except json.JSONDecodeError:
            out[n] = []
    return out


def probe_delivered(number: int) -> bool:
    """Une PR MERGEE cite-t-elle cette issue ?

    Sonde par timeline : les evenements `cross-referenced` portent la PR
    source et sa date de fusion. C'est la seule source qui distingue « citee
    par une PR mergee » d'une simple mention.
    """
    raw = _gh("api", f"repos/{REPO}/issues/{number}/timeline?per_page=100")
    if raw is None:
        return False
    try:
        events = json.loads(raw)
    except json.JSONDecodeError:
        return False
    for ev in events if isinstance(events, list) else []:
        if ev.get("event") != "cross-referenced":
            continue
        pr = ((ev.get("source") or {}).get("issue") or {})
        if pr.get("pull_request", {}) and pr["pull_request"].get("merged_at"):
            return True
    return False


def measure(pool: list[dict], *, delivered_probe=probe_delivered) -> list[dict]:
    """Verdicts de parcage pour les EPICs Origami du pool.

    `delivered_probe` est injectable : le picker passe une lecture SANS
    reseau (le corpus de PRs mergees qu'il a deja paye), l'organe en ligne
    passe la sonde timeline.
    """
    epics = origami_epic_numbers(pool)
    if not epics:
        return []
    by_number = {int(it["number"]): it for it in pool}
    children = fetch_children(epics)
    comments = fetch_comments(epics)
    verdicts = []
    for number in epics:
        epic = by_number.get(number, {"number": number})
        folds = []
        for child in children.get(number, []):
            if not is_fold_of(child, number):
                continue
            state = (child.get("state") or "OPEN").upper()
            delivered = (state == "CLOSED")
            if state == "OPEN":
                delivered = delivered_probe(child["number"])
            folds.append({"number": child["number"],
                          "pli": fold_pli(child),
                          "state": state,
                          "delivered": delivered})
        # Un pli ouvert peut ne pas avoir ete trouve par la recherche (index
        # en retard) : le pool, lui, est exhaustif sur les issues ouvertes.
        # Le pool ne porte pas d'etat : par construction, il ne contient que
        # des issues OUVERTES.
        for item in pool:
            if int(item["number"]) == number:
                continue
            if (item.get("state") or "OPEN").upper() != "OPEN":
                continue
            if is_fold_of(item, number):
                folds.append({"number": int(item["number"]),
                              "pli": fold_pli(item),
                              "state": "OPEN",
                              "delivered": bool(item.get("last_delivery_stamp"))})
        seen = set()
        unique = []
        for f in folds:
            if f["number"] in seen:
                continue
            seen.add(f["number"])
            unique.append(f)
        declarations = unfolded_declarations(comments.get(number) or [])
        verdict = parking_verdict(epic, unique, declarations)
        verdict["title"] = epic.get("title")
        verdict["declarations"] = declarations
        verdicts.append(verdict)
    return verdicts


# ---------------------------------------------------------------------------
# Cache d'etat (partage par la machine, dans %LOCALAPPDATA%).
# ---------------------------------------------------------------------------

def store_dir() -> Path:
    base = os.environ.get("LOCALAPPDATA") or str(Path.home() / ".local" / "share")
    return Path(base) / "CoursIA" / "origami_parking"


def cache_path() -> Path:
    return store_dir() / "state.json"


def load_cache(ttl_seconds: int = PARKING_TTL_SECONDS) -> dict | None:
    path = cache_path()
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    stamp = payload.get("measured_at")
    if not stamp:
        return None
    try:
        when = datetime.fromisoformat(str(stamp).replace("Z", "+00:00"))
    except ValueError:
        return None
    if (datetime.now(timezone.utc) - when).total_seconds() > ttl_seconds:
        return None
    return payload


def save_cache(verdicts: list[dict]) -> Path:
    store_dir().mkdir(parents=True, exist_ok=True)
    payload = {"measured_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
               "verdicts": verdicts}
    path = cache_path()
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=1),
                    encoding="utf-8")
    return path


def parked_numbers(verdicts: list[dict]) -> dict[int, dict]:
    """Les EPICs a parquer, indexes par numero."""
    return {int(v["epic"]): v for v in verdicts if v.get("parked")}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--epic", type=int, action="append", default=[],
                    help="ne mesurer que cet EPIC (repete)")
    ap.add_argument("--refresh", action="store_true",
                    help="ignorer le cache et remesurer")
    args = ap.parse_args(argv)

    if not args.refresh:
        cached = load_cache()
        if cached is not None:
            verdicts = cached.get("verdicts") or []
            if args.epic:
                verdicts = [v for v in verdicts if int(v.get("epic", -1))
                            in set(args.epic)]
            if args.json:
                print(json.dumps({"measured_at": cached.get("measured_at"),
                                  "verdicts": verdicts},
                                 ensure_ascii=False, indent=1))
            else:
                _render(verdicts)
            return 0

    pool = _fetch_pool()
    if pool is None:
        print("UNKNOWN: pool illisible -- aucune mesure, rien n'est parque")
        return 2
    verdicts = measure(pool)
    save_cache(verdicts)
    if args.epic:
        verdicts = [v for v in verdicts if int(v.get("epic", -1)) in set(args.epic)]
    if args.json:
        print(json.dumps({"measured_at": datetime.now(timezone.utc)
                          .strftime("%Y-%m-%dT%H:%M:%SZ"),
                          "verdicts": verdicts}, ensure_ascii=False, indent=1))
    else:
        _render(verdicts)
    return 0


def _fetch_pool() -> list[dict] | None:
    raw = _gh("issue", "list", "--repo", REPO, "--state", "open",
              "--limit", "2000", "--json",
              "number,title,labels,body,createdAt,updatedAt")
    if raw is None:
        return None
    try:
        items = json.loads(raw)
    except json.JSONDecodeError:
        return None
    pool = []
    for it in items:
        pool.append({
            "number": int(it["number"]),
            "title": it.get("title") or "",
            "body": it.get("body") or "",
            "labels": [lb["name"] for lb in it.get("labels") or []],
            "klass": "umbrella" if any(
                (lb["name"] or "").upper() == "EPIC" for lb in it.get("labels") or []
            ) else "grain",
        })
    return pool


def _render(verdicts: list[dict]) -> None:
    parked = [v for v in verdicts if v.get("parked")]
    print(f"{len(verdicts)} EPIC(s) Origami mesure(s) -- {len(parked)} parque(s)")
    for v in verdicts:
        flag = "PARQUE" if v.get("parked") else "servi "
        print(f"  {flag} #{v.get('epic')} : {v.get('reason')}")
        for f in v.get("folds") or []:
            print(f"        pli {f.get('pli')} #{f.get('number')} {f.get('state')}"
                  f"{' (livre)' if f.get('delivered') else ''}")


if __name__ == "__main__":
    sys.exit(main())
