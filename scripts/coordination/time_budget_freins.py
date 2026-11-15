#!/usr/bin/env python3
"""Organe de budget de temps — extrait les [FREINS] chiffres des [DONE] de la flotte.

Pourquoi cet organe existe
--------------------------
Mandat user du 2026-11-14 (verbatim relaye par ai-01, dispatch
msg-20261114T224242-11ronf) : « Faire relever les chiffres, parmi toutes les
obsessions quantitatives dont vous truffez nos documents, celle sur votre time
budget est sans doute la plus saine, car c'est vraiment le nerf de la guerre. »

Le secreariat tient depuis ce mandat un tableau de budget de temps permanent
sur ``workspace-CoursIA-3`` : une ligne par cycle termine et par lane, un cumul
24 h par cause, et la liste des ``[DONE]`` sans ``[FREINS]`` chiffre. Le geste
a ete fait a la main deux fois (tour de table 14/11 : 243 min ; tableau v1 :
+71 min, cumul 314) ; la regle organe du dispatch impose qu'a la troisieme
passe ce soit un script. C'est ce script (issue #26624).

Il ne lit que les fichiers MIROIRS des dashboards RooSync (ecriture primaire :
PostgreSQL ; le fichier est en retard -- fiche memoire du secretariat). Il ne
repare rien : il mesure, il nomme les lanes fautives, il rend un rapport.

Usage
-----
    python scripts/coordination/time_budget_freins.py                     # 24 h glissantes
    python scripts/coordination/time_budget_freins.py --since 2026-11-14T00:00:00Z
    python scripts/coordination/time_budget_freins.py --dashboard-file dashboard.md
    python scripts/coordination/time_budget_freins.py --json              # sortie structuree

Codes de sortie : 0 = rapport rendu (des lanes fautives ne sont PAS une erreur
d'execution : le rapport est le verdict, la relance DM est le geste) ·
2 = erreur d'execution (aucune source lisible, fenetre invalide).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Format des entrees intercom (miroir dashboard RooSync) -- fige sur des extraits
# reels de workspace-CoursIA-3 (2026-11-14) :
#
#   ### [2026-11-14T21:36:21.262Z] myia-po-2028|CoursIA-3
#   [msg: myia-po-2028:CoursIA-3:ic-2026-11-14T21362-j0hs]
#   [tags: DONE]
#
#   [DONE][SECRETARY] c3102 — 14/11 22:43→22:52 local (~21:43–21:52Z) — cron 48c9c8d5
#   ...corps...
#   [FREINS]
#   - Famine runners sur #26581 : 14 jambes queued depuis ~21:26Z (17+ min d'attente) — ... — infra/ai-01.
#
#   ---
#
# Fait portant : l'en-tete `###` est en UTC (suffixe Z), les heures ecrites DANS
# le corps par les lanes sont de la prose locale (UTC+1). La fenetre --since se
# cale sur l'en-tete, jamais sur la prose.
# ---------------------------------------------------------------------------

_HEADER_RE = re.compile(
    r"^###\s+\[(?P<ts>\d{4}-\d{2}-\d{2}T[\d:.]+Z)\]\s+(?P<machine>[\w.\-]+)\|(?P<workspace>[\w.\-]+)\s*$"
)
_TAGS_RE = re.compile(r"^\[tags:\s*(?P<tags>[^\]]*)\]", re.MULTILINE)
# Le marqueur tolere les decorations markdown REELLES des [DONE] de la flotte :
# `**[FREINS]** (demande ai-01)`, `### [FREINS]`, `> [FREINS]`, `[FREINS] — top-3`.
# Mesure du 2026-11-15 : un [DONE] ecrivant ses freins sous `**[FREINS]** — top-3`
# n'etait pas reconnu — ses chiffres existaient et comptaient 0. La classe
# n'inclut PAS `-` : une puce `- [FREINS] ...` reste une puce, pas un marqueur.
_FREINS_MARKER_RE = re.compile(r"^[\s>#*_]*\[FREINS\]", re.IGNORECASE)
# `17+ min`, `~5 min`, `0 min` -- le premier chiffre suivi de `min` fait foi.
# Le `+` optionnel couvre la forme mesuree `35+ min (hosted)` : sans lui, une
# puce REELLE du miroir (c3103) serait lue « sans minutes » et fabriquerait un
# fautif de plus (faux positif -- exactement le defaut que l'acceptance 2
# interdit dans l'autre sens).
_MINUTES_RE = re.compile(r"(\d+)\s*\+?\s*min\b", re.IGNORECASE)
# Duree declaree par la lane dans sa premiere ligne : `22:43→22:52 local`.
_DURATION_RE = re.compile(
    r"(\d{1,2}):(\d{2})\s*(?:→|->|à)\s*(\d{1,2}):(\d{2})"
)
_CYCLE_RE = re.compile(r"\bc(\d{3,5})\b")
_PR_RE = re.compile(r"#(\d{4,6})\b")

_CAUSE_MAX_CHARS = 48


@dataclass
class Frein:
    """Une puce du bloc [FREINS] : cause + minutes quand elles sont chiffrees."""

    cause: str | None  # None = puce « aucun » (rien a compter)
    minutes: int | None  # None = cause nommee SANS minutes (n.c.)
    raw: str

    @property
    def is_aucun(self) -> bool:
        return self.cause is None


@dataclass
class Entry:
    """Une entree intercom [DONE] d'un dashboard, avec son bloc [FREINS]."""

    source: str  # fichier miroir d'origine
    timestamp: datetime  # UTC (en-tete ###)
    lane: str  # machine:workspace
    cycle: str | None  # identifiant cNNNN declare dans le corps
    duration_min: int | None  # duree declaree par la lane, si parsable
    deliverables: list[str]  # PRs citees dans le corps
    freins: list[Frein] = field(default_factory=list)
    body_first_line: str = ""

    @property
    def freins_total_min(self) -> int:
        return sum(f.minutes for f in self.freins if f.minutes is not None)

    @property
    def uncounted_causes(self) -> list[str]:
        """Causes nommees sans minutes : le trou de chiffrage, pas un zero."""
        return [f.cause for f in self.freins if f.cause is not None and f.minutes is None]

    @property
    def faulty_reasons(self) -> list[str]:
        reasons: list[str] = []
        if not self.freins:
            reasons.append("aucun bloc [FREINS]")
        if self.uncounted_causes:
            reasons.append("cause sans minutes : " + " ; ".join(self.uncounted_causes))
        return reasons


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def _parse_header_ts(raw: str) -> datetime | None:
    try:
        return datetime.fromisoformat(raw.replace("Z", "+00:00"))
    except ValueError:
        return None


def _split_entries(text: str) -> list[tuple[str, str]]:
    """Coupe le miroir en blocs (en-tete ###, corps) — tout ce qui precede la
    premiere en-tete est ignore (section status du dashboard)."""
    blocks: list[tuple[str, str]] = []
    parts = re.split(r"(?m)^(?=### )", text)
    for part in parts:
        lines = part.splitlines()
        if not lines or not lines[0].startswith("### "):
            continue
        blocks.append((lines[0], "\n".join(lines[1:])))
    return blocks


def _extract_freins(body: str) -> list[Frein]:
    """Puces du bloc [FREINS] : lignes `- ...` suivant le marqueur, jusqu'au
    separateur `---`, a l'en-tete suivante ou a la fin."""
    freins: list[Frein] = []
    lines = body.splitlines()
    in_block = False
    for line in lines:
        stripped = line.strip()
        if _FREINS_MARKER_RE.match(line):
            in_block = True
            continue
        if not in_block:
            continue
        if stripped.startswith("### ") or stripped == "---":
            break
        if not stripped:
            continue  # ligne vide entre deux puces : tolerate
        if stripped.startswith("- "):
            freins.append(_parse_bullet(stripped[2:].strip()))
        else:
            # Une ligne de prose (pas une puce) ferme le bloc.
            break
    return freins


def _parse_bullet(raw: str) -> Frein:
    """Une puce [FREINS] vers (cause, minutes).

    Formes reels mesurees (miroir 2026-11-14) :
      - `aucun ce cycle (...)`                       -> cause None, 0 min
      - `cause — N min — geste — qui`                -> canonique consigne B
      - `Cause : detail (17+ min d'attente) — ...`   -> prose, minutes entre parentheses
    """
    if raw.lower().startswith("aucun"):
        return Frein(cause=None, minutes=0, raw=raw)
    m = _MINUTES_RE.search(raw)
    minutes = int(m.group(1)) if m else None
    cause = raw
    if " — " in cause:
        cause = cause.split(" — ")[0]
    if " : " in cause:
        cause = cause.split(" : ")[0]
    cause = cause.strip().rstrip(".").strip()
    cause = cause[:_CAUSE_MAX_CHARS]
    return Frein(cause=cause or "cause non nommee", minutes=minutes, raw=raw)


def _parse_duration(body: str) -> int | None:
    """`22:43→22:52 local` dans les premieres lignes -> duree declaree en minutes."""
    head = "\n".join(body.splitlines()[:6])
    m = _DURATION_RE.search(head)
    if not m:
        return None
    h1, m1, h2, m2 = (int(g) for g in m.groups())
    delta = (h2 * 60 + m2) - (h1 * 60 + m1)
    if delta < 0:
        delta += 24 * 60  # cycle a cheval sur minuit
    return delta


def _first_content_line(body: str) -> str:
    """Premiere ligne non vide qui n'est pas une meta [msg:]/[tags:] — c'est la
    premiere ligne de PROSE de l'entree (typiquement son marqueur [DONE])."""
    for ln in body.splitlines():
        stripped = ln.strip()
        if not stripped or stripped.startswith("[msg:") or stripped.startswith("[tags:"):
            continue
        return stripped
    return ""


def parse_dashboard_text(text: str, source: str = "<texte>") -> list[Entry]:
    """Extrait les entrees [DONE] d'un miroir dashboard."""
    entries: list[Entry] = []
    for header, body in _split_entries(text):
        hm = _HEADER_RE.match(header.strip())
        if not hm:
            continue
        ts = _parse_header_ts(hm.group("ts"))
        if ts is None:
            continue
        tm = _TAGS_RE.search(body)
        tags = {t.strip().upper() for t in tm.group("tags").split(",")} if tm else set()
        first_line = _first_content_line(body)
        is_done = "DONE" in tags or first_line.startswith("[DONE]")
        if not is_done:
            continue
        cm = _CYCLE_RE.search("\n".join(body.splitlines()[:6]))
        entries.append(
            Entry(
                source=source,
                timestamp=ts,
                lane=f"{hm.group('machine')}:{hm.group('workspace')}",
                cycle=f"c{cm.group(1)}" if cm else None,
                duration_min=_parse_duration(body),
                deliverables=_extract_prs(body),
                freins=_extract_freins(body),
                body_first_line=first_line[:120],
            )
        )
    return entries


def _extract_prs(body: str) -> list[str]:
    """PRs citees dans le corps, ordonnees, dedoublees — le « livrable » declare."""
    return sorted({"#" + n for n in _PR_RE.findall(body)})


# ---------------------------------------------------------------------------
# Rapport
# ---------------------------------------------------------------------------

def _dedupe_entries(entries: list[Entry]) -> tuple[list[Entry], int]:
    """Ecartes les entrees [DONE] cross-postees sur deux dashboards.

    Une lane peut poster le meme [DONE] sur son dashboard ``workspace`` ET sur un
    ``machine`` ou le ``global`` (crossPost du dashboard MCP). Le miroir porte
    alors DEUX fois le meme bloc, avec le meme en-tete : sans dedup, ses minutes
    comptent double et la lane apparait deux fois dans le tableau par cycle.

    La cle est (horodatage d'en-tete, lane, premiere ligne de corps) : trois
    champs que le cross-post recopie a l'identique, et qu'une AUTRE lane ne peut
    pas produire par hasard -- deux lanes n'ont pas le meme couple
    ``machine:workspace``, et deux cycles d'une meme lane n'ont ni le meme
    horodatage ni le meme marqueur de cycle en tete de corps.
    """
    seen: set[tuple[str, str, str]] = set()
    kept: list[Entry] = []
    doublons = 0
    for e in entries:
        key = (e.timestamp.isoformat(), e.lane, e.body_first_line)
        if key in seen:
            doublons += 1
            continue
        seen.add(key)
        kept.append(e)
    return kept, doublons


def build_report(entries: list[Entry], since: datetime, until: datetime) -> dict:
    """Fenetre + trois sorties du mandat : (a) par cycle, (b) cumul par cause,
    (c) fautifs sans [FREINS] chiffre."""
    window = [e for e in entries if since <= e.timestamp <= until]
    window.sort(key=lambda e: e.timestamp)
    window, doublons = _dedupe_entries(window)

    per_cycle = [
        {
            "lane": e.lane,
            "cycle": e.cycle,
            "timestamp": e.timestamp.isoformat(),
            "duree_min": e.duration_min,
            "livrables": e.deliverables,
            "freins": [
                {"cause": f.cause, "minutes": f.minutes} for f in e.freins
            ],
            "freins_total_min": e.freins_total_min,
        }
        for e in window
    ]

    cumul: dict[str, dict] = {}
    for e in window:
        for f in e.freins:
            if f.cause is None:
                continue  # puce « aucun » : rien a cumuler
            bucket = cumul.setdefault(f.cause.lower(), {"cause": f.cause, "minutes": 0, "occurrences": 0, "non_chiffrees": 0})
            bucket["occurrences"] += 1
            if f.minutes is None:
                bucket["non_chiffrees"] += 1
            else:
                bucket["minutes"] += f.minutes

    # Le cumul par cause buckete le TEXTE LIBRE, borne a 48 car. : trois facons
    # d'ecrire une meme famine sortent en trois lignes. La fenetre du 2026-11-15
    # en portait l'exemple sur #26581 -- « Famine runners sur #26581 »,
    # « Analyze (python) #26581 QUEUED 35+ min », « runners hosted satures ».
    # Quand les mots varient, le point commun d'une cause est l'OBJET qu'elle
    # cite : on agrege donc AUSSI par objet. Une puce citant plusieurs objets est
    # imputee au PREMIER (ordre du texte), si bien que la somme par objet ne
    # depasse jamais le total mesure.
    par_objet: dict[str, dict] = {}
    for e in window:
        for f in e.freins:
            if f.cause is None:
                continue
            cites = _PR_RE.findall(f.raw)
            if not cites:
                continue
            key = "#" + cites[0]
            bucket = par_objet.setdefault(
                key,
                {"objet": key, "minutes": 0, "occurrences": 0, "non_chiffrees": 0, "causes": []},
            )
            bucket["occurrences"] += 1
            if f.minutes is None:
                bucket["non_chiffrees"] += 1
            else:
                bucket["minutes"] += f.minutes
            if f.cause not in bucket["causes"]:
                bucket["causes"].append(f.cause)

    faulties = [
        {
            "lane": e.lane,
            "cycle": e.cycle,
            "timestamp": e.timestamp.isoformat(),
            "raisons": e.faulty_reasons,
        }
        for e in window
        if e.faulty_reasons
    ]

    return {
        "fenetre": {
            "depuis": since.isoformat(),
            "jusqu_a": until.isoformat(),
            "entrees_done": len(window),
            "doublons_ecartes": doublons,
        },
        "par_cycle": per_cycle,
        "cumul_par_cause": sorted(cumul.values(), key=lambda b: (-b["minutes"], -b["non_chiffrees"], b["cause"])),
        "cumul_par_objet": sorted(par_objet.values(), key=lambda b: (-b["minutes"], -b["non_chiffrees"], b["objet"])),
        "total_min_mesurees": sum(b["minutes"] for b in cumul.values()),
        "fautifs": faulties,
        "limites": [
            "miroir fichier en retard sur l'ecriture primaire PostgreSQL : la fraicheur se juge par l'horodatage de la derniere entree lue, pas supposee",
            "durees et minutes declaratives, non verifiees",
            "une cause nommee sans minutes compte n.c. (0 au total, listee en fautifs)",
            "heures ecrites dans le corps des lanes = prose locale (UTC+1) ; la fenetre se cale sur les en-tetes UTC",
            "cumul par cause = texte libre borne a 48 car. : deux ecritures d'une meme cause y restent deux lignes ; le cumul par objet cite les regroupe",
            "cumul par objet : une puce citant plusieurs objets est imputee au premier, et une puce sans objet cite n'y entre pas (elle reste dans le cumul par cause)",
            "un [DONE] ecrivant ses freins en prose SANS marqueur [FREINS] reste hors mesure (faux positif connu, non devinable sans risquer d'inventer des chiffres)",
        ],
    }


def render_markdown(report: dict) -> str:
    """Tableau postable tel quel sur le dashboard — le secretaire n'y ajoute que
    le numero de cycle."""
    lines: list[str] = []
    fen = report["fenetre"]
    doublons = fen.get("doublons_ecartes") or 0
    suffixe = f", {doublons} doublon(s) cross-post écarté(s)" if doublons else ""
    lines.append(
        f"## Budget de temps — fenêtre {fen['depuis']} → {fen['jusqu_a']} "
        f"({fen['entrees_done']} [DONE]{suffixe})"
    )

    lines.append("")
    lines.append("### Par cycle")
    lines.append("| Lane | Cycle | Durée (min) | Livrable | Minutes perdues par cause |")
    lines.append("|---|---|---|---|---|")
    for row in report["par_cycle"]:
        duree = str(row["duree_min"]) if row["duree_min"] is not None else "n.d."
        livrable = " ".join(row["livrables"][:3]) + (" +" + str(len(row["livrables"]) - 3) + " autres" if len(row["livrables"]) > 3 else "") if row["livrables"] else "rien"
        causes = " · ".join(
            (f"{f['cause']} {f['minutes']}" if f["minutes"] is not None else f"{f['cause']} n.c.")
            for f in row["freins"]
            if f["cause"] is not None
        ) or "0"
        lines.append(f"| {row['lane']} | {row['cycle'] or '—'} | {duree} | {livrable} | {causes} |")

    lines.append("")
    lines.append("### Cumul par cause")
    lines.append("| Cause | Minutes | Occurrences | Non chiffrées |")
    lines.append("|---|---|---|---|")
    for b in report["cumul_par_cause"]:
        lines.append(f"| {b['cause']} | {b['minutes']} | {b['occurrences']} | {b['non_chiffrees']} |")
    lines.append(f"| **Total mesuré** | **{report['total_min_mesurees']}** | | |")

    # Le cumul par cause ne regroupe que le texte libre : deux ecritures d'une
    # meme famine y restent deux lignes. La vue par objet cite donne le
    # regroupement que les mots ne donnent pas (« combien a coute #26581 ? »).
    objets = report.get("cumul_par_objet") or []
    if objets:
        lines.append("")
        lines.append("### Cumul par objet cité")
        lines.append("| Objet | Minutes | Occurrences | Non chiffrées | Écritures de la cause |")
        lines.append("|---|---|---|---|---|")
        for b in objets:
            causes = " · ".join(b["causes"][:3]) + (" …" if len(b["causes"]) > 3 else "")
            lines.append(f"| {b['objet']} | {b['minutes']} | {b['occurrences']} | {b['non_chiffrees']} | {causes} |")

    lines.append("")
    lines.append("### [DONE] sans [FREINS] chiffré")
    if report["fautifs"]:
        for f in report["fautifs"]:
            lines.append(f"- {f['lane']} {f['cycle'] or ''} — " + " ; ".join(f["raisons"]))
    else:
        lines.append("- aucun : chaque [DONE] de la fenêtre porte son chiffrage")

    lines.append("")
    lines.append("### Limites de la mesure")
    for lim in report["limites"]:
        lines.append(f"- {lim}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def resolve_dashboard_files(explicit: list[Path] | None, key: str | None = None) -> list[Path]:
    """Sources : --dashboard-file en priorite ; sinon le dossier miroir
    $ROOSYNC_SHARED_PATH/dashboards (toutes cles, hors archive/) — la meme
    resolution que roosync_dashboard refresh. ``key`` restreint par sous-chaine
    sur le nom de fichier (ex. ``CoursIA`` pour la flotte CoursIA seule : le
    dossier partagé porte aussi les dashboards infra des autres workspaces,
    Maintenance/vllm/claudish, qui ne relèvent pas de la consigne B)."""
    if explicit:
        return [p for p in explicit if p.is_file()]
    shared = os.environ.get("ROOSYNC_SHARED_PATH")
    if not shared:
        return []
    root = Path(shared) / "dashboards"
    if not root.is_dir():
        return []
    return sorted(
        p for p in root.glob("*.md")
        if p.is_file() and (key is None or key.lower() in p.name.lower())
    )


def _parse_since(raw: str) -> datetime:
    """ISO 8601 ; sans fuseau = UTC assume (les en-tetes miroir sont UTC)."""
    dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt


def _force_utf8_stdio() -> None:
    """Force stdout/stderr en UTF-8 quand le flux les a ouverts autrement.

    Sous Windows, ``python -I`` (mode isole) ignore ``PYTHONIOENCODING`` : le
    stdout reste en cp1252 et le premier caractere non-ASCII du rapport (``é``,
    ``→``, ``—``) tue le script sur ``UnicodeEncodeError: 'charmap'``. Un organe
    ne peut pas dependre d'une variable d'environnement que son appelant doit
    penser a poser : il force son propre encodage.

    No-op quand le flux est deja en UTF-8 (cas POSIX, et le ``capsys`` de pytest,
    qui n'expose pas ``reconfigure``).
    """
    for stream in (sys.stdout, sys.stderr):
        encoding = (getattr(stream, "encoding", None) or "").lower().replace("-", "")
        if encoding in ("utf8", "utf8mb4"):
            continue
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is None:
            continue
        try:
            reconfigure(encoding="utf-8", errors="replace")
        except (ValueError, OSError):
            pass


def main(argv: list[str] | None = None) -> int:
    _force_utf8_stdio()
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    default_since = datetime.now(timezone.utc) - timedelta(hours=24)
    ap.add_argument(
        "--since",
        type=_parse_since,
        default=default_since,
        help="debut de fenetre ISO 8601 (defaut : 24 h glissantes)",
    )
    ap.add_argument(
        "--dashboard-file",
        action="append",
        type=Path,
        default=None,
        help="fichier miroir dashboard a la place du dossier partagé (repeatable, tests)",
    )
    ap.add_argument(
        "--key",
        default=None,
        help="sous-chaine de filtrage des cles dashboard (ex. CoursIA : sans lui, le "
        "rapport balaie aussi les dashboards infra des autres workspaces)",
    )
    ap.add_argument("--json", action="store_true", help="sortie structurée")
    args = ap.parse_args(argv)

    since = args.since
    until = datetime.now(timezone.utc)

    files = resolve_dashboard_files(args.dashboard_file, key=args.key)
    if not files:
        print(
            "time_budget_freins: aucune source lisible — $ROOSYNC_SHARED_PATH absent et "
            "aucun --dashboard-file (le dossier attendu est <shared>/dashboards)",
            file=sys.stderr,
        )
        return 2

    entries: list[Entry] = []
    unreadable: list[str] = []
    for path in files:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            unreadable.append(f"{path.name}: {exc}")
            continue
        entries.extend(parse_dashboard_text(text, source=path.name))

    report = build_report(entries, since, until)
    if unreadable:
        report["limites"].insert(0, "sources illisibles (exclues du rapport) : " + " ; ".join(unreadable))

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(render_markdown(report))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:  # 2 est reserve aux pannes : un rapport avec fautifs n'est pas une erreur
        print(f"time_budget_freins: erreur d'exécution {exc!r}", file=sys.stderr)
        sys.exit(2)
