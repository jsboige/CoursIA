#!/usr/bin/env python3
r"""belt_service_balance.py -- organe d'equilibre du service du tapis (#18832).

## Why

Le user a constate le 2026-10-07 (deja mesure le 05/10) que les issues recentes
sont servies bien plus que les anciennes. Mesure du 07/10 : sur 278 fermetures
en 7 jours, 116 (42 %) sont intervenues moins de 3 jours apres la creation de
l'issue ; 7 seulement portaient sur les 62 issues d'avant septembre. Le tapis
classe correctement, mais le service le contourne -- les consignes n'ont pas
tenu. Il faut un organe.

## Spec (DM dispatch-ai01c2-18832-service-balance, 2026-10-07)

1. Fenetre `--days 7` par defaut. Un **service** est :
   (a) une issue fermee dans la fenetre (closedEvent), OU
   (b) une PR mergee dans la fenetre qui cite l'issue par
       `closingIssuesReferences`.
2. Lecture GraphQL paginee bornee (pas un `gh issue list` plafonne a 30).
3. Age au service = date du service - `createdAt` de l'issue.
   Trois classes :
   - **courant** (< 7 j),
   - **tapis** (7 <= age <= 30 j),
   - **ancien** (> 30 j).
4. Attribution par lane : par le tag `Grain:` de la PR qui sert. Utiliser le
   **parseur canonique** de `scripts/grain_tag.py` (pas une regex maison -- la
   mienne a rate 39 PRs sur 116). Fermeture manuelle sans PR : classe
   `manuel`. PR sans tag lisible : `sans-lane`, a lister, jamais a ignorer.
5. Sortie texte : une ligne par lane (services, % courant, % ancien,
   `[WARN]` si courant > 1/3), une ligne flotte, une ligne stock (ouvertes
   par mois de creation). Plus mode `--json` et `--dashboard-line` (200 chars).
6. **Advisory** : exit 0 sauf panne gh (exit 2, UNKNOWN, jamais un faux 0).
7. Aucun branchement CI bloquant : un gate exige un sign-off user, qui sera
   demande apres 48 h de mesure.

## Usage

    python scripts/coordination/belt_service_balance.py [--days 7] [--json] [--dashboard-line]
        [--owner jsboige] [--repo CoursIA]
        [--max-pages 30]   # GraphQL pagination bound

## Sortie

- Mode texte : TABLE formatee par lane avec % courant, % ancien, [WARN] si
  > 1/3 du service hebdo. Plus une ligne flotte et une ligne stock.
- Mode `--json` : objet JSON `{services: [...], by_lane: {...}, fleet: {...},
  stock: {open_by_month: {YYYY-MM: N}}}`.
- Mode `--dashboard-line` : 1 ligne d'environ 200 caracteres pour le [DONE]
  du coordinateur.

## Coupling

- Construit sur `scripts/grain_tag.py` (parseur canonique de `Grain:`,
  variation-protocol §1).
- Pas de dependance reseau pour les tests purs (fixtures injectees).
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from collections import Counter as CounterType
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Iterable

# Make the shared tag extractor importable when the script is invoked from
# anywhere in the repo.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

COURANT_MAX_DAYS = 7       # age < 7j -> "courant" (mandat user 07/10)
ANCIEN_MIN_DAYS = 30       # age > 30j -> "ancien"
COURANT_CEILING_FRAC = 1 / 3   # plafond de 1/3 du service hebdo par lane


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------


@dataclass
class Service:
    """Une issue servie dans la fenetre."""
    issue_number: int
    issue_created_at: str          # ISO8601
    service_date: str              # ISO8601 (close date ou PR merge date)
    service_kind: str              # "issue_close" | "pr_merge"
    pr_number: int | None = None
    pr_body: str | None = None
    lane: str | None = None        # attribution via Grain tag
    attribution_kind: str = "unknown"  # "grain" | "manuel" | "sans-lane" | "unknown"

    @property
    def age_days(self) -> float:
        """Age au service = service_date - createdAt, en jours."""
        try:
            d_serv = _parse_iso(self.service_date)
            d_crea = _parse_iso(self.issue_created_at)
            return (d_serv - d_crea).total_seconds() / 86400.0
        except Exception:
            return float("nan")

    @property
    def is_courant(self) -> bool:
        """age < 7 j."""
        a = self.age_days
        return a >= 0 and a < COURANT_MAX_DAYS

    @property
    def is_tapis(self) -> bool:
        """age >= 7 j (inclut ancien)."""
        return self.age_days >= COURANT_MAX_DAYS

    @property
    def is_ancien(self) -> bool:
        """age > 30 j (sous-classe de tapis)."""
        return self.age_days > ANCIEN_MIN_DAYS


@dataclass
class LaneStats:
    """Statistiques agregees par lane."""
    lane: str
    services: int = 0
    courant: int = 0
    tapis: int = 0
    ancien: int = 0
    sans_lane: int = 0
    warn: bool = False

    @property
    def courant_pct(self) -> float:
        if self.services == 0:
            return 0.0
        return self.courant / self.services

    @property
    def ancien_pct(self) -> float:
        if self.services == 0:
            return 0.0
        return self.ancien / self.services

    def finalize(self, threshold: float = COURANT_CEILING_FRAC) -> None:
        self.warn = self.courant_pct > threshold


# ---------------------------------------------------------------------------
# Pure helpers (testables without network)
# ---------------------------------------------------------------------------


def _parse_iso(s: str) -> datetime:
    """Parse ISO 8601 (avec ou sans Z)."""
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    return datetime.fromisoformat(s)


def classify_service(s: Service) -> str:
    """Classifie un service en 'courant', 'tapis' ou 'ancien' (mutuellement exclusif).

    Spec : courant (<7j) / tapis (>=7j) / ancien (>30j, sous-classe de tapis).
    On retourne l'age_class de plus haute specificite, pour les sorties
    individuelles (un service est toujours l'un des trois ; ancien est un
    cas particulier de tapis).
    """
    if s.is_courant:
        return "courant"
    if s.is_ancien:
        return "ancien"
    return "tapis"


def attribute_service(s: Service) -> None:
    """Remplit `s.lane` et `s.attribution_kind` a partir du body PR.

    Utilise le parseur canonique de `grain_tag.py`. Si pas de PR, classe
    `manuel`. Si PR sans tag lisible, `sans-lane` (a lister).
    """
    if s.pr_body is None:
        s.attribution_kind = "manuel"
        s.lane = None
        return

    tag = gt.parse_grain_tag(s.pr_body)
    if tag and tag.get("lane"):
        s.attribution_kind = "grain"
        s.lane = tag["lane"]
        return

    # Body present but tag absent or lane absent
    s.attribution_kind = "sans-lane"
    s.lane = None


def aggregate_by_lane(services: Iterable[Service]) -> dict[str, LaneStats]:
    """Agrege les services par lane attribution.

    Spec : un service est `courant` (<7j) ou `tapis` (>=7j). `ancien` est
    une sous-classe de `tapis` (>30j). Donc un service avec age=60 est
    tapis ET ancien, un service avec age=15 est tapis seulement.

    L'aggregation par lane incremente :
    - `courant` (mutuellement exclusif) OU `tapis` (mutuellement exclusif)
    - `ancien` (en supplement, sous-classe de tapis)

    Les services `sans-lane` sont agreges sous `_sans-lane`, les `manuel`
    sous `_manuel`, etc.
    """
    by_lane: dict[str, LaneStats] = {}
    for s in services:
        # Ensure attribution is computed before bucketing
        if s.attribution_kind == "unknown":
            attribute_service(s)
        if s.lane:
            key = s.lane
        else:
            key = f"_{s.attribution_kind or 'unknown'}"
        if key not in by_lane:
            by_lane[key] = LaneStats(lane=key)
        st = by_lane[key]
        st.services += 1
        if s.is_courant:
            st.courant += 1
            # Pas de tapis, pas de ancien
        elif s.is_tapis:
            st.tapis += 1
            if s.is_ancien:
                st.ancien += 1
        if s.attribution_kind == "sans-lane":
            st.sans_lane += 1
    for st in by_lane.values():
        st.finalize()
    return by_lane


def stock_open_by_month(open_issues: Iterable[dict]) -> dict[str, int]:
    """Stock d'issues ouvertes groupees par mois de creation (YYYY-MM)."""
    out: CounterType[str] = CounterType()
    for issue in open_issues:
        created = issue.get("createdAt", "")
        if not created:
            continue
        try:
            d = _parse_iso(created)
            out[d.strftime("%Y-%m")] += 1
        except Exception:
            continue
    return dict(sorted(out.items()))


# ---------------------------------------------------------------------------
# Network I/O (gh CLI -- paginated, bounded)
# ---------------------------------------------------------------------------


def _gh_graphql_paginated(query: str, owner: str, repo: str, max_pages: int = 30) -> list[dict]:
    """Execute une requete GraphQL paginee via gh api graphql, plafonnee.

    Accepte une query qui prend `$owner: String!, $repo: String!, $cursor: String`
    et DOIT retourner un champ `nodes` et `pageInfo { hasNextPage endCursor }`.
    """
    token = os.environ.get("GH_TOKEN") or _run_capture(["gh", "auth", "token"])
    if not token:
        return []

    cursor = "null"
    nodes: list[dict] = []
    pages = 0
    while pages < max_pages:
        pages += 1
        full_query = query.replace("$cursor: String", f"$cursor: {cursor}")
        result = subprocess.run(
            [
                "gh", "api", "graphql",
                "-f", f"query={full_query}",
                "-f", f"owner={owner}",
                "-f", f"repo={repo}",
                "-H", "GraphQL-Features:MergeCommitInfo",
            ],
            env={**os.environ, "GH_TOKEN": token},
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            timeout=60,
        )
        if result.returncode != 0:
            raise RuntimeError(f"gh api graphql returncode={result.returncode} stderr={result.stderr[:200]!r}")
        try:
            data = json.loads(result.stdout)
        except Exception as e:
            raise RuntimeError(f"gh api graphql JSON parse error: {e!r}")
        # Caller is responsible for the path traversal
        nodes.append(data)
        page_info = data.get("data", {}).get("repository", {}).get("defaultBranchRef", {}) \
            if False else None  # not used; left for caller
        # Generic: caller passes a query whose last field is pageInfo
        break  # the above query template returns at most 100 nodes per page; caller can re-call
    return nodes


def _run_capture(argv: list[str], timeout: int = 30) -> str:
    """gh subcommand capture, returns stdout (stripped)."""
    try:
        r = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=timeout)
        if r.returncode == 0:
            return r.stdout.strip()
    except Exception:
        pass
    return ""


def fetch_services(
    owner: str,
    repo: str,
    window_start: datetime,
    max_pages: int = 30,
) -> list[Service]:
    """Recupere tous les services dans la fenetre.

    Un service = PR mergee referencant une issue via `closingIssuesReferences`.
    Le tri GraphQL est force sur `UPDATED_AT` desc (MERGED_AT NOT supported
    par l'API), donc on filtre en memoire sur `mergedAt >= window_start`.
    Les PRs sans closingIssuesReferences (`See #N`, `Part of #N`) ne sont
    pas comptabilisees comme service d'issue -- c'est le `delivery` au sens
    du tapis.

    Pagination via `gh api graphql --input <JSON>` avec variables JSON
    (null pour la premiere page, string pour les suivantes). Plafonnee a
    `max_pages` (defaut 30 = 1500 PRs explorees).
    """
    services: list[Service] = []
    end_cursor: str | None = None
    pages = 0
    has_next = True
    query = (
        "query($owner: String!, $repo: String!, $endCursor: String) {\n"
        "  repository(owner: $owner, name: $repo) {\n"
        "    pullRequests(first: 50, after: $endCursor, "
        "orderBy: {field: UPDATED_AT, direction: DESC}, "
        "states: [MERGED]) {\n"
        "      nodes {\n"
        "        number\n"
        "        mergedAt\n"
        "        closingIssuesReferences(first: 10) { nodes { number createdAt } }\n"
        "        body\n"
        "      }\n"
        "      pageInfo { hasNextPage endCursor }\n"
        "    }\n"
        "  }\n"
        "}\n"
    )
    token = os.environ.get("GH_TOKEN") or _run_capture(["gh", "auth", "token"])
    if not token:
        raise RuntimeError("GH_TOKEN absent et gh auth muet (token requis)")
    while has_next and pages < max_pages:
        pages += 1
        payload = json.dumps({
            "query": query,
            "variables": {
                "owner": owner,
                "repo": repo,
                "endCursor": end_cursor,  # JSON null on first page
            },
        })
        r = subprocess.run(
            ["gh", "api", "graphql", "--input", "-"],
            input=payload,
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            env={**os.environ, "GH_TOKEN": token},
            timeout=60,
        )
        if r.returncode != 0:
            raise RuntimeError(f"gh api graphql returncode={r.returncode} stderr={r.stderr[:200]!r}")
        try:
            data = json.loads(r.stdout)
        except Exception as e:
            raise RuntimeError(f"gh api graphql JSON parse error: {e!r}")
        if data.get("errors"):
            raise RuntimeError(f"gh api graphql errors: {data['errors']}")
        prs = (
            data.get("data", {}).get("repository", {})
            .get("pullRequests", {})
        )
        page_earliest: datetime | None = None
        for pr in prs.get("nodes", []):
            merged_at = pr.get("mergedAt")
            if not merged_at:
                continue
            try:
                d_merge = _parse_iso(merged_at)
            except Exception:
                continue
            if page_earliest is None or d_merge < page_earliest:
                page_earliest = d_merge
            if d_merge < window_start:
                continue
            body = pr.get("body") or ""
            for ref in pr.get("closingIssuesReferences", {}).get("nodes", []):
                created = ref.get("createdAt")
                if not created:
                    continue
                svc = Service(
                    issue_number=ref.get("number", 0),
                    issue_created_at=created,
                    service_date=merged_at,
                    service_kind="pr_merge",
                    pr_number=pr.get("number"),
                    pr_body=body,
                )
                attribute_service(svc)
                services.append(svc)
        # Stop paginating if this page's earliest merge is well before window
        if page_earliest is not None and page_earliest < window_start - timedelta(days=14):
            break
        pi = prs.get("pageInfo", {})
        has_next = bool(pi.get("hasNextPage"))
        end_cursor = pi.get("endCursor")
    return services


def fetch_open_issues(owner: str, repo: str, max_pages: int = 30) -> list[dict]:
    """Liste les issues ouvertes pour le stock."""
    out: list[dict] = []
    end_cursor: str | None = None
    pages = 0
    has_next = True
    query = (
        "query($owner: String!, $repo: String!, $endCursor: String) {\n"
        "  repository(owner: $owner, name: $repo) {\n"
        "    issues(first: 50, after: $endCursor, "
        "orderBy: {field: UPDATED_AT, direction: DESC}, "
        "states: [OPEN]) {\n"
        "      nodes { number createdAt }\n"
        "      pageInfo { hasNextPage endCursor }\n"
        "    }\n"
        "  }\n"
        "}\n"
    )
    token = os.environ.get("GH_TOKEN") or _run_capture(["gh", "auth", "token"])
    if not token:
        raise RuntimeError("GH_TOKEN absent et gh auth muet (token requis)")
    while has_next and pages < max_pages:
        pages += 1
        payload = json.dumps({
            "query": query,
            "variables": {
                "owner": owner,
                "repo": repo,
                "endCursor": end_cursor,
            },
        })
        r = subprocess.run(
            ["gh", "api", "graphql", "--input", "-"],
            input=payload,
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            env={**os.environ, "GH_TOKEN": token},
            timeout=60,
        )
        if r.returncode != 0:
            raise RuntimeError(f"gh api graphql returncode={r.returncode} stderr={r.stderr[:200]!r}")
        try:
            data = json.loads(r.stdout)
        except Exception as e:
            raise RuntimeError(f"gh api graphql JSON parse error: {e!r}")
        if data.get("errors"):
            raise RuntimeError(f"gh api graphql errors: {data['errors']}")
        nodes = (
            data.get("data", {}).get("repository", {})
            .get("issues", {}).get("nodes", [])
        )
        out.extend(nodes)
        pi = (
            data.get("data", {}).get("repository", {})
            .get("issues", {}).get("pageInfo", {})
        )
        has_next = bool(pi.get("hasNextPage"))
        end_cursor = pi.get("endCursor")
    return out


def fetch_closed_issues(
    owner: str,
    repo: str,
    window_start: datetime,
    max_pages: int = 30,
) -> list[Service]:
    """Issues CLOSED dans la fenetre, attribuees a `manuel` (sans PR).

    Le canal manquant du compteur historique : 278 fermetures sur 7 j ne
    sont pas toutes portees par une PR mergee (cf. review #19786 c.6047207444
    point 1). Une fermeture sans PR fermee (closer issue, sans merge) apparait
    dans la fenetre et doit etre comptee comme service, attribuee a la lane
    `manuel` (les PRs de fermeture batch ne sont pas toutes enregistees).

    Tri GraphQL sur UPDATED_AT desc (CLOSED_AT n'est pas un orderBy field) ;
    on filtre en memoire sur `closedAt >= window_start`.

    Lecteur : `number` + `createdAt` + `closedAt`. Le `body` n'est pas
    requis ici (pas d'attribution par tag, ces services vont tous a `manuel`).
    """
    out: list[Service] = []
    end_cursor: str | None = None
    pages = 0
    has_next = True
    query = (
        "query($owner: String!, $repo: String!, $endCursor: String) {\n"
        "  repository(owner: $owner, name: $repo) {\n"
        "    issues(first: 50, after: $endCursor, "
        "orderBy: {field: UPDATED_AT, direction: DESC}, "
        "states: [CLOSED]) {\n"
        "      nodes { number createdAt closedAt }\n"
        "      pageInfo { hasNextPage endCursor }\n"
        "    }\n"
        "  }\n"
        "}\n"
    )
    token = os.environ.get("GH_TOKEN") or _run_capture(["gh", "auth", "token"])
    if not token:
        raise RuntimeError("GH_TOKEN absent et gh auth muet (token requis)")
    while has_next and pages < max_pages:
        pages += 1
        payload = json.dumps({
            "query": query,
            "variables": {
                "owner": owner,
                "repo": repo,
                "endCursor": end_cursor,
            },
        })
        r = subprocess.run(
            ["gh", "api", "graphql", "--input", "-"],
            input=payload,
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            env={**os.environ, "GH_TOKEN": token},
            timeout=60,
        )
        if r.returncode != 0:
            raise RuntimeError(f"gh api graphql returncode={r.returncode} stderr={r.stderr[:200]!r}")
        try:
            data = json.loads(r.stdout)
        except Exception as e:
            raise RuntimeError(f"gh api graphql JSON parse error: {e!r}")
        if data.get("errors"):
            raise RuntimeError(f"gh api graphql errors: {data['errors']}")
        nodes = (
            data.get("data", {}).get("repository", {})
            .get("issues", {}).get("nodes", [])
        )
        page_earliest: datetime | None = None
        for issue in nodes:
            closed_at = issue.get("closedAt")
            if not closed_at:
                continue
            try:
                d_close = _parse_iso(closed_at)
            except Exception:
                continue
            if page_earliest is None or d_close < page_earliest:
                page_earliest = d_close
            if d_close < window_start:
                continue
            created = issue.get("createdAt")
            if not created:
                continue
            svc = Service(
                issue_number=issue.get("number", 0),
                issue_created_at=created,
                service_date=closed_at,
                service_kind="manuel",
                pr_number=None,
                pr_body="",
            )
            attribute_service(svc)
            out.append(svc)
        if page_earliest is not None and page_earliest < window_start - timedelta(days=14):
            break
        pi = (
            data.get("data", {}).get("repository", {})
            .get("issues", {}).get("pageInfo", {})
        )
        has_next = bool(pi.get("hasNextPage"))
        end_cursor = pi.get("endCursor")
    return out


def deduplicate_services(services: list[Service]) -> list[Service]:
    """Dedoublonne les services sur (issue_number, service_date).

    Une issue fermee par PR est dans `pr_merge` (via closingIssuesReferences)
    ET dans `manuel` (via closedAt). On garde le `pr_merge` (attribution par
    tag `Grain:` de la PR, plus precise) et on retire le `manuel`.

    En cas d'egalite (deux services pour le meme issue_number + service_date
    mais ni pr_merge ni manuels -- defensif), on garde le premier.
    """
    seen: dict[tuple[int, str], Service] = {}
    for s in services:
        key = (s.issue_number, s.service_date)
        if key in seen:
            # Preferer pr_merge (attribution par tag)
            if seen[key].service_kind == "pr_merge":
                continue
            if s.service_kind == "pr_merge":
                seen[key] = s
        else:
            seen[key] = s
    return list(seen.values())


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def render_text(
    by_lane: dict[str, LaneStats],
    fleet_total: int,
    fleet_courant: int,
    fleet_ancien: int,
    stock: dict[str, int],
) -> str:
    """Tableau texte par lane + ligne flotte + ligne stock."""
    lines = []
    lines.append("Belt service balance (7 j)")
    lines.append("-" * 72)
    lines.append(f"{'lane':<32} {'svc':>4} {'courant':>8} {'tapis':>6} {'ancien':>7} {'warn':>5}")
    for lane in sorted(by_lane.keys()):
        st = by_lane[lane]
        warn = "[WARN]" if st.warn else ""
        lines.append(
            f"{lane:<32} {st.services:>4} {st.courant_pct:>7.0%} "
            f"{st.tapis:>6} {st.ancien_pct:>6.0%} {warn:>5}"
        )
    fleet_courant_pct = fleet_courant / fleet_total if fleet_total else 0
    fleet_ancien_pct = fleet_ancien / fleet_total if fleet_total else 0
    fleet_warn = "[WARN]" if fleet_courant_pct > COURANT_CEILING_FRAC else ""
    lines.append("-" * 72)
    lines.append(
        f"{'FLEET':<32} {fleet_total:>4} {fleet_courant_pct:>7.0%} "
        f"{'':>6} {fleet_ancien_pct:>6.0%} {fleet_warn:>5}"
    )
    lines.append("")
    lines.append("Stock (issues ouvertes par mois de creation) :")
    if stock:
        for k in sorted(stock):
            lines.append(f"  {k} : {stock[k]}")
    else:
        lines.append("  (vide)")
    return "\n".join(lines)


def render_json(
    services: list[Service],
    by_lane: dict[str, LaneStats],
    fleet_total: int,
    fleet_courant: int,
    fleet_ancien: int,
    stock: dict[str, int],
) -> str:
    out = {
        "services": [
            asdict(s) | {
                "age_days": s.age_days,
                "is_courant": s.is_courant,
                "is_tapis": s.is_tapis,
                "is_ancien": s.is_ancien,
            }
            for s in services
        ],
        "by_lane": {k: asdict(v) | {"courant_pct": v.courant_pct, "ancien_pct": v.ancien_pct} for k, v in by_lane.items()},
        "fleet": {
            "total": fleet_total,
            "courant": fleet_courant,
            "ancien": fleet_ancien,
            "courant_pct": fleet_courant / fleet_total if fleet_total else 0,
            "ancien_pct": fleet_ancien / fleet_total if fleet_total else 0,
            "warn": (fleet_courant / fleet_total if fleet_total else 0) > COURANT_CEILING_FRAC,
        },
        "stock": {"open_by_month": stock},
    }
    return json.dumps(out, indent=2, ensure_ascii=False)


def render_dashboard_line(by_lane: dict[str, LaneStats], fleet_total: int, fleet_courant: int) -> str:
    """Une ligne compacte d'environ 200 chars pour le [DONE] du coordinateur."""
    fleet_pct = (fleet_courant / fleet_total * 100) if fleet_total else 0
    parts = []
    for lane in sorted(by_lane.keys()):
        st = by_lane[lane]
        if st.services > 0:
            tag = "[WARN] " if st.warn else ""
            parts.append(f"{lane}:{st.courant_pct:.0%}")
    summary = " ".join(parts)
    line = f"belt-balance[7j]: fleet={fleet_total}s {fleet_pct:.0f}%courant -- {summary}"
    return line[:240]


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--days", type=int, default=7,
                        help="Fenetre de service en jours (defaut 7)")
    parser.add_argument("--owner", default="jsboige",
                        help="Proprietaire du repo (defaut jsboige)")
    parser.add_argument("--repo", default="CoursIA",
                        help="Nom du repo (defaut CoursIA)")
    parser.add_argument("--max-pages", type=int, default=30,
                        help="Plafond pagination GraphQL (defaut 30)")
    parser.add_argument("--json", action="store_true",
                        help="Sortie JSON structuree")
    parser.add_argument("--dashboard-line", action="store_true",
                        help="Une ligne ~200 chars pour dashboard [DONE]")
    parser.add_argument("--no-fetch", action="store_true",
                        help="Skip la lecture reseau (utile pour debug fixtures)")
    args = parser.parse_args(argv)

    window_start = datetime.now(timezone.utc) - timedelta(days=args.days)

    if args.no_fetch:
        services = []
        stock: dict[str, int] = {}
    else:
        try:
            services_pr = fetch_services(args.owner, args.repo, window_start, max_pages=args.max_pages)
            services_manuel = fetch_closed_issues(args.owner, args.repo, window_start, max_pages=args.max_pages)
            open_issues = fetch_open_issues(args.owner, args.repo, max_pages=args.max_pages)
        except Exception as e:
            print(f"UNKNOWN: {e}", file=sys.stderr)
            return 2
        services = deduplicate_services(services_pr + services_manuel)
        stock = stock_open_by_month(open_issues)

    by_lane = aggregate_by_lane(services)
    fleet_total = len(services)
    fleet_courant = sum(s.is_courant for s in services)
    fleet_ancien = sum(s.is_ancien for s in services)

    if args.json:
        print(render_json(services, by_lane, fleet_total, fleet_courant, fleet_ancien, stock))
    elif args.dashboard_line:
        print(render_dashboard_line(by_lane, fleet_total, fleet_courant))
    else:
        print(render_text(by_lane, fleet_total, fleet_courant, fleet_ancien, stock))
    return 0


if __name__ == "__main__":
    sys.exit(main())