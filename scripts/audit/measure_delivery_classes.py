#!/usr/bin/env python3
"""Census des CLASSES de marqueur qui arment le label `candidate-delivered`.

Pourquoi cet outil (#23762)
---------------------------
Le detecteur `candidate_delivered.py` s'est resserre (depuis #23762 et #24461) :
seule une PR **mergee** portant un mot-cle **fermant** (`Closes`/`Fixes`/
`Resolves`) arme le label, une **tranche** (`See`/`Part of`/`Refs`) ne l'arme
plus, et l'**attestation** d'une lane (`[INFO] candidate-delivered`, ou
`[RELEASED] ... acceptance deja couverte`) l'arme a elle seule.

La precision rapportee jusqu'ici (~42 %, secretariat, 2026-10-31) porte sur la
population **anterieure** a #24461. Depuis, la classe qui arme le label la
plus souvent n'est plus la classe `candidate` mais la classe `attested` : sur
le balayage du 2026-11-08 (fenetre de 400 issues), `candidate` = **2** et
`attested` = **53**. Cette classe n'avait jamais ete mesuree.

Ce census est ** mecanique** : il ne porte aucun jugement. Il rejoue le code du
balayage (meme `classify()`, memes primitives reseau) et range chaque issue
dans la classe de **preuve** qui soutient -- ou ne soutient pas -- son statut
de livraison :

| classe | sens |
|---|---|
| `fermant` | une PR mergee porte un mot-cle fermant pour l'issue, et le fil est silenceux |
| `attestation_fermant` | le fil porte une attestation vivante, soutenue par une PR mergee portant un mot-cle FERMANT |
| `attestation_tranche` | le fil porte une attestation vivante, soutenue seulement par une PR mergee portant un marqueur PARTIEL : la piece est une tranche, pas l'issue |
| `attestation_sans_piece` | le fil porte une attestation vivante, mais **aucune** PR mergee ne declare l'issue : la seule preuve est la parole de la lane |
| `tranche` | une PR mergee ne declare qu'une contribution PARTIELLE : une tranche n'est pas une livraison |
| `sans_preuve` | aucune PR mergee ne declare l'issue |

`attestation_sans_piece` est la **surface de faux positifs** de la classe
`attested` : sans piece, rien ne verifie l'affirmation. C'est la population a
verifier a la main (G.9), et la population que la re-mesure doit suivre.

Usage
-----
::

    python scripts/audit/measure_delivery_classes.py --limit 200
    python scripts/audit/measure_delivery_classes.py --limit 200 --json out.json

Le balayage CI consomme ~3 appels API par issue ; le budget du jeton est de
1000 appels/heure. La fenetre est donc bornee (`--limit`, `--offset`) comme
celle du balayage lui-meme, et l'outil **dit** s'il a atteint la limite
(`WARN page pleine`) plutot que de rendre une liste partielle silencieuse.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from typing import Iterable

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import candidate_delivered as cd  # noqa: E402
from delivery_grammar import ATTESTED, attestation_state  # noqa: E402

LABEL = cd.LABEL_DEFAULT

CLASSES = (
    "fermant",
    "attestation_fermant",
    "attestation_tranche",
    "attestation_sans_piece",
    "tranche",
    "sans_preuve",
    "autre",
)


def evidence_class(issue: dict, refs: list[dict], verdict: str) -> str:
    """Classe de preuve d'une issue -- fonction PURE (aucun reseau).

    ``verdict`` est celui rendu par ``candidate_delivered.classify`` : le
    census ne rederive pas la decision, il en **classe la preuve** -- c'est ce
    qui permet de comparer la decision d'un organe a la piece qui la soutient.

    La question de la classe `attestation` : une attestation vivante
    (« les criteres sont couverts ») est-elle **soutenue** par une piece ?
    - une PR mergee portant un mot-cle FERMANT soutient l'issue entiere ;
    - une PR mergee portant seulement `See`/`Part of`/`Refs` soutient une
      **tranche** -- c'est une piece, mais pas la preuve de l'issue ;
    - a defaut, l'affirmation reste **sans piece** : c'est ce que l'issue
      #23762 demande de mesurer.

    Le classement ne dit rien de la verite de l'attestation : il dit ce qui
    la **soutient**. Le verdict manuel (G.9) reste au lecteur humain.
    """
    number = issue.get("number")
    merged = [r for r in refs if r.get("merged_at")]
    closing = [r for r in merged
               if number and cd.closing_marker(r.get("body") or "", number)]
    declared = [r for r in merged
                if number and cd.delivery_marker(r.get("body") or "", number)]
    if verdict == "candidate":
        return "fermant"
    if verdict == "attested":
        if closing:
            return "attestation_fermant"
        if declared:
            return "attestation_tranche"
        return "attestation_sans_piece"
    if verdict == "partial":
        return "tranche"
    if verdict == "no_delivery":
        return "sans_preuve"
    return "autre"


def _has_label(issue: dict, name: str) -> bool:
    return name in [lab.get("name", "") for lab in (issue.get("labels") or [])]


def census(repo: str, limit: int = 0, offset: int = 0,
           sleep: float = 0.3) -> dict:
    """Parcourt la fenetre ouverte et rend le census (une entree par issue)."""
    issues = cd._rotate_window(cd.list_open_issues(repo), offset, limit)
    body_cache: dict[int, tuple[str, str]] = {}
    rows = []
    for issue in issues:
        number = issue["number"]
        try:
            refs, label_events = cd.timeline_facts(repo, number, LABEL)
            detail = cd.issue_detail(repo, number)
            refs = cd._with_pr_bodies(repo, refs, body_cache)
        except Exception as exc:  # noqa: BLE001 - reseau : on saute, on ne casse pas
            rows.append({"number": number, "classe": "erreur",
                         "detail": str(exc)[:200]})
            continue
        enriched = {
            "number": number,
            "title": issue.get("title", ""),
            "labels": [lab.get("name", "") for lab in (issue.get("labels") or [])],
            "created_at": detail["created_at"],
            "body": detail.get("body", ""),
            "comments": detail["comments"],
        }
        verdict, why = cd.classify(enriched, refs, label_events)
        klass = evidence_class(enriched, refs, verdict)
        labelled = _has_label(issue, LABEL)
        rows.append({
            "number": number,
            "title": enriched["title"][:120],
            "verdict": verdict,
            "classe": klass,
            "label_actuel": labelled,
            "perdrait_le_label": bool(
                labelled and verdict not in ("candidate", "attested")),
            "raison": why[:200],
        })
        if sleep:
            time.sleep(sleep)
    return {"repo": repo, "issues": len(issues), "rows": rows}


def table(census_out: dict) -> str:
    """Rend le tableau des effectifs (texte)."""
    counts: dict[str, int] = {}
    for row in census_out["rows"]:
        counts[row["classe"]] = counts.get(row["classe"], 0) + 1
    lines = [f"census {census_out['repo']} -- {census_out['issues']} issues parcourues"]
    for name in CLASSES:
        lines.append(f"  {name:<26} {counts.get(name, 0)}")
    losses = [r for r in census_out["rows"] if r.get("perdrait_le_label")]
    lines.append(f"  issues qui PERDRAIENT le label sous le predicat resserre : "
                 f"{len(losses)}")
    for row in losses[:40]:
        lines.append(f"    #{row['number']:<6} [{row['verdict']}] {row['title'][:80]}")
    sans_piece = [r for r in census_out["rows"]
                  if r.get("classe") == "attestation_sans_piece"]
    lines.append(f"  attestations SANS PIECE (surface de faux positifs) : "
                 f"{len(sans_piece)}")
    for row in sans_piece[:40]:
        lines.append(f"    #{row['number']:<6} {row['title'][:80]}")
    return "\n".join(lines)


def main(argv: Iterable[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default="jsboige/CoursIA")
    ap.add_argument("--limit", type=int, default=200,
                    help="issues parcourues (0 = toutes ; le budget API est de "
                         "1000 appels/heure, ~3 par issue)")
    ap.add_argument("--offset", type=int, default=0,
                    help="rotation de la fenetre de depart")
    ap.add_argument("--sleep", type=float, default=0.3)
    ap.add_argument("--json", dest="json_path", default=None,
                    help="ecrire le census complet en JSON")
    args = ap.parse_args(list(argv) if argv is not None else None)

    out = census(args.repo, args.limit, args.offset, args.sleep)
    print(table(out))
    if args.json_path:
        with open(args.json_path, "w", encoding="utf-8") as fh:
            json.dump(out, fh, ensure_ascii=False, indent=2)
        print(f"census ecrit : {args.json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
