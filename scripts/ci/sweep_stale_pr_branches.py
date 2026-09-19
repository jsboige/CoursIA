"""Sweep des PRs ouvertes en retard sur leur base -- pilote de #16915.

`update_stale_pr_branches.py` (#16149) sait METTRE A JOUR une PR nommee :
detection de base empilee-vs-`main`, epinglage TOCTOU par SHA, registre des
mises a jour en vol, `--apply`, plafond `--max-updates`. Mais `--pr` y est un
argument REQUIS : l'organe sait traiter des PRs nommees, il ne sait pas les
TROUVER. Rien ne l'invoque -- aucun workflow, aucun cron, aucun skill.

Ce pilote est la piece manquante, et elle ne fait QUE ca :

  1. enumerer les PRs ouvertes (`gh pr list`, champs gratuits seulement) ;
  2. ecarter localement ce qui ne peut pas etre une candidate (brouillon,
     fork) -- un filtre de COUT, pas de decision : l'organe re-tranche tout ;
  3. ordonner (les plus anciennement mises a jour d'abord : le retard se
     corrige avec le temps qui passe, donc la file la plus ancienne est la
     plus probablement en retard) ;
  4. deleguer chaque numero a `process_one`, qui mesure, epingle, reserve et
     applique -- avec ses propres gardes (CONFLICTING, MERGEABLE_UNKNOWN,
     UP_TO_DATE, CAP_REACHED...), ses propres plafonds et son registre.

Le retard ne se lit PAS dans `mergeStateStatus` (0 `BEHIND` sur les 200
lignes ouvertes lues, mesure 2026-09-17 dans le module) : seuls les brouillons
et les forks sont ecarts ici parce que ces deux champs sont gratuits dans
`gh pr list`. Tout le reste -- y compris une PR `CLEAN` et en retard, le cas
que le pool porte en masse -- part vers l'organe, seul juge du deficit.

Peremption (LE piege de #16915) : un update reecrit la tete, donc checks,
reviews et dossier `[ADJOINT PREFLIGHT]` deviennent STALE. Chaque resultat
d'organe porte `invalidated`; le pilote les AGREGE dans `dossiers_invalides`
en tete de sortie pour que l'adjoint sache quels dossiers refabriquer --
sinon le sweep detruit du premachage en silence.

Le plancher DWELL ne se re-arme PAS sur un update-branch serveur legitime :
l'exemption `last_authoritative_committed_at` (merge_dwell.py, #16149) reste
la seule autorite, et le test `test_sweep_update_ne_re_arme_pas_le_dwell`
verifie l'integration.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ORGANE = HERE / "update_stale_pr_branches.py"

_spec = importlib.util.spec_from_file_location("update_stale_pr_branches", ORGANE)
organe = importlib.util.module_from_spec(_spec)
sys.modules["update_stale_pr_branches"] = organe
_spec.loader.exec_module(organe)

#: Champs gratuits de `gh pr list` : aucun appel de comparaison n'est paye
#: a l'enumeration -- le deficit se mesure dans l'organe, par PR candidate.
LIST_FIELDS = (
    "number",
    "isDraft",
    "isCrossRepository",
    "updatedAt",
    "url",
)

ORDER_OLDEST = "oldest"
ORDER_NEWEST = "newest"
ORDER_NUMBER = "number"
ORDERS = (ORDER_OLDEST, ORDER_NEWEST, ORDER_NUMBER)


def list_open_prs(repo: str, limit: int, run_gh=None) -> list[dict[str, Any]]:
    """PRs ouvertes du depot, telles que `gh pr list` les rend.

    Aucun filtrage ici : la fonction rend la photo COMPLETE, le filtrage de
    cout (drafts, forks) et le tri vivent dans `pick_candidates` pour rester
    testables sans reseau.
    """
    #: Resolution a l'execution (pas un default fige) : la couture `run_gh`
    #: du module organe doit rester patchable par les tests apres import.
    if run_gh is None:
        run_gh = organe.run_gh
    raw = run_gh(
        [
            "pr",
            "list",
            "--repo",
            repo,
            "--state",
            "open",
            "--limit",
            str(limit),
            "--json",
            ",".join(LIST_FIELDS),
        ]
    )
    rows = json.loads(raw)
    if not isinstance(rows, list):
        raise organe.GhError(f"gh pr list: sortie inattendue: {raw[:200]!r}")
    return rows


def pick_candidates(
    rows: list[dict[str, Any]],
    *,
    order: str = ORDER_OLDEST,
) -> list[int]:
    """Filtre de cout + tri. Les brouillons et les forks partent : leur mise
    a jour serait refusee (DRAFT) ou impossible (FORK) par l'organe, et ces
    deux verdicts ne meritent pas un appel de lecture. TOUT le reste est
    candidate -- y compris `CLEAN`, qui ne dit rien du retard."""
    kept = [
        r
        for r in rows
        if not r.get("isDraft") and not r.get("isCrossRepository")
    ]
    if order == ORDER_OLDEST:
        kept.sort(key=lambda r: (r.get("updatedAt") or "", r.get("number") or 0))
    elif order == ORDER_NEWEST:
        kept.sort(
            key=lambda r: (r.get("updatedAt") or "", r.get("number") or 0),
            reverse=True,
        )
    elif order == ORDER_NUMBER:
        kept.sort(key=lambda r: r.get("number") or 0)
    else:  # pragma: no cover - parse_args a deja valide
        raise ValueError(f"ordre inconnu: {order}")
    return [int(r["number"]) for r in kept]


def sweep(
    *,
    repo: str,
    apply: bool,
    max_updates: int,
    limit: int,
    order: str,
    ledger_file: Path,
    in_flight_ttl: int,
    now: float | None = None,
    run_gh=None,
) -> dict[str, Any]:
    """Enumerer, trier, deleguer, agreger. Un seul appel `gh pr list`, puis
    un `process_one` par candidate -- jamais de mise a jour reimplementee."""
    if run_gh is None:
        run_gh = organe.run_gh
    rows = list_open_prs(repo, limit, run_gh=run_gh)
    candidates = pick_candidates(rows, order=order)

    moment = time.time() if now is None else now
    applied = 0
    results: list[dict[str, Any]] = []
    for pr in candidates:
        result = organe.process_one(
            pr,
            repo=repo,
            apply=apply,
            ledger_file=ledger_file,
            key=organe.ledger_key(repo, pr),
            now=moment,
            in_flight_ttl=in_flight_ttl,
            applied=applied,
            max_updates=max_updates,
        )
        if result.get("updated"):
            applied += 1
        results.append(result)

    #: LE piege #16915 : rendre la liste des dossiers perimes, sinon le sweep
    #: detruit du premachage en silence. En tete de payload, pas enterree dans
    #: les resultats : c'est la premiere chose que l'adjoint cherche.
    dossiers_invalides = [
        {
            "pr": r["pr"],
            "previous_head": r.get("previous_head"),
            "invalidated": r.get("invalidated") or [],
        }
        for r in results
        if r.get("updated")
    ]
    by_action: dict[str, int] = {}
    by_code: dict[str, int] = {}
    for r in results:
        by_action[r.get("action") or "?"] = by_action.get(r.get("action") or "?", 0) + 1
        by_code[r.get("code") or "?"] = by_code.get(r.get("code") or "?", 0) + 1

    return {
        "repo": repo,
        "mode": "apply" if apply else "dry-run",
        "order": order,
        "limit": limit,
        "max_updates": max_updates,
        "scanned": len(rows),
        "candidates": len(candidates),
        "updates_applied": applied,
        "dossiers_invalides": dossiers_invalides,
        "summary": {"by_action": by_action, "by_code": by_code},
        "results": results,
    }


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Enumerer les PRs ouvertes et deleguer le rafraichissement "
        "de base a l'organe #16149 (dry-run par defaut)."
    )
    parser.add_argument("--repo", default=organe.DEFAULT_REPO, help="depot cible")
    parser.add_argument(
        "--apply",
        action="store_true",
        help="appliquer les mises a jour (defaut : dry-run, aucune ecriture)",
    )
    parser.add_argument(
        "--max-updates",
        type=int,
        default=organe.DEFAULT_MAX_UPDATES,
        help="plafond de mises a jour par sweep, transmis a l'organe "
        f"(defaut {organe.DEFAULT_MAX_UPDATES} ; 0 = sans plafond) -- "
        "obligatoire et borne dans le workflow cron",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=50,
        help="borne d'enumeration : combien de PRs ouvertes au plus sont "
        "examinees (defaut 50)",
    )
    parser.add_argument(
        "--order",
        choices=ORDERS,
        default=ORDER_OLDEST,
        help="ordre d'examen (defaut oldest : les PRs les moins recemment "
        "mises a jour d'abord, les plus probablement en retard)",
    )
    parser.add_argument(
        "--in-flight-ttl",
        type=int,
        default=organe.DEFAULT_IN_FLIGHT_TTL,
        help="TTL du registre en vol, transmis a l'organe "
        f"(defaut {organe.DEFAULT_IN_FLIGHT_TTL} s)",
    )
    parser.add_argument(
        "--state-dir",
        default=None,
        help="repertoire du registre en vol (defaut : temporaire, partagé "
        "avec l'organe)",
    )
    args = parser.parse_args(argv)
    if args.max_updates < 0:
        parser.error(f"--max-updates ne peut pas etre negatif (recu {args.max_updates})")
    if args.limit <= 0:
        parser.error(f"--limit doit etre > 0 (recu {args.limit})")
    if args.in_flight_ttl <= 0:
        parser.error(f"--in-flight-ttl doit etre > 0 (recu {args.in_flight_ttl})")
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    state_dir = Path(args.state_dir) if args.state_dir else organe.default_state_dir()
    payload = sweep(
        repo=args.repo,
        apply=args.apply,
        max_updates=args.max_updates,
        limit=args.limit,
        order=args.order,
        ledger_file=organe.ledger_path(state_dir),
        in_flight_ttl=args.in_flight_ttl,
    )
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 1 if any(r.get("action") == organe.ACTION_REFUSE for r in payload["results"]) else 0


if __name__ == "__main__":
    sys.exit(main())
