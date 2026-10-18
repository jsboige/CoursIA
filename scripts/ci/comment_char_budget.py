#!/usr/bin/env python3
"""Compteur « commentaires-pompage » sur les grandes PRs ouvertes (#15511, P5).

Cas fondateur : PR #14821 — 31 commentaires totalisant 68 101 caractères sur
5 jours pour un livrable inchangé. P2 (``soft_deadlock_detector``) détecte la
boucle par la conjonction âge + mergeable + churn + immobilité du code ; P5
mesure l'autre face du même symptôme : le **volume** de prose accumulé sur
les PRs massives — un budget qui se consomme en diagnostics au lieu d'actions.

Cet organe est une **mesure passive, jamais un gate** : il rend un compteur
agrégé et un signal ``[ALERT] commentaires-pompage`` au-delà du seuil, et
rend la main. Le signal se poste sur le dashboard workspace par la lane qui
lit la mesure ; le triage reste humain (une alerte n'est pas un verdict de
faute, c'est une invitation à trancher). Pas de câblage automatique : même
règle que P2, l'armement éventuel relève du coordinateur.

Critères (spec #15511 P5) :

1. ``state: OPEN`` (source : ``gh pr list --state open``) ;
2. taille du diff ``additions + deletions > --min-diff-lines`` (défaut
   1000) — la spec parle de « PR ouvertes > 1 000 lignes » ; l'interprétation
   retenue est la taille totale du diff, pas les seules additions ;
3. chars cumulés de **tous** les commentaires (humains et bots — fidélité à
   la mesure fondatrice 68 101 = 31 commentaires toutes origines), avec
   ventilation ``human`` / ``bot`` rendue séparément pour le triage ;
4. ``[ALERT] commentaires-pompage`` quand l'agrégat dépasse
   ``--alert-threshold`` (défaut 30 000) — une PR au-delà de ``--limit``
   est invisible, le plafond default couvre le plateau observé.

Sémantique de sortie (même convention que ``soft_deadlock_detector``) :

* rc=0 — mesure effectuée, alerte ou non ;
* rc=1 — panne opérationnelle (``gh`` injoignable, forme inattendue) ;
* rc=2 — uniquement avec ``--fail-on-findings`` : l'alerte est levée et
  l'appelant veut un code distingué.

Les appels ``gh`` passent par un ``runner`` injectable pour que les tests
rejouent des corpus réels sans réseau.
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Callable, Optional

# Bots mécaniques du dépôt — mêmes logins exacts que soft_deadlock_detector
# (leurs corps comptent dans le volume, mais la ventilation les sépare :
# un gros verdict de bot n'est pas de la pompe d'agent).
BOT_LOGINS = frozenset({
    "github-actions",
    "github-actions[bot]",
    "dependabot[bot]",
    "renovate[bot]",
    "codecov[bot]",
    "coveralls[bot]",
})

DEFAULT_MIN_DIFF_LINES = 1000
DEFAULT_ALERT_THRESHOLD = 30000
DEFAULT_LIMIT = 300
DEFAULT_TIMEOUT = 30

DEFAULT_REPO = "jsboige/CoursIA"


def _default_runner(cmd, **kwargs):  # pragma: no cover - trivial default
    import subprocess
    return subprocess.run(cmd, **kwargs)


def fetch_open_prs(
    repo: str,
    runner: Optional[Callable] = None,
    timeout: int = DEFAULT_TIMEOUT,
    limit: int = DEFAULT_LIMIT,
) -> list:
    """PRs ouvertes avec commentaires et taille de diff, en une requête.

    Le JSON de ``gh pr list`` porte ``additions``, ``deletions`` et
    ``comments`` (auteur, createdAt, body) : une seule requête suffit à
    toute la mesure.
    """
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    proc = runner(
        ["gh", "pr", "list", "--repo", repo, "--state", "open",
         "--limit", str(limit), "--json",
         "number,title,createdAt,additions,deletions,comments"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(f"gh pr list failed: {proc.stderr.strip()}")
    data = json.loads(proc.stdout)
    if not isinstance(data, list):
        raise RuntimeError(
            f"gh pr list: forme inattendue ({type(data).__name__})")
    return data


def _comment_chars(comment: dict) -> int:
    return len(comment.get("body") or "")


def _is_bot(comment: dict) -> bool:
    login = ((comment.get("author") or {}).get("login") or "")
    return login in BOT_LOGINS


def analyze(
    prs: list,
    min_diff_lines: int = DEFAULT_MIN_DIFF_LINES,
    alert_threshold: int = DEFAULT_ALERT_THRESHOLD,
) -> dict:
    """Agrège les chars de commentaires des PRs de plus de ``min_diff_lines``.

    Rend un dictionnaire : ``aggregate_chars`` (toutes origines),
    ``human_chars`` / ``bot_chars`` (ventilation), ``alert`` (booléen),
    ``prs`` (per-PR, triées par chars décroissants) et ``skipped_small``
    (PRs sous le seuil de taille, hors mesure — une petite PR qui discute
    n'est pas le symptôme fondateur).
    """
    per_pr = []
    aggregate = 0
    human_total = 0
    bot_total = 0
    skipped_small = 0
    for pr in prs:
        additions = pr.get("additions") or 0
        deletions = pr.get("deletions") or 0
        if additions + deletions <= min_diff_lines:
            skipped_small += 1
            continue
        comments = pr.get("comments") or []
        human = sum(_comment_chars(c) for c in comments if not _is_bot(c))
        bot = sum(_comment_chars(c) for c in comments if _is_bot(c))
        total = human + bot
        aggregate += total
        human_total += human
        bot_total += bot
        per_pr.append({
            "number": pr.get("number"),
            "title": pr.get("title"),
            "diff_lines": additions + deletions,
            "comments": len(comments),
            "chars": total,
            "chars_human": human,
            "chars_bot": bot,
        })
    per_pr.sort(key=lambda e: e["chars"], reverse=True)
    return {
        "measured_prs": len(per_pr),
        "skipped_small": skipped_small,
        "aggregate_chars": aggregate,
        "human_chars": human_total,
        "bot_chars": bot_total,
        "alert": aggregate > alert_threshold,
        "alert_threshold": alert_threshold,
        "prs": per_pr,
    }


def main(argv: Optional[list] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Compteur commentaires-pompage sur grandes PRs "
                    "ouvertes (#15511 P5) — mesure passive, jamais un gate.")
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--min-diff-lines", type=int,
                        default=DEFAULT_MIN_DIFF_LINES)
    parser.add_argument("--alert-threshold", type=int,
                        default=DEFAULT_ALERT_THRESHOLD)
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--json", action="store_true", dest="as_json",
                        help="sortie machine-lisible (défaut : ligne humaine)")
    parser.add_argument("--fail-on-findings", action="store_true",
                        help="rc=2 si l'alerte est levée")
    args = parser.parse_args(argv)

    try:
        prs = fetch_open_prs(args.repo, limit=args.limit)
        result = analyze(prs, args.min_diff_lines, args.alert_threshold)
    except (RuntimeError, json.JSONDecodeError, OSError) as exc:
        print(f"ERREUR mesure plateau: {exc}", file=sys.stderr)
        return 1

    if args.as_json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        status = "[ALERT] commentaires-pompage" if result["alert"] else "OK"
        print(f"{status} -- {result['aggregate_chars']} chars cumules sur "
              f"{result['measured_prs']} PRs > {args.min_diff_lines} lignes "
              f"(seuil {args.alert_threshold} ; "
              f"{result['skipped_small']} petites PRs hors mesure)")
        for entry in result["prs"]:
            if entry["chars"] == 0:
                continue
            print(f"  #{entry['number']} {entry['chars']:>7} chars "
                  f"({entry['comments']} commentaires, "
                  f"diff {entry['diff_lines']} lignes) "
                  f"{(entry['title'] or '')[:60]}")
    return 2 if (args.fail_on_findings and result["alert"]) else 0


if __name__ == "__main__":
    sys.exit(main())
