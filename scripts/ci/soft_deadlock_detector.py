#!/usr/bin/env python3
"""Détection de deadlock soft sur les PRs ouvertes (#15511, préconisation P2).

Un deadlock soft est une PR **mergeable** (aucun conflit), **ouverte depuis
plus de 72 h**, sur laquelle **le flux de commentaires humains continue**
sans que rien ne converge : le coordinateur attend que « le rouge soit
résolu » pour merger, la lane attend que « le merge soit autorisé » pour
fixer. Cas fondateur : PR #14821 — 31 commentaires / 68 101 caractères sur
5 jours, état livrable inchangé depuis le premier jour, clôturée in fine
sans merge le 2026-09-12.

Cet organe est une **mesure de plateau, jamais un gate** : il émet un
signal ``[DEADLOCK]`` par PR détectée et rend la main. Le triage reste
humain — une détection n'est pas un verdict de faute, c'est une
invitation à trancher (merge, close avec motif, ou provision d'un geste).
Le câblage cron (1x/jour) relève du coordinateur : armement par l'agent
principal, jamais par la lane qui écrit l'organe.

Critères (conjonction, spec #15511 P2) :

1. ``state: OPEN`` (source : ``gh pr list --state open``) ;
2. ``mergeable: MERGEABLE`` — une PR en conflit n'est pas un deadlock
   soft, c'est une candidate réparable par sa lane (picker, file P0) ;
3. âge > ``--min-age-hours`` (défaut 72 h) ;
4. commentaires **humains** > ``--min-comments`` (défaut 5) sur la
   fenêtre ``--window-hours`` (défaut 24 h). Les bots mécaniques
   (github-actions, dependabot...) ne comptent pas : la pompe à
   commentaires mesurée sur #14821 vient des comptes agents, pas des
   organes CI ;
5. **aucun commit dans la fenêtre** — la signature fondatrice est
   « ~6 commentaires par jour pour 0 commit de code ». Une PR dont le
   code bouge (fix poussé, rebase) itère, elle ne deadlock pas : mesuré
   en première passe live (#18158 — réserve levée puis commit poussé
   dans la fenêtre, boucle de review active, fausse positive du critère
   1-4 seul). La date du dernier commit n'est pas dans le JSON de
   ``pr list`` : elle se prend en seconde phase, ``gh pr view`` borné
   aux seules candidates (quelques appels, pas un par PR).

Sémantique de sortie :

* rc=0 — mesure effectuée, avec ou sans détections (convention
  ``prune_merged_worktrees`` : une détection est une **décision rendue**,
  pas une panne) ;
* rc=1 — panne opérationnelle (``gh`` injoignable, forme inattendue) ;
* rc=2 — uniquement avec ``--fail-on-findings`` : des détections
  existent et l'appelant (cron, wrapper) veut un code distingué.

Les appels ``gh`` passent par un ``runner`` injectable (pattern
``guard_comment_upsert``) pour que les tests rejouent des corpus réels
sans réseau.
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from typing import Callable, Optional

# Bots mécaniques du dépôt : leurs commentaires sont le compte-rendu
# d'organes, pas du churn de décision. Appartenance EXACTE, pas un
# préfixe -- sur un dépôt public un tiers peut porter ``github-actions-xyz``
# (review ai-01 #15374, même garde que ``guard_comment_upsert``).
BOT_LOGINS = frozenset({
    "github-actions",
    "github-actions[bot]",
    "dependabot[bot]",
    "renovate[bot]",
    "codecov[bot]",
    "coveralls[bot]",
})

DEFAULT_MIN_AGE_HOURS = 72
DEFAULT_WINDOW_HOURS = 24
DEFAULT_MIN_COMMENTS = 5
DEFAULT_LIMIT = 300
DEFAULT_TIMEOUT = 30

DEFAULT_REPO = "jsboige/CoursIA"


def _default_runner(cmd, **kwargs):  # pragma: no cover - trivial default
    import subprocess
    return subprocess.run(cmd, **kwargs)


def _parse_ts(value: str) -> datetime:
    """ISO-8601 GitHub (« 2026-09-05T20:21:00Z ») -> datetime UTC aware.

    ``fromisoformat`` n'accepte le suffixe ``Z`` qu'à partir de 3.11 ;
    le dépôt cible 3.10+, donc remplacement explicite.
    """
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def fetch_open_prs(
    repo: str,
    runner: Optional[Callable] = None,
    timeout: int = DEFAULT_TIMEOUT,
    limit: int = DEFAULT_LIMIT,
) -> list:
    """PRs ouvertes avec commentaires, via ``gh pr list``.

    Le JSON de ``pr list`` porte ``comments`` (auteur, createdAt, body) :
    une seule requête suffit pour la conjonction âge + churn. Une PR
    au-delà de ``--limit`` (tri par défaut : récence) est invisible — le
    plafond default couvre le plateau observé ; l'option existe pour
    l'élargir.
    """
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    proc = runner(
        ["gh", "pr", "list", "--repo", repo, "--state", "open",
         "--limit", str(limit), "--json",
         "number,title,createdAt,mergeable,comments"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(f"gh pr list failed: {proc.stderr.strip()}")
    data = json.loads(proc.stdout)
    if not isinstance(data, list):
        raise RuntimeError(
            f"gh pr list: forme inattendue ({type(data).__name__})")
    return data


def is_bot_comment(comment: dict) -> bool:
    """Vrai si le commentaire vient d'un bot mécanique (voir BOT_LOGINS)."""
    login = ((comment.get("author") or {}).get("login") or "")
    return login in BOT_LOGINS


def fetch_last_commit_dates(
    numbers: list,
    repo: str,
    runner: Optional[Callable] = None,
    timeout: int = DEFAULT_TIMEOUT,
) -> dict:
    """Date du dernier commit par PR candidate (seconde phase bornée).

    ``gh pr list --json`` ne porte pas ``commits`` : pour les seules PRs
    qui ont passé la conjonction âge + mergeable + churn, un ``gh pr view``
    par candidate récupère ``commits[-1].committedDate``. Une PR dont la
    requête échoue est **conservée** (fail-open vers le signal — le triage
    humain départage) et marquée ``last_commit_unknown``.
    """
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    out: dict = {}
    for number in numbers:
        proc = runner(
            ["gh", "pr", "view", str(number), "--repo", repo,
             "--json", "commits"],
            capture_output=True, text=True, timeout=timeout,
        )
        if getattr(proc, "returncode", 1) != 0:
            out[number] = None
            continue
        try:
            commits = json.loads(proc.stdout).get("commits") or []
            out[number] = (
                commits[-1].get("committedDate") if commits else None)
        except (json.JSONDecodeError, IndexError, AttributeError):
            out[number] = None
    return out


def analyze(
    prs: list,
    now: datetime,
    min_age_hours: int = DEFAULT_MIN_AGE_HOURS,
    window_hours: int = DEFAULT_WINDOW_HOURS,
    min_comments: int = DEFAULT_MIN_COMMENTS,
    last_commit_dates: Optional[dict] = None,
) -> dict:
    """Classe les PRs ouvertes : ``findings`` (deadlock soft) + compteurs.

    ``mergeable: UNKNOWN`` (GitHub n'a pas encore calculé) n'est ni un
    finding ni un refus : compté à part, laissé au tir suivant.

    ``last_commit_dates`` (seconde phase, optionnelle — cf
    ``fetch_last_commit_dates``) exclut les candidates dont un commit
    tombe DANS la fenêtre : le code bouge, la PR itère. Une candidate
    sans date (requête échouée, PR sans commit) reste signalée avec
    ``last_commit_unknown: true``.
    """
    findings = []
    skipped_unknown = 0
    skipped_active = 0
    window_start = now.timestamp() - window_hours * 3600
    for pr in prs:
        number = pr.get("number")
        mergeable = pr.get("mergeable")
        if mergeable == "UNKNOWN":
            skipped_unknown += 1
            continue
        if mergeable != "MERGEABLE":
            continue
        created = _parse_ts(pr["createdAt"])
        age_h = (now.timestamp() - created.timestamp()) / 3600.0
        if age_h <= min_age_hours:
            continue
        recent = [
            c for c in (pr.get("comments") or [])
            if not is_bot_comment(c)
            and _parse_ts(c["createdAt"]).timestamp() >= window_start
        ]
        if len(recent) <= min_comments:
            continue
        if last_commit_dates is not None:
            last_commit = last_commit_dates.get(number, None)
            if last_commit is None:
                unknown = True
            else:
                unknown = False
                if _parse_ts(last_commit).timestamp() >= window_start:
                    skipped_active += 1
                    continue
            findings.append({
                "number": number,
                "title": pr.get("title") or "",
                "age_hours": round(age_h, 1),
                "window_hours": window_hours,
                "human_comments_window": len(recent),
                "chars_window": sum(len(c.get("body") or "") for c in recent),
                "total_comments": len(pr.get("comments") or []),
                "last_commit_unknown": unknown,
            })
        else:
            findings.append({
                "number": number,
                "title": pr.get("title") or "",
                "age_hours": round(age_h, 1),
                "window_hours": window_hours,
                "human_comments_window": len(recent),
                "chars_window": sum(len(c.get("body") or "") for c in recent),
                "total_comments": len(pr.get("comments") or []),
            })
    findings.sort(key=lambda f: (-f["human_comments_window"], f["number"]))
    return {
        "scanned": len(prs),
        "skipped_mergeable_unknown": skipped_unknown,
        "skipped_active_in_window": skipped_active,
        "findings": findings,
    }


def format_finding(f: dict) -> str:
    """Ligne de signal, une par PR détectée."""
    return (
        f"[DEADLOCK] #{f['number']} — âge {f['age_hours']:.0f}h, mergeable, "
        f"{f['human_comments_window']} commentaires humains "
        f"({f['chars_window']} chars) sur {f['window_hours']}h "
        f"— {f['title']}"
    )


def main(argv: Optional[list] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Détection de deadlock soft (#15511 P2) — mesure, pas gate.")
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--min-age-hours", type=int,
                        default=DEFAULT_MIN_AGE_HOURS)
    parser.add_argument("--window-hours", type=int,
                        default=DEFAULT_WINDOW_HOURS)
    parser.add_argument("--min-comments", type=int,
                        default=DEFAULT_MIN_COMMENTS)
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--json", action="store_true",
                        help="sortie structurée (findings + compteurs)")
    parser.add_argument("--fail-on-findings", action="store_true",
                        help="rc=2 si au moins une détection (pour cron)")
    args = parser.parse_args(argv)

    now = datetime.now(timezone.utc)
    try:
        prs = fetch_open_prs(args.repo, limit=args.limit)
        candidates = analyze(
            prs, now,
            min_age_hours=args.min_age_hours,
            window_hours=args.window_hours,
            min_comments=args.min_comments,
        )
        last_commit_dates = None
        if candidates["findings"]:
            # Seconde phase bornée aux candidates : date du dernier commit
            # pour écarter les PRs dont le code bouge encore.
            last_commit_dates = fetch_last_commit_dates(
                [f["number"] for f in candidates["findings"]], args.repo)
        report = analyze(
            prs, now,
            min_age_hours=args.min_age_hours,
            window_hours=args.window_hours,
            min_comments=args.min_comments,
            last_commit_dates=last_commit_dates,
        )
    except (RuntimeError, json.JSONDecodeError, KeyError, ValueError) as exc:
        print(f"[PANNE] soft_deadlock_detector: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        for f in report["findings"]:
            print(format_finding(f))
        print(
            f"— {report['scanned']} PRs ouvertes scannées, "
            f"{len(report['findings'])} deadlock(s) soft, "
            f"{report['skipped_active_in_window']} écartée(s) (commit dans la fenêtre : itération active), "
            f"{report['skipped_mergeable_unknown']} mergeable UNKNOWN (reporté au tir suivant)"
        )
    if args.fail_on_findings and report["findings"]:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
