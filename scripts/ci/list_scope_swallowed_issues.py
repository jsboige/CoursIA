#!/usr/bin/env python3
r"""list_scope_swallowed_issues.py -- issues ouvertes portant un commit de correction merge (#23348).

## Pourquoi cet organe existe

Le depot impose `type(scope): description` (`.claude/rules/git-workflow.md`).
Or GitHub ne ferme une issue que si le mot-cle de fermeture precede
**immediatement** la reference. Dans `Fix(ci,#22937): vague 2`, le mot-cle est
suivi de `(ci,` : la parenthese de scope est du texte intercale, et la
fermeture ne se declenche jamais. La forme que le depot **prescrit** absorbe
donc le mot-cle qui ferme.

La consequence n'est pas cosmetique. Mesure du 2026-10-29 sur `origin/main`,
fenetre de 500 commits :

    sujets de la forme type(scope,#N)          299 numeros distincts
      dont encore OUVERTS                      186
    sous-ensemble a verbe de correction        162 numeros distincts
      dont encore OUVERTS                       95

Ces issues ne sont pas du travail en attente : ce sont des issues dont le
correctif est deja sur `main`. Elles saturent l'assiette du tapis
(`pick_idle_grain.py --belt`), qui sert aux lanes du travail deja fait. Quatre
instances verifiees a la main (#20886, #20871, #21488, #21074) : quatre sur
quatre livrees, quatre sur quatre ouvertes.

Une regle non appliquee demande un organe, pas plus de vigilance : cette
liste se calculait a la main, elle se calcule maintenant ici.

## Ce que fait cet organe, et ce qu'il ne fait pas

Il **liste**. Il ne ferme aucune issue, ne commente rien, ne pousse rien : la
cloture revient au coordinateur (G.9, une issue ne se ferme pas sur un label).
Le script est en lecture seule de bout en bout.

    $ python scripts/ci/list_scope_swallowed_issues.py
    ref=origin/main  commits_scanned=500
    sujets type(scope,#N)            299 numeros distincts
      encore ouverts                 186
    sous-ensemble corrections        162 numeros distincts
      encore ouverts                  95

    #11044   0f3a91b2c1  Fix(ci,#11044): ...
    #11508   7b21c0d49e  Fix(lean,#11508): ...

    ---
    total=95

    $ python scripts/ci/list_scope_swallowed_issues.py --json
    {"ref": "origin/main", ..., "issues": [{"number": 11044, ...}]}

`--all-forms` elargit aux verbes non correctifs (`Add`, `Feat`, ...) : une
issue citee par un `Add(...)` peut legitimement rester ouverte, ce n'est pas
une promesse de fermeture. C'est pourquoi la ligne discriminante est le
sous-ensemble a verbe de correction, jamais le total.

## Ce que l'organe ne peut pas savoir

Un commit de correction **suivi** d'un `Closes #N` sur une ligne propre a bien
ferme son issue : ce couple est exclu (le mot-cle explicite est cherche dans le
corps). Mais un corps qui ferme l'issue par une autre voie -- une PR liee par
`Closes` dans sa description, une fermeture manuelle posterieure -- n'est pas
visible ici. La sortie est donc un **candidat au tri**, pas un verdict : chaque
ligne demande une lecture avant cloture.

## Options

  --ref REF           ref lue par `git log` (defaut : origin/main)
  --commits N         fenetre de commits (defaut : 500)
  --repo OWNER/NAME   depot interroge par `gh` (defaut : jsboige/CoursIA)
  --limit N           plafond de `gh issue list` (defaut : 900)
  --all-forms         inclure les verbes non correctifs
  --json              sortie machine
  --fail-on-findings  sortir en 1 si la liste est non vide (pour un futur gate ;
                      desactive par defaut -- lister n'est pas rougir)
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass

# `Fix(ci,#22937)` : verbe, scope (peut contenir des chiffres, des tirets, des
# points), puis la reference. Le `#` doit suivre la derniere virgule du scope.
SCOPE_SWALLOW_RE = re.compile(
    r"^(?P<verb>[A-Za-z][A-Za-z0-9_-]*)\((?P<scope>[^)]*),#(?P<number>\d+)\)"
)

# Verbes qui annoncent une correction. Un `Add(...)` ou un `Feat(...)` cite une
# issue sans promettre de la fermer : il n'entre pas dans le sous-ensemble
# discriminant.
CORRECTION_VERBS = frozenset(
    {"fix", "fixes", "fixed", "repair", "repairs", "repaired", "re-exec", "reexec", "hotfix"}
)

# Mot-cle de fermeture explicite, precede d'autre chose qu'une lettre (pour ne
# pas matcher `prefix`) et suivi d'un `#` -- jamais d'une parenthese, qui est
# precisement la forme cassee.
_CLOSING_KEYWORD = r"(?<![A-Za-z0-9_-])(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)"

FIELD_SEP = "\x1f"
RECORD_SEP = "\x1e"


@dataclass(frozen=True)
class SwallowedRef:
    """Un commit dont le sujet cite une issue sans pouvoir la fermer."""

    number: int
    commit: str
    verb: str
    subject: str

    @property
    def is_correction(self) -> bool:
        return self.verb.lower() in CORRECTION_VERBS


def parse_subject(subject: str) -> tuple[str, int] | None:
    """Rend ``(verbe, numero)`` si le sujet porte la forme avaleuse, sinon ``None``.

    Le numero est celui qui suit la **derniere** virgule du scope, jamais un
    chiffre du scope lui-meme : `Fix(ANALYSE-04,#21027)` doit rendre 21027.
    """
    match = SCOPE_SWALLOW_RE.match(subject.strip())
    if match is None:
        return None
    return match.group("verb"), int(match.group("number"))


def has_explicit_closing(body: str, number: int) -> bool:
    """Vrai si le corps porte un mot-cle de fermeture qui vise *cette* issue.

    `Closes #12` ferme ; `See #12` ne ferme pas ; `Fix(ci,#12)` ne ferme pas non
    plus -- le mot-cle y est suivi d'une parenthese, pas d'une reference.
    """
    pattern = re.compile(_CLOSING_KEYWORD + r"\s*:?\s*#" + str(number) + r"(?!\d)", re.IGNORECASE)
    return pattern.search(body) is not None


def collect_swallowed(
    commits: list[tuple[str, str, str]],
    open_numbers: set[int],
    *,
    correction_only: bool = True,
) -> list[SwallowedRef]:
    """Croise les commits avec les issues ouvertes et rend les couples candidats.

    ``commits`` est une liste de ``(sha, sujet, corps)``. Un couple est retenu
    quand le sujet porte la forme avaleuse, que l'issue est encore ouverte, que
    le corps ne porte pas de mot-cle de fermeture explicite visant ce numero,
    et -- si ``correction_only`` -- que le verbe annonce une correction.

    Le commit le plus **recent** est conserve par issue : `git log` rend du plus
    recent au plus ancien, donc la premiere occurrence gagne.
    """
    seen: set[int] = set()
    out: list[SwallowedRef] = []
    for sha, subject, body in commits:
        parsed = parse_subject(subject)
        if parsed is None:
            continue
        verb, number = parsed
        if number in seen or number not in open_numbers:
            continue
        if has_explicit_closing(body, number):
            continue
        ref = SwallowedRef(number=number, commit=sha[:10], verb=verb, subject=subject.strip())
        if correction_only and not ref.is_correction:
            continue
        seen.add(number)
        out.append(ref)
    return out


def count_all_forms(commits: list[tuple[str, str, str]]) -> tuple[int, int]:
    """Rend ``(numeros distincts toutes formes, numeros distincts corrections)``."""
    every: set[int] = set()
    corrections: set[int] = set()
    for _sha, subject, _body in commits:
        parsed = parse_subject(subject)
        if parsed is None:
            continue
        verb, number = parsed
        every.add(number)
        if verb.lower() in CORRECTION_VERBS:
            corrections.add(number)
    return len(every), len(corrections)


def _run(cmd: list[str]) -> str:
    result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    if result.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} -> rc={result.returncode} : {result.stderr.strip()[:400]}")
    return result.stdout


def read_commits(ref: str, limit: int) -> list[tuple[str, str, str]]:
    """Lit ``(sha, sujet, corps)`` dans la fenetre de commits demandee."""
    raw = _run(["git", "log", f"--max-count={limit}", f"--format=%H{FIELD_SEP}%s{FIELD_SEP}%b{RECORD_SEP}", ref])
    commits: list[tuple[str, str, str]] = []
    for record in raw.split(RECORD_SEP):
        record = record.strip("\n")
        if not record:
            continue
        parts = record.split(FIELD_SEP)
        if len(parts) < 2:
            continue
        sha, subject = parts[0], parts[1]
        body = parts[2] if len(parts) > 2 else ""
        commits.append((sha, subject, body))
    return commits


def read_open_issues(repo: str, limit: int) -> set[int]:
    """Numeros des issues ouvertes du depot."""
    out = _run(["gh", "issue", "list", "--repo", repo, "--state", "open", "--limit", str(limit), "--json", "number"])
    return {int(item["number"]) for item in json.loads(out)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Liste les issues ouvertes dont le correctif est deja merge (#23348).")
    parser.add_argument("--ref", default="origin/main", help="ref lue par git log (defaut : origin/main)")
    parser.add_argument("--commits", type=int, default=500, help="fenetre de commits (defaut : 500)")
    parser.add_argument("--repo", default="jsboige/CoursIA", help="depot interroge par gh")
    parser.add_argument("--limit", type=int, default=900, help="plafond de gh issue list (defaut : 900)")
    parser.add_argument("--all-forms", action="store_true", help="inclure les verbes non correctifs")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument(
        "--fail-on-findings",
        action="store_true",
        help="sortir en 1 si la liste est non vide (pour un futur gate ; desactive par defaut)",
    )
    args = parser.parse_args(argv)

    try:
        commits = read_commits(args.ref, args.commits)
        open_numbers = read_open_issues(args.repo, args.limit)
    except RuntimeError as exc:
        print(f"[ERREUR] {exc}", file=sys.stderr)
        return 2

    every, corrections = count_all_forms(commits)
    issues = collect_swallowed(commits, open_numbers, correction_only=not args.all_forms)
    open_all = len(open_numbers)

    if args.json:
        payload = {
            "ref": args.ref,
            "commits_scanned": len(commits),
            "open_issues_scanned": open_all,
            "distinct_issues_all_forms": every,
            "distinct_issues_correction": corrections,
            "correction_only": not args.all_forms,
            "total": len(issues),
            "issues": [
                {"number": i.number, "commit": i.commit, "verb": i.verb, "subject": i.subject} for i in issues
            ],
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(f"ref={args.ref}  commits_scanned={len(commits)}")
        print(f"sujets type(scope,#N)      {every} numeros distincts")
        print(f"sous-ensemble corrections  {corrections} numeros distincts")
        print(f"issues ouvertes interrogees {open_all}")
        print()
        for item in issues:
            print(f"#{item.number:<7} {item.commit}  {item.subject[:110]}")
        print()
        print("---")
        print(f"total={len(issues)}  (fenetre={args.commits} commits, ref={args.ref})")
        print("lecture seule : aucune issue n'est fermee, aucun commentaire n'est poste.")

    if args.fail_on_findings and issues:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
