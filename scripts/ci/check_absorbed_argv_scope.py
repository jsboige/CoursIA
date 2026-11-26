#!/usr/bin/env python3
"""Bornage des gardes absorbés : le verdict reste-t-il imputable au diff ?

Programme #12567 (absorption des gardes unitaires dans la voie rapide). Absorber
un garde retire son declencheur `pull_request` du workflow d'origine : le garde
n'est alors plus execute QUE par la voie rapide, avec l'argv du registre. Si cet
argv a perdu l'argument qui **bornait** l'analyse au diff de la PR, le garde
analyse tout l'arbre -- et un finding nouveau, né de la PR d'AUTRUI, rougit
alors une PR sans rapport.

Mesure fondatrice (#20303, 2026-10-10) : `check-nav-chain` absorbait `--check`
seul alors que son workflow d'origine passait `--diff-files pr_files.txt`.
Apres #20100 (un lien Lean-25 -> ICT-15d), ICT-15d est passe de `orphan_entry` a
`unreachable` sur le graphe GLOBAL : `--check` sur `main` rendait 1 NEW, et
toute PR notebook se mettait a rougir. Reparations : #20582 (`--diff-base`) et
#21023 (`check-navlinks`, meme classe).

`check_absorbed_path_parity.py` compare les `paths` du declencheur aux `paths`
du registre : il couvre la COUVERTURE (quels chemins font tourner le garde),
pas le BORNAGE (quels fichiers le garde analyse). C'est le trou que cet organe
ferme -- le registre le dit lui-meme : « l'information de bornage peut manquer a
l'argv absorbe » (champ `diff_bounded`).

Deux invariants :

  I1 -- PAS DE PERTE DE PORTE. Si le workflow d'origine borne l'analyse au
        diff, l'argv du registre doit la borner aussi. Trois formes comptent :
        un jeton de scope dans l'argv du garde, un garde DELTA a trois temps
        via `delta_argv`, ou un **garde a `commenters`** -- dont le bornage
        vit sur l'argv du commenter ou dans la selection de `commenter_paths()`
        (cf `commenter_scope`). Un garde a commentaires a un argv de garde
        vide : ne lire que celui-ci rendait trois absorptions faussement
        perdues (#22244).

  I2 -- PAS DE DECLARATION NON CORROBOREE. `diff_bounded=True` affirme que le
        verdict est un DELTA borne au diff ; l'argv doit porter la preuve. C'est
        l'etat que #20582 a signale sur `check-navlinks` (« porte le meme type
        de declaration `diff_bounded=True` sans portee dans l'argv »).

Fail-closed : un garde dont la source est illisible, ou dont le bornage n'est
pas prouve, est un finding. Le cout d'un faux rouge est une ligne a ajouter au
registre ; le cout d'un faux vert est un garde qui rougit des PR sans rapport,
que personne ne verra.

Usage:
    python check_absorbed_argv_scope.py [--base origin/main] [--json] [--verbose]
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

from check_absorbed_path_parity import all_guards  # noqa: E402  (organe de la meme famille)
from check_unique_check_run_names import _load_yaml, _parse_workflow  # noqa: E402
from fast_lane_registry import FAST_LANE_NATIVE, Guard  # noqa: E402

WORKFLOW_PREFIX = ".github/workflows/"

# Jetons de bornage dans un argv de la voie rapide. `--base`/`--base-ref` sont
# inclus : ils font comparer la base a la tete, ce qui annule tout finding
# deja present sur la base (attribution par delta). `--baseline` ne l'est PAS :
# un fichier de baseline connu n'est pas un bornage.
SCOPE_FLAGS = frozenset({
    "--diff-files", "--diff-base", "--diff", "--pr-diff",
    "--base", "--base-ref", "--paths",
})
SCOPE_PLACEHOLDERS = frozenset({"{changed_paths}", "{base_ref}"})

# Marqueurs de bornage dans une commande de workflow. `--diff ` et `--base `
# sont ecrits avec leur espace : le jeton exact ne matcherait pas
# `--baseline` ni `--diff-files`.
SOURCE_MARKERS = (
    "--diff-files",
    "--diff-base",
    "--pr-diff",
    "--diff ",
    "--base ",
    "--base-ref",
    "pr_files.txt",
    "git diff --name-only",
    "{changed_paths}",
)


def scope_tokens(argv: list[str]) -> list[str]:
    """Jetons de bornage portes par un argv (registre).

    Deux formes portent le bornage :

    * un jeton explicite (`--diff-base`, `--diff-files`, `--base`, ...) ;
    * un placeholder seul : `{changed_paths}` (le garde est execute par
      fichier) ou `{base_ref}` en position (le checker compare la base a la
      tete -- les cliquets « base vs PR » du depot le prennent en position).

    Apres un jeton explicite, le placeholder n'est que sa VALEUR : il n'est
    pas compte une seconde fois.
    """
    found = [token for token in argv if token in SCOPE_FLAGS]
    if not found:
        for placeholder in sorted(SCOPE_PLACEHOLDERS):
            if placeholder in argv:
                found.append(placeholder)
                break
    return found


def commenter_scope(guard: Guard) -> tuple[list[str], bool]:
    """Bornage porte par les `commenters` d'un garde.

    Un garde a commentaires a un `argv` de garde VIDE : c'est le moteur qui
    execute les detecteurs (`fast_lane.run_effects`), et le bornage vit alors
    a deux endroits, tous deux reels :

    * l'**argv du commenter** -- il peut porter lui-meme `--base`, `--diff`
      ou `{changed_paths}` comme n'importe quel argv ;
    * la **selection de chemins** -- un commenter qui declare `paths` fait
      passer son detecteur par `commenter_paths()`, qui ne lui transmet que
      les fichiers du diff (`git diff --name-only --diff-filter=MR
      <merge-base> HEAD -- <motifs>`). Le verdict est alors borne a la PR par
      construction, sans qu'aucun jeton n'apparaisse dans un argv.

    Rend (jetons trouves, bornage par selection de chemins).
    """
    tokens: list[str] = []
    selects_paths = False
    for commenter in getattr(guard, "commenters", ()) or ():
        for token in scope_tokens(list(getattr(commenter, "argv", ()) or ())):
            if token not in tokens:
                tokens.append(token)
        if getattr(commenter, "paths", None):
            selects_paths = True
    return tokens, selects_paths


def source_scope_markers(run_commands: list[str]) -> list[str]:
    """Marqueurs de bornage portes par les commandes du workflow d'origine."""
    found: list[str] = []
    for command in run_commands:
        for marker in SOURCE_MARKERS:
            if marker in command and marker not in found:
                found.append(marker)
    return found


def run_commands(data: dict) -> list[str]:
    """Commandes `run:` de tous les jobs d'un workflow parse.

    Les commentaires du YAML sont ignores par le parseur : un marqueur cite
    dans une explication ne fait pas un workflow borne.
    """
    commands: list[str] = []
    jobs = data.get("jobs") or {}
    if not isinstance(jobs, dict):
        return commands
    for job in jobs.values():
        if not isinstance(job, dict):
            continue
        for step in job.get("steps") or []:
            if not isinstance(step, dict):
                continue
            run = step.get("run")
            if isinstance(run, str):
                commands.append(run)
    return commands


def _git_show(base: str, path: str) -> str | None:
    """Contenu d'un fichier sur la branche de base (None = illisible/absent)."""
    result = subprocess.run(
        ["git", "show", f"{base}:{path}"],
        cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    return result.stdout if result.returncode == 0 else None


def _delta_guard(guard: Guard) -> bool:
    """Vrai si le garde est un DELTA a trois temps (base/head compares).

    Un tel garde annule par construction tout finding deja present sur la
    base : son verdict est imputable a la PR sans porter de jeton de scope.
    """
    return bool(guard.delta_argv)


def findings(base: str) -> tuple[list[str], list[str], dict, list[dict]]:
    """(problems, skipped, stats, evidence).

    `evidence` porte le bornage mesure pour chaque garde (marqueurs du
    workflow d'origine, jetons de l'argv, statut DELTA, declaration
    `diff_bounded`) : le verdict se relit sans refaire la mesure.
    """
    yaml = _load_yaml()
    if yaml is None:
        return (
            ["INSTRUMENT CASSE: PyYAML indisponible"],
            [],
            {"checked": 0},
            [],
        )

    problems: list[str] = []
    skipped: list[str] = []
    checked = 0
    evidence: list[dict] = []

    for guard in all_guards():
        if guard.source == FAST_LANE_NATIVE or not guard.source:
            continue
        if not guard.source.endswith(".yml"):
            continue
        if not guard.absorbed:
            # Seul un garde ABSORBE a perdu son workflow d'origine : un garde
            # non absorbe est double par son workflow, qui borne lui-meme.
            continue

        rel = WORKFLOW_PREFIX + guard.source
        text = _git_show(base, rel)
        if text is None:
            problems.append(
                f"{guard.name!r}: {rel} illisible sur {base} -- bornage non "
                "prouve (fail-closed)"
            )
            continue
        data = _parse_workflow(text, yaml)
        if data is None:
            problems.append(
                f"{guard.name!r}: {rel} non parsable sur {base} -- bornage non "
                "prouve (fail-closed)"
            )
            continue

        checked += 1
        markers = source_scope_markers(run_commands(data))
        tokens = scope_tokens(guard.argv)
        commenter_tokens, commenter_selects = commenter_scope(guard)
        scoped = (
            bool(tokens)
            or bool(commenter_tokens)
            or commenter_selects
            or _delta_guard(guard)
        )
        evidence.append({
            "name": guard.name,
            "source": rel,
            "source_markers": markers,
            "argv_scope_tokens": tokens,
            "commenter_scope_tokens": commenter_tokens,
            "commenter_selects_paths": commenter_selects,
            "delta_guard": _delta_guard(guard),
            "diff_bounded": bool(guard.diff_bounded),
        })

        # I1 -- pas de perte de portee.
        if markers and not scoped:
            problems.append(
                f"{guard.name!r}: le workflow d'origine borne l'analyse au "
                f"diff ({', '.join(markers)}) mais ni l'argv du registre "
                f"({' '.join(guard.argv) or 'vide'}) ni ses commenters n'en "
                "portent le jeton, et aucun commenter ne selectionne les "
                "chemins du diff -- la portee a ete perdue a l'absorption"
            )

        # I2 -- pas de declaration non corroboree.
        if guard.diff_bounded and not scoped:
            problems.append(
                f"{guard.name!r}: `diff_bounded=True` affirme un verdict DELTA "
                "borne au diff, mais l'argv ne porte aucun jeton de bornage "
                f"({' '.join(guard.argv)}) -- la declaration n'est pas "
                "corroboree"
            )

    stats = {"checked": checked, "skipped": len(skipped)}
    return problems, skipped, stats, evidence


def _main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="origin/main",
                        help="branche de reference (defaut: origin/main)")
    parser.add_argument("--json", action="store_true", help="verdict machine")
    parser.add_argument("--verbose", action="store_true",
                        help="detailer le bornage mesure pour chaque garde")
    args = parser.parse_args(argv)

    problems, skipped, stats, evidence = findings(args.base)

    if args.json:
        print(json.dumps({
            "base": args.base,
            "problems": problems,
            "checked": stats["checked"],
            "skipped": skipped if args.verbose else stats["skipped"],
            "evidence": evidence if args.verbose else [],
            "verdict": "SCOPE_LOST" if problems else "SCOPE_OK",
        }, ensure_ascii=False, indent=2))
    else:
        if args.verbose:
            for row in evidence:
                commenters = ",".join(row["commenter_scope_tokens"]) or "-"
                if row["commenter_selects_paths"]:
                    commenters += "+chemins-du-diff"
                print(f"[absorbed-argv-scope] {row['name']}: source="
                      f"{','.join(row['source_markers']) or '-'} argv="
                      f"{','.join(row['argv_scope_tokens']) or '-'} "
                      f"commenters={commenters} "
                      f"delta={row['delta_guard']} "
                      f"diff_bounded={row['diff_bounded']}")
        if problems:
            print(f"[absorbed-argv-scope] BORNAGE PERDU -- {len(problems)} "
                  "garde(s) a reexaminer :")
            for problem in problems:
                print(f"  - {problem}")
            print("  Geste : rendre a l'argv la portee du workflow d'origine "
                  "(jeton `--diff-base {base_ref}`, `--diff-files`, "
                  "`{changed_paths}`), ou corriger la declaration "
                  "`diff_bounded`.")
        else:
            print(f"[absorbed-argv-scope] OK -- {stats['checked']} garde(s) "
                  f"absorbe(s) verifie(s) contre {args.base} : aucune portee "
                  "perdue, aucune declaration non corroboree.")

    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))
