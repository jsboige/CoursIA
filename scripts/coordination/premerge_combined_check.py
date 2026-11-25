#!/usr/bin/env python3
r"""Organe premerge_combined_check -- jouer les tests d'integrite du depot sur
l'ARBRE FUSIONNE (``main`` du moment + tete de la PR) avant le merge.

Pourquoi (mesure du 2026-11-05, 462 jobs ``Scripts Tests (CPU)`` sur 30 h) :
``main`` a ete rouge environ 18 heures sur 30, en cinq episodes de 4 a 9 h.
Chaque episode a ete ouvert par une PR dont la CI etait VERTE a sa propre
tete -- #24632 (vert 10:56, mergee 12:47), #24338 (vert 05:32, mergee 20:40),
#24447 (vert 12:44, mergee 22:41), #24557 (vert 18:25, mergee 00:23), #24507
(vert 12:06, mergee 03:20). Aucune n'etait fautive seule : chacune etait
verte contre le ``main`` de SON dernier run, et c'est la combinaison avec ce
qui avait ete merge entretemps qui rougissait. C'est un conflit SEMANTIQUE,
invisible a ``mergeable_state`` (aucune ligne ne se chevauche) et a la CI de
la PR (qui teste ``pull/N/merge`` tel qu'il etait au dernier push).

Les tests qui ont rougi ``main`` sont ceux qui lisent le depot ENTIER
(registres, inventaires, index) : deux PRs ajoutent chacune une entree
legitime, et les deux entrees ensemble se contredisent. Sur les 158 jobs
rouges de la fenetre, 155 tombaient a l'etape ``Run tests``, et les fichiers
de tests les plus frequents sont ceux de ``INTEGRITY_TESTS`` ci-dessous.
Joues sur l'arbre courant, ils passent en 46 s (243 tests, ``-n 4``).

Geste (lecture seule vis-a-vis des branches : aucune ref n'est creee ni
deplacee, rien n'est pousse) :

1. ``git fetch origin main pull/<N>/head`` -- la base doit etre COURANTE a
   chaque candidat : l'organe existe pour attraper le conflit entre deux
   PRs fusionnees contre le meme ``main@T`` (#24828). Le ``main`` n'ajoute
   que ~0,4 s au fetch (mesure du 22/11) : le cout du fetch est
   l'aller-retour reseau, pas la ref ;
2. ``git merge-tree --write-tree origin/main <tete>`` -- l'arbre que le
   merge produirait ; un conflit textuel rend ``CONFLICT`` ;
3. ``git commit-tree`` -- un commit non reference qui porte cet arbre ;
4. ``git worktree add --detach`` dans ``.tmp/`` (gitignore) -- ou, quand le
   dossier est déjà posé (``--reuse-worktree``), un ``checkout --detach``
   dans ce dossier : une passe ne paie qu'un worktree, pas un par candidat ;
5. ``pytest`` sur les fichiers de ``INTEGRITY_TESTS`` presents dans l'arbre,
   borne par ``--timeout-s`` ;
6. ``git worktree remove`` (jamais ``--force`` : un worktree que git refuse
   de retirer est rapporte par son chemin, pas detruit) -- **seulement** si
   l'organe a pose ce worktree ; un worktree repris appartient à la passe.

Verdicts et codes de sortie :

- ``GREEN`` (0) : les tests passent sur l'arbre fusionne ;
- ``RED`` (1) : au moins un test rougit -- le merge rougirait ``main`` ;
- ``CONFLICT`` (1) : la fusion a un conflit textuel ;
- ``UNREADABLE`` (2) : une etape n'a pas pu etre jouee (fetch, worktree,
  timeout, pytest hors contrat). « Je n'ai pas pu lire » n'est pas « c'est
  propre » : l'appelant ne merge pas.

Re-deriver la liste : lister les runs ``scripts-tests.yml`` declenches par
``push`` sur ``main`` et conclus ``failure`` sur une fenetre, lire les ids
``FAILED`` de leurs journaux, et garder les fichiers qui lisent tout le
depot. Un fichier qui rougit pour une raison d'ENVIRONNEMENT (memoire,
runner, reseau) n'a rien a faire ici : il ne dit rien de la fusion.

Usage::

    python scripts/coordination/premerge_combined_check.py --pr 24801 --json
    python scripts/coordination/premerge_combined_check.py --head <sha> --base origin/main
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Fichiers de tests qui lisent le depot ENTIER et ont rougi ``main`` apres un
# merge vert (mesure du 2026-11-05, cf. docstring). Chemins relatifs a la
# racine ; un fichier absent de l'arbre fusionne est simplement saute.
INTEGRITY_TESTS: tuple[str, ...] = (
    "scripts/notebook_tools/tests/test_twin_registry_integrity.py",
    "scripts/notebook_tools/tests/test_twin_index_collisions.py",
    "scripts/lean/tests/test_check_lean_inventory.py",
    "scripts/notebook_tools/tests/test_check_prose_quantitative_claims.py",
    # Anti-entropy (22/11) : le fichier ENTIER coutait 37,6 s (86 tests, 2
    # skips), dont 36,6 s pour QUATRE tests VIFS -- reseau (`gh api`),
    # histoire git (`git log --before`), inventaire du depot -- dont le
    # verdict ne change pas avec la fusion : les rejouer pour chacun des
    # ~98 candidats de la passe repait la meme reponse 98 fois.
    # On ne rejoue donc par candidat que les DEUX tests dont le verdict
    # depend de l'ARBRE FUSIONNE : les instruments du registre existent
    # encore, et l'instrument reel tourne sur l'arbre fusionne. Les 84
    # autres tests sont invariants (ils lisent le module) et tournent
    # toujours dans la CI complete.
    "scripts/tests/test_anti_entropy_register.py::test_les_instruments_du_registre_existent_dans_le_depot",
    "scripts/tests/test_anti_entropy_register.py::test_l_instrument_reel_rend_encore_une_valeur",
    "scripts/lean/tests/test_lean_theorem_duplicates.py",
    "scripts/tests/test_guard_gauntlet.py",
    "scripts/tests/test_heal_worktree_action.py",
    # #26364 T0 -- le cliquet de taille des scripts lit le depot ENTIER : il
    # echoue des qu'un fichier epingle change d'une ligne, dans un sens comme
    # dans l'autre. Joue sur l'arbre fusionne, il retient la PR qui n'a pas
    # ajuste son plafond -- au lieu de la merger et de rougir `main`
    # (mesure du 2026-11-14 : 7 PRs ouvertes touchaient un fichier epingle).
    "scripts/tests/test_script_size_ratchet.py",
)

DEFAULT_TIMEOUT_S = 600
DEFAULT_WORKERS = 4
# Identite du commit de fusion jetable : fixee ici pour ne dependre d'aucune
# configuration git locale (le commit n'est jamais reference ni pousse).
_COMMIT_ENV = {
    "GIT_AUTHOR_NAME": "premerge-combined-check",
    "GIT_AUTHOR_EMAIL": "premerge@localhost",
    "GIT_COMMITTER_NAME": "premerge-combined-check",
    "GIT_COMMITTER_EMAIL": "premerge@localhost",
}
_FAILED_RE = re.compile(r"^(?:FAILED|ERROR) (\S+)")


def failure_detail(output: str, limit: int = 4000) -> str:
    """La section FAILURES de pytest : la RAISON du rouge, pas son identifiant.

    Le journal portait `FAILED <id>` : on en conclut qu'un test a rougi, pas
    POURQUOI. La section FAILURES porte l'assertion -- c'est elle qui
    distingue un delai depasse d'une valeur qui change (mesure du 22/11 :
    deux PRs approuvees ont ete sautees pour
    `test_guard_gauntlet::test_original_intact_under_all_faults`, sans qu'on
    puisse dire si c'etait un TIMEOUT du bac a sable ou une cible modifiee).

    Le retour est tronque : le journal est une ligne par PR, pas un journal
    de test complet.
    """
    lignes = output.splitlines()
    debut = None
    for i, ligne in enumerate(lignes):
        # Le bandeau de pytest : `==== FAILURES ====`
        if "FAILURES" in ligne and ligne.strip().startswith("="):
            debut = i
    if debut is None:
        for i, ligne in enumerate(lignes):
            if ligne.startswith(("FAILED ", "ERROR ")):
                debut = i
    if debut is None:
        return ""
    detail = "\n".join(lignes[debut:]).strip()
    if len(detail) > limit:
        detail = detail[:limit] + "\n[... tronque ...]"
    return detail


@dataclass
class RunResult:
    returncode: int
    stdout: str
    stderr: str
    timed_out: bool = False


class Runner:
    """Execution reelle ; les tests substituent un faux runner."""

    def run(self, cmd: list[str], cwd: str | None = None,
            env: dict[str, str] | None = None,
            timeout: float | None = None) -> RunResult:
        try:
            proc = subprocess.run(
                cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False,
                encoding="utf-8", errors="replace", timeout=timeout,
            )
        except subprocess.TimeoutExpired as exc:
            out = exc.stdout if isinstance(exc.stdout, str) else ""
            return RunResult(124, out or "", "timeout", timed_out=True)
        return RunResult(proc.returncode, proc.stdout or "", proc.stderr or "")


@dataclass
class Verdict:
    verdict: str
    reason: str | None = None
    base: str | None = None
    head: str | None = None
    merge_commit: str | None = None
    tests: list[str] = field(default_factory=list)
    failed: list[str] = field(default_factory=list)
    duration_s: float = 0.0
    worktree_left: str | None = None
    #: La section FAILURES de pytest : la raison du rouge, lisible par
    #: l'appelant (22/11). Vide quand le verdict n'est pas un rouge de test.
    failure_detail: str = ""
    #: Queue de la sortie pytest (stdout + stderr) sur un verdict NON vert
    #: (#28147). Sans elle, le skip de `merge_ready` ne porte que
    #: l'identifiant du test rouge -- et l'on suppose la cause au lieu de la
    #: mesurer. Bornee : les derniers caracteres suffisent.
    output_tail: str = ""

    @property
    def exit_code(self) -> int:
        if self.verdict == "GREEN":
            return 0
        if self.verdict in ("RED", "CONFLICT"):
            return 1
        return 2


def _git(runner: Runner, repo: Path, *args: str,
         env: dict[str, str] | None = None) -> RunResult:
    return runner.run(["git", "-C", str(repo), *args], env=env)


def _rev(runner: Runner, repo: Path, ref: str) -> str | None:
    res = _git(runner, repo, "rev-parse", "--verify", "--quiet",
               f"{ref}^{{commit}}")
    sha = res.stdout.strip()
    return sha if res.returncode == 0 and sha else None


def parse_failed(output: str) -> list[str]:
    """Ids ``FAILED``/``ERROR`` du resume court de pytest, dans l'ordre."""
    seen: list[str] = []
    for line in output.splitlines():
        m = _FAILED_RE.match(line.strip())
        if m and m.group(1) not in seen:
            seen.append(m.group(1))
    return seen


def _fichier_de(entree: str) -> str:
    """`chemin::test` -> `chemin`.

    Une entree de `INTEGRITY_TESTS` peut designer un NOEUD pytest
    (`chemin::nom_du_test`) et non un fichier entier : c'est ce qui permet
    de ne rejouer par candidat que les tests d'un fichier dont le VERDICT
    depend de l'arbre fusionne (22/11 : le fichier anti-entropy coute 37,6 s
    au total, dont 36,6 s pour quatre tests VIFS -- reseau, histoire git,
    inventaire du depot -- dont le verdict ne change pas avec la fusion).
    """
    return entree.split("::", 1)[0]


#: Taille de la queue de sortie conservee sur un verdict non vert (#28147).
#: Bornee : le motif de journal doit rester lisible en une ligne, et la cause
#: d'un rouge (traceback, assertion, timeout) est presque toujours en fin de
#: sortie, pas au debut.
TAIL_MAX_CHARS = 1200


def _tail(output: str, limit: int = TAIL_MAX_CHARS) -> str:
    """Queue bornee de la sortie pytest (stdout + stderr).

    Vide si la sortie est vide. Tronquee par la FIN, prefixee de ``...`` --
    le debut de la sortie est de la collecte, la fin porte la cause.
    """
    text = (output or "").strip()
    if not text:
        return ""
    if len(text) <= limit:
        return text
    return "..." + text[-limit:]


def pytest_command(tests: list[str], workers: int) -> list[str]:
    cmd = [sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
           "-rfE"]
    if workers > 0 and importlib.util.find_spec("xdist") is not None:
        cmd += ["-n", str(workers)]
    return cmd + tests


def check(runner: Runner, repo: Path, *, base: str, head: str,
          worktree: Path, tests: tuple[str, ...] = INTEGRITY_TESTS,
          workers: int = DEFAULT_WORKERS,
          timeout_s: float = DEFAULT_TIMEOUT_S,
          pr: int | None = None,
          reuse_worktree: bool = False) -> Verdict:
    """Joue ``tests`` sur l'arbre que le merge de ``head`` dans ``base`` produirait."""
    started = time.monotonic()

    def done(v: Verdict) -> Verdict:
        v.duration_s = round(time.monotonic() - started, 1)
        return v

    if pr is not None:
        # Le `main` est fetché AVEC la tete du candidat : la base doit etre
        # COURANTE a chaque candidat. Un `main` resolu une fois par passe
        # serait une base PERIMEE, et l'organe existe precisement pour
        # attraper le conflit entre deux PRs fusionnees contre le meme
        # main@T (fenetre residuelle de #24828) : une base perimee le
        # rendrait muet sur ce cas.
        #
        # Mesure du 22/11 (3 runs, machine chargee) : `fetch origin main`
        # seul = 18,2 / 18,8 / 20,7 s ; `fetch origin pull/N/head` seul =
        # 17,8 / 19,6 / 24,1 s ; les deux ensemble = 17,7 / 18,0 / 18,9 s.
        # Le `main` n'ajoute donc que ~0,4 s : le cout du fetch est
        # l'ALLER-RETOUR reseau, pas la ref. Un `main` par passe
        # n'economiserait que 2 % du fetch -- et acheterait une base
        # perimee. La levee de ce cout-la est ailleurs : le worktree.
        fetch = _git(runner, repo, "fetch", "--quiet", "origin", "main",
                     f"pull/{pr}/head")
        if fetch.returncode != 0:
            return done(Verdict("UNREADABLE", "fetch"))
    base_sha = _rev(runner, repo, base)
    head_sha = _rev(runner, repo, head)
    if base_sha is None or head_sha is None:
        return done(Verdict("UNREADABLE", "rev-parse", base_sha, head_sha))

    mt = _git(runner, repo, "merge-tree", "--write-tree", base_sha, head_sha)
    if mt.returncode == 1:
        return done(Verdict("CONFLICT", "merge-tree", base_sha, head_sha))
    tree = (mt.stdout.splitlines() or [""])[0].strip()
    if mt.returncode != 0 or not re.fullmatch(r"[0-9a-f]{40,64}", tree):
        return done(Verdict("UNREADABLE", "merge-tree", base_sha, head_sha))

    env = {**os.environ, **_COMMIT_ENV}
    ct = _git(runner, repo, "commit-tree", tree, "-p", base_sha, "-p",
              head_sha, "-m", f"premerge combined check (PR {pr or '?'})",
              env=env)
    merge_sha = ct.stdout.strip()
    if ct.returncode != 0 or not merge_sha:
        return done(Verdict("UNREADABLE", "commit-tree", base_sha, head_sha))

    # Worktree REUTILISE (22/11) : un `worktree add` + `worktree remove`
    # par candidat coute 38 s + 9 s (mesure du coordinateur sur l'arbre de
    # main). Quand l'appelant passe un worktree de PASSE (`--reuse-worktree`),
    # ce dossier APPARTIENT a la passe : on le pose au premier candidat s'il
    # n'existe pas, puis on se contente d'un `checkout --detach` pour les
    # suivants -- et on ne le retire JAMAIS ici (c'est l'appelant qui le
    # retire en fin de passe). `worktree add` + `worktree remove` reste le
    # chemin par defaut (appel isole).
    reuse = reuse_worktree
    if reuse and (worktree / ".git").exists():
        co = runner.run(["git", "-C", str(worktree), "checkout", "--detach",
                         "--force", "--quiet", merge_sha], env=env)
        if co.returncode != 0:
            return done(Verdict("UNREADABLE", "worktree-checkout", base_sha,
                                head_sha, merge_sha))
    else:
        add = _git(runner, repo, "worktree", "add", "--detach", "--quiet",
                   str(worktree), merge_sha)
        if add.returncode != 0:
            return done(Verdict("UNREADABLE", "worktree-add", base_sha,
                                head_sha, merge_sha))
    verdict = Verdict("UNREADABLE", None, base_sha, head_sha, merge_sha)
    try:
        present = [t for t in tests if (worktree / _fichier_de(t)).is_file()]
        verdict.tests = present
        if not present:
            verdict.reason = "no-tests-present"
        else:
            run_env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
            res = runner.run(pytest_command(present, workers),
                             cwd=str(worktree), env=run_env,
                             timeout=timeout_s)
            output = res.stdout + "\n" + res.stderr
            if res.timed_out:
                verdict.reason = "timeout"
                verdict.failure_detail = failure_detail(output)
                verdict.output_tail = _tail(output)
            elif res.returncode == 0:
                verdict.verdict = "GREEN"
            elif res.returncode == 1:
                verdict.verdict = "RED"
                verdict.failed = parse_failed(output)
                verdict.failure_detail = failure_detail(output)
                verdict.reason = "tests-failed"
                verdict.output_tail = _tail(output)
            else:
                verdict.reason = f"pytest-rc-{res.returncode}"
                verdict.failed = parse_failed(output)
                verdict.failure_detail = failure_detail(output)
                verdict.output_tail = _tail(output)
    finally:
        # Un worktree REPRIS n'est pas retire ici : il sert au candidat
        # suivant de la passe. Seul celui que l'organe a pose lui-meme est
        # retire (jamais `--force` : un worktree que git refuse de retirer
        # est rapporte par son chemin, pas detruit).
        if not reuse:
            rm = _git(runner, repo, "worktree", "remove", str(worktree))
            if rm.returncode != 0:
                verdict.worktree_left = str(worktree)
    return done(verdict)


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--pr", type=int, help="numero de PR (fetch pull/N/head)")
    p.add_argument("--head", help="tete a fusionner (defaut : FETCH de pull/N/head)")
    p.add_argument("--base", default="origin/main")
    p.add_argument("--repo", type=Path, default=REPO_ROOT)
    p.add_argument("--worktree", type=Path,
                   help="chemin du worktree jetable (defaut : .tmp/premerge-<pr>-<pid>)")
    p.add_argument("--reuse-worktree", action="store_true",
                   help="le worktree passe peut deja exister : on y fait un "
                        "checkout --detach au lieu d'un worktree add, et on ne "
                        "le retire pas (il appartient a la passe)")
    p.add_argument("--cleanup", action="store_true",
                   help="retire le worktree de la passe et sort (jamais "
                        "--force : un worktree que git refuse de retirer est "
                        "rapporte, pas detruit)")
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS,
                   help="workers xdist (0 = sequentiel)")
    p.add_argument("--timeout-s", type=float, default=DEFAULT_TIMEOUT_S)
    p.add_argument("--test", action="append", dest="tests",
                   help="remplace la liste INTEGRITY_TESTS (repetable)")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    if not args.cleanup and args.pr is None and args.head is None:
        p.error("--pr ou --head requis")
    return args


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    repo = args.repo.resolve()
    runner = Runner()

    def worktree_de_passe() -> Path:
        """Chemin du worktree : absolu, resolu contre le depot.

        Un chemin relatif est resolu contre la RACINE DU DEPOT, pas contre
        le repertoire courant du processus : l'appelant (la passe) donne un
        chemin relatif au depot, et l'organe doit aboutir au meme dossier
        que lui.
        """
        if args.worktree is None:
            return repo / ".tmp" / f"premerge-{args.pr or 'head'}-{os.getpid()}"
        chemin = Path(args.worktree)
        return chemin if chemin.is_absolute() else repo / chemin

    if args.cleanup:
        # Retrait du worktree de PASSE (22/11) : c'est l'organe qui sait le
        # poser et le retirer. Jamais `--force` : un worktree que git refuse
        # de retirer est RAPPORTE par son chemin, pas detruit.
        worktree = worktree_de_passe()
        if not (worktree / ".git").exists():
            print(f"worktree de passe absent : {worktree}")
            return 0
        rm = _git(runner, repo, "worktree", "remove", str(worktree))
        if rm.returncode != 0:
            print(f"worktree de passe non retire : {worktree}", file=sys.stderr)
            return 1
        return 0
    head = args.head
    if head is None:
        # pull/N/head n'a pas de ref de suivi locale, et FETCH_HEAD rend la
        # PREMIERE ref recuperee (main) : la tete se lit a la source.
        ls = _git(runner, repo, "ls-remote", "origin", f"refs/pull/{args.pr}/head")
        head = (ls.stdout.split() or [""])[0]
        if ls.returncode != 0 or not head:
            verdict = Verdict("UNREADABLE", "ls-remote")
            print(json.dumps({**asdict(verdict), "exit_code": 2})
                  if args.json else "UNREADABLE (ls-remote)")
            return 2
    worktree = worktree_de_passe()
    verdict = check(
        runner, repo, base=args.base, head=head, worktree=worktree,
        tests=tuple(args.tests) if args.tests else INTEGRITY_TESTS,
        workers=args.workers, timeout_s=args.timeout_s, pr=args.pr,
        reuse_worktree=args.reuse_worktree,
    )
    if args.json:
        print(json.dumps({**asdict(verdict), "exit_code": verdict.exit_code},
                         ensure_ascii=False))
    else:
        print(f"{verdict.verdict}"
              + (f" ({verdict.reason})" if verdict.reason else "")
              + f" -- {len(verdict.tests)} fichier(s), {verdict.duration_s} s")
        for test_id in verdict.failed:
            print(f"  FAILED {test_id}")
        if verdict.failure_detail:
            for ligne in verdict.failure_detail.splitlines():
                print(f"  | {ligne}")
        if verdict.worktree_left:
            print(f"  worktree non retire : {verdict.worktree_left}")
    return verdict.exit_code


if __name__ == "__main__":
    sys.exit(main())
