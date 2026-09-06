"""Moteur de la VOIE RAPIDE (#11835) -- un checkout, N verdicts nommes.

Contexte et mesures : voir `fast_lane_registry.py`. En deux phrases : dans ce
depot de 2,1 Go, 89 a 99 % du temps d'un workflow de garde est son
`actions/checkout`, et 1 a 5 secondes son analyse. Ce moteur paie le checkout
une fois, enchaine les analyses, et **emet un check-run nomme par garde** via
l'API Checks pour que la PR conserve exactement la meme granularite de
verdicts qu'aujourd'hui.

Deroulement :

  phase 1  gardes non-mutants, sur HEAD
  phase 2  UNE bascule d'arbre vers la base, tous les scans `base` des gardes
           delta, restauration, puis VERIFICATION que l'arbre est propre
  phase 3  comparaisons delta, puis emission des check-runs

Le risque propre a la mutualisation est qu'un garde lise l'arbre bascule par
un autre. Il est traite en phase 2 : bascule unique, restauration verifiee, et
arret net si l'arbre ne revient pas a son etat -- un verdict rendu sur un arbre
inconnu vaut moins que pas de verdict du tout.

MODE OMBRE (defaut). Les check-runs sont emis sous un nom prefixe, donc a cote
des workflows d'origine sans leur voler leur nom ni leur role. On compare les
verdicts sur des PR reelles ; le basculement (retrait des workflows unitaires,
reprise des noms canoniques) est un second geste, separe et reversible.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))

from fast_lane_registry import (  # noqa: E402
    PILOT, TRANCHE1, TRANCHE2, TRANCHE3, TRANCHE4, TRANCHE5, TRANCHE6,
    TRANCHE7, Guard,
)

SHADOW_PREFIX = "fast-lane (ombre): "
GUARD_TIMEOUT_S = 600
OUTPUT_LIMIT = 60000  # marge sous la limite de 65535 de l'API Checks


# ---------------------------------------------------------------------------
# Selection par chemin
# ---------------------------------------------------------------------------

def path_matches(path: str, pattern: str) -> bool:
    """Semantique des `paths:` GitHub, pour le sous-ensemble qu'on utilise.

    Le piege est le segment `**/` : chez GitHub il matche ZERO ou plus
    repertoire(s), alors que `fnmatch` traite `**` comme un simple `*` et
    exige le separateur. Deux cas concrets du registre : le prefixe racine
    (`**/*.ipynb` couvre `a.ipynb`) et le segment median
    (`MyIA.AI.Notebooks/**/*.ipynb` couvre `MyIA.AI.Notebooks/x.ipynb` --
    GradeBook.ipynb vit exactement la). Un motif qui rate ne leve pas
    d'erreur -- il rend un ensemble de gardes plus petit, donc un CI plus
    vert et plus rapide : le faux negatif exact que ce depot a deja paye
    ailleurs. D'ou le test dedie sur ces cas precis.
    """
    path = path.replace(os.sep, "/")
    if fnmatch.fnmatch(path, pattern):
        return True
    if pattern.startswith("**/"):
        if fnmatch.fnmatch(path, pattern[3:]):
            return True
    if "/**/" in pattern:
        if fnmatch.fnmatch(path, pattern.replace("/**/", "/")):
            return True
    return False


def guard_applies(guard: Guard, changed: list[str]) -> bool:
    if not guard.paths:
        return True
    return any(path_matches(f, p) for f in changed for p in guard.paths)


def changed_files(base_ref: str) -> list[str]:
    out = subprocess.run(
        ["git", "diff", "--name-only", f"{base_ref}...HEAD"],
        cwd=REPO_ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if out.returncode != 0:
        raise SystemExit(
            "[fast-lane] impossible de calculer le diff contre "
            f"{base_ref} : {out.stderr.strip()}"
        )
    return [line.strip() for line in out.stdout.splitlines() if line.strip()]


# ---------------------------------------------------------------------------
# Execution d'un garde
# ---------------------------------------------------------------------------

def substitute(argv: list[str], ctx: dict[str, str]) -> list[str]:
    """Remplace les seuls placeholders connus, en laissant les autres accolades.

    Volontairement PAS `str.format` : celui-ci traite toute accolade du token
    comme un champ de format, donc un garde dont la commande porte un filtre
    `jq`, un quantificateur de regex `{2,3}` ou un litteral JSON leverait un
    `KeyError` a l'execution -- une panne d'infrastructure indiscernable, dans
    le log, d'un verdict de garde. Le registre pilote n'en contient aucun ; a
    trente gardes il y en aura. On substitue donc par cle nommee et rien
    d'autre.
    """
    out = []
    for token in argv:
        for key, value in ctx.items():
            token = token.replace("{" + key + "}", value)
        out.append(token)
    return out


def run_argv(argv: list[str], ctx: dict[str, str]) -> tuple[int, str]:
    cmd = substitute(argv, ctx)
    started = time.time()
    try:
        proc = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True,
                              text=True, encoding="utf-8", errors="replace", timeout=GUARD_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        joined = " ".join(cmd)
        return 124, f"[fast-lane] delai depasse ({GUARD_TIMEOUT_S}s) : {joined}"
    elapsed = time.time() - started
    body = (proc.stdout or "")
    if proc.stderr:
        body = body + "\n" + proc.stderr
    header = " ".join(cmd)
    return proc.returncode, (
        f"$ {header}\n(exit {proc.returncode}, {elapsed:.1f}s)\n\n{body}"
    )


def expand_paths_token(argv: list[str], paths: list[str]) -> list[str]:
    """Remplace `{changed_paths}` par un chemin a la fois ; les autres
    tokens restent inchanges. Si le placeholder n'est pas present, c'est
    un no-op (la fonction rend l'argv inchange)."""
    if "{changed_paths}" not in argv:
        return argv
    out: list[str] = []
    for token in argv:
        if token == "{changed_paths}":
            out.extend(paths)
        else:
            out.append(token)
    return out


def run_iter(argv_template: list[str], paths: list[str],
             ctx: dict[str, str],
             warn_rc: tuple[int, ...] = (),
             fail_on_all_warn: bool = False) -> tuple[int, str]:
    """Execute un garde Pattern 1 (boucle par chemin) en aggregeant un rc
    = max(rc_par_iteration) et une log concatenee. Si `paths` est vide,
    rend un rc=0 no-op (log explicite) -- un CI sans chemin est un vert
    silencieux, pas un garde qui a travaille. Les rc listes dans `warn_rc`
    comptent comme succes : les detecteurs de la serie figure/texte rendent
    rc=2 sur fichier illisible, et leur workflow d'origine l'affiche en
    warning -- l'agreger en echec rendrait la lane plus stricte que ce
    qu'elle absorbe.

    `fail_on_all_warn` rend l'anti-auto-desarmement AGREGE des workflows qui
    le portent (md-content-loss-gate, clause #8655/#8656) : si CHAQUE fichier
    examine a rendu un rc de `warn_rc`, le garde n'a RIEN analyse et rend 1
    (fail loud) au lieu d'un quitus vert -- un detecteur casse ne doit pas
    produire la bonne conclusion par silence."""
    if not paths:
        return 0, "[fast-lane] iterates_paths vide : aucun fichier a examiner"
    rc_agg = 0
    warned = 0
    chunks: list[str] = []
    for path in paths:
        local_ctx = dict(ctx, changed_paths=path)
        rc, log = run_argv(argv_template, local_ctx)
        if rc in warn_rc:
            rc = 0
            warned += 1
        chunks.append(f"--- {path} ---\n{log}")
        if rc > rc_agg:
            rc_agg = rc
    if fail_on_all_warn and warned > 0 and warned == len(paths):
        return 1, (
            "[fast-lane] TOUS les fichiers examines etaient illisibles "
            f"(rc {warn_rc}) : le garde n'a rien analyse et ne peut pas "
            "certifier -- fail loud (anti-auto-desarmement, #8655/#8656)\n\n"
            + "\n\n".join(chunks))
    return rc_agg, "\n\n".join(chunks)


def payload_of(log: str) -> str:
    """Sortie standard seule, sans l'en-tete ajoute par `run_argv`."""
    parts = log.split("\n\n", 1)
    return parts[1] if len(parts) == 2 else ""


def git(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=REPO_ROOT,
                          capture_output=True, text=True, encoding="utf-8", errors="replace")


def tree_is_clean(paths: list[str]) -> tuple[bool, str]:
    proc = git("status", "--porcelain", "--", *paths) if paths \
        else git("status", "--porcelain")
    return (proc.stdout.strip() == ""), proc.stdout.strip()


def stale_added_paths(porcelain: str) -> list[str]:
    """Chemins en addition staged (``A ``) d'un `git status --porcelain`.

    Apres `git checkout <base> -- <dir>` puis `git checkout HEAD -- <dir>`,
    les fichiers presents a la base mais renommes (donc absents) dans HEAD
    survivent : `git checkout <tree> -- <path>` ecrit les fichiers de
    <tree>, il ne supprime JAMAIS ceux qui n'y sont pas. Ces fantomes sont
    staged comme additions ; les purger restaure l'arbre exact de HEAD.
    Les untracked (``??``) ne sont PAS purges : un garde qui ecrit dans le
    repo doit continuer de declencher l'arret net.
    """
    out = []
    for line in porcelain.splitlines():
        if not line.startswith("A "):
            continue
        path = line[3:].strip()
        if path.startswith('"') and path.endswith('"'):
            path = path[1:-1]
        if path:
            out.append(path)
    return out


# ---------------------------------------------------------------------------
# Emission des check-runs
# ---------------------------------------------------------------------------

def emit_check_run(repo: str, head_sha: str, name: str, conclusion: str,
                   title: str, summary: str, dry_run: bool) -> None:
    payload = {
        "name": name,
        "head_sha": head_sha,
        "status": "completed",
        "conclusion": conclusion,
        "output": {
            "title": title[:255],
            "summary": summary[:OUTPUT_LIMIT],
        },
    }
    if dry_run:
        print(f"[fast-lane][a-blanc] check-run {name!r} -> {conclusion} ({title})")
        return
    proc = subprocess.run(
        ["gh", "api", "-X", "POST", f"repos/{repo}/check-runs", "--input", "-"],
        input=json.dumps(payload), capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        # Ne pas faire echouer le job entier : un verdict non publie doit
        # rester visible dans le log plutot que de masquer les autres.
        print(f"[fast-lane] ECHEC de publication du check-run {name!r} : "
              f"{proc.stderr.strip()}", file=sys.stderr)
    else:
        print(f"[fast-lane] check-run publie : {name} -> {conclusion}")


def conclusion_for(guard: Guard, rc: int, shadow: bool = False) -> str:
    if rc in guard.warn_rc:
        rc = 0
    if rc == 0:
        return "success"
    if shadow:
        # La phase ombre se declare observationnelle : elle ne doit donc pas
        # pouvoir bloquer une PR. Or `pr_gate` ne traite en advisory que les
        # check-runs dont le NOM contient `advisory` -- le prefixe ombre n'en
        # contient pas, donc un `failure` ombre entrait dans `bad` et rendait
        # le gate REQUIS rouge. Mesure du 2026-08-25 : 2 PR ouvertes (#12791,
        # #12820) avaient pour SEUL rouge un check ombre, sur 125 PR portant
        # un check ombre. Le verdict reste visible dans le titre et le resume
        # du check-run ; seule sa capacite a bloquer est retiree.
        return "neutral"
    return "failure" if guard.blocking else "neutral"


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Voie rapide CI (#11835)")
    parser.add_argument("--base-ref",
                        default=os.environ.get("FAST_LANE_BASE", "origin/main"))
    parser.add_argument("--base-sha",
                        default=os.environ.get("FAST_LANE_BASE_SHA", ""))
    parser.add_argument("--head-sha",
                        default=os.environ.get("FAST_LANE_HEAD_SHA", ""))
    parser.add_argument("--pr-number",
                        default=os.environ.get("FAST_LANE_PR", ""))
    parser.add_argument("--repo",
                        default=os.environ.get("GITHUB_REPOSITORY",
                                               "jsboige/CoursIA"))
    parser.add_argument("--shadow", action="store_true", default=True,
                        help="prefixer les noms de check-run (defaut pilote)")
    parser.add_argument("--no-shadow", dest="shadow", action="store_false")
    parser.add_argument("--dry-run", action="store_true",
                        help="ne rien publier ; afficher les verdicts")
    parser.add_argument("--only", default="",
                        help="ne lancer qu'un garde, par nom")
    args = parser.parse_args(argv)

    changed = changed_files(args.base_ref)
    print(f"[fast-lane] {len(changed)} fichier(s) modifie(s) "
          f"contre {args.base_ref}")

    guards = [g for g in PILOT + TRANCHE1 + TRANCHE2 + TRANCHE3 + TRANCHE4
              + TRANCHE5 + TRANCHE6 + TRANCHE7
              if not args.only or g.name == args.only]
    selected = [g for g in guards if guard_applies(g, changed)]
    for guard in guards:
        if guard not in selected:
            print(f"[fast-lane] hors perimetre (filtre paths) : {guard.name}")

    ctx = {
        "base_ref": args.base_ref,
        "base_sha": args.base_sha,
        "head_sha": args.head_sha,
        "pr_number": args.pr_number,
        "base_json": "",
        "head_json": "",
    }
    results: dict[str, tuple[int, str]] = {}
    head_json: dict[str, str] = {}
    tmp = Path(os.environ.get("RUNNER_TEMP") or (REPO_ROOT / ".fast-lane-tmp"))
    tmp.mkdir(parents=True, exist_ok=True)

    # -- phase 1 : HEAD, aucun garde ne mute l'arbre -------------------------
    for guard in selected:
        if guard.pre_argv:
            # Pre-controle (self-test du detecteur, #11685) : un rc non nul
            # EST le verdict du garde et le scan n'est pas execute -- un
            # detecteur qui ne prouve pas qu'il tire ne doit pas rendre vert.
            rc, log = run_argv(guard.pre_argv, ctx)
            if rc != 0:
                results[guard.name] = (rc, log)
                print(f"[fast-lane] pre-contrôle {guard.name} : exit {rc} "
                      "-- garde non execute")
                continue
        if guard.iterates_paths:
            # Fidelite aux boucles d'origine : les workflows iteratifs
            # sautent les fichiers SUPPRIMES par la PR (`[ -f "$nb" ] ||
            # continue`). Un chemin absent passe au detecteur rendrait son
            # code "illisible" (rc=2), qui sans ce filtre deviendrait un
            # faux verdict sur un fichier que l'original n'examinait pas.
            # `iterate_paths` (si renseigne) restreint l'ITERATION au glob
            # d'actifs, distinct du declencheur `paths` -- sans lui, le
            # detecteur/workflow present dans `paths` serait passe au
            # detecteur de notebooks -> rc=2 -> faux echec (incident
            # #13220 : la PR qui ajoute la garde echouait dessus).
            iter_patterns = guard.iterate_paths or guard.paths
            arg_paths = sorted({f for f in changed
                                for p in iter_patterns
                                if path_matches(f, p)
                                and (REPO_ROOT / f).is_file()})
            rc, log = run_iter(guard.argv, arg_paths, ctx,
                               warn_rc=guard.warn_rc,
                               fail_on_all_warn=guard.fail_on_all_warn)
            results[guard.name] = (rc, log)
            print(f"[fast-lane] phase 1 {guard.name} (iter sur {len(arg_paths)} "
                  f"fichier(s)) : exit {rc}")
            continue
        rc, log = run_argv(guard.argv, ctx)
        if guard.delta_argv:
            dest = tmp / f"{guard.name}.head.json"
            dest.write_text(payload_of(log), encoding="utf-8")
            head_json[guard.name] = str(dest)
            print(f"[fast-lane] phase 1 (HEAD) {guard.name} : scan capture")
        else:
            results[guard.name] = (rc, log)
            print(f"[fast-lane] phase 1 {guard.name} : exit {rc}")

    # -- phase 2 : UNE bascule pour tous les gardes delta --------------------
    delta_guards = [g for g in selected if g.delta_argv]
    base_json: dict[str, str] = {}
    if delta_guards:
        swap = sorted({p for g in delta_guards for p in g.swap_paths})
        if not args.base_sha:
            print("[fast-lane] pas de base-sha : phase delta ignoree",
                  file=sys.stderr)
        else:
            print(f"[fast-lane] phase 2 : bascule de {swap} "
                  f"vers {args.base_sha[:12]}")
            swapped = git("checkout", args.base_sha, "--", *swap)
            if swapped.returncode != 0:
                raise SystemExit("[fast-lane] bascule impossible : "
                                 f"{swapped.stderr.strip()}")
            try:
                for guard in delta_guards:
                    _, log = run_argv(guard.argv, ctx)
                    dest = tmp / f"{guard.name}.base.json"
                    dest.write_text(payload_of(log), encoding="utf-8")
                    base_json[guard.name] = str(dest)
            finally:
                git("checkout", "HEAD", "--", *swap)
                # git checkout <tree> -- <path> ne supprime pas les fichiers
                # absents de <tree> : les renames base->HEAD laissent des
                # additions fantomes qu'on purge avant l'attestation.
                st = git("status", "--porcelain", "--", *swap)
                stale = stale_added_paths(st.stdout)
                if stale:
                    git("rm", "-fq", "--", *stale)
            clean, dirt = tree_is_clean(swap)
            if not clean:
                # Arret net : les verdicts suivants porteraient sur un arbre
                # dont on ne sait plus ce qu'il contient. On ne publie RIEN,
                # dans les DEUX modes -- c'est la partie fail-closed, et
                # elle ne bouge pas.
                msg = ("[fast-lane] l'arbre n'est PAS revenu a son etat "
                       "apres la bascule -- aucun verdict ne sera publie."
                       "\n" + dirt)
                if args.shadow:
                    # ... mais en OMBRE le job ne doit pas rougir pour
                    # autant. Le check du job s'appelle `Fast lane (ombre)
                    # -- N gardes, 1 checkout` : il ne contient pas
                    # `advisory`, donc `pr_gate` le compte comme un defaut
                    # et BLOQUE la PR. Une panne de la voie ombre bloque
                    # alors une PR saine -- exactement ce que la phase
                    # pilote promet de ne pas faire. Mesure du 2026-08-25 :
                    # #12820 etait retenue par ce chemin (run 32774643069)
                    # sans porter aucun defaut propre.
                    print(msg, file=sys.stderr)
                    print("[fast-lane] mode ombre : panne interne signalee,"
                          " job non bloquant (exit 0).", file=sys.stderr)
                    return 0
                raise SystemExit(msg)
            print("[fast-lane] phase 2 : arbre restaure et verifie")

    # -- phase 3 : comparaisons delta ---------------------------------------
    for guard in delta_guards:
        if guard.name not in base_json:
            results[guard.name] = (
                0, "[fast-lane] phase delta non executee (pas de base)")
            continue
        local = dict(ctx, base_json=base_json[guard.name],
                     head_json=head_json[guard.name])
        rc, log = run_argv(guard.delta_argv, local)
        results[guard.name] = (rc, log)
        print(f"[fast-lane] phase 3 {guard.name} : exit {rc}")

    # -- emission ------------------------------------------------------------
    # Mode MIXTE (#12567, tranche 1 d'absorption) : un garde `absorbed` rend
    # son verdict SOUS SON NOM CANONIQUE avec une conclusion REELLE meme quand
    # la lane tourne en ombre -- c'est le basculement annonce par le pilote,
    # applique garde par garde. Les gardes du pilote conservent le prefixe
    # ombre et la neutralisation jusqu'a la conclusion de la comparaison.
    head_sha = args.head_sha or git("rev-parse", "HEAD").stdout.strip()
    blocking_failed = False
    for guard in selected:
        rc, log = results.get(guard.name, (0, "(aucune sortie)"))
        if rc in guard.warn_rc:
            rc = 0  # meme mapping que conclusion_for : un seul verdict
        effective_shadow = args.shadow and not guard.absorbed
        conclusion = conclusion_for(guard, rc, shadow=effective_shadow)
        if rc == 0:
            title = "OK"
        elif guard.blocking:
            title = ("echec (ombre : non bloquant)" if effective_shadow
                     else "echec")
        else:
            title = "signale (advisory)"
        name = ((SHADOW_PREFIX + guard.name) if effective_shadow
                else guard.name)
        emit_check_run(
            args.repo, head_sha, name, conclusion,
            f"{guard.name} -- {title}",
            f"Source : `{guard.source}`\n\n```\n{log}\n```",
            args.dry_run,
        )
        if guard.blocking and rc != 0 and not effective_shadow:
            blocking_failed = True

    verdict = ("au moins un bloquant en echec" if blocking_failed
               else "aucun bloquant en echec")
    print(f"[fast-lane] {len(selected)} garde(s) evalue(s), {verdict}")

    # En mode ombre le job ne rougit jamais : il observe, il ne juge pas
    # encore. Les verdicts vivent dans les check-runs. En mode MIXTE
    # (#12567), `blocking_failed` ne compte deja que les gardes reels
    # (absorbes, ou lane --no-shadow) : si l'un d'eux echoue, le job DOIT
    # rougir, meme si le reste de la lane observe.
    if args.shadow and not blocking_failed:
        return 0
    return 1 if blocking_failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
