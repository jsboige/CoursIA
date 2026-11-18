#!/usr/bin/env python3
"""Reproduction harness for the HopfProblem formalization (plby/HopfProblem).

Verifies and summarizes a LOCAL, PINNED checkout of the upstream repository
(git@github.com:plby/HopfProblem.git @ 9ac8a456b526527837d7082ff775213ca8bc9809)
that reproduces the S^6 complex-structure proof on this machine:

    elan toolchain install leanprover/lean4:v4.33.0
    lake update
    lake exe cache get          # Mathlib v4.33.0 oleans
    lake build lean4export
    lake build Challenge        # 8707 jobs
    lake build Solution         # 248,818-line monolith (single file)
    lake exe comparator comparator/config.json   # Lean + nanoda kernels

Le comparator tourne sous le bac a sable Landrun : `full` lit le type de ce
binaire dans son en-tete ELF AVANT de lancer le comparator, et refuse
l'etape s'il est absent, non executable ou d'une autre architecture --
`check` publie le meme type (`landrun_type`) et sort en echec s'il n'est
pas `elf64-x86-64`. Un chemin present dans une variable d'environnement
n'est pas un binaire disponible.

The notebook Lean-28-Complex-Structure-S6.ipynb consumes the JSON emitted by
`check` so that every committed output traces back to a real artifact on disk
(build.log, comparator.log written by the actual runs -- never hand-edited).
`full` capture (tee) les builds Challenge/Solution dans build.log et le
comparator dans comparator.log (enveloppe ``{ time ... ; }`` : la ligne
``real XmY.Ys`` du timing est ecrite DANS le log, ou ``check`` la relit en
``real_seconds``) : pipefail garde visible le rc du producteur,
et un log precedent est mis de cote sous un suffixe .bak date UTC (GNU
--backup=numbered : deux rotations dans la meme seconde s'empilent, jamais
ne se remplacent) -- jamais d'ecrasement silencieux. `check` sort en echec
(rc != 0, JSON diagnostique conserve) quand checkout, pin, artefacts de
build ou verdicts comparator manquent ou sont invalides : une absence n'est
jamais presentee comme un compte nul. La preparation est idempotente :
toolchain deja installee = detectee sans reinstall (elan refuse de
reinstaller, rc 1 'already installed') ; checkout existant reinspecte
(origin attendue + arbre propre) puis reutilise, jamais supprime.

Usage:
    python hopf_s6_reproduction.py check          # verify artifacts, emit JSON
    python hopf_s6_reproduction.py full --dry-run # print the full protocol
    python hopf_s6_reproduction.py full           # EXECUTE the full protocol
                                                  # (clone+build+comparator,
                                                  #  ~35 min + toolchains)

The checkout lives in WSL (ext4) because lake cache-get stalls on /mnt drvfs.
"""
import argparse
import json
import re
import subprocess
import sys

PINNED_SHA = "9ac8a456b526527837d7082ff775213ca8bc9809"
HOPF_DIR = "/home/jesse/HopfProblem"
HOPF_URL = "https://github.com/plby/HopfProblem.git"
BUILD_LOG = f"{HOPF_DIR}/build.log"
COMPARATOR_LOG = f"{HOPF_DIR}/comparator.log"
TOOLCHAIN = "leanprover/lean4:v4.33.0"
PERMITTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
LANDRUN_BIN = "$HOME/bin/landrun"


def rotate_if_present(log: str) -> str:
    """Conserve une preuve existante avant nouvelle capture.

    Rotation datee UTC + ``mv --backup=numbered`` (GNU) : deux rotations dans
    la meme seconde se numerotent (``.bak``, ``.bak.~1~``, ...), jamais de
    remplacement d'une sauvegarde existante.
    """
    stamp = "$(date -u +%Y%m%dT%H%M%SZ)"
    return (
        f"if [ -f {log} ]; then "
        f"mv --backup=numbered {log} {log}.{stamp}.bak; fi"
    )


def captured_step(work: str, log: str, append: bool = False,
                  cwd: str = HOPF_DIR, timed: bool = False) -> str:
    """Etape executee au checkout : conserver le log precedent, capturer via tee.

    Lecture shell (precedence verifiee par les tests bash reels, cf. tests/) :
    le pipeline lie plus fort que ``&&`` -- la forme se lit
    ``cd && rotation && set && (producteur | tee)`` :

    - si ``cd`` ou la rotation echoue, court-circuit : tee ne s'execute pas,
      le log existant n'est ni tronque ni ouvert ;
    - ``set -o pipefail`` s'applique au pipeline final : le rc de l'etape reste
      celui du producteur (lake/comparator), tee ne masque pas un echec ;
    - rotation datee UTC avec ``mv --backup=numbered`` : deux rotations dans la
      meme seconde se numerotent, jamais de remplacement d'une sauvegarde ;
    - ``append=True`` : le build Solution complete le build.log fraichement
      ouvert par le build Challenge (pas de rotation) ;
    - ``timed=True`` : le producteur est enveloppe ``{ time ... ; }`` -- le
      timing bash de ``time`` (``real XmY.Ys``, ecrit sur stderr DU GROUPE)
      suit la redirection 2>&1 et atterrit donc dans le log ; ``time``
      retournant le rc de la commande enveloppee, pipefail garde le rc du
      producteur. ``parse_comparator_log`` consomme cette ligne
      (``real_seconds``), et ``check`` refuse un comparator sans timing lu.
    """
    preserve = "" if append else rotate_if_present(log) + " && "
    append_flag = "-a " if append else ""
    producer = f"{{ time {work} ; }} 2>&1" if timed else f"{work} 2>&1"
    return (
        f"cd {cwd} && {preserve}set -o pipefail && {producer} "
        f"| tee {append_flag}{log}"
    )


def prepare_checkout_step(directory: str = HOPF_DIR, url: str = HOPF_URL,
                          pin: str = PINNED_SHA) -> str:
    """Preparation idempotente du checkout -- jamais de suppression.

    - cible absente : clone ;
    - cible presente sans etre un depot git : refus explicite (rc 1) ;
    - depot present : origin doit etre l'URL attendue ET l'arbre propre,
      sinon refus explicite -- un repertoire etranger ou sale n'est ni
      supprime ni reutilise ;
    - toute lecture (origin, status) passe par une affectation TESTEE : un
      echec de lecture est un refus, jamais un etat inconnu accepte (une
      substitution non testee rendrait une chaine vide, lue a tort comme
      'propre') ;
    - ensuite checkout du pin, qui echoue tel quel si le pin manque du depot.
    Reexecutable : une cible propre deja au pin est un no-op.
    """
    return (
        f'if [ ! -e {directory} ]; then git clone {url} {directory}; '
        f'else '
        f'if [ ! -d {directory}/.git ]; then '
        f'echo "refus: {directory} existe sans etre un depot git" >&2; exit 1; fi; '
        f'if ! origin=$(git -C {directory} remote get-url origin); then '
        f'echo "refus: pas de remote origin" >&2; exit 1; fi; '
        f'if [ "$origin" != "{url}" ]; then '
        f'echo "refus: origin inattendu: $origin" >&2; exit 1; fi; '
        f'if ! status=$(git -C {directory} status --porcelain); then '
        f'echo "refus: lecture de l\'etat du depot impossible" >&2; exit 1; fi; '
        f'if [ -n "$status" ]; then '
        f'echo "refus: arbre de travail sale" >&2; exit 1; fi; '
        f'fi '
        f'&& git -C {directory} checkout -q {pin}'
    )


def toolchain_step(toolchain: str = TOOLCHAIN) -> str:
    """elan idempotent : n'installer que si la toolchain EXACTE manque.

    Le listing passe par une affectation TESTEE : un echec d'elan toolchain
    list est un refus explicite, pas une absence transformee en tentative
    d'installation. Format mesure sur po-2025 (2026-10-19) : un nom par ligne,
    sans suffixe -- ``cut -d' ' -f1`` tolere un eventuel suffixe '(default)'
    et ``grep -qxF`` exige le nom exact (v4.33.0 ne matche pas v4.33.0-rc1).
    Pas de '|| true' general : un echec reel d'installation reste l'echec de
    l'etape -- le cas evite est le rc 1 'already installed' du run bzu0eqmo3.
    """
    return (
        f"if ! installed=$(elan toolchain list); then "
        f'echo "refus: elan toolchain list a echoue" >&2; exit 1; fi; '
        f'echo "$installed" | cut -d\' \' -f1 '
        f"| grep -qxF '{toolchain}' || elan toolchain install {toolchain}"
    )


def _landrun_probe_sh(path: str = LANDRUN_BIN) -> str:
    """Fragment shell qui pose ``landrun_type`` en lisant l'en-tete ELF.

    ``od`` est dans coreutils : pas de dependance nouvelle a ``file`` ni a
    ``readelf``. Les vingt premiers octets sont aplatis en une chaine
    hexadecimale contigue (``tr -d``), puis decoupes par ``cut`` aux champs
    qui portent le type : 1-8 magie ELF, 9-10 classe (``02`` = 64 bits),
    37-40 ``e_machine`` (``3e00`` = x86-64 en petit-boutiste).

    Les parametres positionnels sont evites deliberement : ``$19`` se lit
    ``${1}9`` (parametre 1 suivi du litteral ``9``), ce qui rendait la lecture
    de ``e_machine`` silencieusement fausse -- mesure sur ``/bin/true`` le
    2026-10-24 (``$19$20`` rendait ``7f9450``). Une longueur hexadecimale
    inferieure a 40 caracteres signale un fichier trop court pour porter un
    en-tete ELF : c'est un etat distinct, jamais un refus generique.
    """
    return (
        "if [ ! -e " + path + " ]; then landrun_type=missing; "
        "elif [ ! -f " + path + " ]; then landrun_type=not-a-file; "
        "elif [ ! -x " + path + " ]; then landrun_type=not-executable; "
        "else h=$(od -An -tx1 -N20 " + path + " 2>/dev/null | tr -d ' \\n'); "
        'if [ "$(printf %s "$h" | wc -c)" -lt 40 ]; then '
        "landrun_type=too-short; "
        'elif [ "$(printf %s "$h" | cut -c1-8)" != "7f454c46" ]; then '
        "landrun_type=not-elf; "
        'elif [ "$(printf %s "$h" | cut -c9-10)" != "02" ]; then '
        "landrun_type=elf-not-64bit; "
        'elif [ "$(printf %s "$h" | cut -c37-40)" != "3e00" ]; then '
        "landrun_type=elf64-not-x86-64; "
        "else landrun_type=elf64-x86-64; fi; fi"
    )


LANDRUN_PROBE = _landrun_probe_sh()


def landrun_gate() -> str:
    """Garde fail-closed : le binaire Landrun, lu, avant le comparator.

    Le nom de la variable ``COMPARATOR_LANDRUN`` ne prouve rien : un chemin
    absent, un fichier homonyme non executable ou un binaire d'une autre
    architecture laissait le comparator s'executer et rendait, au mieux, un
    echec tardif au milieu du protocole. Le type est donc lu dans l'en-tete
    ELF (cf. ``LANDRUN_PROBE``) et un type inattendu coupe l'etape avant
    ``lake exe comparator``. Le message de refus part sur stderr, donc dans
    ``comparator.log`` via le ``2>&1`` de ``captured_step`` -- la trace du
    refus survit a l'execution qui l'a produit.
    """
    return (
        LANDRUN_PROBE + "; "
        'if [ "$landrun_type" != "elf64-x86-64" ]; then '
        'echo "refus: binaire Landrun attendu (ELF64 x86-64 executable) en '
        + LANDRUN_BIN + ' -- lu: $landrun_type" >&2; exit 1; fi; '
        'echo "landrun: $landrun_type"; '
    )


COMPARATOR_WORK = (
    "{gate}"
    "COMPARATOR_LANDRUN=" + LANDRUN_BIN + " "
    "COMPARATOR_LEAN4EXPORT={d}/.lake/packages/lean4export/.lake/build/bin/lean4export "
    "COMPARATOR_NANODA=$HOME/nanoda_lib/target/release/nanoda_bin "
    "lake exe comparator comparator/config.json"
).format(d=HOPF_DIR, gate=landrun_gate())

FULL_PROTOCOL = [
    prepare_checkout_step(),
    toolchain_step(),
    f"cd {HOPF_DIR} && lake update",
    f"cd {HOPF_DIR} && lake exe cache get",
    f"cd {HOPF_DIR} && lake build lean4export",
    captured_step("lake build Challenge", BUILD_LOG),
    captured_step("lake build Solution", BUILD_LOG, append=True),
    captured_step(COMPARATOR_WORK, COMPARATOR_LOG, timed=True),
]


def wsl(cmd: str, timeout: int = 120) -> str:
    """Run a command inside the WSL distro (login shell for elan PATH)."""
    proc = subprocess.run(
        ["wsl", "-e", "bash", "-lc", cmd],
        capture_output=True, text=True, timeout=timeout, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"WSL command failed (rc={proc.returncode}): {cmd}\n{proc.stderr}")
    return proc.stdout.strip()


def sh(cmd: str, default: str = "") -> str:
    """WSL command that may legitimately fail (grep no-match) -> default."""
    try:
        return wsl(cmd)
    except (RuntimeError, subprocess.TimeoutExpired):
        return default


def landrun_probe(path: str = LANDRUN_BIN) -> str:
    """Type mesure du binaire Landrun (cf. ``_landrun_probe_sh``) ; "" si muet.

    Une chaine vide n'est pas un verdict : ``cmd_check`` la rend ``None`` et
    l'absence de lecture ne valide jamais le protocole (meme discipline que
    pour les comptes ``grep`` nuls lus avec ``|| true``).
    """
    return sh(
        _landrun_probe_sh(path) + '; printf "%s" "$landrun_type"', default=""
    )


def parse_build_log(log: str) -> dict:
    info = {"jobs_counts": None, "solution_seconds": None, "axioms_line": None}
    counts = [int(m.group(1)) for m in
              re.finditer(r"Build completed successfully \((\d+) jobs?\)", log)]
    info["jobs_counts"] = counts
    m = re.search(r"Built Solution \((\d+)s\)", log)
    if m:
        info["solution_seconds"] = int(m.group(1))
    m = re.search(r"^info: Solution\.lean:\d+:\d+: (.+depends on axioms.+)$",
                  log, re.MULTILINE)
    if m:
        info["axioms_line"] = m.group(1)
    return info


def parse_comparator_log(log: str) -> dict:
    info = {"real_seconds": None, "nanoda": None, "lean_kernel": None, "verdict": None}
    m = re.search(r"real\s+(\d+)m([\d.]+)s", log)
    if m:
        info["real_seconds"] = round(int(m.group(1)) * 60 + float(m.group(2)), 1)
    if "Nanoda kernel accepts the solution" in log:
        info["nanoda"] = "accepts"
    if "Lean default kernel accepts the solution" in log:
        info["lean_kernel"] = "accepts"
    if "Your solution is okay!" in log:
        info["verdict"] = "Your solution is okay!"
    return info


def sh_int(cmd: str) -> int | None:
    """Entier lu via WSL ; None si la source est absente -- jamais 0 par defaut.

    Une absence de preuve ne doit pas se presenter comme un compte nul
    (acceptance #21442 : « zero ligne ou absence d'artefact ne doit pas etre
    presente comme une preuve d'integrite »).
    """
    raw = sh(cmd, default="")
    return int(raw) if raw.strip() else None


def cmd_check() -> int:
    head = sh(f"git -C {HOPF_DIR} rev-parse HEAD")
    out = {
        "pinned_sha": head or None,
        "sha_matches_pin": head == PINNED_SHA,
        "toolchain": sh(f"cat {HOPF_DIR}/lean-toolchain", default=""),
        "solution_present": sh(
            f"test -f {HOPF_DIR}/Solution.lean && echo yes") == "yes",
        "solution_lines": sh_int(f"wc -l < {HOPF_DIR}/Solution.lean"),
        "solution_olean_bytes": sh_int(
            f"stat -c %s {HOPF_DIR}/.lake/build/lib/lean/Solution.olean"),
        # '|| true' : grep -c sort un compte REEL de 0 avec rc 1 ; sans lui,
        # un fichier present sans match serait indiscernable d'un fichier
        # absent (les deux rendraient le defaut "" -> None).
        "sorry_proof_count": sh_int(
            rf"grep -cE '^\s*sorry\s*$' {HOPF_DIR}/Solution.lean || true"),
        "sorry_word_count": sh_int(
            rf"grep -cw sorry {HOPF_DIR}/Solution.lean || true"),
        "axiom_decl_count": sh_int(
            rf"grep -cE '^\s*axiom\s' {HOPF_DIR}/Solution.lean || true"),
        "native_decide_count": sh_int(
            rf"grep -cw native_decide {HOPF_DIR}/Solution.lean || true"),
        "license": sh(f"head -1 {HOPF_DIR}/LICENSE", default=""),
        # Critere 2 de #21442 : le binaire Landrun se verifie, il ne se nomme
        # pas. Le type est lu dans l'en-tete ELF ; une sonde muette rend None,
        # jamais une valeur par defaut presentee comme conforme.
        "landrun_path": LANDRUN_BIN,
        "landrun_type": landrun_probe() or None,
    }
    build_log = sh(f"cat {BUILD_LOG}", default="")
    comp_log = sh(f"cat {COMPARATOR_LOG}", default="")
    out["build"] = parse_build_log(build_log) if build_log else None
    out["comparator"] = parse_comparator_log(comp_log) if comp_log else None
    out["build_log_present"] = bool(build_log)
    out["comparator_log_present"] = bool(comp_log)
    # Datation UTC des logs : un log present mais anterieur au checkout courant
    # ne doit pas passer pour une preuve fraiche (les .bak de rotation restent
    # hors lecture, seuls les logs courants sont consommes).
    out["build_log_mtime_utc"] = sh(
        f"date -u -r {BUILD_LOG} +%Y-%m-%dT%H:%M:%SZ", default="") or None
    out["comparator_log_mtime_utc"] = sh(
        f"date -u -r {COMPARATOR_LOG} +%Y-%m-%dT%H:%M:%SZ", default="") or None

    ax = out.get("build", {}).get("axioms_line") if out.get("build") else None
    out["axioms_within_permitted"] = (
        sorted(re.findall(r"\w+(?:\.\w+)*", ax.split(":", 1)[-1]))
        == sorted(PERMITTED_AXIOMS)
        if ax else False
    )
    comparator = out["comparator"] or {}
    # Verdict fail-closed : chaque membre distingue « preuve lue et conforme »
    # de « absence » (None != 0). Aucune absence ne valide le protocole.
    out["check_ok"] = all([
        # checkout et pin
        out["pinned_sha"] is not None,
        out["sha_matches_pin"],
        # binaire Landrun : un type MESURE, pas un chemin suppose (#21442)
        out["landrun_type"] == "elf64-x86-64",
        # artefacts de build : sources presentes et non vides
        out["solution_present"],
        (out["solution_lines"] or 0) > 0,
        (out["solution_olean_bytes"] or 0) > 0,
        # preuves dans build.log : build reussi + axiomes permis
        out["build_log_present"],
        bool((out["build"] or {}).get("jobs_counts")),
        out["axioms_within_permitted"],
        # integrite de la solution : comptes NULS LUS, pas absence
        out["sorry_proof_count"] == 0,
        out["axiom_decl_count"] == 0,
        out["native_decide_count"] == 0,
        # comparator : les trois verdicts d'acceptation ET le timing --
        # real_seconds est consomme par le notebook (cellule verdict, division
        # par 60) : un comparator execute sans capture time (ligne ``real``
        # absente du log) ne valide pas le protocole, meme si les verdicts y
        # sont (mesure 2026-10-19 : check_ok true + real_seconds None a fait
        # echouer la cellule 18 du notebook).
        out["comparator_log_present"],
        comparator.get("verdict") == "Your solution is okay!",
        comparator.get("nanoda") == "accepts",
        comparator.get("lean_kernel") == "accepts",
        comparator.get("real_seconds") is not None,
    ])
    print(json.dumps(out, indent=2, ensure_ascii=False))
    return 0 if out["check_ok"] else 1


def cmd_full(dry_run: bool) -> int:
    print("Full reproduction protocol (see docstring for hardware notes):")
    for step in FULL_PROTOCOL:
        print(f"  $ {step}")
    if dry_run:
        print("\n(dry-run: nothing executed)")
        return 0
    print("\nExecuting... (this takes ~35 min of build + 11 min of comparator)")
    for step in FULL_PROTOCOL:
        print(f"\n$ {step}")
        # Pas de timeout court ici (wsl() en applique un de 120 s) : les builds
        # Challenge/Solution et le comparator durent bien plus longtemps.
        proc = subprocess.run(["wsl", "-e", "bash", "-lc", step])
        if proc.returncode != 0:
            print(f"\nStep failed (rc={proc.returncode}): {step}", file=sys.stderr)
            return proc.returncode
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("check", help="verify artifacts and emit JSON summary")
    full = sub.add_parser("full", help="run or print the full protocol")
    full.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    if args.cmd == "check":
        return cmd_check()
    return cmd_full(args.dry_run)


if __name__ == "__main__":
    sys.exit(main())
