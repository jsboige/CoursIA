"""Perimetre local de la voie rapide (#27012, point 2) -- plan et passe ciblee.

Mesures a l'origine (tour de table du 16/11, reprises en #27012) :

  - lane ``myia-po-2027:CoursIA`` : 25 min par ``fast_lane.py --dry-run`` ; la
    latence « correctif -> push » passe de 10 a plus de 40 min ;
  - lane ``myia-po-2024:CoursIA`` : 40 gardes joues a l'aveugle pour 10 min de
    correctif.

Les deux demandes disent la meme chose sous deux noms : ne payer que les
gardes concernes par les fichiers qu'on vient de toucher. La suite rapide
selectionne deja ses gardes par `paths` (`fast_lane.guard_applies`), mais elle
n offers aucun moyen de RESTREINDRE cette selection a un sous-ensemble de
fichiers, ni de voir le plan d'une passe sans l'executer.

Ce module ne reecrit pas la selection du moteur : il pilote
``fast_lane.main`` en se branchant sur trois coutures du module, sans
modifier ``fast_lane.py`` (ce fichier est touche par des PRs ouvertes
d'autres lanes : #28769 et #28126).

  - ``changed_files`` : la liste des fichiers modifies, restreinte aux chemins
    demandes ;
  - ``run_argv`` / ``run_iter`` : enregistres (mode plan) ou chronometres
    (mode passe) ;
  - ``emit_check_run`` : neutralise -- **aucune publication n'est possible**,
    par construction.

La selection reste celle du moteur : le plan rendu est celui que la CI
produirait pour ce sous-ensemble de fichiers. Un outil qui recopierait la
chaine des tranches deriverait a la tranche suivante (57 tranches au 28/11) ;
ici la chaine n'est jamais ecrite.

Le module rend aussi le DEFAUT que la chaine du moteur contient : une garde
listee deux fois est executee deux fois par passe. Mesure du 28/11 (branche
`fix/23384-canon-3-13-sk8-mcp`, 2 fichiers modifies) : le garde « Prose-numbers
vs outputs ratchet » s'execute deux fois, 45,7 s puis 41,2 s -- 87 s de
moteur dont environ 41 s dupliques.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import re
import sys
import time
from pathlib import Path

CI_DIR = Path(__file__).resolve().parent
REPO_ROOT = CI_DIR.parents[1]
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import fast_lane  # noqa: E402
import fast_lane_registry  # noqa: E402
from fast_lane_registry import Guard  # noqa: E402

# Sorties du moteur qu'on relit.
_EVALUATED_RE = re.compile(
    r"^\[fast-lane\] (?:phase \d(?: \(HEAD\))?|effets) "
    r"(?P<name>.+?)(?: \(iter sur \d+ fichier\(s\)\))? : (?P<tail>.*)$"
)
_OUT_RE = re.compile(
    r"^\[fast-lane\] hors perimetre \(filtre paths\) : (?P<name>.+)$"
)
_EXIT_RE = re.compile(r"exit (?P<rc>-?\d+)")


def registry_guards() -> list[Guard]:
    """Toutes les gardes exportees par le registre, sans recopier la chaine.

    Le moteur enchaîne ses tranches dans ``fast_lane.main`` ; recopier cette
    chaine ici deriverait a la tranche suivante. On collecte donc les
    collections exportees par le registre, sans les nommer une a une.
    """
    out: list[Guard] = []
    for name, value in vars(fast_lane_registry).items():
        if name.startswith("_"):
            continue
        if (isinstance(value, (list, tuple)) and value
                and all(isinstance(item, Guard) for item in value)):
            out.extend(value)
    return out


def restrict_changed(changed: list[str], patterns: list[str]) -> list[str]:
    """Fichiers modifies qui repondent a l'un des motifs demandes.

    La semantique des motifs est celle du moteur (``fast_lane.path_matches``) :
    un chemin exact matche, un motif GitHub (`**/`, `/ ** /`) aussi.
    """
    if not patterns:
        return list(changed)
    return [f for f in changed
            if any(fast_lane.path_matches(f, p) for p in patterns)]


def parse_engine_output(text: str) -> tuple[list[tuple[str, int | None]], list[str]]:
    """Relit la sortie du moteur : gardes evaluees (nom, rc) et hors perimetre.

    Le rc est ``None`` quand la ligne ne porte pas de code de sortie (scan
    capture en HEAD, delta non execute) : le verdict n'est pas connu, il ne
    doit pas etre lu comme un zero.
    """
    evaluated: list[tuple[str, int | None]] = []
    out_of_perimeter: list[str] = []
    for line in text.splitlines():
        match = _EVALUATED_RE.match(line)
        if match:
            exit_match = _EXIT_RE.search(match.group("tail"))
            rc = int(exit_match.group("rc")) if exit_match else None
            evaluated.append((match.group("name"), rc))
            continue
        out_match = _OUT_RE.match(line)
        if out_match:
            out_of_perimeter.append(out_match.group("name"))
    return evaluated, out_of_perimeter


def _argv_key(argv: list[str] | None) -> tuple[str, ...]:
    return tuple(argv or ())


def _timed(real, durations: dict[tuple[str, ...], float]):
    """Enveloppe une fonction du moteur et cumule sa duree par argv."""
    def wrapper(*args, **kwargs):
        argv = args[0] if args else kwargs.get("argv")
        started = time.time()
        try:
            return real(*args, **kwargs)
        finally:
            key = _argv_key(argv)
            durations[key] = durations.get(key, 0.0) + (time.time() - started)
    return wrapper


def _guard_names_by_argv() -> dict[tuple[str, ...], str]:
    """argv (gabarit) -> nom de garde, pour attribuer les durees."""
    names: dict[tuple[str, ...], str] = {}
    for guard in registry_guards():
        for argv in (guard.argv, guard.pre_argv):
            if argv:
                names.setdefault(_argv_key(argv), guard.name)
    return names


def scoped_pass(paths: list[str], base_ref: str,
                execute: bool) -> dict[str, object]:
    """Passe ciblee sur les seuls fichiers demandes.

    Rend un rapport : fichiers retenus, gardes evaluees, gardes hors
    perimetre, gardes executees plusieurs fois, durees, rc du moteur.

    Le moteur tourne toujours en `--dry-run` et `emit_check_run` est
    neutralise : cet outil ne publie rien, il constate.
    """
    originals = (fast_lane.changed_files, fast_lane.run_argv,
                 fast_lane.run_iter, fast_lane.emit_check_run)
    durations: dict[tuple[str, ...], float] = {}
    buffer = io.StringIO()
    try:
        changed = originals[0](base_ref)
        kept = restrict_changed(changed, paths)
        if not kept:
            raise SystemExit(
                "[fast-lane][scope] aucun fichier modifie ne repond aux "
                f"chemins demandes ({', '.join(paths)}) ; "
                f"{len(changed)} fichier(s) modifie(s) contre {base_ref}. "
                "Aucun garde n'a ete selectionne."
            )
        fast_lane.changed_files = lambda _base: list(kept)
        fast_lane.emit_check_run = lambda *a, **k: False
        if execute:
            fast_lane.run_argv = _timed(originals[1], durations)
            fast_lane.run_iter = _timed(originals[2], durations)
        else:
            fast_lane.run_argv = lambda argv, ctx: (0, "")
            fast_lane.run_iter = (lambda argv, files, ctx, warn_rc=(),
                                   fail_on_all_warn=False: (0, ""))
        started = time.time()
        with contextlib.redirect_stdout(buffer):
            rc = fast_lane.main(["--base-ref", base_ref, "--dry-run"])
        elapsed = time.time() - started
    finally:
        (fast_lane.changed_files, fast_lane.run_argv,
         fast_lane.run_iter, fast_lane.emit_check_run) = originals

    evaluated, out_of_perimeter = parse_engine_output(buffer.getvalue())
    counts: dict[str, int] = {}
    for name, _rc in evaluated:
        counts[name] = counts.get(name, 0) + 1
    names_by_argv = _guard_names_by_argv()
    reported: dict[str, float] = {}
    for key, seconds in durations.items():
        reported[names_by_argv.get(key, "(garde non identifiee)")] = (
            reported.get(names_by_argv.get(key, "(garde non identifiee)"), 0.0)
            + seconds)
    return {
        "mode": "passe" if execute else "plan",
        "base_ref": base_ref,
        "paths": paths,
        "files_total": len(changed),
        "files_kept": len(kept),
        "files_dropped": len(changed) - len(kept),
        "guards_evaluated": [{"name": n, "rc": r} for n, r in evaluated],
        "guards_out_of_perimeter": out_of_perimeter,
        "duplicated_guards": sorted(n for n, c in counts.items() if c > 1),
        "durations_s": {k: round(v, 2) for k, v in sorted(
            reported.items(), key=lambda kv: -kv[1])},
        "engine_rc": rc,
        "seconds": round(elapsed, 2),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Perimetre local de la voie rapide (#27012, point 2)")
    parser.add_argument("--paths", required=True,
                        help="chemins ou motifs (separes par des virgules) "
                             "a considerer comme modifies")
    parser.add_argument("--base-ref",
                        default=os.environ.get("FAST_LANE_BASE", "origin/main"))
    parser.add_argument("--run", action="store_true",
                        help="executer la passe ciblee (dry-run : rien n'est "
                             "publie, aucun check-run n'est ecrit)")
    parser.add_argument("--json", action="store_true",
                        help="rendre le rapport en JSON")
    args = parser.parse_args(argv)

    paths = [p.strip() for p in args.paths.split(",") if p.strip()]
    report = scoped_pass(paths, args.base_ref, args.run)

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
        return 0

    print(f"[scope] {report['files_kept']} fichier(s) retenu(s) sur "
          f"{report['files_total']} ({report['files_dropped']} hors perimetre "
          f"demande) contre {report['base_ref']}")
    guards = report["guards_evaluated"]
    print(f"[scope] {len(guards)} garde(s) concernee(s) -- "
          f"{len(report['guards_out_of_perimeter'])} hors perimetre")
    for guard in guards:
        rc = guard["rc"]
        state = "rc inconnu" if rc is None else f"exit {rc}"
        duration = report["durations_s"].get(guard["name"])
        if duration is not None:
            state += f", {duration:.1f}s"
        print(f"  - {guard['name']} ({state})")
    duplicated = report["duplicated_guards"]
    if duplicated:
        print("[scope] garde(s) executee(s) plusieurs fois par la chaine du "
              "moteur : " + ", ".join(duplicated))
    print(f"[scope] mode {report['mode']}, {report['seconds']}s, rc moteur "
          f"{report['engine_rc']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
