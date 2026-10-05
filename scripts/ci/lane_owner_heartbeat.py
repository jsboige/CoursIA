#!/usr/bin/env python3
r"""Battement du marqueur `.lane-owner` (#19010, suite #18494).

Le marqueur `.lane-owner` (convention #3895) est pose au spawn et porte
l'attribution de lane d'un worktree d'agent. `prune_merged_worktrees.py`
protege un worktree dont le marqueur -- ou, a defaut, le dossier -- est plus
jeune que `--activity-window-h` (defaut 6 h), via
`recent_activity_age_hours()` : le retrait est alors refuse avec
`reason=recent_activity:<age>h`.

Le trou mesure (#19010) : **rien ne rafraichit le marqueur pendant la vie de
l'agent**. Un agent vivant en LECTURE SEULE longue -- corrective-auditor de
plus de 6 h sur un worktree propre, sans commit ni ecriture dans le dossier --
voit son marqueur et son dossier vieillir au-dela de la fenetre et redevient
retirable, exactement comme un worktree abandonne.

Ce battement avance le mtime du marqueur, sans toucher a son contenu.

Trois bornes deliberees, pinnees par les tests :

1. **Il ne CREE jamais de marqueur.** Rafraichir un marqueur absent
   fabriquerait une attribution de lane que personne n'a posee : le worktree
   d'une autre lane, ou un worktree sans proprietaire, serait protege au nom
   d'une lane qui n'y travaille pas. Marqueur absent => refus (rc 2), aucune
   ecriture. Le marqueur reste un ACTE de revendication, pas un effet de bord.
2. **Le contenu ne bouge pas.** Seul le mtime est avance (`os.utime`) ; jamais
   une reecriture. Le marqueur porte une attribution (une lane), pas un
   horodatage : deux processus -- ou un agent et un outil -- peuvent le battre
   concurremment sans se corrompre, et le fichier reste byte-identique.
   Le battement ne recule jamais le mtime (marqueur deja plus frais : no-op),
   pour ne jamais AFFAIBLIR une protection en cours.
3. **Le battement doit MOURIR avec l'agent.** Il est TIRE par l'agent -- un
   appel `--once` dans sa propre boucle, ou `--loop` en fils de sa session,
   tue avec elle. Un demon detache qui survivrait a la session maintiendrait
   frais le marqueur d'un agent mort : la protection deviendrait permanente,
   ce que #18494 a precisement ecarte (« protection auto-expirante
   inchangee »). Ne jamais installer ce script en tache planifiee.

Le dossier du worktree n'est pas touche : le predicat du pruner prend le PLUS
RECENT des deux marqueurs (`.lane-owner`, dossier), donc rafraichir le seul
marqueur suffit, et une ecriture de dossier serait un effet de bord inutile.

Usage :
    python scripts/ci/lane_owner_heartbeat.py <worktree>            # un battement
    python scripts/ci/lane_owner_heartbeat.py <worktree> --status   # age, sans ecrire
    python scripts/ci/lane_owner_heartbeat.py <worktree> --loop 900 --beats 0
"""
from __future__ import annotations

import argparse
import os
import sys
import time
from pathlib import Path
from typing import Optional

MARKER_NAME = ".lane-owner"
# Intervalle minimal entre deux battements de la boucle : un battement par
# minute suffit largement pour une fenetre de plusieurs heures, et borner le
# plancher evite qu'un harnais fautif martele le disque.
MIN_LOOP_SECONDS = 30.0

EXIT_OK = 0
EXIT_REFUSED = 2
EXIT_USAGE = 3


def marker_path(worktree: str | os.PathLike[str]) -> Path:
    """Chemin du marqueur de lane d'un worktree (existence non garantie)."""
    return Path(worktree) / MARKER_NAME


def marker_age_hours(worktree: str | os.PathLike[str],
                     now: Optional[float] = None) -> Optional[float]:
    """Age en heures du mtime du marqueur, ou None si le marqueur n'existe pas."""
    p = marker_path(worktree)
    try:
        if not p.is_file():
            return None
        mtime = p.stat().st_mtime
    except OSError:
        return None
    return ((time.time() if now is None else now) - mtime) / 3600.0


def refresh(worktree: str | os.PathLike[str],
            now: Optional[float] = None) -> tuple[bool, str]:
    """Avance le mtime du marqueur sans toucher au contenu.

    Rend ``(ok, message)``. Refuse (``ok=False``) quand le marqueur est absent :
    ce script ne cree jamais d'attribution de lane. Quand le marqueur est deja
    plus frais que ``now``, ne fait rien (jamais de recul du mtime).
    """
    p = marker_path(worktree)
    try:
        st = p.stat()
    except OSError:
        return False, (
            f"marqueur absent ({p}) : ce battement ne cree pas d'attribution de "
            "lane -- le marqueur est pose au spawn (#3895), pas par le battement"
        )
    ts = time.time() if now is None else now
    if ts <= st.st_mtime:
        age_min = (st.st_mtime - ts) / 60.0
        return True, (
            f"marqueur deja plus frais que l'instant du battement "
            f"(+{age_min:.1f} min) : mtime inchange, aucun recul de protection"
        )
    # atime conserve, mtime avance : le contenu du marqueur n'est jamais relu
    # ni reecrit, donc deux battements concurrents ne peuvent pas le corrompre.
    os.utime(p, (st.st_atime, ts))
    return True, f"marqueur battu (mtime avance a {time.strftime('%H:%M:%S', time.localtime(ts))})"


def _status_line(worktree: str, window_h: float) -> tuple[int, str]:
    age = marker_age_hours(worktree)
    if age is None:
        return EXIT_REFUSED, f"marqueur absent ({marker_path(worktree)}) : aucun battement possible"
    verdict = "protege" if age < window_h else "fenetre ecoulee (retirable)"
    return EXIT_OK, f"marqueur age de {age:.2f} h (fenetre {window_h:g} h) : {verdict}"


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Battement du marqueur .lane-owner (#19010)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("worktree", help="racine du worktree portant .lane-owner")
    ap.add_argument("--status", action="store_true",
                    help="n'ecrit rien : rend l'age du marqueur et le verdict de fenetre")
    ap.add_argument("--loop", type=float, metavar="SECONDS", default=None,
                    help="bat en boucle (premier plan, tue avec la session) ; "
                         f"plancher {MIN_LOOP_SECONDS:g} s")
    ap.add_argument("--beats", type=int, default=0,
                    help="nombre de battements en mode --loop (0 = illimite)")
    ap.add_argument("--window-h", type=float, default=6.0,
                    help="fenetre du predicat du pruner, pour --status (defaut 6)")
    ap.add_argument("--quiet", action="store_true", help="n'imprimer que les refus")
    args = ap.parse_args(argv)

    if not Path(args.worktree).is_dir():
        print(f"battement: {args.worktree} n'est pas un dossier", file=sys.stderr)
        return EXIT_USAGE

    if args.status:
        code, line = _status_line(args.worktree, args.window_h)
        print(line)
        return code

    interval = args.loop
    if interval is not None and interval < MIN_LOOP_SECONDS:
        print(
            f"battement: --loop {interval:g} sous le plancher {MIN_LOOP_SECONDS:g} s -- "
            "la fenetre se compte en heures, un battement par minute suffit",
            file=sys.stderr,
        )
        return EXIT_USAGE

    def beat() -> int:
        ok, message = refresh(args.worktree)
        if not ok or not args.quiet:
            print(message)
        return EXIT_OK if ok else EXIT_REFUSED

    if interval is None:
        return beat()

    beats = 0
    try:
        while args.beats <= 0 or beats < args.beats:
            code = beat()
            if code != EXIT_OK:
                # Un refus (marqueur absent) n'est pas transitoire : sortir
                # plutot que battre un worktree qui n'a pas de proprietaire.
                return code
            beats += 1
            if args.beats > 0 and beats >= args.beats:
                break
            time.sleep(interval)
    except KeyboardInterrupt:
        return EXIT_OK
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
