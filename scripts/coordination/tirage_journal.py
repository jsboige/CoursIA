#!/usr/bin/env python3
r"""Journal des tirages du picker -- geste 5 de #18203.

Pourquoi ce module existe
-------------------------
Le geste 5 de #18203 constate : *"\`Proposee puis ecantee\` ne se mesure pas.
Le tirage ne laisse aucune trace : une issue proposee a dix lanes et ecantee
dix fois ne se distingue pas d'une issue jamais proposee."* La solution
envisagee est un journal append-only qui consigne, a chaque tirage :

- la lane qui a tire (machine:workspace),
- le timestamp serveur (UTC ISO-8601 Z),
- la liste des candidats consideres (numeros d'issue + urn),
- le grain retenu (numero d'issue + urn + tier/genre si declares),
- l'identifiant unique du tirage (``draw_id``, UUID4 court),
- le mode du picker (``belt`` / pondere / ``--admissible <N>`` / etc.).

Le module est **deliberement separe** de ``scripts/pick_idle_grain.py`` (lane
proprietaire : po-2024:CoursIA-2) : il offre une API stable, importable par
le picker **quand** po-2024 decide de l'integrer. L'integration effective
(ajout d'un appel ``journal.log_tirage(...)`` dans ``main()``) reste du
ressort de la lane proprietaire ; en attendant, le module est utilisable
manuellement (CLI) et testable seuellement.

Format de stockage
------------------
Par defaut, JSONL append-only : un ``TirageRecord`` par ligne, sous
``%LOCALAPPDATA%\CoursIA\tirage_journal\journal.jsonl`` -- le meme state dir
machine que les autres organes de coordination (``merge_ready``,
``prune_task``, ``lean_exec``) -- surchargeable par ``TIRAGE_JOURNAL_PATH``.
Le chemin est resolu **a chaque appel** par ``default_journal_path()``,
jamais fige a l'import : une surcharge d'environnement posee apres l'import
est honoree. Le fichier est cree au premier ecrit, jamais ecrase en bloc.
Une rotation externe (date / taille) reste a mettre en place : ce module
consigne, il ne fait pas de politique de retention.

Concurrence -- un verrou FICHIER interprocessus, pas un verrou d'instance
------------------------------------------------------------------------
Le journal est ecrit par plusieurs lanes en parallele, donc par plusieurs
**processus**. Un ``threading.Lock`` ne couvre pas ce cas : il appartient a
une instance, et deux instances -- a fortiori deux processus -- n'en
partagent aucun.

Le seul mecanisme qui serialise reellement est un verrou du systeme pose sur
un fichier compagnon ``<journal>.lock`` : ``msvcrt.locking`` sous Windows,
``fcntl.flock`` sous POSIX (le meme choix que ``AdmissionLock`` dans
``scripts/lean/lean_exec.py``). Il est pris en non-bloquant avec reprise
bornee, donc ni blocage indefini ni interblocage. La ligne complete -- JSON
**et** son saut de ligne -- part en **un seul** ``write()`` sous ce verrou :
il n'existe aucune fenetre ou deux processus pourraient s'entrelacer.

API publique
------------
- ``TirageRecord`` : dataclass figee representant un tirage.
- ``Journal`` : classe d'ecriture. Constructeur prend le chemin du journal.
- ``log_tirage(...)`` : helper module-level qui ouvre un ``Journal`` et
  consigne un ``TirageRecord``. Il emprunte la meme voie verrouillee.
- ``read_journal(path)`` : helper de lecture (utilise par les tests et par
  un futur organe d'audit).
- ``default_journal_path()`` : resolution du chemin par defaut.
- CLI : ``python scripts/coordination/tirage_journal.py --lane <m:w> \
  --candidates 123,456 --retained 123 --urn grain --draw-id <uuid>``.

Anti-patterns attrapes
----------------------
1. Le picker est appele depuis plusieurs lanes en parallele. Un append en
   mode texte n'est **pas** atomique au-dela de ``PIPE_BUF`` (4096 o) -- et
   ``PIPE_BUF`` ne concerne de toute facon que les pipes, pas les fichiers
   texte ordinaires. C'est le verrou fichier de ``Journal.log`` qui couvre
   le cas, pas la taille de la ligne.
2. Le journal **ne remplace pas** le dashboard RooSync : il consigne des
   tirages, le dashboard consigne l'etat de la lane. Les deux sont
   complementaires.
3. Le module n'ecrit **rien** sous le clone (``D:\CoursIA-2``) : le chemin
   par defaut vit dans le state dir machine, hors depot.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import os
import sys
import time
import uuid
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Iterator, Sequence


# ---------------------------------------------------------------------------
# Verrou fichier interprocessus (msvcrt cote Windows, fcntl cote POSIX)
# ---------------------------------------------------------------------------

if os.name == "nt":
    import msvcrt

    def _try_lock(fh) -> bool:
        try:
            fh.seek(0)
            msvcrt.locking(fh.fileno(), msvcrt.LK_NBLCK, 1)
            return True
        except OSError:
            return False

    def _unlock(fh) -> None:
        try:
            fh.seek(0)
            msvcrt.locking(fh.fileno(), msvcrt.LK_UNLCK, 1)
        except OSError:
            pass

else:
    import fcntl

    def _try_lock(fh) -> bool:
        try:
            fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            return True
        except OSError:
            return False

    def _unlock(fh) -> None:
        try:
            fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
        except OSError:
            pass


LOCK_TIMEOUT_S = 30.0


@contextmanager
def file_lock(lock_path: Path, timeout_s: float = LOCK_TIMEOUT_S) -> Iterator[None]:
    """Verrou exclusif interprocessus sur ``lock_path``.

    Ouvre le fichier compagnon, tente le verrou du systeme en non-bloquant et
    reprend tant qu'il est tenu, jusqu'a ``timeout_s``. Le verrou est rendu au
    ``finally``, y compris sur exception dans la section critique -- c'est ce
    qui garantit qu'un corps qui echoue ne laisse pas le journal verrouille.
    """
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    fh = open(lock_path, "a+b")
    deadline = time.monotonic() + timeout_s
    try:
        while not _try_lock(fh):
            if time.monotonic() >= deadline:
                raise TimeoutError(
                    f"verrou du journal non obtenu en {timeout_s}s : {lock_path}"
                )
            time.sleep(0.02)
        yield
    finally:
        _unlock(fh)
        fh.close()


# ---------------------------------------------------------------------------
# Emplacement du journal
# ---------------------------------------------------------------------------

def _state_base() -> Path:
    """Racine d'etat de la machine, hors depot.

    Meme resolution que ``scripts/lean/lean_exec.py`` : ``LOCALAPPDATA``
    d'abord (Windows), puis ``XDG_STATE_HOME`` (POSIX), puis ``~/.local/state``.
    """
    local = os.environ.get("LOCALAPPDATA")
    if local:
        return Path(local)
    xdg = os.environ.get("XDG_STATE_HOME")
    if xdg:
        return Path(xdg)
    return Path.home() / ".local" / "state"


def default_journal_path() -> Path:
    """Chemin par defaut du journal, resolu a l'appel.

    ``TIRAGE_JOURNAL_PATH`` prime s'il est pose ; sinon le journal vit sous le
    state dir machine, a cote des autres journaux de coordination
    (``<state>/CoursIA/tirage_journal/journal.jsonl``). Jamais sous le clone :
    un journal committe par accident serait un artefact de mesure dans l'arbre
    de travail.
    """
    override = os.environ.get("TIRAGE_JOURNAL_PATH")
    if override:
        return Path(override)
    return _state_base() / "CoursIA" / "tirage_journal" / "journal.jsonl"


# ---------------------------------------------------------------------------
# Modele
# ---------------------------------------------------------------------------

@dataclasses.dataclass(frozen=True)
class TirageRecord:
    """Un tirage, vu par le journal.

    Champs obligatoires : ``lane``, ``candidates``, ``retained``, ``urn``,
    ``draw_id``, ``ts``. Tous sont serialises en JSON par ``to_jsonl``.
    Le champ ``mode`` est libre (exemples : ``"belt"``, ``"weighted"``,
    ``"admissible"``).
    """

    lane: str
    candidates: list[int]
    retained: int | None
    urn: str
    draw_id: str
    ts: str
    mode: str = "belt"
    extras: dict[str, object] | None = None

    def to_jsonl(self) -> str:
        d = dataclasses.asdict(self)
        # JSONL : pas d'indentation, clefs triees pour reproductibilite.
        line = json.dumps(d, sort_keys=True, ensure_ascii=False)
        # Defense en profondeur : un newline reel (non escape) dans la ligne
        # tronquerait le journal. ``json.dumps`` escape toujours les
        # newlines, donc cette garde ne devrait jamais tirer -- mais elle
        # protege contre un ``extras`` qui contournerait le serialiseur.
        if "\n" in line or "\r" in line:
            raise ValueError(
                "TirageRecord serialise contient un newline (refus)"
            )
        return line

    @classmethod
    def from_jsonl(cls, line: str) -> "TirageRecord":
        d = json.loads(line)
        return cls(**d)

    @classmethod
    def new(
        cls,
        *,
        lane: str,
        candidates: Iterable[int],
        retained: int | None,
        urn: str,
        mode: str = "belt",
        draw_id: str | None = None,
        ts: str | None = None,
        extras: dict[str, object] | None = None,
    ) -> "TirageRecord":
        return cls(
            lane=lane,
            candidates=[int(c) for c in candidates],
            retained=(int(retained) if retained is not None else None),
            urn=str(urn),
            draw_id=str(draw_id or uuid.uuid4().hex[:12]),
            ts=str(ts or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")),
            mode=str(mode),
            extras=extras,
        )


# ---------------------------------------------------------------------------
# Ecriture / lecture
# ---------------------------------------------------------------------------

class Journal:
    """Ecriture append-only sur un fichier JSONL, sous verrou interprocessus.

    Aucun verrou n'est tenu par l'instance : chaque appel a ``log`` ouvre son
    propre descripteur sur ``<journal>.lock``, prend le verrou du systeme,
    ecrit, puis le rend. Deux instances -- et deux processus -- se
    serialisent donc, ce qu'un verrou d'instance ne ferait pas.
    """

    def __init__(self, path: Path | str | None = None) -> None:
        self.path = Path(path) if path is not None else default_journal_path()
        self.path.parent.mkdir(parents=True, exist_ok=True)

    @property
    def lock_path(self) -> Path:
        """Fichier compagnon qui porte le verrou (jamais le journal lui-meme)."""
        return Path(str(self.path) + ".lock")

    def log(self, record: TirageRecord) -> None:
        line = record.to_jsonl()
        if "\n" in line or "\r" in line:
            raise ValueError("TirageRecord serialise contient un newline (refus)")
        # UN seul write() : la ligne ET son saut de ligne partent ensemble sous
        # le verrou. Deux write() successifs laisseraient une fenetre ou un
        # autre processus inserer sa ligne entre les deux.
        payload = line + "\n"
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with file_lock(self.lock_path):
            with self.path.open("a", encoding="utf-8", newline="\n") as f:
                f.write(payload)


def log_tirage(
    *,
    lane: str,
    candidates: Iterable[int],
    retained: int | None,
    urn: str,
    mode: str = "belt",
    draw_id: str | None = None,
    path: Path | str | None = None,
) -> TirageRecord:
    """Helper module-level : consigne un tirage dans le journal.

    Emprunte exactement la meme voie que ``Journal.log``, verrou fichier
    interprocessus compris -- un helper qui ecrirait directement rouvrirait
    le defaut que ce verrou ferme.
    """
    record = TirageRecord.new(
        lane=lane,
        candidates=candidates,
        retained=retained,
        urn=urn,
        mode=mode,
        draw_id=draw_id,
    )
    Journal(path).log(record)
    return record


def read_journal(path: Path | str | None = None) -> list[TirageRecord]:
    """Lit integralement le journal. Utilise par les tests et l'audit futur."""
    p = Path(path) if path is not None else default_journal_path()
    if not p.exists():
        return []
    out: list[TirageRecord] = []
    for line in p.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        out.append(TirageRecord.from_jsonl(line))
    return out


def _build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="tirage_journal",
        description="Consigne un tirage du picker dans le journal JSONL.",
    )
    p.add_argument("--lane", required=True, help="lane au format machine:workspace")
    p.add_argument(
        "--candidates",
        required=True,
        help="liste separee par des virgules (numeros d'issue)",
    )
    p.add_argument(
        "--retained",
        type=int,
        default=None,
        help="numero d'issue retenu (ou absent si aucun)",
    )
    p.add_argument("--urn", required=True, help="urne du tirage (grain, umbrella, ...)")
    p.add_argument("--mode", default="belt", help="mode du picker (belt, weighted, ...)")
    p.add_argument("--draw-id", default=None, help="identifiant du tirage (defaut UUID)")
    p.add_argument(
        "--path",
        default=None,
        help="chemin du journal (defaut : state dir machine, cf default_journal_path)",
    )
    return p


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_argparser().parse_args(argv)
    candidates = [int(x) for x in args.candidates.split(",") if x.strip()]
    record = log_tirage(
        lane=args.lane,
        candidates=candidates,
        retained=args.retained,
        urn=args.urn,
        mode=args.mode,
        draw_id=args.draw_id,
        path=args.path,
    )
    print(record.to_jsonl())
    return 0


if __name__ == "__main__":
    sys.exit(main())
