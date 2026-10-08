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

Le module est **delibrement separe** de ``scripts/pick_idle_grain.py`` (lane
proprietaire : po-2024:CoursIA-2) : il offre une API stable, importable par
le picker **quand** po-2024 decide de l'integrer. L'integration effective
(ajout d'un appel ``journal.log_tirage(...)`` dans ``main()``) reste du
ressort de la lane proprietaire ; en attendant, le module est utilisable
manuellement (CLI) et testable seuellement.

Format de stockage
------------------
Par defaut, JSONL append-only : un ``TirageRecord`` par ligne, dans
``D:\Dev\tirage_journal.jsonl`` (configurable via ``TIRAGE_JOURNAL_PATH``).
Le fichier est cree au premier ecrit, jamais ecrase en bloc. Une rotation
externe (date / taille) reste a mettre en place : ce module consigne, il
ne fait pas de politique de retention.

API publique
------------
- ``TirageRecord`` : dataclass figee representant un tirage.
- ``Journal`` : classe d'ecriture. Constructeur prend le chemin du journal.
- ``log_tirage(...)`` : helper module-level qui ouvre un ``Journal`` sur le
  chemin par defaut et consigne un ``TirageRecord``.
- ``read_journal(path)`` : helper de lecture (utilise par les tests et par
  un futur organe d'audit).
- CLI : ``python scripts/coordination/tirage_journal.py --lane <m:w> \
  --candidates 123,456 --retained 123 --urn grain --draw-id <uuid>``.

Anti-patterns attrapes
----------------------
1. Le picker est appele depuis plusieurs lanes en parallele. ``append`` en
   mode texte (``open(..., "a", encoding="utf-8")``) est line-atomic sur
   Windows tant que la ligne tient dans le buffer (``PIPE_BUF`` 4096 o
   Linux / ``_O_APPEND`` Windows). Au-dela, l'atomicite n'est plus
   garantie : un lock applicatif (``Journal._lock``) couvre le cas.
2. Le journal **ne remplace pas** le dashboard RooSync : il consigne des
   tirages, le dashboard consigne l'etat de la lane. Les deux sont
   complementaires.
3. Le module n'ecrit **rien** sous ``D:\CoursIA-2`` (depot). Le chemin par
   defaut est ``D:\Dev\tirage_journal.jsonl``, hors depot, comme les autres
   artefacts de mesure (``D:\Dev\probe15099_runs``, etc.).
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import os
import sys
import threading
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Sequence


DEFAULT_PATH = Path(
    os.environ.get("TIRAGE_JOURNAL_PATH", r"D:\Dev\tirage_journal.jsonl")
)


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


class Journal:
    """Ecriture append-only sur un fichier JSONL, avec lock applicatif."""

    def __init__(self, path: Path | str = DEFAULT_PATH) -> None:
        self.path = Path(path)
        self._lock = threading.Lock()
        self.path.parent.mkdir(parents=True, exist_ok=True)

    def log(self, record: TirageRecord) -> None:
        line = record.to_jsonl()
        if "\n" in line:
            raise ValueError("TirageRecord serialise contient un newline (refus)")
        with self._lock:
            with self.path.open("a", encoding="utf-8", newline="\n") as f:
                f.write(line)
                f.write("\n")


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
    """Helper module-level : consigne un tirage dans le journal par defaut."""
    record = TirageRecord.new(
        lane=lane,
        candidates=candidates,
        retained=retained,
        urn=urn,
        mode=mode,
        draw_id=draw_id,
    )
    Journal(path or DEFAULT_PATH).log(record)
    return record


def read_journal(path: Path | str = DEFAULT_PATH) -> list[TirageRecord]:
    """Lit integralement le journal. Utilise par les tests et l'audit futur."""
    p = Path(path)
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
        help="chemin du journal (defaut D:\\Dev\\tirage_journal.jsonl)",
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
