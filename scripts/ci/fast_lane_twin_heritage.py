"""Specification du garde « heritage d'execution entre carnets jumeaux ».

Le corps du garde vit ici, a cote de son organe
(`scripts/notebook_tools/check_twin_execution_heritage.py`), et non dans le
registre `scripts/ci/fast_lane_registry.py` : le registre est un REGISTRE,
il porte l'appel ; le corps porte la specification. C'est le meme decoupage
que `scripts/ci/fast_lane_commenters.py` (module importe par le registre) et
que `scripts/ci/nit_rapport.py` (module extrait de l'organe B.0) : un
registre qui porte les corps cesse d'etre un registre, et son plafond de
taille cesse de borner quoi que ce soit.

La classe `Guard` et la source canonique des gardes natifs ne sont pas
importes ici (ils vivaient dans le registre : l'import serait circulaire) :
ils sont recus en parametres, comme les collaborateurs d'un organe.
"""
from __future__ import annotations


def twin_execution_heritage_guard(guard_cls, fast_lane_native: str):
    """Construit le garde `twin-execution-heritage-guard`.

    `guard_cls` est la classe `Guard` du registre ; `fast_lane_native` est la
    source canonique des gardes natifs (aucun workflow d'origine).
    """
    return guard_cls(
        # Heritage d'execution entre carnets jumeaux : l'artefact COPIE
        # (#27992, decouvert sur la PR #27872). Un carnet qui porte les
        # horodatages d'execution d'un autre carnet de sa famille n'a pas ete
        # execute : il a ete copie, et ses sorties ne sont pas les siennes.
        # Le verdict est un DELTA borne au diff (seules les familles touchees
        # par la PR sont examinees) : un rouge ne peut pas heriter de `main`.
        name="twin-execution-heritage-guard",
        source=fast_lane_native,
        paths=[
            "scripts/notebook_tools/twin_pairs.d/**",
            "scripts/notebook_tools/rust_conformance.d/**",
            "**/*.ipynb",
            "scripts/notebook_tools/check_twin_execution_heritage.py",
            "scripts/ci/fast_lane.py",
            "scripts/ci/fast_lane_registry.py",
        ],
        argv=[
            "python", "scripts/notebook_tools/check_twin_execution_heritage.py",
            "--diff", "{base_ref}...HEAD", "--gate",
        ],
        blocking=True,
        absorbed=True,
        needs_base=True,
        diff_bounded=True,
        warn_rc=(2,),
    )
