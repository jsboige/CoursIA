"""Preparation de calibration pour les lanceurs de baseline (#1453).

Port de la mecanique que #13907 a posee sur les **deux** lanceurs
``run_prover_bg.py`` (racine ``agent_tests/`` et paquet ``prover/``), et qui
n'avait jamais atteint ``baselines/run_baselines.py``.

Un DEMO declarant ``sorry_type: sorry_replacement`` cible un scaffolding
committe **avec sa preuve approuvee** : cette preuve est la verite terrain que
le prouveur doit reproduire, pas un etat a conserver. Sans cette preparation,
le pre-vol des deux prouveurs (``provers.py``, ``already_solved``) compte
**0 sorry reel** sur le fichier cible et rend un faux vert en quelques
secondes — ``success=True``, ``iterations=0``, ``attempts=0``, sans jamais
lancer un agent ni compiler. C'est exactement le defaut mesure par #1453 sur
les DEMOS 39-52, et qui reste vivant sur le chemin des baselines.

Les octets d'origine sont restaures dans ``finally`` — E/S binaires, aucune
traduction de fin de ligne — donc la restauration survit a toute exception, y
compris une annulation. Un echec de ``stub_theorem_proof`` (declaration
inconnue, pas de ``:=``) leve **avant** toute ecriture : une passe de
calibration doit echouer bruyamment plutot que stubber la mauvaise region.
"""

from __future__ import annotations

import contextlib
from pathlib import Path
from typing import Iterator

from prover.lean_utils import count_real_sorries, stub_theorem_proof


def flag_false_green(prepared: dict, result: dict) -> bool:
    """Detecte un ``already_solved`` sur une cible de calibration stubulee.

    Le scaffolding de calibration est committe AVEC sa preuve approuvee : si le
    pre-vol rend ``already_solved`` alors que la cible vient d'etre stubulee, la
    preparation n'a pas atteint le prouveur et le resultat est un **faux vert**
    — ``success=True`` sur du travail non fait, le defaut que #13907 a ferme sur
    les lanceurs BG. Le rendre visible et refuser de le compter comme un succes
    est le seul comportement sur : un harnais qui rapporte vert sur du travail
    non fait est la classe de defaut la plus couteuse de cet Epic.
    """
    if not (prepared.get("calibration_stubbed") and result.get("already_solved")):
        return False
    print(f"[CALIBRATION_DEFECT] {prepared.get('name')}: pre-flight reports "
          f"already_solved on a stubbed calibration target -- the stub did not "
          f"reach the prover (#1453/#13907)")
    return True


def _peek_sorry_count(filepath: str) -> int:
    """Nombre de ``sorry`` reels du fichier cible, sans lever s'il est absent.

    Un chemin non lisible vaut ``-1`` : different de ``0``, il **desactive**
    la preparation, et la passe suit son cours normal. Le pre-vol tranchera.
    """
    try:
        return count_real_sorries(Path(filepath).read_text(encoding="utf-8"))
    except OSError:
        return -1


@contextlib.contextmanager
def calibration_stub(demo: dict) -> Iterator[dict]:
    """Rend une copie de ``demo`` dont la cible de calibration est stubulee.

    La copie porte ``calibration_stubbed`` (le stub a-t-il ete ecrit) et, quand
    il l'est, ``pre_stub_sorry_count`` : le compte **committe** du scaffolding,
    que les gardes du prouveur comparent a l'enonce d'origine plutot qu'au
    fichier stubbe (#17433). Copie et non mutation : les entrees ``DEMOS`` sont
    des dictionnaires de module partages entre les passes.

    Sans effet quand le DEMO ne declare pas ``sorry_replacement``, quand il ne
    nomme ni fichier ni theoreme, ou quand le fichier porte deja un ``sorry``
    reel (il n'y a alors rien a preparer : la cible a bien un trou a prouver).
    """
    prepared = {**demo, "calibration_stubbed": False}

    filepath = demo.get("file") or ""
    theorem_name = demo.get("theorem_name") or ""
    if demo.get("sorry_type") != "sorry_replacement" or not filepath or not theorem_name:
        yield prepared
        return
    if _peek_sorry_count(filepath) != 0:
        yield prepared
        return

    target_path = Path(filepath)
    original_bytes = target_path.read_bytes()
    committed_sorry = count_real_sorries(original_bytes.decode("utf-8"))
    stubbed = stub_theorem_proof(original_bytes.decode("utf-8"), theorem_name)
    target_path.write_bytes(stubbed.encode("utf-8"))
    print(
        f"[CALIBRATION_STUB] theorem={theorem_name} line={demo.get('line')} "
        f"- approved proof stubbed to sorry, original restored on exit"
    )
    try:
        yield {**prepared,
               "calibration_stubbed": True,
               "pre_stub_sorry_count": committed_sorry}
    finally:
        target_path.write_bytes(original_bytes)
