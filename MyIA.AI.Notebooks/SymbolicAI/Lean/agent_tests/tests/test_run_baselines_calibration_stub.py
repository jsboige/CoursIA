"""Preparation de calibration du lanceur de baselines (#1453).

#13907 a pose le stub de calibration sur les **deux** lanceurs
``run_prover_bg.py`` ; ``baselines/run_baselines.py`` ne l'a jamais recu. Sur un
DEMO declarant ``sorry_type: sorry_replacement`` — scaffolding committe AVEC sa
preuve approuvee, donc 0 ``sorry`` reel — le pre-vol de ``provers.py`` rend
``already_solved`` en quelques secondes : ``success=True``, ``iterations=0``,
aucun agent, aucune compilation. Un faux vert, mesure firsthand sur
``conway_lean/Conway/Angel.lean`` (0 sorry) et le DEMO 44.

Ces tests verrouillent la preparation elle-meme : stub ecrit, octets restaures
(y compris sur exception), pas de stub quand il n'y a rien a preparer, et
signalement du faux vert. Le cablage complet (stub -> run -> restore) reste
couvert par la ligne ``[CALIBRATION_STUB]`` des lanceurs BG.

Fixtures EMBEDDED : lire ``conway_lean/Conway/*.lean`` en echantillon ferait
courir le test contre une passe de prouveur qui stubbe le meme fichier en place
(la course mesuree dans ``test_calibration_stub.py``).
"""

import pytest

from prover.baselines.calibration_stub import calibration_stub, flag_false_green
from prover.lean_utils import count_real_sorries

# Forme d'un scaffolding de calibration : une ancre prouvee, puis la cible que
# le harnais doit reproduire, committée avec sa preuve approuvee.
LEAN_SOURCE = """\
namespace Calibration

/-- Ancre prouvee. -/
theorem anchor_add_zero (n : Nat) : n + 0 = n := rfl

/-- Cible de calibration : elle porte sa preuve approuvee dans le depot. -/
theorem card_pair : (Finset.univ : Finset (Fin 2)).card = 2 := by
  decide

/-- Voisine, avec sa docstring : le stub ne doit pas l'absorber. -/
theorem sibling (n : Nat) : n = n := rfl

end Calibration
"""


def _write(tmp_path, content=LEAN_SOURCE):
    target = tmp_path / "Calibration" / "Fixture.lean"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(content.encode("utf-8"))
    return target


def _demo(target, **overrides):
    demo = {
        "name": "CALIBRATION_FIXTURE",
        "file": str(target),
        "line": 8,
        "sorry_type": "sorry_replacement",
        "theorem_name": "card_pair",
    }
    demo.update(overrides)
    return demo


def test_fixture_starts_without_real_sorry():
    assert count_real_sorries(LEAN_SOURCE) == 0


def test_stub_exposes_the_target_to_the_preflight(tmp_path):
    target = _write(tmp_path)
    original_bytes = target.read_bytes()

    with calibration_stub(_demo(target)) as prepared:
        assert prepared["calibration_stubbed"] is True
        assert prepared["pre_stub_sorry_count"] == 0
        # Le pre-vol ne peut plus rendre `already_solved` : il voit un trou.
        assert count_real_sorries(target.read_text(encoding="utf-8")) == 1

    assert target.read_bytes() == original_bytes


def test_original_demo_is_not_mutated(tmp_path):
    target = _write(tmp_path)
    demo = _demo(target)
    snapshot = dict(demo)

    with calibration_stub(demo):
        pass

    assert demo == snapshot


def test_stub_is_restored_when_the_run_raises(tmp_path):
    target = _write(tmp_path)
    original_bytes = target.read_bytes()

    with pytest.raises(RuntimeError):
        with calibration_stub(_demo(target)):
            raise RuntimeError("prover blew up mid-run")

    assert target.read_bytes() == original_bytes


def test_no_stub_when_the_demo_is_not_a_replacement(tmp_path):
    target = _write(tmp_path)

    with calibration_stub(_demo(target, sorry_type="sorry_injection")) as prepared:
        assert prepared["calibration_stubbed"] is False
        assert count_real_sorries(target.read_text(encoding="utf-8")) == 0


def test_no_stub_when_the_target_already_has_a_real_sorry(tmp_path):
    target = _write(tmp_path, LEAN_SOURCE.replace(
        "theorem card_pair : (Finset.univ : Finset (Fin 2)).card = 2 := by\n  decide",
        "theorem card_pair : (Finset.univ : Finset (Fin 2)).card = 2 := by\n  sorry",
    ))

    with calibration_stub(_demo(target)) as prepared:
        assert prepared["calibration_stubbed"] is False
        assert count_real_sorries(target.read_text(encoding="utf-8")) == 1


def test_unknown_theorem_fails_loud_and_leaves_the_file_untouched(tmp_path):
    target = _write(tmp_path)
    original_bytes = target.read_bytes()

    with pytest.raises(ValueError):
        with calibration_stub(_demo(target, theorem_name="does_not_exist")):
            pass

    assert target.read_bytes() == original_bytes


def test_empty_file_path_is_a_no_op(tmp_path):
    with calibration_stub(_demo("", file="")) as prepared:
        assert prepared["calibration_stubbed"] is False


def test_flag_false_green_marks_a_stubbed_target_reported_already_solved():
    prepared = {"name": "CALIBRATION_FIXTURE", "calibration_stubbed": True}
    assert flag_false_green(prepared, {"success": True, "already_solved": True}) is True


def test_flag_false_green_ignores_a_genuine_already_solved():
    # Hors calibration, `already_solved` est legitime : la cible n'avait
    # simplement pas de trou a prouver.
    prepared = {"name": "SMOKE", "calibration_stubbed": False}
    assert flag_false_green(prepared, {"success": True, "already_solved": True}) is False


def test_flag_false_green_ignores_a_real_run():
    prepared = {"name": "CALIBRATION_FIXTURE", "calibration_stubbed": True}
    assert flag_false_green(prepared, {"success": True, "iterations": 3}) is False
