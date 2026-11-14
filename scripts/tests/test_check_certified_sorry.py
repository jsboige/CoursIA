#!/usr/bin/env python3
"""Unit tests for check_certified_sorry.py — the certified-modules gate of #12330.

The issue's acceptance criteria demand POSITIVE CONTROLS on both polarities
(criterion 3): a module whose docstring says `sorry` but whose code has none
must stay GREEN (the old grep blushed on it), and a module with a real
`:= by sorry` must blush (the old loop, fail-open on missing files, did not
need to be fooled — it just went quiet). These tests replay both, plus the
fail-open fix (criterion 1: a missing certified file FAILS, named) and the
exhaustiveness contract (criterion 5: an unaccounted module is STALE-LIST).

Run: python -m pytest scripts/tests/test_check_certified_sorry.py
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lean"))

import check_certified_sorry as ccs  # noqa: E402


# --- fixtures ----------------------------------------------------------------

def make_lake(tmp_path: Path, files: dict[str, str], manifest: str,
              subdir: str = "Sub") -> Path:
    """Lay out a fake lake: lakefile + subdir with files + CERTIFIED.txt."""
    lake = tmp_path / "lake"
    tree = lake / subdir
    tree.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("-- fake lake\n", encoding="utf-8")
    for name, body in files.items():
        (tree / name).write_text(body, encoding="utf-8")
    (tree / ccs.MANIFEST_NAME).write_text(manifest, encoding="utf-8")
    return lake


CLEAN_MODULE = """import Mathlib.Tactic
theorem clean_thm (p : Prop) : p → p := by intro h; exact h
"""

DOCSTRING_SORRY_MODULE = """/-
  Docstring mentioning sorry on purpose: the module documents that it carries
  zero sorry, which the old grep counted as one.
-/
import Mathlib.Tactic
theorem doc_ok (p : Prop) : p → p := by intro h; exact h
"""

REAL_SORRY_MODULE = """import Mathlib.Tactic
theorem broken_thm (p : Prop) : p := by sorry
"""


# --- criterion 1: fail-open fixed (missing file blushes, named) ---------------

def test_missing_certified_file_fails_with_name(tmp_path):
    # Sen.lean is certified but absent (renamed/moved): the gate must blush
    # AND name it. The old loop passed in silence (if [ -f ] without else).
    lake = make_lake(tmp_path, {"Arrow.lean": CLEAN_MODULE},
                     "Arrow.lean\nSen.lean\n")
    failures, _ = ccs.check_subtree(lake, "Sub")
    assert any("MISSING: Sub/Sen.lean" in f for f in failures), failures


def test_missing_manifest_is_a_failure_not_a_pass(tmp_path):
    # No CERTIFIED.txt at all: a gate with no contract must not read as green.
    lake = tmp_path / "lake"
    (lake / "Sub").mkdir(parents=True)
    failures, _ = ccs.check_subtree(lake, "Sub")
    assert any("MISSING-MANIFEST" in f for f in failures), failures


# --- criterion 3: positive controls on both polarities ------------------------

def test_docstring_sorry_stays_green(tmp_path):
    # `sorry` inside a docstring is prose, not proof debt: canonical
    # instrument (comment-stripped) must keep this GREEN. The old
    # `grep -c sorry` blushed on it (the over-counting polarity).
    lake = make_lake(tmp_path, {"Arrow.lean": DOCSTRING_SORRY_MODULE},
                     "Arrow.lean\n")
    failures, report = ccs.check_subtree(lake, "Sub")
    assert failures == [], failures
    # the docstring says "sorry" twice -- grep sees 2, the real debt is 0
    assert report["per_file"]["Arrow.lean"]["naive_sorry"] == 2
    assert report["per_file"]["Arrow.lean"]["code_sorry"] == 0


def test_real_sorry_blushes_with_declaration_and_line(tmp_path):
    # A real tactic sorry must blush, naming the declaration and its line.
    lake = make_lake(tmp_path, {"Arrow.lean": REAL_SORRY_MODULE},
                     "Arrow.lean\n")
    failures, _ = ccs.check_subtree(lake, "Sub")
    assert any("SORRY: theorem broken_thm (Sub/Arrow.lean:2)" in f
               for f in failures), failures


def test_sorry_in_en_mirror_also_blushes(tmp_path):
    # _en siblings are compiled modules: proof debt there is debt too.
    lake = make_lake(tmp_path, {"Arrow.lean": CLEAN_MODULE,
                                "Arrow_en.lean": REAL_SORRY_MODULE},
                     "Arrow.lean\nArrow_en.lean\n")
    failures, _ = ccs.check_subtree(lake, "Sub")
    assert any("Arrow_en.lean" in f and "SORRY" in f for f in failures), failures


# --- criterion 5: exhaustiveness is verifiable --------------------------------

def test_unaccounted_module_is_stale_list(tmp_path):
    # A module in the subtree that is neither certified nor excluded is a
    # stale contract: the PR that adds a module must add it here (this is
    # the #12329 lesson — MechanismDesign entered the tree silently).
    lake = make_lake(tmp_path, {"Arrow.lean": CLEAN_MODULE,
                                "NewModule.lean": CLEAN_MODULE},
                     "Arrow.lean\n")
    failures, _ = ccs.check_subtree(lake, "Sub")
    assert any("STALE-LIST: Sub/NewModule.lean" in f for f in failures), failures


def test_explicit_exclusion_is_visible_and_ok(tmp_path):
    # `!name.lean` excludes on purpose and passes — an exclusion is a
    # decision, not a silence. The excluded file is NOT sorry-scanned.
    lake = make_lake(tmp_path, {"Arrow.lean": CLEAN_MODULE,
                                "_SmokeTest.lean": REAL_SORRY_MODULE},
                     "Arrow.lean\n!_SmokeTest.lean\n")
    failures, report = ccs.check_subtree(lake, "Sub")
    assert failures == [], failures
    assert report["excluded"] == ["_SmokeTest.lean"]
    assert "_SmokeTest.lean" not in report["per_file"]


def test_certified_and_excluded_is_contradiction(tmp_path):
    lake = make_lake(tmp_path, {"Arrow.lean": CLEAN_MODULE},
                     "Arrow.lean\n!Arrow.lean\n")
    failures, _ = ccs.check_subtree(lake, "Sub")
    assert any("CONTRADICTION" in f for f in failures), failures


def test_inline_comments_in_manifest_do_not_break_names(tmp_path):
    # Regression of the first live run: `Arrow.lean  # reason` parsed as a
    # filename-with-comment matched no file and read as MISSING.
    lake = make_lake(tmp_path, {"Arrow.lean": CLEAN_MODULE},
                     "Arrow.lean  # the impossibility module\n")
    failures, _ = ccs.check_subtree(lake, "Sub")
    assert failures == [], failures


# --- the real contract, pinned -------------------------------------------------

REAL_LAKE = Path(__file__).resolve().parents[2] / (
    "MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_core_lean")


def test_real_socialchoice_contract_holds():
    # The committed manifest must hold against the committed tree: this is
    # what CI runs on every PR touching the lake. Since the descent of #24183
    # (#25262), the SocialChoice contract lives in the autonomous lake under
    # the SC notebooks, not in game_theory_lean anymore.
    if not REAL_LAKE.is_dir():  # pragma: no cover - repo layout guarantee
        pytest.skip("social_choice_core_lean not found")
    failures, report = ccs.check_subtree(REAL_LAKE, "SocialChoice")
    assert failures == [], failures
    assert len(report["certified"]) >= 17  # 9 FR + 8 EN in the autonomous lake


def test_workflow_targets_match_manifest():
    # Criterion 5, second surface: the B.3 target list is ALSO a list — pin it
    # to the manifest so the two cannot drift apart silently (same class as
    # the STALE-LIST check). Depuis #17374 la liste vit dans le manifeste
    # matriciel (ci_lakes.json) ; depuis la descente #24183 (#25262) le lac
    # SocialChoice est autonome sous les carnets SC — l'entree pinee est
    # « socialchoicecore », et gametheory ne porte plus que ses compagnons.
    import json
    repo = Path(__file__).resolve().parents[2]
    manifest = (REAL_LAKE / "SocialChoice" / ccs.MANIFEST_NAME).read_text(
        encoding="utf-8")
    certified, _ = ccs.parse_manifest(manifest)
    expected = sorted("SocialChoice." + f[:-len(".lean")] for f in certified)
    lakes = json.loads(
        (repo / "scripts/lean/ci_lakes.json").read_text(encoding="utf-8"))
    entry = next(e for e in lakes["lakes"] if e["lake"] == "socialchoicecore")
    raw = entry["axiom-target-modules"]
    actual = {m.strip() for m in raw.split(",")}
    expected_set = set(expected)
    # The root SocialChoice.lean is a docstring-only aggregator listed as a
    # matrix target (it roots the import graph) but not a certified module:
    # the only allowed extra. A future addition to target-modules is an
    # explicit test change, never a silent drift.
    # SocialChoice._SmokeTest vit dans le dossier et ne figure pas au
    # CERTIFIED.txt ; main l'auditait comme compagnon du lake gametheory,
    # il a demenage avec le lac et garde sa cible (aucune perte de
    # couverture au merge).
    allowed_extras = {"SocialChoice", "SocialChoice._SmokeTest"}
    assert expected_set <= actual, (
        f"ci_lakes.json socialchoicecore axiom-target-modules omitted entries "
        f"from SocialChoice/CERTIFIED.txt: matrix={sorted(actual)} "
        f"manifest={expected}")
    assert actual - expected_set == allowed_extras, (
        f"socialchoicecore matrix entry has unreviewed targets: "
        f"extras={sorted(actual - expected_set)} "
        f"allowed={sorted(allowed_extras)}")

    # La descente doit etre complete : gametheory ne porte plus AUCUNE cible
    # SocialChoice.* — ses compagnons legitimes (Abstraction, ProgramGames)
    # restent seuls dans son entree.
    gametheory = next(e for e in lakes["lakes"] if e["lake"] == "gametheory")
    gt = {m.strip() for m in gametheory["axiom-target-modules"].split(",")}
    assert not any(m.startswith("SocialChoice.") for m in gt), (
        f"gametheory still carries SocialChoice targets after the descent: "
        f"{sorted(m for m in gt if m.startswith('SocialChoice.'))}")

    # Compagnons du lac gametheory : la descente ne les touche pas, et
    # leur liste reste epinglee ici pour qu'un ajout de cible soit un
    # changement de test explicite, jamais une derive silencieuse
    # (#25858, #25686/#26022). Les deux cibles SocialChoice.* en sont
    # retirees : elles vivent dans le lac autonome, et l'assertion
    # ci-dessus verifie qu'elles ne sont pas revenues.
    allowed_companions = {
        "Abstraction", "Abstraction.Basic",
        "ProgramGames.Basic", "ProgramGames.Basic_en",
        "ProgramGames.Bounded", "ProgramGames.Bounded_en",
        # #25858 : 30 modules de gametheory hors SocialChoice, ajoutes a
        # axiom-target-modules apres recensement (chacun verifie a
        # code_sorry = 0 et 0 occurrence des classes forbidden par le
        # prescreen de la PR). Meme statut de revue que les precedents,
        # epingles ici pour que le prochain ajout reste un changement de
        # test explicite, jamais une derive silencieuse.
        "CongestionGames.PoA",
        "CooperativeGames.Basic", "CooperativeGames.Basic_en",
        "CooperativeGames.ConeKernel", "CooperativeGames.ConeKernel_en",
        "CooperativeGames.Shapley", "CooperativeGames.Shapley_en",
        "ProgramGames.FairBot", "ProgramGames.FairBot_en",
        "RepeatedGames.Discounting", "RepeatedGames.Discounting_en",
        "RepeatedGames.GrimTrigger", "RepeatedGames.GrimTrigger_en",
        "RepeatedGames.Stage", "RepeatedGames.Stage_en",
        "RepeatedGames_en",
        "StableMarriage.Definitions", "StableMarriage.Definitions_en",
        "StableMarriage.GSState", "StableMarriage.GSState_en",
        "StableMarriage.GaleShapley", "StableMarriage.GaleShapley_en",
        "StableMarriage.Lattice", "StableMarriage.Lattice_en",
        "StableMarriage.Lemmas", "StableMarriage.Lemmas_en",
        "StableMarriage_en",
        "Swaps.Basic", "Swaps.Parite",
        # #25858 (reserve du 11/11) : les RACINES de lib compilees par
        # `X.*` (Lake les compile : « including itself »). Chacune est un
        # simple aggregateur d'imports, 0 declaration -- l'instrument du
        # gate les classe `declaration_free_module`, donc NOTE non
        # fatale, et aucune ne peut masquer un sorry. Les laisser hors
        # liste faisait paraitre l'ecart du recensement comme un manque
        # de couverture alors qu'il n'y avait rien a auditer : la racine
        # est desormais une cible explicite, comme les trois racines
        # declaration-free deja presentes (Abstraction, RepeatedGames_en,
        # StableMarriage_en). Elles sont 7 ici et non 8 : la racine
        # SocialChoice a suivi la descente #24183 (#25262) dans le lac
        # autonome, ou elle figure parmi les `allowed_extras`.
        "CongestionGames", "CooperativeGames", "ProgramGames",
        "RepeatedGames", "StableMarriage",
        "StackelbergBilevel", "Swaps",
        # #25686/#26022 : LegalLoophole (racine aggregatrice, sans
        # declaration) + LegalLoophole.Toy (module reel, 0 sorry / 0 axiome
        # ad hoc) ajoutes a axiom-target-modules avec le default_target --
        # la revendication d'axiomes de la PR devient mesuree par l'organe.
        "LegalLoophole", "LegalLoophole.Toy",
    }
    assert gt == allowed_companions, (
        f"gametheory matrix entry has unreviewed companion targets: "
        f"extras={sorted(gt - allowed_companions)} "
        f"missing={sorted(allowed_companions - gt)}")

    # Le declencheur lake-entier suit le lac autonome : glob **.lean du
    # nouveau repertoire, strictement plus large que les sous-chemins
    # explicites (#17374).
    assert any(p.endswith("social_choice_core_lean/**.lean")
               for p in entry["paths"]), (
        "socialchoicecore manifest entry lost its whole-lake .lean trigger")
