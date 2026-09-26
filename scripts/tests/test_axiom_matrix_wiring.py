#!/usr/bin/env python3
"""Anti-drift pins for the matrix axiom wiring (#17336, template of #17287).

The wiring spans five surfaces that can silently drift apart, the exact class
`check_lake_matrix_paths.py` closes for build coverage: a manifest entry
without its dispatcher paths is a lake no trigger sees, an axiom key without
the matrix step is a declaration that never runs, and a workflow heredoc
re-implemented in the composite would be a second copy of the rule. These
tests pin each joint so the next edit that separates them fails loud.

Run: python -m pytest scripts/tests/test_axiom_matrix_wiring.py
"""
import sys
from pathlib import Path

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

REPO = Path(__file__).resolve().parents[2]
MANIFEST = REPO / "scripts/lean/ci_lakes.json"
SERRE_PATHS = [
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean/**.lean",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean/lakefile.lean",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean/lean-toolchain",
    # Self-cover B.3 herite du wrapper supprime : le moteur d'axiomes
    # (lean_server.py / lean_utils.py) change -> le gate axiom rejoue.
    "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/lean_server.py",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/lean_utils.py",
]
AXIOM_SELF_COVER = [
    ".github/actions/lean-axiom/action.yml",
    "scripts/lean/axiom_check_step.py",
]
# Self-cover du contrat certifie herite du wrapper lean-social-choice.yml
# supprime (#17374) : l'instrument, le compteur canonique et le test pinneur
# sont des fichiers du gate.
CERTIFIED_SELF_COVER = [
    "scripts/lean/check_certified_sorry.py",
    "scripts/lean/count_code_sorry.py",
    "scripts/tests/test_check_certified_sorry.py",
]


def _manifest():
    import json
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def test_serre100_manifest_entry_carries_the_axiom_key():
    """The opt-in key IS the wiring on the manifest side: without it the
    matrix step interpolates '' and the lake never gets its B.3 pass."""
    entry = next(e for e in _manifest()["lakes"] if e["lake"] == "serre100")
    assert entry["axiom-target-modules"] == "*"
    assert entry["sorry-baseline"] == "0"
    assert entry["paths"] == SERRE_PATHS


def test_matrix_step_is_gated_on_the_manifest_key():
    """lean-build.yml ci-matrix must (a) have the conditional axiom step and
    (b) gate it on `matrix.axiom-target-modules` -- the 19 lakes without the
    key keep their exact behaviour (step skipped), and a lake WITH the key
    cannot silently lose its axiom pass."""
    doc = yaml.safe_load(
        (REPO / ".github/workflows/lean-build.yml").read_text(encoding="utf-8"))
    steps = doc["jobs"]["ci-matrix"]["steps"]
    axiom = [s for s in steps if s.get("uses", "").endswith("actions/lean-axiom")]
    assert len(axiom) == 1, "exactly one axiom step in the matrix job"
    assert axiom[0]["if"] == "matrix.axiom-target-modules != ''"
    assert axiom[0]["with"]["target-modules"] == "${{ matrix.axiom-target-modules }}"
    assert axiom[0]["with"]["project-path"] == "${{ matrix.project-path }}"


def test_one_copy_of_the_rule_workflow_calls_the_shared_script():
    """lean-axiom.yml must invoke scripts/lean/axiom_check_step.py (not a
    heredoc), and the composite must invoke the same script -- one copy of
    the axiom rule for both callers."""
    wf = (REPO / ".github/workflows/lean-axiom.yml").read_text(encoding="utf-8")
    assert "scripts/lean/axiom_check_step.py" in wf
    assert "<<'PY'" not in wf, "the heredoc must not come back (#17336)"
    comp = (REPO / ".github/actions/lean-axiom/action.yml").read_text(encoding="utf-8")
    assert "scripts/lean/axiom_check_step.py" in comp
    comp_doc = yaml.safe_load(comp)
    step = comp_doc["runs"]["steps"][0]
    assert set(step["env"]) == {
        "MODULES", "ALLOW", "DISPLAY_NAME", "PROJECT_PATH",
        "FAIL_ON_SORRY", "INCLUDE_I18N_SIBLINGS",
    }, "the composite must feed the script's full env contract"


def test_axiom_gate_files_are_self_covered():
    """A change to the axiom rule must re-run the gate (lecon #8712): the
    two new gate files sit in BOTH trigger unions of the dispatcher and in
    GATE_SELF_COVER."""
    doc = yaml.safe_load(
        (REPO / ".github/workflows/lean-ci-matrix.yml").read_text(encoding="utf-8"))
    on = doc.get("on") or doc.get(True)
    for event in ("push", "pull_request"):
        paths = on[event]["paths"]
        for p in AXIOM_SELF_COVER:
            assert p in paths, f"{p} missing from on.paths[{event}]"
    sys.path.insert(0, str(REPO / "scripts/lean"))
    import lake_matrix_dispatch
    for p in AXIOM_SELF_COVER:
        assert p in lake_matrix_dispatch.GATE_SELF_COVER


def test_extracted_script_compiles():
    """The extracted body is a flat STEP SCRIPT, not a module: importing it
    would EXECUTE the check (env reads, sys.exit). py_compile is the right
    probe -- it proves the file is valid Python without running it."""
    import py_compile
    py_compile.compile(
        str(REPO / "scripts/lean/axiom_check_step.py"), doraise=True)


def test_serre100_historical_wrapper_is_gone():
    """lean-serre.yml was the lake's PRE-migration gate (filename does not
    derive from the lake name -- the exact shape the filename check of the
    guard missed). With serre100 in the manifest it is a DOUBLE trigger: the
    witness PR built the lake twice (wrapper via lean-build.yml@main + matrix
    leg). The migration contract: a manifest lake keeps no wrapper (#17336).
    """
    assert not (REPO / ".github/workflows/lean-serre.yml").exists(), (
        "le wrapper historique de serre100 est revenu -- double build")


def test_gametheory_entry_carries_axiom_and_certified_keys():
    """#17374: gametheory's B.3 pass and SocialChoice certified contract
    migrated from the deleted wrapper into the manifest. The exact target
    list is pinned against CERTIFIED.txt by
    test_check_certified_sorry.py::test_workflow_targets_match_manifest --
    here we pin the KEYS and the trigger surface, the two joints a silent
    edit could break."""
    entry = next(e for e in _manifest()["lakes"] if e["lake"] == "gametheory")
    assert entry["axiom-target-modules"].startswith("SocialChoice."), (
        "gametheory lost its B.3 target list")
    assert entry["axiom-fail-on-sorry"] == "true"
    assert entry["certified-subdir"] == "SocialChoice"
    for p in (["MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/"
               "CERTIFIED.txt"] + CERTIFIED_SELF_COVER):
        assert p in entry["paths"], (
            f"gametheory manifest entry lost gate trigger {p}")


def test_certified_step_is_gated_on_the_manifest_key():
    """The certified contract runs only for manifest entries carrying
    `certified-subdir` -- the other lakes keep their exact behaviour (step
    skipped), and a lake WITH the key cannot silently lose its contract."""
    doc = yaml.safe_load(
        (REPO / ".github/workflows/lean-build.yml").read_text(encoding="utf-8"))
    steps = doc["jobs"]["ci-matrix"]["steps"]
    cert = [s for s in steps
            if "check_certified_sorry.py" in s.get("run", "")]
    assert len(cert) == 1, "exactly one certified-contract step in the matrix job"
    assert cert[0]["if"] == "matrix.certified-subdir != ''"
    assert "${{ matrix.certified-subdir }}" in cert[0]["run"]


def test_certified_gate_files_are_self_covered():
    """A change to the certified rule must re-run the gate (lecon #8712):
    the three gate files sit in BOTH trigger unions of the dispatcher."""
    doc = yaml.safe_load(
        (REPO / ".github/workflows/lean-ci-matrix.yml").read_text(encoding="utf-8"))
    on = doc.get("on") or doc.get(True)
    for event in ("push", "pull_request"):
        paths = on[event]["paths"]
        for p in CERTIFIED_SELF_COVER + [
            "MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/"
            "CERTIFIED.txt",
        ]:
            assert p in paths, f"{p} missing from on.paths[{event}]"


def test_social_choice_historical_wrapper_is_gone():
    """#17374: lean-social-choice.yml was gametheory's pre-migration
    dispatcher -- with the lake in the manifest it was a DOUBLE trigger
    (matrix leg + wrapper build/axiom). The migration contract: a manifest
    lake keeps no wrapper."""
    assert not (REPO / ".github/workflows/lean-social-choice.yml").exists(), (
        "le wrapper historique de gametheory est revenu -- double build")


def test_guard_double_trigger_allowlist_is_empty():
    """The recroisement guard is STRICT since #17374 tranched both pairs:
    KNOWN_DOUBLE_TRIGGERS must stay empty -- a new pair is a temporary,
    issue-cited debt, never a permanent fixture."""
    sys.path.insert(0, str(REPO / "scripts/ci"))
    import check_lake_matrix_paths
    assert check_lake_matrix_paths.KNOWN_DOUBLE_TRIGGERS == set()
