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
    assert len(axiom) == 2, "one advisory step and one optional blocking step"
    advisory = next(s for s in axiom if "axiom-target-modules" in s["if"])
    blocking = next(s for s in axiom if "axiom-blocking-target-modules" in s["if"])
    assert advisory["if"] == "matrix.axiom-target-modules != ''"
    assert advisory["with"]["target-modules"] == "${{ matrix.axiom-target-modules }}"
    assert advisory["with"]["project-path"] == "${{ matrix.project-path }}"
    assert blocking["if"] == "matrix.axiom-blocking-target-modules != ''"
    assert blocking["with"]["target-modules"] == "${{ matrix.axiom-blocking-target-modules }}"
    assert blocking["with"]["allow-axioms"] == "${{ matrix.axiom-blocking-allow-axioms || '' }}"
    assert blocking["with"]["fail-on-sorry"] == "${{ matrix.axiom-blocking-fail-on-sorry || 'true' }}"
    assert blocking["with"]["project-path"] == "${{ matrix.project-path }}"
    assert blocking["with"]["display-name"] == "${{ matrix.display-name }} (blocking)"


def test_blocking_profile_is_optional_and_conway_is_its_only_manifest_user():
    """Les champs plats `axiom-blocking-*` sont optionnels et seuls conway
    les porte : une matrice créée par le dispatcher laisse les autres lakes
    hors de ce second passage."""
    lakes = _manifest()["lakes"]
    blocking_keys = {
        "axiom-blocking-target-modules",
        "axiom-blocking-allow-axioms",
        "axiom-blocking-fail-on-sorry",
    }
    conway = next(e for e in lakes if e["lake"] == "conway")
    assert conway["axiom-blocking-target-modules"] == (
        "Conway.KochenSpecker,Conway.FreeWillTheorem")
    assert conway["axiom-blocking-allow-axioms"] == (
        "Classical.choice,propext,funext,Quot.lift,Quot.mk,Quot.sound")
    assert conway["axiom-blocking-fail-on-sorry"] == "true"
    for lake in lakes:
        if lake["lake"] != "conway":
            assert blocking_keys.isdisjoint(lake), lake["lake"]


def test_matrix_step_passes_the_thread_cap_under_the_composite_input_name():
    """The ci-matrix job passes the manifest key `build-threads` to the
    composite -- whose DECLARED input is `build-jobs` (#23247). Under any
    other name the composite ignores the value with a mere warning
    (measured warning, run 42475534833) -- the cap never reaches
    LEAN_NUM_THREADS, exposing Conway to the previously reported OOM
    risk (#23247). This run stopped before the build. The wiring is part of the conway
    migration contract (#13751)."""
    doc = yaml.safe_load(
        (REPO / ".github/workflows/lean-build.yml").read_text(encoding="utf-8"))
    steps = doc["jobs"]["ci-matrix"]["steps"]
    build = [s for s in steps if s.get("uses", "").endswith("actions/lean-build")]
    assert len(build) == 1, "exactly one lean-build step in the matrix job"
    with_block = build[0]["with"]
    assert "build-threads" not in with_block, (
        "l'input composite s'appelle `build-jobs` : un `build-threads:` passe "
        "au composite est IGNORE avec un simple warning (run 42475534833) -- "
        "le cap ne pose jamais LEAN_NUM_THREADS, avec un risque d'OOM")
    assert with_block.get("build-jobs") == "${{ matrix.build-threads || '' }}", (
        "la cle manifeste `build-threads` doit rejoindre l'input composite "
        "`build-jobs` -- seul chemin vers LEAN_NUM_THREADS (#23247)")



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
    edit could break.

    Depuis la descente #24183 (#25262), le contrat vit sur l'entree
    `socialchoicecore` (lac autonome sous les carnets SC) ; gametheory ne
    porte plus que ses compagnons (Abstraction, ProgramGames). Le test
    epingle la migration dans les DEUX sens : le nouveau porteur a les
    cles, l'ancien n'en garde aucune."""
    entry = next(e for e in _manifest()["lakes"]
                 if e["lake"] == "socialchoicecore")
    targets = [m.strip() for m in entry["axiom-target-modules"].split(",")]
    assert any(m == "SocialChoice" or m.startswith("SocialChoice.")
               for m in targets), (
        "socialchoicecore lost its B.3 target list")
    assert entry["axiom-fail-on-sorry"] == "true"
    assert entry["certified-subdir"] == "SocialChoice"
    for p in (["MyIA.AI.Notebooks/GameTheory/SocialChoice/"
               "social_choice_core_lean/SocialChoice/CERTIFIED.txt"]
              + CERTIFIED_SELF_COVER):
        assert p in entry["paths"], (
            f"socialchoicecore manifest entry lost gate trigger {p}")

    gt = next(e for e in _manifest()["lakes"] if e["lake"] == "gametheory")
    gt_targets = [m.strip() for m in gt["axiom-target-modules"].split(",")]
    assert not any(m.startswith("SocialChoice.") for m in gt_targets), (
        "gametheory still carries SocialChoice targets after the descent: "
        f"{sorted(m for m in gt_targets if m.startswith('SocialChoice.'))}")
    assert "certified-subdir" not in gt, (
        "gametheory still carries a certified contract after the descent")


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
            # Descente #24183 (#25262) : le contrat certified vit dans le
            # lac autonome sous les carnets SocialChoice.
            "MyIA.AI.Notebooks/GameTheory/SocialChoice/"
            "social_choice_core_lean/SocialChoice/CERTIFIED.txt",
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


# --- #22453 : la porte d'axiomes doit voir les freres i18n `_en` -------

def test_knot_gate_opts_in_the_i18n_siblings():
    """knot_lean's axiom gate must opt in explicitly -- via its manifest
    entry since the matrix migration (#13751) deleted lean-knot.yml.

    The `'*'` derivation enumerates every module `lake build` compiles; the
    FR-only filter then drops the `_en` siblings. Measured locally, without
    Lean: 48 modules discovered on knot_lean, 24 inspected, 751 declarations
    carried by the 24 excluded siblings. conway and mimo already pass
    `include-i18n-siblings: "true"`; knot did not (#22453). The wrapper pin
    moved to the manifest at migration: the matrix step interpolates
    `matrix.axiom-include-i18n-siblings || 'false'` -- a dropped key would
    silently re-exclude the 24 siblings."""
    entry = next(e for e in _manifest()["lakes"] if e["lake"] == "knot")
    assert entry["axiom-target-modules"] == "*"
    assert entry["axiom-include-i18n-siblings"] == "true", (
        "knot_lean garde ses 24 freres `_en` hors de la porte d'axiomes")
    # Les 8 sorries reconnus (distinct_code_sorry mesure) sont rapportes
    # has_sorry, non gates : fail-on-sorry false, exact contrat du wrapper.
    assert entry["axiom-fail-on-sorry"] == "false"
    assert entry["sorry-baseline"] == "8"


def test_knot_historical_wrapper_is_gone():
    """lean-knot.yml was knot_lean's PRE-migration gate. With knot in the
    manifest it is a DOUBLE trigger (wrapper + matrix leg build the lake
    twice). The migration contract: a manifest lake keeps no wrapper
    (#17336, #17374)."""
    assert not (REPO / ".github/workflows/lean-knot.yml").exists(), (
        "le wrapper historique de knot_lean est revenu -- double build")


def test_composites_trigger_on_the_axiom_step_program():
    """The axiom step IS the gate's program (extracted from the reusable
    workflow in #17336). It was missing from the composites' `on.paths`
    while `lean_server.py` and `check_target_coverage.py` were listed: a
    change to the rule could ship without the gate ever running on it --
    the #8712 lesson applied one layer down (#22453). lean-knot.yml left
    this loop at its matrix migration (#13751): the dispatcher's own
    self-cover (test_axiom_gate_files_are_self_covered) carries the rule
    for matrix lakes. lean-conway.yml -- the LAST autonomous wrapper with
    an axiom gate -- left it at its own matrix migration (2026-11-08,
    #13751 axe workflows, lane myia-ai-01:CoursIA-2): the loop is EMPTY
    since, every manifest lake rides the dispatcher's self-cover. A future
    autonomous wrapper born with an axiom gate MUST add itself back here."""
    for wf in ():
        doc = yaml.safe_load(
            (REPO / f".github/workflows/{wf}.yml").read_text(encoding="utf-8"))
        on = doc.get("on") or doc.get(True)
        for event in ("push", "pull_request"):
            assert "scripts/lean/axiom_check_step.py" in on[event]["paths"], (
                f"{wf}: le programme de la porte ne declenche pas la porte "
                f"(on.paths[{event}])")


def test_the_i18n_surface_is_derived_from_the_single_filter():
    """The gate must not carry a second copy of the `_en` rule: the
    excluded surface is the set difference of the SAME call to
    `filter_i18n_siblings`, and the step prints it (#22453)."""
    src = (REPO / "scripts/lean/axiom_check_step.py").read_text(encoding="utf-8")
    assert "filter_i18n_siblings" in src
    assert "i18n siblings (_en)" in src, (
        "la porte ne dit plus quelle surface i18n elle a inspectee")
    assert src.count("endswith(\"_en\")") == 0, (
        "une seconde copie du predicat `_en` est apparue dans la porte")


def test_the_filter_splits_the_bilingual_surface_of_a_real_lake():
    """Property, not snapshot: on a lake that HAS `_en` siblings, the
    filter keeps the FR modules and excludes exactly the siblings. A
    snapshot of counts would rot on every module added."""
    sys.path.insert(0, str(REPO / "scripts" / "lean"))
    from check_target_coverage import discover_modules, filter_i18n_siblings
    project = REPO / "MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean"
    discovered = set(discover_modules(project, None))
    kept = set(filter_i18n_siblings(discovered))
    excluded = discovered - kept
    assert excluded, "knot_lean n'a plus de freres `_en` -- la mesure change"
    for mod in excluded:
        assert any(part.endswith("_en") for part in mod.split(".")), mod
    for mod in kept:
        assert not any(part.endswith("_en") for part in mod.split(".")), mod
