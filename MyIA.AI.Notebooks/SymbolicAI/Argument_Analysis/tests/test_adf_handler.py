"""Contract tests for the locally adapted ADF handler (issue #23278).

The upstream verbatim copy of `argumentation_lib/_adf_handler.py` targeted a
Tweety API that the vendored jar `Tweety/libs/adf-1.30.jar` no longer
exposes. Four drifts were measured firsthand (JVM started, vendored jars on the
classpath); the local adaptation fixes each one and is documented in the
header of the module and in `argumentation_lib/NOTICE-EPITA`:

1. `builder.add(arg)` — no such overload in 1.30 (`TypeError`).
2. `TautologyAcceptanceCondition` / `ContradictionAcceptanceCondition` are
   enumerations in 1.30 (constants `T` / `F`), not instantiable classes.
3. The ADF graph requires its links (the builder is `eager` by default).
4. The ADF reasoners are SAT-based: `GroundReasoner(IncrementalSatSolver)` is
   the only constructor that exists.

The handler was an **orphan organ** — no notebook of the series exercised it —
so nothing caught the drift. These tests pin the contract; the notebook
`Argumentation-03d-ADF-Semantiques-Python.ipynb` exercises the same path and
renders its outputs.

Two families of tests:

- **JVM-free** (always collected): the condition vocabulary validation and the
  explicit gate-out of the KPPADF file reader. They use an instance built
  without `__init__` so that no JVM is needed.
- **JVM-bound** (skipped when `jpype` or the local Tweety jars are absent, as
  on the CPU-only CI job): the analysis itself, run in a **child process**.

The child process is not decoration: the JVM is process-global, and the
sibling test `test_jvm_compat_reporting.py` asserts the behaviour of
`initialize_jvm` on a path where the JVM **fails** to start — a state only
reachable on a process that has not started one yet. Running the ADF analysis
in-process would start the JVM and break that sibling. The child process also
proves the organ works from a cold start, with no inherited global state.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

# Make `argumentation_lib` importable (../argumentation_lib relative to tests/).
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)

import pytest  # noqa: E402

import argumentation_lib  # noqa: E402

try:  # ADF layer dependency; absent from the CPU-only jobs
    import jpype
except ImportError:  # pragma: no cover - depends on the runner's wheels
    jpype = None
    _HAS_JPYPE = False
else:
    _HAS_JPYPE = True

# The handler module is importable WITHOUT jpype (adaptation 5 of
# `argumentation_lib/_adf_handler.py`, 2026-10-29): only its INSTANTIATION
# needs the JVM. Importing it at module level used to make this whole file
# fail at COLLECTION on the CPU-only CI job (`ModuleNotFoundError: No module
# named 'jpype'`), which failed the entire `Scripts Tests (CPU)` job — 21 846
# tests green, one collection error, exit 1. Same convention as the package
# itself (cf `argumentation_lib/__init__.py`, whose `get_adf_handler_symbol`
# already degrades gracefully without jpype).
from argumentation_lib._adf_handler import ADFHandler  # noqa: E402


def _tweety_libs_available() -> bool:
    """True when the vendored Tweety jars are present on this machine.

    The lookup goes through the library's own finder
    (`argumentation_lib._paths.get_tweety_jar_dir`), NOT through a private
    re-implementation of a single path. The finder searches
    `Argument_Analysis/libs/` first and `Tweety/libs/` second, and
    `.gitignore` provisions the first one (`Argument_Analysis/libs/*.jar`):
    a jar sitting there is where the organ actually looks for it, and a
    guard hard-coded on `Tweety/libs` alone would report "absent" while the
    organ works — the six semantic assertions would then be skipped with a
    motif pointing at the wrong cause.
    """
    try:
        from argumentation_lib._paths import get_tweety_jar_dir
    except Exception:  # pragma: no cover - defensive: paths shim is stdlib-only
        return False
    libs = get_tweety_jar_dir()
    return libs is not None and any(libs.glob("adf-*.jar"))


requires_jvm = pytest.mark.skipif(
    not (_HAS_JPYPE and _tweety_libs_available()),
    reason=(
        "the ADF analysis needs jpype and the vendored Tweety jars "
        "(Tweety/libs/adf-*.jar); the CPU-only CI job skips this leg "
        "(tranche #23278)"
    ),
)


def _handler_without_jvm() -> ADFHandler:
    """An instance that never touched `__init__` (no JVM required).

    Only the pure-Python validation paths of the handler are reachable on it;
    every code path that would need the JVM raises before reaching Java.
    """
    return ADFHandler.__new__(ADFHandler)


def _run_probe(body: str):
    """Run `body` in a child process that owns its own JVM.

    The child prints one JSON document on stdout; the JVM's own crash-handler
    chatter goes to stderr and is ignored.
    """
    code = (
        "import json, sys\n"
        f"sys.path.insert(0, r'{_ARG_ANALYSIS_DIR}')\n"
        "from argumentation_lib import initialize_jvm\n"
        "assert initialize_jvm(verbose=False), 'JVM not started'\n"
        "import argumentation_lib\n"
        f"{body}\n"
    )
    out = subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=300,
    )
    assert out.returncode == 0, out.stderr[-3000:]
    # La derniere ligne JSON emitted par la sonde (liste ou objet).
    for line in reversed(out.stdout.splitlines()):
        line = line.strip()
        if not line:
            continue
        try:
            return json.loads(line)
        except json.JSONDecodeError:
            continue
    raise AssertionError(f"Aucune charge JSON dans la sortie de la sonde :\n{out.stdout[-2000:]}")


# ---------------------------------------------------------------------------
# JVM-free : the condition vocabulary
# ---------------------------------------------------------------------------


def test_unknown_condition_is_rejected_with_the_vocabulary():
    """An unknown condition fails loudly and names the accepted vocabulary."""
    handler = _handler_without_jvm()

    with pytest.raises(ValueError) as excinfo:
        handler._parse_condition("foo", {"a": None})

    message = str(excinfo.value)
    assert "foo" in message
    for attendu in ("tautology", "contradiction", "negation:", "or:", "and:"):
        assert attendu in message


def test_disjunction_requires_exactly_two_conditions():
    """`or:` with three operands is a configuration error, not a silent drop."""
    handler = _handler_without_jvm()

    with pytest.raises(ValueError) as excinfo:
        handler._parse_condition("or:negation:a,negation:b,negation:c", {})

    assert "exactement deux" in str(excinfo.value)


def test_nested_composition_is_refused_with_an_explicit_message():
    """The composition limit is one level, and the message says so.

    The vocabulary presents `or:<c1>,<c2>` / `and:<c1>,<c2>` where `c1` and
    `c2` are *conditions* — which reads as if composites could nest. The
    parser splits on commas, so `and:negation:a,or:negation:b,negation:c`
    counts THREE fragments and used to be rejected with a bare "attend
    exactement deux conditions, 3 fournie(s)", leaving the author of a
    two-condition spec without a clue about the real limit.

    The error now names the limit and gives the accepted shape.
    """
    handler = _handler_without_jvm()

    with pytest.raises(ValueError) as excinfo:
        handler._parse_condition("and:negation:a,or:negation:b,negation:c", {})

    message = str(excinfo.value)
    assert "exactement deux" in message
    assert "un seul niveau" in message
    assert "and:negation:a,negation:b" in message


def test_the_handler_refuses_to_instantiate_without_jpype():
    """Without JPype the handler says why, instead of raising a NameError.

    `ADFHandler.__init__` is the first point that genuinely needs the JVM.
    The message names the missing dependency and the way to install it, so
    a reader on a CPU-only machine is not left with a bare
    `ModuleNotFoundError` from deep inside the class body.
    """
    if jpype is not None:  # pragma: no cover - depends on the runner's wheels
        pytest.skip("jpype is installed on this runner: the refusal path is unreachable")

    with pytest.raises(RuntimeError) as excinfo:
        ADFHandler()

    message = str(excinfo.value)
    assert "jpype" in message.lower()
    assert "JPype1" in message


def test_negation_of_an_unknown_statement_is_rejected():
    """A condition citing an argument outside the framework is an error."""
    handler = _handler_without_jvm()

    with pytest.raises(ValueError) as excinfo:
        handler._parse_condition("negation:absent", {"a": None})

    message = str(excinfo.value)
    assert "absent" in message
    assert "['a']" in message


def test_kpp_reader_gates_out_explicitly():
    """`parse_adf_file` refuses to pretend it can read a KPPADF file.

    The vendored 1.30 reader needs a `LinkStrategy` and a boolean, and reading
    the jar's own `adf_example.txt` fails on `EmptyStackException`. The method
    must say so instead of raising a cryptic overload error.
    """
    handler = _handler_without_jvm()

    with pytest.raises(RuntimeError) as excinfo:
        handler.parse_adf_file("adf_example.txt", "grounded")

    message = str(excinfo.value)
    assert "1.30" in message
    assert "analyze_adf" in message


def test_reasoner_table_exposes_the_seven_adf_semantics():
    """The public table of reasoners keeps its upstream shape."""
    assert set(ADFHandler.REASONERS) == {
        "grounded",
        "complete",
        "preferred",
        "admissible",
        "model",
        "naive",
        "conflict_free",
    }
    for fqcn in ADFHandler.REASONERS.values():
        assert fqcn.startswith("org.tweetyproject.arg.adf.reasoner.")


# ---------------------------------------------------------------------------
# JVM-bound : the analysis itself (child process)
# ---------------------------------------------------------------------------

_PROBE_ANALYZE = """
handler = argumentation_lib.get_adf_handler_symbol()()
result = handler.analyze_adf({statements!r}, {conditions!r}, {semantics!r})
print(json.dumps(result["interpretations_detailed"], ensure_ascii=False))
"""


def _analyze(statements, conditions, semantics):
    return _run_probe(
        _PROBE_ANALYZE.format(
            statements=statements, conditions=conditions, semantics=semantics
        )
    )


@requires_jvm
def test_mutual_negation_leaves_both_arguments_undecided():
    """The ADF grounded interpretation of `a <-> b` decides nothing.

    This is the first measured difference from Dung: the grounded extension of
    the same framework in Dung is empty (both arguments rejected), while the
    ADF grounded interpretation leaves both *undecided*.
    """
    interpretations = _analyze(
        ["a", "b"], {"a": "negation:b", "b": "negation:a"}, "grounded"
    )

    assert len(interpretations) == 1
    interpretation = interpretations[0]
    assert interpretation["undecided"] == ["a", "b"]
    assert interpretation["accepted"] == []
    assert interpretation["rejected"] == []


@requires_jvm
def test_preferred_semantics_accepts_exactly_one_of_the_two():
    """Each preferred interpretation accepts one argument and rejects the other."""
    interpretations = _analyze(
        ["a", "b"], {"a": "negation:b", "b": "negation:a"}, "preferred"
    )

    assert len(interpretations) == 2
    for interpretation in interpretations:
        assert len(interpretation["accepted"]) == 1
        assert len(interpretation["rejected"]) == 1
        assert interpretation["undecided"] == []


@requires_jvm
def test_contradiction_condition_rejects_an_unattacked_argument():
    """A contradiction condition rejects an argument no one attacks.

    Dung cannot express that: an argument without attacker is always accepted.
    """
    interpretations = _analyze(
        ["x", "y"], {"x": "contradiction", "y": "tautology"}, "grounded"
    )

    interpretation = interpretations[0]
    assert interpretation["accepted"] == ["y"]
    assert interpretation["rejected"] == ["x"]
    assert interpretation["undecided"] == []


@requires_jvm
def test_disjunction_condition_survives_the_choice_between_a_and_b():
    """The canonical example: `c` is accepted in every MODEL.

    Scope note (this assertion is deliberately scoped to `model`): the
    notebook's claim that "the disjunction makes `c` robust to the choice
    between `a` and `b`" holds for the `model` semantics, and only for it.
    Under `preferred` the same framework yields FOUR interpretations, two
    of which REJECT `c` — see
    `test_preferred_semantics_yields_two_interpretations_rejecting_c`.
    """
    interpretations = _analyze(
        ["a", "b", "c"],
        {
            "a": "negation:b",
            "b": "negation:a",
            "c": "or:negation:a,negation:b",
        },
        "model",
    )

    assert len(interpretations) == 2
    for interpretation in interpretations:
        assert "c" in interpretation["accepted"]
        assert interpretation["undecided"] == []


@requires_jvm
def test_preferred_semantics_yields_two_interpretations_rejecting_c():
    """`preferred` rejects `c` in two of its four interpretations.

    Measured 2026-10-29 on the vendored `adf-1.30.jar`. This pins the fact
    that the notebook's section 5 must NOT generalise: the canonical
    disjunction is NOT unconditionally robust under `preferred`.

    The four interpretations of the canonical framework under `preferred`
    are:

        {t(a) f(c) u(b)}   {t(a) t(c) f(b)}
        {t(b) f(c) u(a)}   {t(b) t(c) f(a)}

    Two of them accept `c`, two reject it. The two that reject it are
    exactly the two PARTIAL ones (an argument left `u`).

    Why the rejection is not a bug (this is the point the notebook teaches):
    the value of an argument is NOT the pointwise three-valued evaluation
    of its acceptance condition over its parents' values. The decisive
    counter-measurement is `test_a_decided_argument_can_have_both_parents_undecided`.
    """
    interpretations = _analyze(
        ["a", "b", "c"],
        {
            "a": "negation:b",
            "b": "negation:a",
            "c": "or:negation:a,negation:b",
        },
        "preferred",
    )

    assert len(interpretations) == 4

    acceptant_c = [i for i in interpretations if "c" in i["accepted"]]
    rejetant_c = [i for i in interpretations if "c" in i["rejected"]]
    assert len(acceptant_c) == 2
    assert len(rejetant_c) == 2

    # The two that reject `c` are the partial ones: exactly one argument is
    # left undecided, and it is a PARENT of `c`.
    for interpretation in rejetant_c:
        assert interpretation["accepted"], interpretation
        assert interpretation["undecided"], interpretation
        assert len(interpretation["undecided"]) == 1
        assert interpretation["undecided"][0] in {"a", "b"}

    # And the two that accept `c` are the total (two-valued) ones.
    for interpretation in acceptant_c:
        assert interpretation["undecided"] == [], interpretation
        assert len(interpretation["rejected"]) == 1


@requires_jvm
def test_a_decided_argument_can_have_both_parents_undecided():
    """The value of an argument is NOT a pointwise evaluation of its condition.

    This is the decisive counter-measurement for the tempting-but-wrong
    reading of the ADF output: "the condition of `c` is
    `or:negation:a,negation:b`, so with `a = t` and `b = u` we get
    `f ∨ u = u`, hence `c` should be UNDECIDED, not rejected".

    Measured 2026-10-29 on the vendored `adf-1.30.jar`: under the
    `complete` semantics, the canonical framework yields the interpretation
    `{t(c) u(a) u(b)}` — `c` is DECIDED (`t`) while BOTH its parents are
    `u`. A pointwise evaluation would have forced `c` to be `u` in every
    such interpretation. The ADF semantics therefore decides an argument
    from the framework as a whole (through the SAT encoding), not from a
    truth table applied to the parents' three values.

    The same framework also yields `{ f(c) u(a) u(b)}` under `complete`:
    with both parents undecided, `c` is decided `t` in one interpretation
    and `f` in another. The parent's values do not determine the child's.
    """
    interpretations = _analyze(
        ["a", "b", "c"],
        {
            "a": "negation:b",
            "b": "negation:a",
            "c": "or:negation:a,negation:b",
        },
        "complete",
    )

    c_decide_avec_parents_indecis = [
        i
        for i in interpretations
        if ("c" in i["accepted"] or "c" in i["rejected"])
        and set(i["undecided"]) == {"a", "b"}
    ]
    assert c_decide_avec_parents_indecis, interpretations

    # `c` is decided in BOTH directions with both parents undecided: the
    # parent's values do not determine the child's.
    valeurs_c = {
        ("t" if "c" in i["accepted"] else "f")
        for i in c_decide_avec_parents_indecis
    }
    assert valeurs_c == {"t", "f"}, interpretations


@requires_jvm
def test_default_condition_for_a_statement_without_one_is_tautological():
    """A statement absent from the mapping is always acceptable."""
    interpretations = _analyze(["p", "q"], {"q": "negation:p"}, "grounded")

    interpretation = interpretations[0]
    assert interpretation["accepted"] == ["p"]
    assert interpretation["rejected"] == ["q"]


@requires_jvm
def test_dung_and_adf_disagree_on_the_grounded_extension_of_the_same_framework():
    """The contrast measured in the notebook: Dung empties, ADF decides nothing.

    The Dung side is read by the AF organ of the same library (Tweety's
    `SimpleGroundedReasoner`), so the two verdicts come from the same jar.
    """
    payload = _run_probe(
        """
initialiseur = argumentation_lib.get_tweety_initializer_symbol()()
initialiseur.ensure_jvm_and_components_are_ready()
initialiseur.initialize_af_components()
af = argumentation_lib.get_af_handler_symbol()(initialiseur)
dung = af.analyze_dung_framework(["a", "b"], [["a", "b"], ["b", "a"]], "grounded")
handler = argumentation_lib.get_adf_handler_symbol()()
adf = handler.analyze_adf(
    ["a", "b"], {"a": "negation:b", "b": "negation:a"}, "grounded"
)
print(json.dumps({"dung": dung["extensions"]["grounded"],
                  "adf": adf["interpretations_detailed"][0]}, ensure_ascii=False))
"""
    )

    assert payload["dung"] == [[]]
    assert payload["adf"]["undecided"] == ["a", "b"]
