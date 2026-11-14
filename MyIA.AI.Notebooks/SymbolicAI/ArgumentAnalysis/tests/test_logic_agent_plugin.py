# test_logic_agent_plugin.py — contrat de l'adaptateur LogicAgentPlugin (#18390)
#
# Verrouille le contrat de la moitie VERDICT de la phase formelle :
#   - surface : les 8 @kernel_function de l'inventaire EPITA du 27/10,
#     constructibles a zero argument
#   - gardes #23120 AVANT le solveur : une phrase (prose) rend une erreur
#     de contenu, pas un verdict ; `->` est reecrit en `=>`
#   - moities FOL/Modales : erreur honnete et precise, AUCUN verdict
#     simule (aucune cle accepted/is_consistent)
#   - integration : le VRAI solveur Tweety decide via l'adaptateur
#     (marquee, sautee sans les jars — meme garde que
#     test_pl_verdict_contract.py)
#
# semantic_kernel n'est pas une dependance dure : meme mock minimal que
# test_pl_verdict_contract.py / test_state_manager_plugin.py.

from __future__ import annotations

import json
import os
import sys
from types import ModuleType

import pytest

_THIS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARGUMENT_ANALYSIS_DIR = os.path.dirname(_THIS_DIR)
if _ARGUMENT_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARGUMENT_ANALYSIS_DIR)


def _install_sk_mock() -> None:
    """Mock semantic_kernel si absent (meme strategie que les tests voisins)."""
    if "semantic_kernel" in sys.modules:
        return

    sk = ModuleType("semantic_kernel")
    functions = ModuleType("semantic_kernel.functions")

    def kernel_function(*args, **kwargs):
        def decorator(func):
            return func

        if args and callable(args[0]) and not kwargs:
            return args[0]
        return decorator

    functions.kernel_function = kernel_function
    sk.functions = functions
    sys.modules["semantic_kernel"] = sk
    sys.modules["semantic_kernel.functions"] = functions


_install_sk_mock()

from argumentation_lib import get_logic_agent_plugin_symbol  # noqa: E402
from argumentation_lib._logic_agent_plugin import LogicAgentPlugin  # noqa: E402


# --------------------------------------------------------------------------
# Surface : 8 fonctions moteur, constructibles a zero argument
# --------------------------------------------------------------------------

EXPECTED_FUNCTIONS = [
    "parse_pl_formula",
    "execute_pl_query",
    "check_pl_consistency",
    "execute_fol_query",
    "check_fol_consistency",
    "execute_modal_query",
    "check_modal_consistency",
    "validate_formula",
]


def test_accessor_exposes_plugin():
    """`get_logic_agent_symbol` (l'accessor __init__) rend la meme classe."""
    assert get_logic_agent_plugin_symbol() is LogicAgentPlugin


def test_surface_8_kernel_functions():
    """L'inventaire EPITA du 27/10 compte 8 @kernel_function : elles y sont."""
    plugin = LogicAgentPlugin()
    for name in EXPECTED_FUNCTIONS:
        assert callable(getattr(plugin, name, None)), (
            f"fonction moteur absente de la surface : {name}"
        )


def test_zero_arg_construction():
    """L'inventaire EPITA exige une construction a zero argument (15/18)."""
    plugin = LogicAgentPlugin()
    assert plugin._engine is None


# --------------------------------------------------------------------------
# Gardes #23120 : AVANT le solveur, sans exiger la JVM
# --------------------------------------------------------------------------


def test_parse_prose_rejected_before_solver():
    """Une phrase n'est pas une formule (regression #23120, garde amont)."""
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.parse_pl_formula("Si elle pleut alors la route est mouillee"))
    assert out["is_valid"] is False
    assert "propositionnelle" in out["error"]


def test_parse_arrow_normalized_not_prose_error():
    """`->` est reecrit en `=>` : l'erreur renvoyee n'est PAS une erreur de
    contenu (la garde passe), c'est au pire l'indisponibilite moteur."""
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.parse_pl_formula("R1 -> R2"))
    assert "propositionnelle" not in json.dumps(out)


def test_pl_query_prose_belief_set_rejected():
    plugin = LogicAgentPlugin()
    payload = json.dumps({"belief_set": "Il pleut donc la route est mouillee", "query": "mouillee"})
    out = json.loads(plugin.execute_pl_query(payload))
    assert "error" in out
    assert "propositionnelle" in out["error"]
    assert "accepted" not in out


def test_pl_query_prose_query_rejected():
    plugin = LogicAgentPlugin()
    payload = json.dumps({"belief_set": "a => b\na", "query": "est-ce que b"})
    out = json.loads(plugin.execute_pl_query(payload))
    assert "error" in out
    assert "requête non propositionnelle" in out["error"]


def test_pl_query_empty_belief_set():
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.execute_pl_query(json.dumps({"belief_set": "", "query": "b"})))
    assert "vide" in out["error"]


def test_pl_query_bad_payload():
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.execute_pl_query("ceci n'est pas du json"))
    assert "payload illisible" in out["error"]


def test_consistency_empty_belief_set_convention():
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.check_pl_consistency(""))
    assert out["is_consistent"] is True
    assert "convention" in out["message"]


def test_consistency_prose_rejected():
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.check_pl_consistency("Toute action juste est permise"))
    assert "error" in out
    assert "propositionnelle" in out["error"]


# --------------------------------------------------------------------------
# Moities FOL/Modales : erreur honnete, JAMAIS un verdict simule
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    "call",
    [
        lambda p: p.execute_fol_query('{"belief_set": "forall X: p(X)", "query": "exists Y: p(Y)"}'),
        lambda p: p.check_fol_consistency("forall X: p(X)"),
        lambda p: p.execute_modal_query('{"belief_set": "[](a => b)", "query": "[](a)", "logic_type": "K"}'),
        lambda p: p.check_modal_consistency('{"belief_set": "[](a)", "logic_type": "S5"}'),
    ],
    ids=["fol-query", "fol-consistency", "modal-query", "modal-consistency"],
)
def test_fol_modal_honest_error_never_simulated(call):
    """Erreur precise nommant ce qui manque ; aucune cle de verdict."""
    out = json.loads(call(LogicAgentPlugin()))
    assert "error" in out
    assert "indisponible" in out["error"]
    # Jamais un verdict simule : aucune des cles de decision amont.
    assert "accepted" not in out
    assert "is_consistent" not in out
    assert "result" not in out


def test_validate_formula_propositional_routes_to_pl():
    plugin = LogicAgentPlugin()
    out = json.loads(
        plugin.validate_formula(json.dumps({"formula": "Si a alors b", "logic_type": "propositional"}))
    )
    assert out["logic_type"] == "propositional"
    assert out["is_valid"] is False


def test_validate_formula_fol_honest_error():
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.validate_formula(json.dumps({"formula": "forall X: p(X)", "logic_type": "fol"})))
    assert "indisponible" in out["error"]


def test_validate_formula_unknown_logic_type():
    plugin = LogicAgentPlugin()
    out = json.loads(plugin.validate_formula(json.dumps({"formula": "a", "logic_type": "temporel"})))
    assert "Unknown logic_type" in out["error"]


# --------------------------------------------------------------------------
# Integration : le VRAI solveur decide via l'adaptateur (marquee)
# --------------------------------------------------------------------------

#: Sonde executee en sous-processus : l'adaptateur est exercé de bout en
#: bout (zero argument, JVM reelle) et rend ses verdicts dans le stdout.
_REAL_PROBE = """
import json
import sys

sys.path.insert(0, sys.argv.pop(1))
from argumentation_lib._logic_agent_plugin import LogicAgentPlugin

plugin = LogicAgentPlugin()

# Modus ponens : R1 -> R2 (reecrit en =>) + R1 rend R2 accepte.
out = json.loads(
    plugin.execute_pl_query(
        json.dumps({"belief_set": "R1 -> R2\\nR1", "query": "R2"})
    )
)
print("MP_ACCEPTED=" + str(out.get("accepted")))
print("MP_HAS_ERROR=" + str("error" in out))

# Coherence : a && !a est incoherent, decide par la sonde ex falso.
inc = json.loads(plugin.check_pl_consistency("a\\n!a"))
print("INCONSISTENT=" + str(inc.get("is_consistent")))

# Coherence : modus ponens coherent.
cons = json.loads(plugin.check_pl_consistency("a => b\\na"))
print("CONSISTENT=" + str(cons.get("is_consistent")))

# Parse : formule valide, et formule cassee (erreur de syntaxe du parseur).
ok = json.loads(plugin.parse_pl_formula("a => (b || !c)"))
print("PARSE_VALID=" + str(ok.get("is_valid")))
bad = json.loads(plugin.parse_pl_formula("a =>"))
print("PARSE_INVALID=" + str(bad.get("is_valid")))
print("PARSE_BAD_HAS_ERROR=" + str(bad.get("error") is not None))
"""


def _tweety_jars_present() -> bool:
    """Vrai si les jars Tweety sont provisions (ils ne sont pas versionnes)."""
    try:
        from argumentation_lib._paths import get_tweety_jar_dir

        jar_dir = get_tweety_jar_dir()
        return bool(jar_dir) and os.path.isdir(str(jar_dir))
    except Exception:
        return False


@pytest.mark.skipif(
    not _tweety_jars_present(),
    reason="jars Tweety absents : provisionner via "
    "Tweety/scripts/download_tweety_tools.py --jars --jdk",
)
def test_real_solver_through_adapter():
    """Le VRAI solveur decide a travers l'adaptateur (mandat anti-theatre
    #2137) : la JVM vit et meurt dans le sous-processus."""
    import subprocess

    proc = subprocess.run(
        [sys.executable, "-c", _REAL_PROBE, _ARGUMENT_ANALYSIS_DIR],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=600,
    )
    assert proc.returncode == 0, (
        f"la sonde a echoue (rc={proc.returncode})\n"
        f"stdout:\n{proc.stdout[-2000:]}\nstderr:\n{proc.stderr[-2000:]}"
    )
    assert "MP_ACCEPTED=True" in proc.stdout, proc.stdout
    assert "MP_HAS_ERROR=False" in proc.stdout, proc.stdout
    assert "INCONSISTENT=False" in proc.stdout, proc.stdout
    assert "CONSISTENT=True" in proc.stdout, proc.stdout
    assert "PARSE_VALID=True" in proc.stdout, proc.stdout
    assert "PARSE_INVALID=False" in proc.stdout, proc.stdout
    assert "PARSE_BAD_HAS_ERROR=True" in proc.stdout, proc.stdout
