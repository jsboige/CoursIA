"""Paramètres des fonctions kernel de `argumentation_lib` (See #28671).

Semantic Kernel injecte lui-même la valeur de quatre noms de paramètres :
`kernel`, `service`, `execution_settings` et `arguments`
(`semantic_kernel/functions/kernel_function_from_method.py`,
`gather_function_parameters`). Une fonction kernel qui déclare l'un d'eux ne
reçoit jamais la valeur de la clé : `arguments` reçoit l'objet
`KernelArguments` entier. Le verbatim amont nommait ainsi le paramètre de
`StateManagerPlugin.add_identified_arguments`, et l'outil de masse enregistrait
le snapshot d'état comme argument.

Trois gardes, parce que `Scripts Tests (CPU)` n'installe pas Semantic Kernel :

- **statique, sans dépendance** : aucune fonction décorée par
  `kernel_function` dans la lib ne déclare un paramètre réservé, hors le
  fichier verbatim annoté, et chaque fonction ainsi annotée a une surcharge
  dans `GuardedStateManagerPlugin`. C'est ce que la CI exerce.
- **en Python direct, sans dépendance** : la surcharge compte les arguments
  réellement écrits.
- **par le kernel, avec le vrai Semantic Kernel** : l'outil de masse du plugin
  gardé enregistre une formulation par élément de la liste. Elle tourne dans
  un interpréteur séparé — celui de l'utilisateur, sans le simulacre de
  Semantic Kernel que posent les modules voisins — et est sautée si le paquet
  n'est pas installé.

Le test du verbatim épingle son comportement par le kernel : si une
re-vendorisation corrige son paramètre, ce test rougit, et la surcharge devient
redondante — aller voir.
"""

from __future__ import annotations

import ast
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

_TESTS_DIR = Path(__file__).resolve().parent
_SERIES_DIR = _TESTS_DIR.parent
if str(_SERIES_DIR) not in sys.path:
    sys.path.insert(0, str(_SERIES_DIR))

_LIB_DIR = _SERIES_DIR / "argumentation_lib"
_VERBATIM = "_state_manager_plugin.py"
_GARDE = "_guarded_state.py"

#: Noms que Semantic Kernel injecte lui-même (lus dans 1.42.0,
#: `gather_function_parameters`, lignes 158-169).
RESERVED = ("kernel", "service", "execution_settings", "arguments")

#: Fonctions du fichier verbatim (copie de l'amont EPITA, non modifiable) qui
#: portent un paramètre réservé, avec la surcharge qui les neutralise dans
#: `_guarded_state.py`. Toute autre entrée est un défaut.
NEUTRALISEES = {
    (_VERBATIM, "add_identified_arguments", "arguments"),
}

FORMULATIONS = [
    "tous les experts s'accordent à dire que le projet est utile",
    "soit on finance le projet, soit on abandonne toute innovation",
    "les coûts sont élevés mais le bénéfice attendu justifie l'investissement",
]


# -- analyse statique -------------------------------------------------------
def _decorator_name(node: ast.expr) -> str | None:
    """Nom terminal d'un décorateur, appelé ou non."""
    if isinstance(node, ast.Call):
        node = node.func
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Name):
        return node.id
    return None


def kernel_functions(source: str, filename: str = "<source>") -> dict[str, list[str]]:
    """Paramètres de chaque fonction décorée par `kernel_function`, hors `self` et `cls`."""
    fonctions: dict[str, list[str]] = {}
    for node in ast.walk(ast.parse(source, filename=filename)):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if not any(_decorator_name(d) == "kernel_function" for d in node.decorator_list):
            continue
        arguments = node.args
        positions = [
            parametre.arg
            for parametre in arguments.posonlyargs + arguments.args
            if parametre.arg not in ("self", "cls")
        ]
        fonctions[node.name] = positions + [p.arg for p in arguments.kwonlyargs]
    return fonctions


def parametres_reserves(source: str, filename: str = "<source>") -> list[tuple[str, str]]:
    """(fonction, paramètre) de chaque fonction kernel à paramètre réservé."""
    return [
        (nom, parametre)
        for nom, parametres in kernel_functions(source, filename).items()
        for parametre in parametres
        if parametre in RESERVED
    ]


def test_la_lib_ne_declare_aucun_parametre_reserve_hors_verbatim_annote():
    trouve = [
        (chemin.name, fonction, parametre)
        for chemin in sorted(_LIB_DIR.rglob("*.py"))
        for fonction, parametre in parametres_reserves(
            chemin.read_text(encoding="utf-8"), str(chemin)
        )
    ]
    assert [t for t in trouve if t not in NEUTRALISEES] == []


def test_chaque_fonction_verbatim_annotee_a_une_surcharge_gardee():
    verbatim = kernel_functions(
        (_LIB_DIR / _VERBATIM).read_text(encoding="utf-8"), _VERBATIM
    )
    garde = kernel_functions((_LIB_DIR / _GARDE).read_text(encoding="utf-8"), _GARDE)
    for fichier, fonction, parametre in sorted(NEUTRALISEES):
        assert fichier == _VERBATIM, "seul le fichier verbatim peut être annoté"
        assert fonction in verbatim, f"{_VERBATIM} n'a plus de fonction {fonction}"
        assert parametre in verbatim[fonction], (
            f"annotation périmée : {_VERBATIM}::{fonction} n'a plus de paramètre "
            f"{parametre!r} — retirer l'entrée"
        )
        assert fonction in garde, f"{_GARDE} ne surcharge pas {fonction}"
        assert not set(garde[fonction]) & set(RESERVED), (
            f"la surcharge de {fonction} garde un paramètre réservé : {garde[fonction]}"
        )


def test_la_garde_voit_les_quatre_noms_sur_une_fonction_kernel():
    source = (
        "from semantic_kernel.functions import kernel_function\n"
        "class P:\n"
        "    @kernel_function(description='sans appel', name='f_sync')\n"
        "    def f_sync(self, kernel, service, execution_settings, arguments, x):\n"
        "        return 'OK'\n"
        "\n"
        "    @kernel_function(name='f_async')\n"
        "    async def f_async(self, *, arguments, descriptions):\n"
        "        return 'OK'\n"
    )
    fonctions = kernel_functions(source)
    assert fonctions["f_sync"] == ["kernel", "service", "execution_settings", "arguments", "x"]
    assert fonctions["f_async"] == ["arguments", "descriptions"]
    assert parametres_reserves(source) == [
        ("f_sync", "kernel"),
        ("f_sync", "service"),
        ("f_sync", "execution_settings"),
        ("f_sync", "arguments"),
        ("f_async", "arguments"),
    ]


def test_une_fonction_ordinaire_peut_garder_un_parametre_arguments():
    source = (
        "class P:\n"
        "    def ecrire(self, arguments):\n"
        "        return len(arguments)\n"
    )
    assert kernel_functions(source) == {}
    assert parametres_reserves(source) == []


# -- surcharge, en Python direct -------------------------------------------
def _sk_absent() -> bool:
    try:
        return importlib.util.find_spec("semantic_kernel") is None
    except ImportError:
        return True


def _install_sk_mock() -> None:
    """Simulacre de `semantic_kernel` s'il est absent (motif des voisins).

    `_guarded_state` importe `semantic_kernel.functions.kernel_function` au
    niveau module : sans Semantic Kernel installé, l'import du fichier seul
    échoue. Même stratégie que `test_task_answer_guard.py`, sans remplacer le
    vrai paquet quand il est installé.
    """
    if "semantic_kernel" in sys.modules or not _sk_absent():
        return

    from types import ModuleType

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


def _plugin_garde(etat):
    _install_sk_mock()
    from argumentation_lib._guarded_state import GuardedStateManagerPlugin

    return GuardedStateManagerPlugin(etat)


def test_la_surcharge_compte_les_arguments_ecrits():
    from argumentation_lib import UnifiedAnalysisState

    etat = UnifiedAnalysisState("texte de test")
    plugin = _plugin_garde(etat)
    assert (
        plugin.add_identified_arguments(["premier argument", "second argument"])
        == "OK: 2 arguments ajoutés."
    )
    assert list(etat.identified_arguments.values()) == [
        "premier argument",
        "second argument",
    ]
    assert plugin.add_identified_arguments(["troisième argument"]) == "OK: 1 argument ajouté."


def test_une_cle_d_etat_n_est_pas_comptee_comme_un_argument():
    from argumentation_lib import UnifiedAnalysisState

    etat = UnifiedAnalysisState("texte de test")
    plugin = _plugin_garde(etat)
    assert plugin.add_identified_arguments(["analysis_state", "vrai argument"]) == (
        "OK: 1 argument ajouté."
    )
    assert list(etat.identified_arguments.values()) == ["vrai argument"]


def test_aucune_formulation_ecrite_est_un_refus_visible():
    from argumentation_lib import UnifiedAnalysisState

    etat = UnifiedAnalysisState("texte de test")
    plugin = _plugin_garde(etat)
    for charge in ([], ["analysis_state"], ["  "]):
        retour = plugin.add_identified_arguments(charge)
        assert retour.startswith("FUNC_ERROR: aucune formulation enregistrée"), retour
    assert etat.identified_arguments == {}


# -- par le kernel, avec le vrai Semantic Kernel ----------------------------
_SONDE = r'''
import asyncio
import importlib.metadata as md
import json
import sys

sys.path.insert(0, sys.argv[1])
try:
    from semantic_kernel import Kernel
    from semantic_kernel.functions import KernelArguments
except ImportError as erreur:
    print("SONDE " + json.dumps({"semantic_kernel": None, "raison": str(erreur)}))
    raise SystemExit(0)

from argumentation_lib import UnifiedAnalysisState
from argumentation_lib._guarded_state import GuardedStateManagerPlugin
from argumentation_lib._state_manager_plugin import StateManagerPlugin

FORMULATIONS = [
    "tous les experts s'accordent à dire que le projet est utile",
    "soit on finance le projet, soit on abandonne toute innovation",
    "les coûts sont élevés mais le bénéfice attendu justifie l'investissement",
]


async def appel(classe, cle, valeur):
    """Un appel par le kernel, comme celui d'un agent : le snapshot plus la charge utile."""
    etat = UnifiedAnalysisState("Voici mon raisonnement.")
    snapshot = json.dumps(etat.get_state_snapshot(summarize=True), ensure_ascii=False)
    noyau = Kernel()
    expose = noyau.add_plugin(classe(etat), plugin_name="StateManager")
    fonction = expose["add_identified_arguments"]
    charge = {} if cle is None else {cle: valeur}
    arguments = KernelArguments(analysis_state=snapshot, **charge)
    retour, erreur = None, None
    try:
        resultat = await noyau.invoke(fonction, arguments=arguments)
        retour = str(resultat.value)
    except Exception as e:
        erreur = f"{type(e).__name__}: {e}"
    return {
        "parametres": [p.name for p in fonction.parameters],
        "retour": retour,
        "erreur": erreur,
        "stocke": list(etat.identified_arguments.values()),
    }, snapshot


async def main():
    mesures, snapshots = {}, {}
    cas = {
        "garde": (GuardedStateManagerPlugin, "descriptions", FORMULATIONS),
        "garde_cle_ancienne": (GuardedStateManagerPlugin, "arguments", FORMULATIONS),
        "garde_sans_charge": (GuardedStateManagerPlugin, None, None),
        "garde_chaine_seule": (GuardedStateManagerPlugin, "descriptions", FORMULATIONS[0]),
        "verbatim": (StateManagerPlugin, "arguments", FORMULATIONS),
    }
    for nom, (classe, cle, valeur) in cas.items():
        mesures[nom], snapshots[nom] = await appel(classe, cle, valeur)
    print("SONDE " + json.dumps(
        {"semantic_kernel": md.version("semantic_kernel"),
         "mesures": mesures, "snapshots": snapshots}, ensure_ascii=False))


asyncio.run(main())
'''


@pytest.fixture(scope="module")
def sonde_kernel():
    proc = subprocess.run(
        [sys.executable, "-c", _SONDE, str(_SERIES_DIR)],
        capture_output=True,
        encoding="utf-8",
        timeout=300,
        env={**os.environ, "PYTHONIOENCODING": "utf-8", "PYTHONUTF8": "1"},
    )
    lignes = [ligne for ligne in proc.stdout.splitlines() if ligne.startswith("SONDE ")]
    assert lignes, f"sonde muette (rc={proc.returncode}) : {proc.stderr[-800:]}"
    mesure = json.loads(lignes[-1][len("SONDE "):])
    if mesure["semantic_kernel"] is None:
        pytest.skip(f"Semantic Kernel absent : {mesure['raison']}")
    return mesure["mesures"], mesure["snapshots"]


def test_l_outil_de_masse_du_plugin_garde_enregistre_les_formulations(sonde_kernel):
    mesures, _ = sonde_kernel
    garde = mesures["garde"]
    assert garde["parametres"] == ["descriptions"]
    assert garde["erreur"] is None
    assert garde["retour"] == "OK: 3 arguments ajoutés."
    assert garde["stocke"] == FORMULATIONS


def test_le_verbatim_recoit_l_objet_des_arguments_entier(sonde_kernel):
    mesures, snapshots = sonde_kernel
    verbatim = mesures["verbatim"]
    assert verbatim["parametres"] == ["arguments"]
    assert verbatim["retour"] == "OK: 2 arguments ajoutés."
    assert verbatim["stocke"] == [snapshots["verbatim"], str(FORMULATIONS)], (
        "le verbatim amont ne porte plus le défaut : la surcharge de "
        "`GuardedStateManagerPlugin` est peut-être devenue redondante (#28671)"
    )


@pytest.mark.parametrize(
    "cas", ["garde_cle_ancienne", "garde_sans_charge", "garde_chaine_seule"]
)
def test_une_charge_invalide_n_ecrit_rien_et_remonte_a_l_appelant(sonde_kernel, cas):
    mesures, _ = sonde_kernel
    mesure = mesures[cas]
    assert mesure["parametres"] == ["descriptions"]
    assert mesure["stocke"] == []
    assert mesure["retour"] is None
    assert mesure["erreur"].startswith("KernelInvokeException"), mesure["erreur"]
