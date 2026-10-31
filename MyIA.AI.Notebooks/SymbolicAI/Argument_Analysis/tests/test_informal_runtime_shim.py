"""Suite pytest du shim runtime de la couche informal (See #23633, Volet B etape 4).

Verrouille le contrat de `install_informal_runtime_shim()` (extension #18391 du
`_epita_vendor_shim`) : les deux fichiers verbatim de la couche informal
(`_taxonomy_sophism_detector.py` + `_informal_definitions.py`, epingles a8025f60)
deviennent importables au runtime SANS modifier leur contenu (integrite
verbatim = contrat, NOTICE-EPITA).

Les criteres d'acceptance de l'issue, un test par case :

1. `get_taxonomy_sophism_detector()` ne leve plus `ModuleNotFoundError`.
2. `get_informal_definitions_symbols()` expose `InformalAnalysisPlugin` importable.
3. Les deux fichiers verbatim restent intacts (aucun des modules shimes n'ecrase
   leur identite de fichier -- verifie par `__file__`).
4. Temoin negatif : sans le shim, l'import direct du detecteur leve de nouveau
   `ModuleNotFoundError` -- c'est le shim qui porte la charge.
5. `semantic_kernel` : le job CI `Scripts Tests (CPU)` ne l'installe pas ; la
   surface SK exacte que `_informal_definitions.py` importe au niveau module est
   moquee structurellement (convention `test_runner.py` #2137, avec une
   difference : chaque sous-module y est enregistre comme MODULE dote de
   `__path__`, car le fichier verbatim importe `semantic_kernel.kernel` en
   sous-module -- le mock module-level de test_runner, pose a la collection,
   est donc REMPLACE pendant chaque test puis restaure en teardown).
   Avec le vrai SK installe (regle F, machine locale), la chaine a ete
   mesuree bout-en-bout : voir NOTICE-EPITA section #23633.
6. La deviation declaree de `_epita_paths.py` fait son office : l'import ne
   recree PAS `Argument_Analysis/libs/` (retire par l'arbitrage #23109).
"""
from __future__ import annotations

import importlib
import os
import sys
from types import ModuleType

import pytest

# Rendre `argumentation_lib` importable quel que soit le rootdir/cwd de pytest.
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)

SHIM_ENTRIES = [
    "argumentation_analysis.paths",
    "argumentation_analysis.core.utils.file_loaders",
    "argumentation_analysis.utils.taxonomy_loader",
    "argumentation_lib.prompts",
    "argumentation_lib.informal_definitions",
]


# ---------------------------------------------------------------------------
# Mock structurel de semantic_kernel (surface exacte importee au niveau module
# par _informal_definitions.py:50-63 -- convention test_runner.py #2137).
# Le mock n'est pose QUE s'il n'y a pas deja un mock CoursIA (idempotence) ;
# il est RETIRE en fin de test (save/restore) pour ne pas masquer un vrai SK.
# ---------------------------------------------------------------------------
# Noms poses dans sys.modules par CE mock. Chaque sous-module importe au
# niveau module par `_informal_definitions.py:50-63` y est enregistre EN
# TANT QUE MODULE (parent dote de `__path__`) : `from semantic_kernel.kernel
# import Kernel` est un import de SOUS-MODULE, pas un acces d'attribut.
_SK_MOCK_FLAG = "_informal_shim_test_mock"

_SK_NAMES = [
    "semantic_kernel",
    "semantic_kernel.functions",
    "semantic_kernel.functions.kernel_arguments",
    "semantic_kernel.functions.kernel_function",
    "semantic_kernel.functions.kernel_function_metadata",
    "semantic_kernel.functions.kernel_parameter_metadata",
    "semantic_kernel.kernel",
    "semantic_kernel.connectors",
    "semantic_kernel.connectors.ai",
    "semantic_kernel.connectors.ai.open_ai",
    "semantic_kernel.connectors.ai.open_ai.prompt_execution_settings",
    "semantic_kernel.connectors.ai.open_ai."
    "prompt_execution_settings.open_ai_prompt_execution_settings",
    "semantic_kernel.contents",
    "semantic_kernel.contents.chat_history",
]


def _install_sk_mock() -> dict:
    """Remplace les entrees SK par le mock de CE fichier ; retourne l'etat ante.

    Le mock module-level de `test_runner.py` (#2137) est pose a la COLLECTION
    de la suite, avant toute execution : `semantic_kernel` y est un module
    SANS `__path__` et `Kernel` un simple attribut -- l'import de sous-module
    `from semantic_kernel.kernel import Kernel` du fichier verbatim y leve
    ``... is not a package``. Ce mock le REMPLACE donc systematiquement
    pendant chaque test (etat frais), et `_restore_sk_mock` remet l'etat
    ante (mock test_runner ou vrai SK) en teardown : test_runner.py, execute
    apres dans l'ordre de collection, retrouve son propre mock.
    """
    saved = {name: sys.modules.get(name) for name in _SK_NAMES}

    def _mod(name: str) -> ModuleType:
        m = ModuleType(name)
        setattr(m, _SK_MOCK_FLAG, True)
        m.__path__ = []  # package : les sous-modules resolvent via sys.modules
        sys.modules[name] = m
        return m

    sk = _mod("semantic_kernel")

    class Kernel:  # sk.Kernel (annotation evaluee au def, l.772)
        pass

    sk.Kernel = Kernel

    functions = _mod("semantic_kernel.functions")

    def kernel_function(*args, **kwargs):
        def decorator(func):
            return func

        if args and callable(args[0]) and not kwargs:
            return args[0]
        return decorator

    functions.kernel_function = kernel_function

    class KernelArguments(dict):
        pass

    functions.KernelArguments = KernelArguments
    functions.kernel_arguments = _mod(
        "semantic_kernel.functions.kernel_arguments"
    )
    functions.kernel_arguments.KernelArguments = KernelArguments

    kf = _mod("semantic_kernel.functions.kernel_function")
    kf.kernel_function = kernel_function

    class KernelFunction:  # noqa: D401 -- classe-fake, meme nom que l'amont
        pass

    kf.KernelFunction = KernelFunction

    kfm = _mod("semantic_kernel.functions.kernel_function_metadata")

    class KernelFunctionMetadata:
        pass

    kfm.KernelFunctionMetadata = KernelFunctionMetadata

    kpm = _mod("semantic_kernel.functions.kernel_parameter_metadata")

    class KernelParameterMetadata:
        pass

    kpm.KernelParameterMetadata = KernelParameterMetadata

    kmod = _mod("semantic_kernel.kernel")
    kmod.Kernel = Kernel

    _mod("semantic_kernel.connectors")
    _mod("semantic_kernel.connectors.ai")
    _mod("semantic_kernel.connectors.ai.open_ai")
    _mod(
        "semantic_kernel.connectors.ai.open_ai.prompt_execution_settings"
    )
    oai = _mod(
        "semantic_kernel.connectors.ai.open_ai."
        "prompt_execution_settings.open_ai_prompt_execution_settings"
    )

    class OpenAIChatPromptExecutionSettings:
        pass

    oai.OpenAIChatPromptExecutionSettings = OpenAIChatPromptExecutionSettings

    _mod("semantic_kernel.contents")
    ch = _mod("semantic_kernel.contents.chat_history")

    class ChatHistory:
        pass

    ch.ChatHistory = ChatHistory

    return saved


def _restore_sk_mock(saved: dict) -> None:
    for name, mod in saved.items():
        if mod is not None:
            sys.modules[name] = mod
        else:
            current = sys.modules.get(name)
            if current is not None and getattr(current, _SK_MOCK_FLAG, False):
                del sys.modules[name]  # notre mock uniquement, jamais celui d'un autre test


@pytest.fixture()
def informal_shim_env():
    """Pose le mock SK, purge l'etat informal, execute le test, restaure tout."""
    purge_names = SHIM_ENTRIES + [
        "argumentation_lib._epita_paths",
        "argumentation_lib._file_loaders",
        "argumentation_lib._taxonomy_loader",
        "argumentation_lib._prompts",
        "argumentation_lib._informal_definitions",
        "argumentation_lib._taxonomy_sophism_detector",
        "argumentation_lib._epita_vendor_shim",
    ]
    saved_modules = {name: sys.modules.pop(name, None) for name in purge_names}

    import argumentation_lib

    saved_attrs = {}
    for attr in ("prompts", "informal_definitions"):
        if hasattr(argumentation_lib, attr):
            saved_attrs[attr] = getattr(argumentation_lib, attr)
            delattr(argumentation_lib, attr)

    sk_saved = _install_sk_mock()
    try:
        yield argumentation_lib
    finally:
        _restore_sk_mock(sk_saved)
        for name in SHIM_ENTRIES:
            sys.modules.pop(name, None)
        for name, mod in saved_modules.items():
            if mod is not None:
                sys.modules[name] = mod
        for attr, value in saved_attrs.items():
            setattr(argumentation_lib, attr, value)
        # Le drapeau du shim est repose a False : le module vendu vient d'etre
        # restore depuis saved_modules (ou retire), l'installation doit pouvoir
        # rejouer au test suivant.
        shim_mod = sys.modules.get("argumentation_lib._epita_vendor_shim")
        if shim_mod is not None:
            shim_mod._informal_shim_installed = False


# ---------------------------------------------------------------------------
# Acceptance 1 : l'accesseur detecteur ne leve plus ModuleNotFoundError
# ---------------------------------------------------------------------------
def test_accessors_resolve_without_module_not_found(informal_shim_env):
    detector_cls = informal_shim_env.get_taxonomy_sophism_detector()
    assert detector_cls.__name__ == "TaxonomySophismDetector"
    # Le symbole vient bien du fichier verbatim sur disque, pas d'une fabrique.
    assert detector_cls.__module__ == "argumentation_lib._taxonomy_sophism_detector"
    import argumentation_lib._taxonomy_sophism_detector as det_mod

    assert detector_cls is det_mod.TaxonomySophismDetector


# ---------------------------------------------------------------------------
# Acceptance 2 : les 5 symboles publics informal sont exposables
# ---------------------------------------------------------------------------
def test_get_informal_definitions_symbols_expose_le_plugin(informal_shim_env):
    (
        plugin,
        identified,
        result,
        setup,
        instructions,
    ) = informal_shim_env.get_informal_definitions_symbols()
    assert plugin.__name__ == "InformalAnalysisPlugin"
    assert identified.__name__ == "IdentifiedFallacy"
    assert result.__name__ == "FallacyAnalysisResult"
    assert callable(setup)
    assert isinstance(instructions, str) and instructions


# ---------------------------------------------------------------------------
# Integrite : les fichiers verbatim restent LES fichiers sur disque
# ---------------------------------------------------------------------------
def test_les_modules_shimes_sont_les_fichiers_vendus(informal_shim_env):
    informal_shim_env.get_informal_definitions_symbols()
    import argumentation_lib._informal_definitions as informal_mod
    import argumentation_lib._prompts as prompts_mod

    assert informal_mod.__file__.endswith(
        os.path.join("argumentation_lib", "_informal_definitions.py")
    )
    assert prompts_mod.__file__.endswith(
        os.path.join("argumentation_lib", "_prompts.py")
    )
    # Les alias siblings pointent vers les MEMES objets module.
    assert sys.modules["argumentation_lib.informal_definitions"] is informal_mod
    assert sys.modules["argumentation_lib.prompts"] is prompts_mod


# ---------------------------------------------------------------------------
# Helpers amont : exposes sous leurs noms upstream, fonctionnels
# ---------------------------------------------------------------------------
def test_helpers_amont_exposes_sous_leurs_noms(informal_shim_env):
    informal_shim_env.get_informal_definitions_symbols()
    from argumentation_analysis.paths import DATA_DIR  # noqa: F401 -- resolution
    from argumentation_analysis.core.utils.file_loaders import load_csv_file
    from argumentation_analysis.utils.taxonomy_loader import get_taxonomy_path

    assert callable(load_csv_file)
    assert callable(get_taxonomy_path)


# ---------------------------------------------------------------------------
# Acceptance 4 : temoin negatif -- sans le shim, le bris revient
# ---------------------------------------------------------------------------
def test_temoin_negatif_sans_shim_le_bris_revient(informal_shim_env):
    # Installer une fois pour prouver que la chaine marche dans CE process...
    informal_shim_env.get_taxonomy_sophism_detector()
    # ...puis retirer le shim (entrees + alias + modules caches) et verifier
    # que l'import direct du detecteur re-leve l'empreinte du bris.
    import argumentation_lib

    for name in SHIM_ENTRIES:
        sys.modules.pop(name, None)
    for attr in ("prompts", "informal_definitions"):
        if hasattr(argumentation_lib, attr):
            delattr(argumentation_lib, attr)
    sys.modules.pop("argumentation_lib._taxonomy_sophism_detector", None)

    with pytest.raises(ModuleNotFoundError) as excinfo:
        importlib.import_module("argumentation_lib._taxonomy_sophism_detector")
    # Couche 1 : l'empreinte exacte mesuree au scoping de l'issue.
    assert "argumentation_lib.informal_definitions" in str(excinfo.value)


# ---------------------------------------------------------------------------
# Acceptance 6 : la deviation declaree de _epita_paths fait son office
# ---------------------------------------------------------------------------
def test_import_epita_paths_ne_recree_pas_libs():
    # Test isole (hors fixture) : l'import de _epita_paths ne doit PAS creer
    # Argument_Analysis/libs/ -- la deviation NOT-VERBATIM declaree supprime
    # l'appel module-level ensure_directories_exist() (arbitrage #23109).
    if _ARG_ANALYSIS_DIR not in sys.path:
        sys.path.insert(0, _ARG_ANALYSIS_DIR)
    importlib.import_module("argumentation_lib._epita_paths")
    libs_dir = os.path.join(_ARG_ANALYSIS_DIR, "libs")
    assert not os.path.exists(libs_dir), (
        "L'import de _epita_paths.py a recree Argument_Analysis/libs/ "
        "(retire par l'arbitrage #23109) -- la deviation declaree est cassee"
    )


# ---------------------------------------------------------------------------
# Bonus contrat : DATA_DIR vendo reste dans le perimetre du paquet
# ---------------------------------------------------------------------------
def test_data_dir_amont_dans_le_perimetre_du_paquet(informal_shim_env):
    informal_shim_env.get_informal_definitions_symbols()
    from argumentation_analysis.paths import DATA_DIR

    # Semantique amont vendoee : DATA_DIR = ROOT_DIR/"data" ou ROOT_DIR est le
    # repertoire du module paths -> argumentation_lib/data (pas d'ecriture hors
    # perimetre du paquet au seul niveau de la constante).
    assert str(DATA_DIR).replace("\\", "/").endswith("argumentation_lib/data")
