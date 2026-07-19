"""Tests pour le module ``tweety_init`` (initialisation partagee Tweety).

Couvre les contrats du module d'init consomme par les notebooks Tweety :
  - ``get_tool_path`` : resolution de chemin d'outil externe (empty/which/file/dir/invalid)
  - ``_detect_tools`` : auto-detection CLINGO/SPASS/EPROVER/SAT/MARCO (mutate global)
  - ``_find_jdk_portable`` / ``_find_libs_dir`` : recherche JDK portable + dossier libs
  - ``init_tweety`` : branches early-return (JVM deja lancee, JAVA_HOME absent, libs absent, jars absents) via mock jpype
  - ``print_tools_summary`` : format de sortie (capsys)

Le module importe ``jpype`` LAZILY (a l'interieur de ``init_tweety``), donc
l'import du module lui-meme ne requiert pas jpype -> tests hermetiques stdlib-only.
``init_tweety`` est exerce en injectant un faux ``jpype`` dans ``sys.modules``.

Run with: pytest Tweety/test_tweety_init.py -v
"""

import sys
import types
from pathlib import Path

import pytest

# Module sous test : SymbolicAI/Tweety/tweety_init.py
# Ce test :          SymbolicAI/Tweety/test_tweety_init.py
sys.path.insert(0, str(Path(__file__).resolve().parent))

import tweety_init as t  # noqa: E402


# --------------------------------------------------------------------------- #
#  Fixture : snapshot/restore de la globale EXTERNAL_TOOLS                    #
# --------------------------------------------------------------------------- #
# Le module auto-execute ``_detect_tools()`` a l'import et plusieurs tests
# mute EXTERNAL_TOOLS -> on snapshot l'etat a l'entree et restore en sortie.

@pytest.fixture
def tools_snapshot():
    saved = dict(t.EXTERNAL_TOOLS)
    yield
    t.EXTERNAL_TOOLS.clear()
    t.EXTERNAL_TOOLS.update(saved)


# --------------------------------------------------------------------------- #
#  get_tool_path                                                              #
# --------------------------------------------------------------------------- #

class TestGetToolPath:
    """get_tool_path : empty->None, which/file/dir resolus, invalid->None."""

    def test_empty_string_returns_none(self, tools_snapshot):
        t.EXTERNAL_TOOLS["CLINGO"] = ""
        assert t.get_tool_path("CLINGO") is None

    def test_unknown_tool_returns_none(self, tools_snapshot):
        # Outil hors du dict -> .get default "" -> None.
        assert t.get_tool_path("DOES_NOT_EXIST") is None

    def test_file_path_resolves(self, tools_snapshot, tmp_path):
        f = tmp_path / "clingo.exe"
        f.write_text("x")
        t.EXTERNAL_TOOLS["CLINGO"] = str(f)
        result = t.get_tool_path("CLINGO")
        assert result == str(f.resolve())

    def test_directory_path_resolves(self, tools_snapshot, tmp_path):
        t.EXTERNAL_TOOLS["SPASS"] = str(tmp_path)
        result = t.get_tool_path("SPASS")
        assert result == str(tmp_path.resolve())

    def test_invalid_path_returns_none(self, tools_snapshot, tmp_path):
        t.EXTERNAL_TOOLS["EPROVER"] = str(tmp_path / "nonexistent_tool")
        assert t.get_tool_path("EPROVER") is None

    def test_which_resolvable_returns_string(self, tools_snapshot):
        # ``python`` est sur le PATH dans tout env de test.
        t.EXTERNAL_TOOLS["MARCO"] = "python"
        result = t.get_tool_path("MARCO")
        # shutil.which trouve python -> retourne la string elle-meme.
        assert result == "python"


# --------------------------------------------------------------------------- #
#  _find_jdk_portable + _find_libs_dir                                        #
# --------------------------------------------------------------------------- #

class TestFinders:
    """Recherche JDK portable et dossier libs (depend de cwd)."""

    def test_find_jdk_portable_finds_zulu(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        jdk = tmp_path / "jdk-17-portable" / "zulu-17.44.13"
        jdk.mkdir(parents=True)
        result = t._find_jdk_portable()
        assert result is not None
        assert result.name.startswith("zulu")

    def test_find_jdk_portable_no_jdk_returns_none(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        assert t._find_jdk_portable() is None

    def test_find_jdk_portable_empty_dir_returns_none(self, tmp_path, monkeypatch):
        # jdk-17-portable/ existe MAIS sans sous-dossier zulu*.
        monkeypatch.chdir(tmp_path)
        (tmp_path / "jdk-17-portable").mkdir()
        assert t._find_jdk_portable() is None

    def test_find_libs_dir_founds_local(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        (tmp_path / "libs").mkdir()
        result = t._find_libs_dir()
        assert result is not None
        assert result.name == "libs"

    def test_find_libs_dir_none(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        assert t._find_libs_dir() is None


# --------------------------------------------------------------------------- #
#  _detect_tools (mutate EXTERNAL_TOOLS via fake ext_tools)                   #
# --------------------------------------------------------------------------- #

class TestDetectTools:
    """_detect_tools : peuple EXTERNAL_TOOLS depuis ext_tools/ ou le PATH."""

    def test_detect_sat_solver_python_from_ext_tools(self, tmp_path, monkeypatch, tools_snapshot):
        # SAT_SOLVER_PYTHON cherche ../ext_tools/sat_solver.py ou ext_tools/sat_solver.py.
        monkeypatch.chdir(tmp_path)
        (tmp_path / "ext_tools" / "sat_solver.py").parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / "ext_tools" / "sat_solver.py").write_text("# fake")
        # Reinit puis detecte.
        t.EXTERNAL_TOOLS["SAT_SOLVER_PYTHON"] = ""
        t._detect_tools()
        assert t.EXTERNAL_TOOLS["SAT_SOLVER_PYTHON"] != ""
        assert "sat_solver.py" in t.EXTERNAL_TOOLS["SAT_SOLVER_PYTHON"]

    def test_detect_marco_from_ext_tools(self, tmp_path, monkeypatch, tools_snapshot):
        monkeypatch.chdir(tmp_path)
        (tmp_path / "ext_tools").mkdir(exist_ok=True)
        (tmp_path / "ext_tools" / "marco.py").write_text("# fake")
        t.EXTERNAL_TOOLS["MARCO"] = ""
        t._detect_tools()
        assert t.EXTERNAL_TOOLS["MARCO"] != ""
        assert "marco.py" in t.EXTERNAL_TOOLS["MARCO"]

    def test_detect_eprover_executable_from_ext_tools(self, tmp_path, monkeypatch, tools_snapshot):
        # EProver cherche ext_tools/EProver/eprover[.exe].
        monkeypatch.chdir(tmp_path)
        exe = tmp_path / "ext_tools" / "EProver" / ("eprover" + (".exe" if sys.platform == "win32" else ""))
        exe.parent.mkdir(parents=True, exist_ok=True)
        exe.write_text("# fake exe")
        t.EXTERNAL_TOOLS["EPROVER"] = ""
        t._detect_tools()
        assert t.EXTERNAL_TOOLS["EPROVER"] != ""
        assert "eprover" in t.EXTERNAL_TOOLS["EPROVER"]

    def test_detect_tools_empty_env_leaves_unfound_empty(self, tmp_path, monkeypatch, tools_snapshot):
        # Aucun ext_tools, aucun outil sur PATH (cwd isole) -> les outils non
        # trouves restent vides (pas d'exception).
        monkeypatch.chdir(tmp_path)
        for k in t.EXTERNAL_TOOLS:
            t.EXTERNAL_TOOLS[k] = ""
        t._detect_tools()
        # SAT_SOLVER_PYTHON et MARCO (path-based only) restent vides sans ext_tools.
        assert t.EXTERNAL_TOOLS["SAT_SOLVER_PYTHON"] == ""
        assert t.EXTERNAL_TOOLS["MARCO"] == ""


# --------------------------------------------------------------------------- #
#  init_tweety (early-return branches via fake jpype)                         #
# --------------------------------------------------------------------------- #

class TestInitTweety:
    """init_tweety : branches early-return mockees (pas de vraie JVM).

    Le module importe jpype LAZILY dans init_tweety -> on injecte un faux module
    jpype dans sys.modules pour exercer les branches de decision sans JVM.
    """

    @pytest.fixture
    def fake_jpype(self, monkeypatch):
        """Injecte un faux jpype; startJVM leve pour detecter les appels."""
        fake = types.ModuleType("jpype")
        fake.imports = types.ModuleType("jpype.imports")
        state = {"started": False}

        def _is_started():
            return state["started"]

        def _start(*args, **kwargs):
            state["started"] = True

        fake.isJVMStarted = _is_started
        fake.startJVM = _start
        monkeypatch.setitem(sys.modules, "jpype", fake)
        monkeypatch.setitem(sys.modules, "jpype.imports", fake.imports)
        return fake, state

    def test_jvm_already_started_returns_true(self, fake_jpype, tmp_path, monkeypatch):
        _fake, state = fake_jpype
        state["started"] = True
        monkeypatch.chdir(tmp_path)
        assert t.init_tweety(verbose=False) is True

    def test_no_java_home_returns_false(self, fake_jpype, tmp_path, monkeypatch):
        # Pas de JDK portable, pas de JAVA_HOME -> False (verbose=False).
        monkeypatch.chdir(tmp_path)
        monkeypatch.delenv("JAVA_HOME", raising=False)
        assert t.init_tweety(verbose=False) is False

    def test_no_libs_dir_returns_false(self, fake_jpype, tmp_path, monkeypatch):
        # JAVA_HOME set (via env) mais aucun dossier libs -> False.
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("JAVA_HOME", str(tmp_path))
        assert t.init_tweety(verbose=False) is False

    def test_libs_empty_returns_false(self, fake_jpype, tmp_path, monkeypatch):
        # libs/ existe mais sans JAR -> False.
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("JAVA_HOME", str(tmp_path))
        (tmp_path / "libs").mkdir()
        assert t.init_tweety(verbose=False) is False

    def test_libs_with_jar_starts_jvm_returns_true(self, fake_jpype, tmp_path, monkeypatch):
        # libs/ avec un JAR -> startJVM appele, retour True.
        _fake, state = fake_jpype
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("JAVA_HOME", str(tmp_path))
        libs = tmp_path / "libs"
        libs.mkdir()
        (libs / "tweety.jar").write_bytes(b"PK\x03\x04")  # en-tete ZIP/JAR
        assert t.init_tweety(verbose=False) is True
        assert state["started"] is True

    def test_verbose_true_prints_banner(self, fake_jpype, tmp_path, monkeypatch, capsys):
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("JAVA_HOME", str(tmp_path))
        (tmp_path / "libs").mkdir()
        result = t.init_tweety(verbose=True)
        out = capsys.readouterr().out
        assert "--- Initialisation Tweety ---" in out
        # result False (no jars) mais le banner est imprime.
        assert result is False


# --------------------------------------------------------------------------- #
#  print_tools_summary                                                        #
# --------------------------------------------------------------------------- #

class TestPrintToolsSummary:
    """print_tools_summary : formate la liste des outils (capsys)."""

    def test_prints_configured_and_unconfigured(self, tools_snapshot, capsys):
        t.EXTERNAL_TOOLS["CLINGO"] = "/some/path/clingo"
        t.EXTERNAL_TOOLS["SPASS"] = ""
        t.print_tools_summary()
        out = capsys.readouterr().out
        assert "CLINGO" in out
        assert "SPASS" in out
        # Compteur "n/5".
        assert "/5" in out

    def test_count_matches_configured(self, tools_snapshot, capsys):
        for k in t.EXTERNAL_TOOLS:
            t.EXTERNAL_TOOLS[k] = ""
        t.EXTERNAL_TOOLS["CLINGO"] = "/x"
        t.print_tools_summary()
        out = capsys.readouterr().out
        # Exactement 1 outil configure sur 5.
        assert "Outils: 1/5" in out

    def test_zero_configured(self, tools_snapshot, capsys):
        for k in t.EXTERNAL_TOOLS:
            t.EXTERNAL_TOOLS[k] = ""
        t.print_tools_summary()
        out = capsys.readouterr().out
        assert "Outils: 0/5" in out


# --------------------------------------------------------------------------- #
#  EXTERNAL_TOOLS global structure                                            #
# --------------------------------------------------------------------------- #

class TestExternalToolsGlobal:
    """Structure de la globale EXTERNAL_TOOLS (contrat d'init)."""

    def test_all_five_tools_present(self):
        assert set(t.EXTERNAL_TOOLS) == {
            "CLINGO", "SPASS", "EPROVER", "SAT_SOLVER_PYTHON", "MARCO"
        }

    def test_values_are_strings(self):
        for v in t.EXTERNAL_TOOLS.values():
            assert isinstance(v, str)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
