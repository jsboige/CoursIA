#!/usr/bin/env python3
"""Tests de `scripts/notebook_tools/check_kernelspec_temp_paths.py` (#23997).

Le defaut vise est mesure sur une machine, pas sur le depot : un kernelspec
enregistre avec un `argv[0]` dans un scratchpad de session fonctionne le jour
de sa creation et meurt au nettoyage. Le critere d'acceptation exige donc un
**controle negatif rouge** -- un cas construit qui fait rougir l'organe -- et
un **controle negatif de faux positif** : les commandes nues (`dotnet`, `wsl`)
et les interpretes durables ne doivent jamais remonter.

Cas couverts :

1. un interpreteur sous une racine temporaire remonte `TEMP_ROOT` ;
2. la racine temporaire elle-meme remonte `TEMP_ROOT` (cas limite du prefixe) ;
3. les **commandes nues** ne remontent jamais -- testees nommement, parce que
   ce sont elles qui feraient rougir un parc sain si le filtre sautait ;
4. un chemin **relatif** n'est pas mesure (il se resout par `PATH`) ;
5. un interpreteur **durable et present** ne remonte pas ;
6. un composant `scratchpad` hors racine temporaire remonte
   `SCRATCHPAD_COMPONENT` -- la forme exacte du constat de #23941 ;
7. un interpreteur **absent** ne remonte que sous `--check-exists`, et
   `MISSING_INTERPRETER` n'est jamais confondu avec `TEMP_ROOT` ;
8. `main()` rend **1** sur un repertoire rouge et **0** sur un repertoire vert ;
9. `--kernelspec-dir` lit `<nom>/kernel.json` et `--from-json` accepte la forme
   imbriquee de `jupyter kernelspec list --json` ;
10. un **perimetre vide** rend **2**, jamais 0 : un repertoire mal designe ne
    passe pas pour un parc propre ;
11. un `kernel.json` illisible rend **2** ;
12. la sortie `--json` porte `verdict`, `offenders` et le compte mesure.

Le module est charge **par chemin** : `scripts/notebook_tools/` n'est pas un
paquet importable depuis la racine du depot.

Usage : python scripts/tests/test_check_kernelspec_temp_paths.py
"""
import importlib.util
import json
import os
import sys
import tempfile
from pathlib import Path

TOOL = Path(__file__).resolve().parents[1] / "notebook_tools" / "check_kernelspec_temp_paths.py"

# Racines artificielles : les tests ne dependent ni de `%TEMP%` de la machine
# ni du systeme d'exploitation du runner.
FAKE_TEMP = os.path.join(os.path.abspath(os.sep), "coursia-fake-temp")
DURABLE_ROOT = os.path.join(os.path.abspath(os.sep), "coursia-durable")
BARE_COMMANDS = ("dotnet", "wsl", "wsl.exe", "python", "python3", "bash")


def load_tool():
    spec = importlib.util.spec_from_file_location(
        "check_kernelspec_temp_paths", TOOL)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def roots():
    """Racines passees explicitement : la machine ne doit pas influencer."""
    return [os.path.normcase(os.path.normpath(FAKE_TEMP))]


def make_kernelspec_dir(base, specs):
    """Ecrit `<base>/<nom>/kernel.json` pour chaque entree de `specs`."""
    for name, argv in specs.items():
        folder = Path(base) / name
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "kernel.json").write_text(
            json.dumps({"argv": argv, "display_name": name, "language": "python"}),
            encoding="utf-8")
    return base


def test_temp_root_is_flagged():
    tool = load_tool()
    interpreter = os.path.join(FAKE_TEMP, "session-ee3e", "venv", "Scripts", "python.exe")
    assert tool.classify_interpreter(interpreter, roots()) == "TEMP_ROOT"


def test_temp_root_itself_is_flagged():
    """Le prefixe ne doit pas exiger un separateur de plus que la racine."""
    tool = load_tool()
    assert tool.classify_interpreter(FAKE_TEMP, roots()) == "TEMP_ROOT"


def test_posix_roots_absent_on_windows():
    """CONTROLE DE FAUX POSITIF : `/tmp` ne doit pas devenir `D:\\tmp`.

    Sous Windows, `realpath("/tmp")` resout relativement au lecteur courant.
    Laisser ces entrees dans la liste fabriquerait des racines inexistantes.
    """
    tool = load_tool()
    measured = tool.temp_roots([])
    if os.name == "nt":
        assert tool._platform_temp_roots() == (), measured
        fabricated = os.path.normcase(
            os.path.normpath(os.path.join(os.path.abspath(os.sep), "tmp")))
        assert fabricated not in measured, measured
    else:
        assert "/tmp" in [os.path.normpath(r) for r in measured], measured


def test_bare_commands_are_never_flagged():
    """CONTROLE DE FAUX POSITIF : `dotnet`/`wsl` se resolvent par PATH."""
    tool = load_tool()
    for command in BARE_COMMANDS:
        assert tool.classify_interpreter(command, roots()) is None, command


def test_relative_path_is_not_measured():
    tool = load_tool()
    assert tool.classify_interpreter(os.path.join(".", "venv", "python"), roots()) is None


def test_durable_interpreter_is_clean():
    """Un interprete present, hors des racines mesurees, ne remonte jamais.

    Les racines sont **passees explicitement** (`roots()`) : la mesure ne
    consulte jamais l'environnement de la machine du runner.
    """
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "venv" / "python.exe"
        exe.parent.mkdir(parents=True)
        exe.write_text("", encoding="utf-8")
        assert tool.classify_interpreter(str(exe), roots()) is None
        assert tool.classify_interpreter(str(exe), roots(), check_exists=True) is None


def test_scratchpad_component_is_flagged():
    """La forme exacte du constat #23941, hors de toute racine temporaire."""
    tool = load_tool()
    interpreter = os.path.join(
        DURABLE_ROOT, "3b22fd82", "scratchpad", "cleanenv", "Scripts", "python.exe")
    assert tool.classify_interpreter(interpreter, roots()) == "SCRATCHPAD_COMPONENT"


def test_missing_interpreter_only_under_check_exists():
    tool = load_tool()
    interpreter = os.path.join(DURABLE_ROOT, "gone", "python.exe")
    assert tool.classify_interpreter(interpreter, roots()) is None
    assert tool.classify_interpreter(
        interpreter, roots(), check_exists=True) == "MISSING_INTERPRETER"


def test_temp_root_wins_over_missing():
    """Les deux causes ne se confondent pas : un temporaire absent reste TEMP."""
    tool = load_tool()
    interpreter = os.path.join(FAKE_TEMP, "dead-session", "python.exe")
    assert tool.classify_interpreter(
        interpreter, roots(), check_exists=True) == "TEMP_ROOT"


def test_main_returns_one_on_red_directory():
    """CONTROLE NEGATIF : un repertoire rouge fait rougir l'organe."""
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        make_kernelspec_dir(tmp, {
            "coursia-canonical": [
                os.path.join(FAKE_TEMP, "cac66769", "scratchpad", "venv", "python.exe"),
                "-m", "ipykernel_launcher", "-f", "{connection_file}",
            ],
            "dotnet": ["dotnet", "--interactive", "jupyter", "--default-kernel",
                       "csharp", "{connection_file}"],
        })
        assert tool.main(["--kernelspec-dir", tmp, "--temp-root", FAKE_TEMP]) == 1


def test_main_returns_zero_on_clean_directory():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        make_kernelspec_dir(tmp, {
            "dotnet": ["dotnet", "--interactive", "jupyter", "--default-kernel",
                       "csharp", "{connection_file}"],
            "python-wsl": ["wsl.exe", "-e", "python3", "-m", "ipykernel_launcher"],
            "durable": [os.path.join(DURABLE_ROOT, "python313", "python.exe")],
        })
        assert tool.main(["--kernelspec-dir", tmp, "--temp-root", FAKE_TEMP]) == 0


def test_main_reads_nested_jupyter_json():
    """`jupyter kernelspec list --json` imbrique `spec` sous chaque noyau."""
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        payload = {
            "kernelspecs": {
                "coursia-canonical": {
                    "resource_dir": str(Path(tmp) / "coursia-canonical"),
                    "spec": {
                        "argv": [os.path.join(FAKE_TEMP, "a780fc74", "venv", "python.exe"),
                                 "-m", "ipykernel_launcher"],
                    },
                },
                "dotnet": {"spec": {"argv": ["dotnet", "--interactive"]}},
            }
        }
        dump = Path(tmp) / "kernelspecs.json"
        dump.write_text(json.dumps(payload), encoding="utf-8")
        assert tool.main(["--from-json", str(dump), "--temp-root", FAKE_TEMP]) == 1

        specs = json.loads(dump.read_text(encoding="utf-8"))["kernelspecs"]
        findings = tool.audit(specs, roots())
        assert [f["kernel"] for f in findings] == ["coursia-canonical"], findings
        assert findings[0]["reason"] == "TEMP_ROOT", findings


def test_empty_scope_is_incident():
    """Un perimetre vide n'est pas un vert ; il ne doit jamais rendre 0."""
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        assert tool.main(["--kernelspec-dir", tmp, "--temp-root", FAKE_TEMP]) == 2
        assert tool.main(["--from-json", str(Path(tmp) / "absent.json")]) == 2


def test_unreadable_kernelspec_is_incident():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp) / "broken"
        folder.mkdir()
        (folder / "kernel.json").write_text("{ pas du json", encoding="utf-8")
        assert tool.main(["--kernelspec-dir", tmp, "--temp-root", FAKE_TEMP]) == 2


def test_json_output_carries_verdict():
    tool = load_tool()
    with tempfile.TemporaryDirectory() as tmp:
        make_kernelspec_dir(tmp, {
            "coursia-canonical": [os.path.join(FAKE_TEMP, "x", "python.exe")],
            "dotnet": ["dotnet", "--interactive"],
        })
        import contextlib
        import io

        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            rc = tool.main(["--kernelspec-dir", tmp, "--temp-root", FAKE_TEMP, "--json"])
        assert rc == 1
        payload = json.loads(buffer.getvalue())
        assert payload["verdict"] == "OFFENDERS", payload
        assert payload["kernels"] == 2, payload
        assert len(payload["offenders"]) == 1, payload
        assert payload["offenders"][0]["kernel"] == "coursia-canonical", payload


def main():
    tests = [value for name, value in sorted(globals().items()) if name.startswith("test_")]
    failures = 0
    for test in tests:
        try:
            test()
        except AssertionError as exc:
            failures += 1
            print("FAIL %s: %s" % (test.__name__, exc))
        else:
            print("ok   %s" % test.__name__)
    print("%d/%d tests passes" % (len(tests) - failures, len(tests)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
