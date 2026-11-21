"""Teste le déploiement Automata avec des dépendances et commandes simulées."""

import os
from pathlib import Path
import subprocess

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "environment/automata-build-deploy.sh"


@pytest.fixture
def deployment(tmp_path: Path, bash: str, stub_as_function):
    sub = tmp_path / "sub"
    project = sub / "src/Automata/Automata.csproj"
    project.parent.mkdir(parents=True)
    project.write_text("project")
    commands = tmp_path / "bin"
    commands.mkdir()
    dotnet = commands / "dotnet"
    output = project.parent / "bin/Release/net8.0"
    # Chemins en forme POSIX : MSYS bash mange les antislashs (issue #27685).
    # newline="\n" : un shebang CRLF casse l'interpreteur sous msys.
    dotnet.write_text(f'#!/bin/bash\nmkdir -p "{output.as_posix()}"\nprintf CharSetSolver > "{output.as_posix()}/Microsoft.Automata.dll"\n',
                      newline="\n")
    dotnet.chmod(0o755)
    # Le deuxième déplacement échoue uniquement lors de la publication.
    mv = commands / "mv"
    mv.write_text('''#!/bin/bash
if [[ "$1" == */.deploy-stage.*/deploy ]]; then
  if [[ -n "${TEST_SIGNAL:-}" ]]; then kill -"$TEST_SIGNAL" "$PPID"; exit 1; fi
  if [[ "${FAIL_PUBLISH:-0}" == 1 ]]; then exit 1; fi
fi
exec /bin/mv "$@"
''', newline="\n")
    mv.chmod(0o755)
    cache = tmp_path / "nuget"
    cache.mkdir()
    codedom = cache / "system.codedom/8.0.0/lib/net8.0/System.CodeDom.dll"
    env = os.environ.copy()
    env.update(PATH=os.pathsep.join((str(commands), env["PATH"])),
               NUGET_PACKAGES=cache.as_posix())
    stub_as_function(commands, ("dotnet", "mv"), env)

    def run(*args: str, fail_publish: bool = False, signal: str = "") -> subprocess.CompletedProcess:
        return subprocess.run([bash, SCRIPT.as_posix(), sub.as_posix(), *args],
                              capture_output=True, check=False,
                              encoding="utf-8", errors="replace",
                              env=env | {"FAIL_PUBLISH": str(int(fail_publish)), "TEST_SIGNAL": signal})

    return sub, codedom, run


def test_failed_rebuild_preserves_deployment_and_retry(deployment):
    sub, codedom, run = deployment
    deploy = sub / ".deploy"
    deploy.mkdir()
    (deploy / "Microsoft.Automata.dll").write_text("old assembly")
    (deploy / "System.CodeDom.dll").write_text("old dependency")
    result = run("--force")
    assert result.returncode != 0 and "dependency not found" in result.stdout
    assert (deploy / "Microsoft.Automata.dll").read_text() == "old assembly"
    assert (deploy / "System.CodeDom.dll").read_text() == "old dependency"
    assert not list(sub.glob(".deploy-stage.*"))
    codedom.parent.mkdir(parents=True)
    codedom.write_text("new dependency")
    result = run("--force")
    assert result.returncode == 0, result.stdout + result.stderr
    assert (deploy / "Microsoft.Automata.dll").read_text() == "CharSetSolver"
    assert (deploy / "System.CodeDom.dll").read_text() == "new dependency"
    assert deploy.stat().st_mode & 0o111
    assert "already complete" in run().stdout


def test_empty_file_triggers_rebuild_and_failed_publication_restores(deployment):
    sub, codedom, run = deployment
    deploy = sub / ".deploy"
    deploy.mkdir()
    (deploy / "Microsoft.Automata.dll").write_text("")
    (deploy / "System.CodeDom.dll").write_text("old dependency")
    codedom.parent.mkdir(parents=True)
    codedom.write_text("new dependency")
    result = run(fail_publish=True)
    assert result.returncode != 0 and "could not publish" in result.stdout
    assert (deploy / "Microsoft.Automata.dll").read_text() == ""
    assert (deploy / "System.CodeDom.dll").read_text() == "old dependency"
    assert not list(sub.glob(".deploy-stage.*"))
    result = run()
    assert result.returncode == 0 and "already complete" not in result.stdout
    assert (deploy / "Microsoft.Automata.dll").read_text() == "CharSetSolver"


@pytest.mark.parametrize("signal", ["TERM", "KILL"])
def test_interrupted_publication_recovers_previous_deployment(deployment, signal):
    sub, codedom, run = deployment
    deploy = sub / ".deploy"
    deploy.mkdir()
    (deploy / "Microsoft.Automata.dll").write_text("old assembly")
    (deploy / "System.CodeDom.dll").write_text("old dependency")
    codedom.parent.mkdir(parents=True)
    codedom.write_text("new dependency")
    result = run("--force", signal=signal)
    assert result.returncode != 0
    if signal == "KILL":
        # SIGKILL ne permet aucun nettoyage ; la sauvegarde reste récupérable.
        backups = list(sub.glob(".deploy-backup.*"))
        assert len(backups) == 1 and not deploy.exists()
        backups[0].rename(deploy)
    assert (deploy / "Microsoft.Automata.dll").read_text() == "old assembly"
    assert (deploy / "System.CodeDom.dll").read_text() == "old dependency"
    result = run("--force")
    assert result.returncode == 0, result.stdout + result.stderr
    assert (deploy / "Microsoft.Automata.dll").read_text() == "CharSetSolver"
    assert (deploy / "System.CodeDom.dll").read_text() == "new dependency"
