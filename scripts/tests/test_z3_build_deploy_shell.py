"""Vérifie les déploiements Z3 simulés sans téléchargement ni hôte macOS."""

import os
from pathlib import Path
import subprocess
import sys

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "environment/z3-build-deploy.sh"


@pytest.fixture
def deployment(tmp_path: Path):
    sub = tmp_path / "sub"
    project = sub / "solutions/Z3.Linq/Z3.Linq.csproj"
    project.parent.mkdir(parents=True)
    project.write_text('<PackageReference Include="Microsoft.Z3" Version="4.12.2"/>')
    commands = tmp_path / "bin"
    commands.mkdir()
    nuget = tmp_path / "nuget"
    for name, content in (
        ("microsoft.z3/4.12.2/lib/netstandard2.0/Microsoft.Z3.dll", "managed"),
        ("miaplaza.expressionutils/1.2.0/lib/netstandard2.0/ExpressionUtils.dll", "expr"),
        ("microsoft.z3/4.12.2/runtimes/osx-x64/native/libz3.dylib", "x64"),
    ):
        path = nuget / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def stub(name: str, body: str) -> None:
        path = commands / name
        path.write_text("#!/bin/bash\n" + body + "\n")
        path.chmod(0o755)

    stub("uname", 'if [[ "$1" == -s ]]; then echo "$TEST_OS"; else echo "$TEST_ARCH"; fi')
    output = project.parent / "bin/Release/net8.0"
    stub("dotnet", f'mkdir -p "{output}"; echo CollectionHandling > "{output}/Z3.Linq.dll"; echo win > "{output}/libz3.dll"')
    # La wheel est synthétique ; sa corruption provoque une vraie erreur CRC zipfile.
    wheel_writer = tmp_path / "wheel.py"
    wheel_writer.write_text('''import os, pathlib, sys, zipfile
p = pathlib.Path(sys.argv[1]) / "z3_solver-test.whl"
with zipfile.ZipFile(p, "w") as z:
    z.writestr("z3/lib/" + os.environ["TEST_LIB"], "wheel")
if os.environ.get("CORRUPT") == "1":
    data = bytearray(p.read_bytes())
    data[data.index(b"wheel")] = ord("X")
    p.write_bytes(data)
''')
    stub("python3", f'''if [[ "$1" == -m ]]; then
  while [[ "$1" != -d ]]; do shift; done
  shift
  exec "{sys.executable}" "{wheel_writer}" "$1"
fi
exec "{sys.executable}" "$@"''')
    env = os.environ.copy()
    env.update(PATH=f'{commands}:{env["PATH"]}', NUGET_PACKAGES=str(nuget), HOME=str(tmp_path))

    def run(os_name: str, arch: str, lib: str, force: str = "1", corrupt: str = "0"):
        run_env = env | {"TEST_OS": os_name, "TEST_ARCH": arch, "TEST_LIB": lib,
                         "Z3_FORCE": force, "CORRUPT": corrupt}
        return subprocess.run(["bash", str(SCRIPT), str(sub)], env=run_env,
                              text=True, capture_output=True, check=False)

    return sub, run


@pytest.mark.parametrize("os_name,arch,lib,content", [
    ("Darwin", "x86_64", "libz3.dylib", "x64"),
    ("Darwin", "arm64", "libz3.dylib", "wheel"),
    ("Linux", "x86_64", "libz3.so", "wheel"),
    ("MINGW64_NT", "x86_64", "libz3.dll", "win"),
])
def test_native_selection_and_idempotence(deployment, os_name, arch, lib, content):
    sub, run = deployment
    result = run(os_name, arch, lib)
    assert result.returncode == 0, result.stdout + result.stderr
    assert (sub / ".deploy" / lib).read_text().strip() == content
    result = run(os_name, arch, lib, force="0")
    assert result.returncode == 0 and "already complete" in result.stdout


@pytest.mark.parametrize("os_name,arch,lib", [
    ("Darwin", "arm64", "libz3.dylib"), ("Linux", "x86_64", "libz3.so"),
])
def test_bad_crc_retry_and_preserve_existing(deployment, os_name, arch, lib):
    sub, run = deployment
    result = run(os_name, arch, lib, corrupt="1")
    assert result.returncode != 0 and "CRC" in result.stderr
    assert not (sub / ".deploy").exists()
    assert not list(sub.glob(".deploy-stage.*"))
    result = run(os_name, arch, lib, force="0")
    assert result.returncode == 0 and "already complete" not in result.stdout
    assert (sub / ".deploy" / lib).read_text() == "wheel"
    result = run(os_name, arch, lib, corrupt="1")
    assert result.returncode != 0
    assert (sub / ".deploy" / lib).read_text() == "wheel"
    assert not list(sub.glob(".deploy-stage.*"))
