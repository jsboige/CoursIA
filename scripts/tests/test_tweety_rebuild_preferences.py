"""Contrôles de refus du lanceur PowerShell ; aucun accès réseau requis."""
from pathlib import Path
import shutil
import subprocess
import zipfile

import pytest

SCRIPT = Path(__file__).resolve().parents[2] / "MyIA.AI.Notebooks/SymbolicAI/Tweety/dotnet-build/rebuild-preferences.ps1"
PWSH = shutil.which("pwsh")
pytestmark = pytest.mark.skipif(not PWSH, reason="PowerShell 7 absent")


def test_archive_corrompue_ne_produit_pas_de_jar(tmp_path):
    if not all(shutil.which(name) for name in ("javac", "jar", "tar")):
        pytest.skip("JDK ou tar absent")
    work = tmp_path / "chemin avec espaces" / "dotnet-build"
    work.mkdir(parents=True)
    shutil.copy(SCRIPT, work)
    jars = work / "jars"
    sources = work / "sources-jar"
    jars.mkdir()
    sources.mkdir()
    for name in ("jama-1.0.3", "slf4j-api-1.7.36", "commons-math-2.2", "commons-math3-3.6.1", "ojalgo-45.1.1", "org.sat4j.core-2.3.1", "commons-1.21", "jspf-core-1.0.2"):
        (jars / f"{name}.jar").touch()
    for name in ("math-1.21", "commons-1.21", "preferences-1.30"):
        with zipfile.ZipFile(sources / f"{name}-sources.jar", "w"):
            pass
    (sources / "plugin-1.30-sources.jar").write_bytes(b"invalid")
    result = subprocess.run([PWSH, "-NoProfile", "-File", str(work / SCRIPT.name)], text=True, capture_output=True, timeout=30)
    assert result.returncode != 0
    assert "Extraction impossible pour" in result.stderr
    assert "plugin-1.30-sources.jar" in result.stderr
    assert not (work.parent / "libs" / "org.tweetyproject.tweety-preferences-java8-shade.jar").exists()
