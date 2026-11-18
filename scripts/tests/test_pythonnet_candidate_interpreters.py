"""Mirror of PythonNetLoader.CandidateInterpreters/PythonDirectories logic on a fake FS.

Hermes's proof (review body of #21247, c.586) showed the prior c.584 fix was a no-op:
- C:\\Python313/python.exe works (root = C:\\, child = Python313)
- C:\\Program Files\\Python313/python.exe fails (root = Program Files\\Python313,
  glob Python3* children matches nothing because the layout is the leaf itself)

This test reproduces the corrected logic and pins it. C# itself isn't built in CI
(only notebook hooks run), so the proof rides on the Python port.
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path


def python_directories(root: Path) -> list[str]:
    """Mirror of C# PythonDirectories(root): list subdirs matching Python3*, sorted desc by minor."""
    if not root.is_dir():
        return []
    children = [
        d for d in root.iterdir()
        if d.is_dir() and d.name.startswith("Python3") and d.name[6:].isdigit()
    ]
    children.sort(key=lambda d: -int(d.name[6:]))
    return [str(d) for d in children]


def candidate_interpreters_windows(
    program_files: Path, program_files_x86: Path,
    local_app_data: Path, home: Path,
) -> list[str]:
    """Mirror of C# CandidateInterpreters() Windows branch with the corrected fix.

    The fix: pass program_files / program_files_x86 as the ROOT (not the leaf).
    python_directories then globs Python3* children at the right level.
    """
    roots: list[str] = []
    # legacy per-user top-level
    roots.extend(python_directories(Path("C:\\")))
    # all-users (cf #20270)
    if str(program_files):
        roots.extend(python_directories(program_files))
    if str(program_files_x86):
        roots.extend(python_directories(program_files_x86))
    # per-user local app data
    if str(local_app_data):
        roots.extend(python_directories(local_app_data / "Programs" / "Python"))
    # conda
    roots.extend([
        str(home / "miniconda3"),
        str(home / "anaconda3"),
        "C:\\ProgramData\\miniconda3",
        "C:\\ProgramData\\anaconda3",
    ])
    out = []
    for root in roots:
        exe = Path(root) / "python.exe"
        if exe.is_file():
            out.append(str(exe))
    return out


CS_REL_PATH = "MyIA.AI.Notebooks/Config/PythonNetLoader.cs"


def _cs_source() -> str:
    """Source C# reellement livree (racine du depot = parents[2] de ce fichier)."""
    repo_root = Path(__file__).resolve().parents[2]
    return (repo_root / CS_REL_PATH).read_text(encoding="utf-8")


def _make_fake_fs(tmp: Path) -> dict[str, Path]:
    """Build a fake filesystem mirroring the measured layout of po-2027."""
    pf = tmp / "Program Files"
    (pf / "Python313").mkdir(parents=True)
    (pf / "Python313" / "python.exe").touch()
    (pf / "Python312").mkdir(parents=True)
    (pf / "Python312" / "python.exe").touch()
    # per-user top-level (legacy)
    (tmp / "Python39").mkdir()
    (tmp / "Python39" / "python.exe").touch()
    return {
        "program_files": pf,
        "program_files_x86": tmp / "Program Files (x86)",
        "local_app_data": tmp / "AppData" / "Local",
        "home": tmp / "home",
    }


def test_all_users_probe_finds_python_exe():
    """The c.586 corrected fix probes ProgramFiles/Python3xx/python.exe."""
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        env = _make_fake_fs(base)
        cands = candidate_interpreters_windows(
            program_files=env["program_files"],
            program_files_x86=env["program_files_x86"],
            local_app_data=env["local_app_data"],
            home=env["home"],
        )
        expected_313 = str(env["program_files"] / "Python313" / "python.exe")
        expected_312 = str(env["program_files"] / "Python312" / "python.exe")
        assert expected_313 in cands, f"missing {expected_313} in {cands}"
        assert expected_312 in cands, f"missing {expected_312} in {cands}"


def test_minor_sort_desc():
    """Python313 should be listed before Python312 (minor desc)."""
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        env = _make_fake_fs(base)
        cands = candidate_interpreters_windows(
            program_files=env["program_files"],
            program_files_x86=env["program_files_x86"],
            local_app_data=env["local_app_data"],
            home=env["home"],
        )
        expected_313 = str(env["program_files"] / "Python313" / "python.exe")
        expected_312 = str(env["program_files"] / "Python312" / "python.exe")
        assert cands.index(expected_313) < cands.index(expected_312), \
            f"313 not before 312: {cands}"


def test_cs_source_pins_the_root_form():
    """Epingle le FICHIER C# lui-meme, pas seulement son portage Python.

    Le portage ci-dessus reproduit la logique, mais il ne verrait pas une
    regression du `.cs` : le test resterait vert si la forme feuille (le no-op
    reproche par la review Hermes du 18/10) revenait dans la source. Ce test
    lit donc `PythonNetLoader.cs` et exige la forme racine.
    """
    src = _cs_source()
    # la RACINE est passee a l'enumerateur d'enfants
    assert "PythonDirectories(programFiles)" in src, "forme racine absente (ProgramFiles)"
    assert "PythonDirectories(programFilesX86)" in src, "forme racine absente (ProgramFilesX86)"
    # la forme feuille -- le no-op -- ne doit pas revenir
    assert 'PythonDirectories(Path.Combine(programFiles, "Python313"))' not in src, \
        "la forme feuille est revenue : l'enumerateur ne trouverait rien"
    # le consommateur construit root/python.exe : la racine est le dossier Python3xx
    assert 'Path.Combine(root, "python.exe")' in src, \
        "le consommateur ne construit plus root/python.exe"


def test_legacy_per_user_still_works():
    """C:\\Python39/python.exe (per-user top-level) still probed."""
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        env = _make_fake_fs(base)
        # Pretend the per-user C:\\ is `base`
        # The function hardcodes C:\\ -- so this test only confirms the glob
        # function is correct on the per-user root by mirroring it.
        per_user_root = base
        dirs = python_directories(per_user_root)
        # Python39 should be found
        assert any(d.endswith("Python39") for d in dirs), f"Python39 not in {dirs}"


if __name__ == "__main__":
    test_all_users_probe_finds_python_exe()
    print("OK: test_all_users_probe_finds_python_exe")
    test_minor_sort_desc()
    print("OK: test_minor_sort_desc")
    test_legacy_per_user_still_works()
    print("OK: test_legacy_per_user_still_works")
    print("All tests passed.")
