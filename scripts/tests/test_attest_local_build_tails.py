"""Temoins positifs du fix #25002 (review Hermes 2026-11-06, prouve par
execution) : les queues stdout/stderr de ``run_lake_build`` doivent etre
non vides quand l'organe de build a bien ecrit les deux fichiers.

Le defaut corrige : ``_read_if_present`` etait appele APRES la sortie du
bloc ``with tempfile.TemporaryDirectory(...)`` -- le dossier etait deja
detruit, les queues revenaient ``""`` a chaque appel, y compris sur echec
de build (la ou le JSON est la seule trace diagnostique). Ce test rouge sur
le code casse, vert sur le fix : c'est le temoin positif qui l'empêche de
revenir.
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import attest_local_build as alb  # noqa: E402


def test_run_lake_build_tails_survive_the_tempdir(monkeypatch, tmp_path):
    """Les queues sont lues DANS le bloc `with` : l'organe ecrit, le payload
    rend le texte. Sur le code casse (lecture apres destruction du dossier),
    stdout_tail/stderr_tail reviennent vides et ce test rougit."""
    written: dict[str, Path] = {}

    def fake_argv(payload, *, lake_dir, timeout, stdout_file, stderr_file, **kwargs):
        written["out"] = Path(stdout_file)
        written["err"] = Path(stderr_file)
        return [sys.executable, "-c",
                "from pathlib import Path\n"
                f"Path(r'{stdout_file}').write_text('OUT-LINE-42\\n',"
                " encoding='utf-8')\n"
                f"Path(r'{stderr_file}').write_text('ERR-LINE-43\\n',"
                " encoding='utf-8')\n"]

    monkeypatch.setattr(alb, "_lean_exec_argv", fake_argv)

    payload = alb.run_lake_build(tmp_path, timeout=30.0)

    assert payload["stdout_tail"].rstrip().endswith("OUT-LINE-42"), (
        f"stdout_tail vide ou perime : {payload['stdout_tail']!r} -- "
        "le fichier etait-il lu apres la sortie du TemporaryDirectory ?")
    assert payload["stderr_tail"].rstrip().endswith("ERR-LINE-43"), (
        f"stderr_tail vide ou perime : {payload['stderr_tail']!r} -- "
        "meme defaut, meme remede : lire DANS le bloc `with`.")
