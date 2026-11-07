"""Tests for write_notebook papermill metadata preservation (#24434).

``write_notebook`` est un writer generique : il ne reexecute aucune cellule et
ne doit donc PAS retirer ``metadata.papermill`` / ``metadata.execution`` --
seuls les executeurs qui reecrivent des sorties strippent (cf. ``_papermill_meta``,
cable directement dans ``dotnet_executor``, ``exec_single_cell``, etc.).

Cas fondateur : une edition markdown-only de 2 phrases via ``write_notebook``
supprimait 344 lignes de metadonnees papermill (PR #24411), rendant la preuve
d'execution invisible alors que ``execution_count`` et ``outputs`` restaient
en place.
"""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from notebook_helpers import read_notebook, write_notebook  # noqa: E402


def _nb_with_papermill():
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "id": "aaa",
                "metadata": {
                    "execution": {
                        "iopub.status.idle": "2026-11-03T08:36:38.519650Z",
                        "shell.execute_reply": "2026-11-03T08:36:38.519003Z",
                    },
                    "papermill": {
                        "duration": 0.009247,
                        "end_time": "2026-11-03T08:36:38.520588+00:00",
                        "exception": False,
                        "start_time": "2026-11-03T08:36:38.511341+00:00",
                        "status": "completed",
                    },
                },
                "outputs": [{"name": "stdout", "output_type": "stream", "text": ["ok\n"]}],
                "source": ["print('ok')\n"],
            },
            {
                "cell_type": "markdown",
                "id": "bbb",
                "metadata": {
                    "papermill": {
                        "duration": 0.003066,
                        "end_time": "2026-11-03T08:36:38.508118+00:00",
                        "exception": False,
                        "start_time": "2026-11-03T08:36:38.505052+00:00",
                        "status": "completed",
                    }
                },
                "source": ["### Interpretation\n"],
            },
        ],
        "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


class TestWriteNotebookPreservesPapermill(unittest.TestCase):
    def test_markdown_only_edit_preserves_metadata(self):
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            path = str(Path(td) / "nb.ipynb")
            nb = _nb_with_papermill()
            # edition markdown-only : on remplace la source de la cellule 1
            nb["cells"][1]["source"] = ["### Interpretation corrigee\n"]
            write_notebook(path, nb)

            reread = read_notebook(path)
            cell_code = reread["cells"][0]
            cell_md = reread["cells"][1]
            self.assertIn("papermill", cell_code["metadata"], "le bloc papermill du code doit survivre")
            self.assertIn("execution", cell_code["metadata"], "le bloc execution du code doit survivre")
            self.assertIn("papermill", cell_md["metadata"], "le bloc papermill du markdown doit survivre")
            self.assertEqual(
                cell_code["metadata"]["papermill"]["end_time"],
                "2026-11-03T08:36:38.520588+00:00",
            )
            self.assertEqual("".join(cell_md["source"]), "### Interpretation corrigee\n")

    def test_optin_strip_still_strips(self):
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            path = str(Path(td) / "nb.ipynb")
            nb = _nb_with_papermill()
            write_notebook(path, nb, strip_stale_metadata=True)

            reread = read_notebook(path)
            for cell in reread["cells"]:
                self.assertNotIn("papermill", cell.get("metadata", {}))

    def test_default_roundtrip_is_byte_stable(self):
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            path = str(Path(td) / "nb.ipynb")
            nb = _nb_with_papermill()
            write_notebook(path, nb)
            first = Path(path).read_text(encoding="utf-8")
            # relecture + reecriture sans edition : byte-identique
            write_notebook(path, read_notebook(path))
            second = Path(path).read_text(encoding="utf-8")
            self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()
