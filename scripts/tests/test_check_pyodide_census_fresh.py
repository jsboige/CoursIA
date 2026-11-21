#!/usr/bin/env python3
"""Tests pour check_pyodide_census_fresh.py — issue #27617.

Les tests sont hermetiques : un faux depot (generateur factice) remplace le
depot reel, donc aucun acces reseau et aucune dependance a l'etat de l'arbre.
Le cas le plus important est le **controle positif** : un census deliberement
perime doit rendre l'organe ROUGE.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

from check_pyodide_census_fresh import comparer, verifier  # noqa: E402

GENERATEUR_FACTICE = '''\
#!/usr/bin/env python3
"""Generateur factice : ecrit un contenu derive de l'argument --sortie."""
import argparse
import sys

parser = argparse.ArgumentParser()
parser.add_argument("--format")
parser.add_argument("--out")
parser.add_argument("--refus-out")
parser.add_argument("--pyodide-lock")
parser.add_argument("--wheel-cache")
args = parser.parse_args()

if {echec!r}:
    sys.exit(3)

with open(args.out, "w", encoding="utf-8", newline="\\n") as fh:
    fh.write("# census factice\\n\\nCensus : **1** carnet.\\n")
with open(args.refus_out, "w", encoding="utf-8", newline="\\n") as fh:
    fh.write("chemin\\tserie\\n")
'''


def _faux_depot(tmp_path: Path, contenu_rapport: str = "# census factice\n\nCensus : **1** carnet.\n",
                contenu_refus: str = "chemin\tserie\n", echec: bool = False) -> Path:
    """Construit un depot minimal contenant un generateur factice."""
    repo = tmp_path / "depot"
    generateur = repo / "scripts" / "notebook_tools" / "pyodide_eligibility.py"
    generateur.parent.mkdir(parents=True, exist_ok=True)
    source = GENERATEUR_FACTICE.format(echec=echec)
    generateur.write_text(source, encoding="utf-8")

    docs = repo / "docs" / "reference"
    docs.mkdir(parents=True, exist_ok=True)
    (docs / "pyodide-eligibilite.md").write_text(contenu_rapport, encoding="utf-8")
    (docs / "pyodide-refus.tsv").write_text(contenu_refus, encoding="utf-8")
    (docs / "pyodide-lock.json").write_text("{}", encoding="utf-8")
    (docs / "pyodide-wheel-cache.json").write_text("{}", encoding="utf-8")
    return repo


def test_census_a_jour_rend_vert(tmp_path):
    repo = _faux_depot(tmp_path)
    verdict = verifier(repo)
    assert verdict["ok"] is True
    assert verdict["ecarts"] == []
    assert verdict["regeneration_rc"] == 0


def test_census_perime_rend_rouge(tmp_path):
    """Controle positif : un census stale doit faire echouer l'organe."""
    repo = _faux_depot(tmp_path, contenu_rapport="# census factice\n\nCensus : **999** carnets.\n")
    verdict = verifier(repo)
    assert verdict["ok"] is False
    assert verdict["ecarts"], "un ecart doit etre rapporte"
    assert any("pyodide-eligibilite.md" in ligne for ligne in verdict["ecarts"])


def test_fichier_manquant_rend_rouge(tmp_path):
    repo = _faux_depot(tmp_path)
    (repo / "docs" / "reference" / "pyodide-refus.tsv").unlink()
    verdict = verifier(repo)
    assert verdict["ok"] is False
    assert any("fichier manquant" in ligne for ligne in verdict["ecarts"])


def test_generateur_en_echec_rend_rouge(tmp_path):
    repo = _faux_depot(tmp_path, echec=True)
    verdict = verifier(repo)
    assert verdict["ok"] is False
    assert any("rendu 3" in ligne for ligne in verdict["ecarts"])


def test_comparer_signale_un_ecart_de_contenu(tmp_path):
    a = tmp_path / "a.md"
    b = tmp_path / "b.md"
    a.write_text("ligne 1\n", encoding="utf-8")
    b.write_text("ligne 1\n", encoding="utf-8")
    assert comparer(a, b) == []
    b.write_text("ligne 2\n", encoding="utf-8")
    ecarts = comparer(a, b)
    assert ecarts
    assert any("ligne 2" in ligne for ligne in ecarts)
