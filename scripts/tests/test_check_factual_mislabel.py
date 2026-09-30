"""Tests de l'organe factual-mislabel (#18354 tranche 2).

Canon mesure sur App-5-Timetabling : « 3 salles » (x2, cellules 2 et 4)
et « (3 \\times 20)^8 » contredits par le stream committé
« Salles : 4 » / « (4 x 20)^8 = 1.68e+15 ». Echantillon sain : 0 FP / 30
carnets (GenAI/ML/GameTheory/IIT/Probas, seed 42).
"""

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_factual_mislabel.py"


def _nb(cells):
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _md(src):
    return {"cell_type": "markdown", "metadata": {}, "source": src}


def _code(out_text):
    return {
        "cell_type": "code", "execution_count": 1, "metadata": {},
        "outputs": [{"output_type": "stream", "name": "stdout", "text": out_text}],
        "source": "print(1)",
    }


def _run(cells, tmp_path):
    p = tmp_path / "fixture.ipynb"
    p.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    return r.returncode, json.loads(r.stdout)


DATA_STREAM = (
    "Donnees du probleme\n=======================\n"
    "Cours       : 8\nSalles      : 4\nCreneaux    : 20 (5 jours x 4 creneaux)\n"
    "Enseignants : 4\nEspace brut : (4 x 20)^8 = 1.68e+15\n"
)


def test_canonical_salle_contradiction(tmp_path):
    rc, out = _run(
        [_code("Imports OK"),
         _md("$$\\text{Espace brut} = (3 \\times 20)^8 = 60^8$$"),
         _md("## 2. Donnees"),
         _code(DATA_STREAM),
         _md("instance maitrisee : 8 cours, 3 salles, 20 creneaux.")],
        tmp_path,
    )
    assert rc == 1
    units = [f for f in out["findings"] if f["kind"] == "unit-count"]
    assert any(f["claimed"] == "3" and f["stream"] == [4] for f in units)
    tuples = [f for f in out["findings"] if f["kind"] == "tuple-formula"]
    assert tuples and tuples[0]["claimed"] == "(3 x 20)^"


def test_consistent_counts_pass(tmp_path):
    rc, out = _run(
        [_code(DATA_STREAM),
         _md("instance maitrisee : 8 cours, 4 salles, 20 creneaux, 4 enseignants.")],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


def test_subcount_not_contradiction(tmp_path):
    # « Dupont enseigne 2 cours » : sous-compte par entite, le total 8
    # du stream ne le contredit pas (3 faux positifs tues par cette
    # garde, mesures App-5 c.6)
    rc, out = _run(
        [_code(DATA_STREAM),
         _md("| Dupont enseigne 2 cours | Idem |\n| Martin enseigne 2 cours | Idem |\n3. Dupont et Martin ont chacun 2 cours.")],
        tmp_path,
    )
    assert rc == 0


def test_hyphen_compound_and_ratio_guarded(tmp_path):
    rc, out = _run(
        [_code(DATA_STREAM),
         _md("petites instances : 8 cours x 80 creneaux-salles theoriques, 4 creneaux/jour.")],
        tmp_path,
    )
    assert rc == 0


def test_absent_number_not_flagged_here(tmp_path):
    # l'absence pure (nombre introuvable) releve de stale-claim, pas de
    # factual-mislabel : aucun stream => aucune contradiction possible
    rc, out = _run(
        [_code("done"),
         _md("il y aurait 12 solutions au total environ.")],
        tmp_path,
    )
    assert rc == 0
