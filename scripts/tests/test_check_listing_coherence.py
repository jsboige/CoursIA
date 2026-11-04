"""Tests de l'organe listing-coherence (#18354 tranche stale-table, #23394).

Canon mesure sur Lean-37-Capstone-Serre100.ipynb au commit 6986f3f43b :
la prose annonce « huit carnets », la table de la section 2 s'arrete a `08`,
le stream de la cellule de code liste `01` a `15` -- manquants `09` a `15`.
La version corrigee sur main rend rc=0 (controle negatif).

Le discriminant est le PREFIXE CONTIGU : un tableau qui liste un
sous-ensemble arbitraire n'est pas signale.
"""

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_listing_coherence.py"


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


def _table(ids, annonce="## 2. Ou entrer : les huit carnets"):
    lignes = [annonce, "", "| # | Carnet | Sujet |", "|---|---|---|"]
    for i in ids:
        lignes.append(f"| {i} | carnet {i} | sujet |")
    return _md("\n".join(lignes))


def _run(cells, tmp_path):
    p = tmp_path / "fixture.ipynb"
    p.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    return r.returncode, json.loads(r.stdout)


LISTING_15 = "\n".join(f"{i:02d}-carnet-{i}.ipynb" for i in range(1, 16))
LISTING_15 = "15 carnets dans Serre100/\n" + LISTING_15


def test_canonical_table_tronquee(tmp_path):
    """Cas fondateur : table a 08, listing a 15, total annonce."""
    rc, out = _run(
        [_code("Import OK"),
         _table([f"{i:02d}" for i in range(1, 9)]),
         _code(LISTING_15)],
        tmp_path,
    )
    assert rc == 1
    assert len(out["findings"]) == 1
    f = out["findings"][0]
    assert f["identifiants_table"] == [f"{i:02d}" for i in range(1, 9)]
    assert len(f["identifiants_stream"]) == 15
    assert f["manquants"] == [f"{i:02d}" for i in range(9, 16)]


def test_table_complete_propre(tmp_path):
    """Table, listing ET total annonce d'accord : rien a signaler."""
    rc, out = _run(
        [_table([f"{i:02d}" for i in range(1, 16)], "## 2. Les 15 carnets"),
         _code(LISTING_15)],
        tmp_path,
    )
    assert rc == 0
    assert out["findings"] == []


def test_annonce_non_tenue_par_le_listing(tmp_path):
    """Classe INVERSE : table reparee a 15, prose restee a « huit ».

    Mesure de la review #24557 (reserve 4) : la table et le stream sont
    d'accord, et le total annonce ne l'est pas. Sans ce cas, le nombre
    capture par `ANNONCE_RE` n'etait compare a rien et le carnet sortait vert.
    """
    rc, out = _run(
        [_table([f"{i:02d}" for i in range(1, 16)], "## 2. Les huit carnets"),
         _code(LISTING_15)],
        tmp_path,
    )
    assert rc == 1
    assert len(out["findings"]) == 1
    f = out["findings"][0]
    assert f["kind"] == "annonce"
    assert f["annonce"] == 8
    assert len(f["identifiants_stream"]) == 15


def test_annonce_d_une_selection_n_est_pas_un_total(tmp_path):
    """« trois carnets choisis » decrit la selection, pas le listing."""
    rc, out = _run(
        [_table(["03", "07", "11"], "trois carnets choisis"), _code(LISTING_15)],
        tmp_path,
    )
    assert rc == 0
    assert out["findings"] == []


def test_carnet_illisible_n_est_pas_vert(tmp_path):
    """Un carnet non-UTF8 ou corrompu n'est pas un carnet propre (#24557 R1/R2)."""
    p = tmp_path / "casse.ipynb"
    p.write_bytes(b'{"cells": [ this is not json')
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    assert r.returncode == 1, "un carnet illisible ne doit jamais rendre rc=0"
    out = json.loads(r.stdout)
    assert out["findings"] == []
    assert out["non_lus"] == 1


def test_carnet_latin1_accentue_n_est_pas_une_accusation(tmp_path):
    """Un encodage non-UTF8 est un NON-LU, pas un finding de troncature."""
    p = tmp_path / "latin1.ipynb"
    p.write_bytes(
        '{"cells": [{"cell_type": "markdown", "metadata": {}, '
        '"source": ["r\\u00e9sum\\u00e9"]}], "metadata": {}, "nbformat": 4, '
        '"nbformat_minor": 5}'.encode("utf-8").replace(b"\\u00e9", b"\xe9")
    )
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    assert r.returncode == 1
    out = json.loads(r.stdout)
    assert out["findings"] == []
    assert out["non_lus"] == 1


def test_sous_ensemble_non_prefixe_non_signe(tmp_path):
    """Discriminant : « les 3 plus longs » n'est pas un prefixe tronque."""
    rc, out = _run(
        [_table(["03", "07", "11"], "trois carnets choisis"), _code(LISTING_15)],
        tmp_path,
    )
    assert rc == 0
    assert out["findings"] == []


def test_sans_annonce_de_total_non_signe(tmp_path):
    """Sans total annonce, une table partielle est legitime."""
    rc, out = _run(
        [_table([f"{i:02d}" for i in range(1, 9)], "## 2. Quelques carnets"),
         _code(LISTING_15)],
        tmp_path,
    )
    assert rc == 0
    assert out["findings"] == []


def test_sans_listing_stream_non_signe(tmp_path):
    """Aucun listing numerote cote stream : rien a comparer."""
    rc, out = _run(
        [_table([f"{i:02d}" for i in range(1, 9)]), _code("tout va bien\n")],
        tmp_path,
    )
    assert rc == 0
    assert out["findings"] == []


def test_rc2_chemin_introuvable(tmp_path):
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "chemin/absent/x.ipynb"],
        capture_output=True, text=True, encoding="utf-8", cwd=str(tmp_path),
    )
    assert r.returncode == 2
