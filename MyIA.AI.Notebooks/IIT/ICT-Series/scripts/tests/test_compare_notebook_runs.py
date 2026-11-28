"""Tests du contrat de ``compare_notebook_runs.py`` (preuve de #22297).

Ce que ces tests prouvent
-------------------------
 1. Deux executions identiques se lisent IDENTIQUE, meme quand
    ``metadata.papermill`` differe (horodatages, chemins, durees) : ce ne
    sont pas des sorties de cellule.
 2. Un texte de sortie different se lit DIVERGENT, et l'ecart nomme la
    cellule.
 3. Un decoupage different des blocs ``stream`` **consecutifs** ne fait pas
    lire DIVERGENT : c'est le faux positif mesure sur ICT-40a le 28/11.
 4. Un resultat intercale entre deux flux garde l'ordre des sorties : deux
    flux separes ne valent pas leur concatenation.
 5. Une source differente, un ``execution_count`` different, un nombre de
    cellules different se lisent chacun DIVERGENT.
 6. ``--code-only`` ignore une difference de markdown, pas une difference de
    code.
 7. Une image est comparee par son **contenu** : deux images differentes de
    meme decoupage en lignes se lisent DIVERGENT.
 8. Une cellule en erreur dans les deux executions est identique mais
    **nommee** : deux echecs identiques ne se lisent pas comme une reussite.
 9. ``main()`` rend 0 si identique, 1 si divergent, 2 si un fichier est
    illisible.

Aucune dependance lourde : json et pytest seulement.
"""

from pathlib import Path
import json
import sys

import pytest

# Une chaine, pas un objet Path : PathFinder saute sans bruit les entrees de
# sys.path qui ne sont pas des str, et le test ne passerait alors que depuis le
# dossier du module (le dossier courant y sert de repli).
_scripts = str(Path(__file__).resolve().parents[1])
if _scripts not in sys.path:
    sys.path.insert(0, _scripts)

from compare_notebook_runs import comparer, decrire, main  # noqa: E402


def _code(source="print('a')", outputs=None, execution_count=1):
    return {"cell_type": "code", "execution_count": execution_count,
            "metadata": {}, "outputs": outputs if outputs is not None else [],
            "source": [source]}


def _md(source="du texte"):
    return {"cell_type": "markdown", "metadata": {}, "source": [source]}


def _flux(*blocs):
    return [{"output_type": "stream", "name": "stdout", "text": [bloc]}
            for bloc in blocs]


def _carnet(cellules, **papermill):
    meta = {"input_path": "nb.ipynb", "output_path": "out.ipynb",
            "start_time": "2026-11-28T06:00:00+00:00"}
    meta.update(papermill)
    return {"cells": cellules, "metadata": {"papermill": meta},
            "nbformat": 4, "nbformat_minor": 5}


def _ecrire(chemin, contenu):
    chemin.write_text(json.dumps(contenu), encoding="utf-8")
    return chemin


def test_identiques_malgre_un_papermill_different():
    a = _carnet([_code(outputs=_flux("x = 3\n"))])
    b = _carnet([_code(outputs=_flux("x = 3\n"))],
                start_time="2026-11-28T07:00:00+00:00", duration=12.5,
                output_path="ailleurs.ipynb")
    rapport = comparer(a, b)
    assert rapport.identite
    assert (rapport.identiques, rapport.compares) == (1, 1)
    assert decrire(rapport).splitlines()[-1] == "VERDICT : IDENTIQUE"


def test_un_texte_different_est_divergent_et_nomme_la_cellule():
    a = _carnet([_md(), _code(outputs=_flux("0.25\n"))])
    b = _carnet([_md(), _code(outputs=_flux("0.26\n"))])
    rapport = comparer(a, b)
    assert not rapport.identite
    (ecart,) = rapport.ecarts
    assert ecart.index == 1 and ecart.type_cellule == "code"
    assert ecart.meme_source and not ecart.meme_sortie
    assert ecart.meme_execution_count
    texte = decrire(rapport)
    assert "--- cellule 1 (code)" in texte
    assert "A: '0.25\\n'" in texte and "B: '0.26\\n'" in texte
    assert texte.splitlines()[-1] == "VERDICT : DIVERGENT"


def test_le_decoupage_des_flux_consecutifs_est_ignore():
    a = _carnet([_code(outputs=_flux("vloss 0.51\n", "seed 0\n", "ok\n"))])
    b = _carnet([_code(outputs=_flux("vloss 0.51\nseed 0\nok\n"))])
    assert comparer(a, b).identite


def test_un_resultat_intercale_garde_l_ordre_des_sorties():
    resultat = {"output_type": "display_data", "metadata": {},
                "data": {"text/plain": ["42"]}}
    a = _carnet([_code(outputs=_flux("a\nb\n") + [resultat])])
    b = _carnet([_code(outputs=_flux("a\n") + [resultat] + _flux("b\n"))])
    assert not comparer(a, b).identite
    c = _carnet([_code(outputs=_flux("a\n") + [resultat] + _flux("b\n"))])
    assert comparer(b, c).identite


def test_une_source_differente_est_divergente():
    rapport = comparer(_carnet([_code(source="x = 3")]),
                       _carnet([_code(source="x = 4")]))
    assert not rapport.identite
    assert not rapport.ecarts[0].meme_source


def test_un_execution_count_different_est_divergent():
    a = _carnet([_code(execution_count=1), _code(execution_count=2)])
    b = _carnet([_code(execution_count=1), _code(execution_count=3)])
    rapport = comparer(a, b)
    assert not rapport.identite
    assert [ecart.index for ecart in rapport.ecarts] == [1]
    assert not rapport.ecarts[0].meme_execution_count


def test_un_nombre_de_cellules_different_est_divergent():
    rapport = comparer(_carnet([_code()]), _carnet([_code(), _code()]))
    assert not rapport.identite
    assert rapport.nb_cellules == (1, 2)
    assert "nombre de cellules different" in decrire(rapport)


def test_code_only_ignore_le_markdown_pas_le_code():
    a = _carnet([_md("ancienne valeur : 0.71"), _code(outputs=_flux("0.71\n"))])
    b = _carnet([_md("nouvelle valeur : 0.72"), _code(outputs=_flux("0.71\n"))])
    c = _carnet([_md("nouvelle valeur : 0.72"), _code(outputs=_flux("0.72\n"))])
    assert not comparer(a, b).identite
    rapport = comparer(a, b, code_only=True)
    assert rapport.identite
    assert (rapport.identiques, rapport.compares) == (1, 1)
    assert "restreinte aux cellules de code" in decrire(rapport, code_only=True)
    assert not comparer(a, c, code_only=True).identite


def test_une_image_est_comparee_par_son_contenu():
    def _png(derniere_ligne):
        return {"output_type": "display_data", "metadata": {},
                "data": {"image/png": ["AAAA", derniere_ligne]}}
    assert not comparer(_carnet([_code(outputs=[_png("BBBB")])]),
                        _carnet([_code(outputs=[_png("BBBC")])])).identite
    assert comparer(_carnet([_code(outputs=[_png("BBBB")])]),
                    _carnet([_code(outputs=[_png("BBBB")])])).identite


def test_une_erreur_identique_est_nommee():
    erreur = {"output_type": "error", "ename": "ValueError", "evalue": "x",
              "traceback": ["Traceback"]}
    rapport = comparer(_carnet([_code(outputs=[erreur])]),
                       _carnet([_code(outputs=[erreur])]))
    assert rapport.identite
    assert rapport.cellules_en_erreur == [0]
    assert "cellules en erreur" in decrire(rapport)
    autre = dict(erreur, evalue="y")
    assert not comparer(_carnet([_code(outputs=[erreur])]),
                        _carnet([_code(outputs=[autre])])).identite


def test_main_rend_0_1_2_selon_le_verdict(tmp_path, capsys):
    a = _ecrire(tmp_path / "a.ipynb",
                _carnet([_code(outputs=_flux("ok\n"))]))
    b = _ecrire(tmp_path / "b.ipynb",
                _carnet([_code(outputs=_flux("ok\n"))], duration=1.0))
    c = _ecrire(tmp_path / "c.ipynb",
                _carnet([_code(outputs=_flux("ko\n"))]))
    (tmp_path / "pas_json.ipynb").write_text("{ouvert", encoding="utf-8")
    assert main([str(a), str(b)]) == 0
    assert main([str(a), str(c)]) == 1
    assert main([str(a), str(c), "--code-only"]) == 1
    assert main([str(a), str(tmp_path / "absent.ipynb")]) == 2
    assert main([str(a), str(tmp_path / "pas_json.ipynb")]) == 2
    sortie = capsys.readouterr().out
    lignes = [ligne for ligne in sortie.splitlines()
              if ligne.startswith("VERDICT")]
    assert lignes == ["VERDICT : IDENTIQUE", "VERDICT : DIVERGENT",
                      "VERDICT : DIVERGENT"]
    assert sortie.count("illisible") == 2


def test_sur_le_carnet_lui_meme():
    """Controle positif sur le vrai ICT-40a s'il est present a cote."""
    carnet = Path(_scripts).parent / "ICT-40a-TriangulationCausale-Python.ipynb"
    if not carnet.exists():
        pytest.skip("carnet ICT-40a absent de ce checkout")
    nb = json.loads(carnet.read_text(encoding="utf-8"))
    rapport = comparer(nb, nb)
    assert rapport.identite
    assert rapport.compares == len(nb["cells"])
