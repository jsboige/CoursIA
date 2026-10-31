"""Unit tests for check_kernel_drift.py.

We test the pure functions (no git, no filesystem) and provide a small
end-to-end harness using tmp_path + a fake git that exposes two blobs.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_kernel_drift as ckd


def _nb(kernel_name, lang_version, code_outputs):
    """Build a minimal notebook JSON dict."""
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "outputs": [{"output_type": "stream", "name": "stdout",
                             "text": code_outputs}],
            }
        ],
        "metadata": {
            "kernelspec": {"name": kernel_name, "display_name": "Python"},
            "language_info": {"version": lang_version},
        },
    }


def test_kernel_info_extracts_fields():
    nb = _nb("python3", "3.11.16", [])
    info = ckd.kernel_info(nb)
    assert info["kernelspec_name"] == "python3"
    assert info["language_version"] == "3.11.16"
    assert info["kernelspec_display"] == "Python"


def test_kernel_info_missing_fields():
    nb = {"metadata": {}}
    info = ckd.kernel_info(nb)
    assert info == {"kernelspec_name": "", "language_version": "",
                    "kernelspec_display": ""}


def test_diff_kernel_no_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    assert ckd.diff_kernel(a, b) == []


def test_diff_kernel_python_version_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1
    assert "language_info.version" in diffs[0]
    assert "3.11.16" in diffs[0] and "3.13.3" in diffs[0]


def test_diff_kernel_kernelspec_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.11.16", "kernelspec_name": "python311"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1
    assert "kernelspec.name" in diffs[0]


def test_diff_kernel_both_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    # Only version differs; kernelspec.name identical.
    assert len(diffs) == 1


# --- #17371: patch-level language_info.version drift is not a regression ---


def test_version_prefix_shapes():
    assert ckd._version_prefix("3.13.3") == "3.13"
    assert ckd._version_prefix("3.13.15") == "3.13"
    assert ckd._version_prefix("3.13.15rc1") == "3.13"
    assert ckd._version_prefix("3.13") == "3.13"
    assert ckd._version_prefix("3") == "3"
    assert ckd._version_prefix("") == ""


def test_version_prefix_null_version_does_not_crash():
    # `"version": null` is valid nbformat: the `.get("version", "")`
    # extraction default only covers a MISSING key, so the helper received
    # None and raised AttributeError -- a traceback where the pre-fix
    # comparison emitted a degraded but handled drift (NanoClaw, 2026-09-22).
    assert ckd._version_prefix(None) == ""


def test_diff_kernel_null_version_vs_version_flagged():
    a = {"language_version": None, "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1
    assert "language_info.version" in diffs[0]
    assert "None" in diffs[0] and "3.13.3" in diffs[0]


def test_diff_kernel_null_version_on_both_sides_not_flagged():
    a = {"language_version": None, "kernelspec_name": "python3"}
    b = {"language_version": None, "kernelspec_name": "python3"}
    assert ckd.diff_kernel(a, b) == []


def test_diff_kernel_patch_level_drift_not_flagged():
    # Measured on #16858: base stamp 3.13.3, fresh re-exec under the
    # project venv 3.13.15 -- same kernel, same repr() semantics.
    a = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    assert ckd.diff_kernel(a, b) == []


def test_diff_kernel_patch_drift_with_rc_suffix_not_flagged():
    a = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15rc1", "kernelspec_name": "python3"}
    assert ckd.diff_kernel(a, b) == []


def test_diff_kernel_minor_change_still_flagged():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1
    assert "3.11.16" in diffs[0] and "3.13.15" in diffs[0]
    assert "3.11 -> 3.13" in diffs[0]


def test_diff_kernel_major_change_still_flagged():
    a = {"language_version": "2.7.18", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1


def test_diff_kernel_empty_vs_full_version_flagged():
    a = {"language_version": "", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    assert len(ckd.diff_kernel(a, b)) == 1


def test_float_signatures_matches_array_shape():
    nb = _nb("python3", "3.13.3",
             ["n=5: distances = [1.0, 0.9999999999999999, 1.0, 1.0, 1.0]\n"])
    sig = ckd.float_signatures(nb)
    assert len(sig) == 1
    assert len(sig[0]) == 1  # one array-shaped match
    assert "0.9999999999999999" in sig[0][0]


def test_float_signatures_ignores_non_code_cells():
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["[1.0, 1.0, 1.0]"]},
            {"cell_type": "code", "outputs": [], "execution_count": 1},
        ],
        "metadata": {"kernelspec": {}, "language_info": {}},
    }
    sig = ckd.float_signatures(nb)
    assert sig == ((),)


def test_float_signatures_empty():
    nb = _nb("python3", "3.11.16", [])
    assert ckd.float_signatures(nb) == ((),)


def test_diff_signatures_identical():
    a = (("[1.0, 1.0, 1.0]",),)
    b = (("[1.0, 1.0, 1.0]",),)
    assert ckd.diff_signatures(a, b) == []


def test_diff_signatures_float_drift():
    # #19961 : la paire NumPy 1.x/2.x (1.0 vs 0.9999999999999999, 1 ULP)
    # est du bruit assume (contre-temoin 1-ULP en fin de fichier) ; le
    # controle positif garde un drift reel a 2 ULP.
    a = (("[1.0, 1.0, 1.0, 1.0, 1.0]",),)
    b = (("[1.0, 0.9999999999999998, 1.0, 1.0, 1.0]",),)
    assert ckd.diff_signatures(a, b) == [0]


def test_diff_signatures_added_cell():
    a = (("[1.0, 1.0]",),)
    b = (("[1.0, 1.0]",), ("[2.0, 2.0]",))
    assert ckd.diff_signatures(a, b) == [1]


def test_diff_signatures_removed_cell():
    a = (("[1.0, 1.0]",), ("[2.0, 2.0]",))
    b = (("[1.0, 1.0]",),)
    assert ckd.diff_signatures(a, b) == [1]


def test_diff_signatures_complex_float_with_exponent():
    a = (("[-1.5e+00, 2.5e-01, 3.14159]",),)
    b = (("[-1.5e+00, 0.2500000000000001, 3.14159]",),)
    assert ckd.diff_signatures(a, b) == [0]


def _nb_ids(cells):
    """Build a notebook from (cell_id, output_text) code cells.

    ``output_text`` None means "the cell has no output at all" (the shape of
    papermill's `injected-parameters` cell, and of a parameters cell).
    """
    return {
        "cells": [
            {
                "cell_type": "code",
                "id": cid,
                "source": src,
                "execution_count": 1,
                "outputs": ([] if text is None else
                            [{"output_type": "stream", "name": "stdout",
                              "text": text}]),
            }
            # (cid, text) ou (cid, text, source) : la source est l'identite
            # stable d'une cellule a travers une re-serialisation (#23364).
            for cid, text, src in (c if len(c) == 3 else (c[0], c[1], "")
                                   for c in cells)
        ],
        "metadata": {
            "kernelspec": {"name": "python3", "display_name": "Python 3"},
            "language_info": {"version": "3.13.3"},
        },
    }


def _id_aligned_diffs(base_cells, head_cells):
    """Run diff_signatures through the id-aligned branch (notebooks given)."""
    base = _nb_ids(base_cells)
    head = _nb_ids(head_cells)
    return ckd.diff_signatures(ckd.float_signatures(base),
                               ckd.float_signatures(head),
                               base_nb=base, head_nb=head)


def test_diff_signatures_added_empty_cell_not_reported():
    """#17232 founding instance (PR #17145).

    Papermill replaces its `injected-parameters` cell on every re-execution,
    and nbformat 4.5 hands the replacement a fresh cell id. The added cell
    carries no output at all, so it cannot be a float-repr drift: the pair
    (one id removed, one id added) is the normal fingerprint of a
    re-execution, not a regression.
    """
    assert _id_aligned_diffs(
        [("params", None), ("c-work", "ok\n")],
        [("params-new", None), ("c-work", "ok\n")],
    ) == []


def test_diff_signatures_added_cell_with_float_still_reported():
    """Positive control: the fix must not blind the gate.

    A cell RE-IDENTIFIED by a re-serialisation (same source, fresh id) whose
    float output really changed is still a drift: the base signature exists,
    so the comparison is meaningful. What #23364 removes is the added cell
    with NO base counterpart, not this one.

    `c-keep` keeps the id-aligned branch reachable: with no common id at all
    the organ falls back to ordinal alignment by design, which is a
    different contract than the one under test here.
    """
    assert _id_aligned_diffs(
        [("c-keep", "ok\n", "keep()"), ("c1", "[1.0, 1.0]\n", "df.head()")],
        [("c-keep", "ok\n", "keep()"), ("c1-b", "[2.0, 2.0]\n", "df.head()")],
    ) == ["c1-b"]


def test_diff_signatures_added_empty_cell_does_not_mask_a_real_drift():
    """An empty added cell must not mask drift on a common cell."""
    assert _id_aligned_diffs(
        [("c1", "[1.0, 1.0]\n"), ("c2", "[2.0, 2.0]\n")],
        [("params-new", None), ("c1", "[1.0, 0.9999999999999998]\n"),
         ("c2", "[2.0, 2.0]\n")],
    ) == ["c1"]


def test_diff_signatures_added_mixed_only_reidentified_ones_reported():
    """Among several added cells, only a re-identified one can drift.

    `injected` carries no signature (papermill's parameters cell), `c3` is
    genuinely new content, `old-new` is the base cell `old` under a fresh id:
    only the last one has a base signature to differ from.
    """
    assert _id_aligned_diffs(
        [("c1", "ok\n", "a"), ("old", "[9.0, 9.0]\n", "df.tail()")],
        [("c1", "ok\n", "a"), ("injected", None, "# Parameters"),
         ("c3", "[3.0, 3.0]\n", "new_analysis()"),
         ("old-new", "[8.0, 8.0]\n", "df.tail()")],
    ) == ["old-new"]


def test_diff_signatures_added_cell_printing_intervals_not_reported():
    """#23364 founding instance, measured on PR #23273.

    The PR ADDED two cells that print Wilson confidence intervals. Their
    output text `[0.57,1.00]` matches FLOAT_ARRAY_RE exactly as a 2-element
    ndarray would, so the added-cell branch reported them as
    `signature_drift_cells` -- while `origin/main` had no cell with the same
    source, i.e. there was no base value to drift from.

    The guard must stay silent here: 8 -> 10 code cells, 0 id lost, both
    flagged cells genuine additions.
    """
    assert _id_aligned_diffs(
        [("c1", "[0.10, 0.20]\n", "report()")],
        [("c1", "[0.10, 0.20]\n", "report()"),
         ("wilson", "[0.57,1.00]\n[0.00,0.20]\n", "wilson_ci(wins, n)")],
    ) == []



# --- #17679 : table d'acceptation canon C# 13.0 ------------------------------
# Decision coordinateur 2026-09-26 (option 1) : C# 13.0 devient le canon ;
# la derive 12.0 -> 13.0 est attendue et couverte par la table, pas une
# regression. Controles exigés par la décision : un positif (12.0 -> 13.0
# vert) et deux negatifs (13.0 -> 12.0 rouge ; changement de kernelspec.name
# rouge).


def test_canonical_transition_cs12_to_cs13_accepted():
    a = {"language_version": "12.0", "kernelspec_name": ".net-csharp"}
    b = {"language_version": "13.0", "kernelspec_name": ".net-csharp"}
    assert ckd.accepted_canonical_transition(a, b) is True
    # la derive brute existe bien (le guard la mesure) -- c'est la table
    # qui l'accepte, pas une absence de detection
    assert ckd.diff_kernel(a, b)


def test_canonical_transition_cs13_to_cs12_refused():
    # Negatif 1 : la direction inverse est une regression du canon.
    a = {"language_version": "13.0", "kernelspec_name": ".net-csharp"}
    b = {"language_version": "12.0", "kernelspec_name": ".net-csharp"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_kernelspec_change_refused():
    # Negatif 2 : un changement de kernelspec.name reste rouge, meme avec
    # des versions couvertes par la table.
    a = {"language_version": "12.0", "kernelspec_name": ".net-csharp"}
    b = {"language_version": "13.0", "kernelspec_name": ".net-fsharp"}
    assert ckd.accepted_canonical_transition(a, b) is False


# --- #19181 : table d'acceptation canon Python (QC/Python) -----------------
# Mesure du 2026-10-05 sur la serie QC/Python : 11 versions heterogenes
# (3.8.10 a 3.13.14) ; 60 carnets ``python3`` + 2 ``conda-torch``.
# Decision duale coord. (2026-10-05T03:43:46Z, DM
# msg-20261005T034346-qyldsl) :
#   - canon des algorithmes deployes sur QC Cloud = Python 3.11
#     (documented in ``MyIA.AI.Notebooks/QuantConnect/requirements.txt``) ;
#   - canon de l'execution locale des carnets = Python 3.13 (l'interpreteur
#     de la flotte qui ecrit ``language_info.version`` a chaque rejeu).
# Transitions acceptees en direction du canon : 3.10 -> 3.11 (historique
# QC Cloud), 3.11 -> 3.13 (convergence locale), 3.10 -> 3.13 (cas
# fondateur de #19181, PR #19163 : 3.10.11 -> 3.13.3), et 3.12 -> 3.13
# (anticipation de convergence ; ICT-47 sur main est a `py310-gpu`
# 3.12.13, kernelspec distinct de `python3`, donc hors scope de ce
# tuple -- l'entree anticipe un futur carnet `python3` a 3.12). La
# direction inverse reste rouge.


def test_canonical_transition_python_311_to_313_accepted():
    # Positif 1 : la convergence vers Python 3.13 (canon d'execution) est
    # couverte.
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is True
    # la derive brute existe bien -- c'est la table qui l'accepte.
    assert ckd.diff_kernel(a, b)


def test_canonical_transition_python_310_to_311_accepted():
    # Positif 2 : la migration historique vers le canon QC Cloud 3.11 est
    # couverte.
    a = {"language_version": "3.10.19", "kernelspec_name": "python3"}
    b = {"language_version": "3.11.9", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is True


def test_canonical_transition_python_31011_to_3133_accepted():
    # Positif 3 (cas fondateur #19181, PR #19163) : la convergence directe
    # 3.10.11 -> 3.13.3 est couverte. La flotte rejette les carnets en
    # 3.13 (interpreteur local), donc cette transition est le passage
    # reel ; les transitions via 3.11 sont possibles mais ne se
    # composent pas (cle tuple exact).
    a = {"language_version": "3.10.11", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is True


def test_canonical_transition_python_38_to_313_refused():
    # Negatif 5 : 3.8 -> 3.13 reste rouge par construction. Le saut 3.8
    # n'est pas couvert par la table (serie ICT pinnée <3.10, pyphi==1.2.0,
    # mesure #19160 ; sans scope par chemin/série, ajouter la transition
    # ferait passer vert un carnet ICT rejoue par erreur -- reserve Hermes
    # PRR_kwDOH2Odns8AAAABQnPfEQ, 2026-10-05). Les 2 rescapes 3.8.10/3.9.0
    # sont traites au cas par cas : QC-Py-16 via la table scoped
    # (tests ci-dessous), QC-Py-03 verdict INTRINSIC (metadonnee fossile,
    # aucune cellule executable localement).
    a = {"language_version": "3.8.10", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_python_39_to_313_refused():
    # Negatif 6 : 3.9 -> 3.13 reste rouge (meme raison que 3.8).
    a = {"language_version": "3.9.0", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_scoped_qcpy16_38_to_313_accepted():
    # Cas par cas #19181 (decision coordinateur du 11/10) : le seul carnet
    # nominatif porte sa transition -- QC-Py-16, re-execution selective du
    # sous-ensemble local (cellules REF QC Cloud non executables
    # localement) sous le canon d'execution 3.13.
    a = {"language_version": "3.8.10", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.14", "kernelspec_name": "python3"}
    path = ("MyIA.AI.Notebooks/QuantConnect/Python/"
            "QC-Py-16-Alternative-Data.ipynb")
    assert ckd.accepted_canonical_transition(a, b, nb_path=path) is True


def test_canonical_transition_scoped_does_not_leak_to_other_paths():
    # La meme transition 3.8 -> 3.13 reste rouge ailleurs : le scope protege
    # la serie ICT (<3.10) -- c'est la raison d'etre de la table scoped.
    a = {"language_version": "3.8.10", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.14", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False
    assert ckd.accepted_canonical_transition(
        a, b, nb_path="MyIA.AI.Notebooks/IIT/ICT-47.ipynb") is False


def test_canonical_transition_scoped_reverse_still_refused():
    # Direction inverse : rouge meme sur le chemin scope (le cliquet ne
    # descend pas).
    a = {"language_version": "3.13.14", "kernelspec_name": "python3"}
    b = {"language_version": "3.8.10", "kernelspec_name": "python3"}
    path = ("MyIA.AI.Notebooks/QuantConnect/Python/"
            "QC-Py-16-Alternative-Data.ipynb")
    assert ckd.accepted_canonical_transition(a, b, nb_path=path) is False


# --- #23187 : portee SERIE (prefixe de repertoire) --------------------------
# Le canon 3.13 est celui de la serie 02-ML-Cours entiere, declare par son
# requirements.txt -- pas celui du seul 2.8c. Quatre carnets de la serie
# tournent sous ``coursia-ml-training`` (releves le 2026-10-29 sur main) :
# 2.8c et 2.14b a 3.11.15, 2.9d et 2.9g a 3.10.19 -- deux directions, donc
# deux entrees. La portee est un PREFIXE de repertoire, jamais le kernelspec
# nu : 50 carnets hors serie partagent ce kernelspec sans declarer 3.13
# (54 au total, 4 dans la serie). Le chiffre se relit par lecture des
# METADONNEES de chaque carnet -- la commande et son instantane sont
# consignes dans #23187 :
#   python -c "import json, pathlib; print(sum(1 for p in
#   pathlib.Path('MyIA.AI.Notebooks').rglob('*.ipynb') if
#   (json.loads(p.read_text(encoding='utf-8')).get('metadata') or {})
#   .get('kernelspec', {}).get('name') == 'coursia-ml-training'))"
# (un comptage par sous-chaine dans le fichier rend 67 : il additionne les
# carnets dont le kernelspec est un autre mais dont une cellule cite le
# nom -- la population qui compte pour ce garde est celle des METADONNEES).
# La reserve de revue de #22979 a refuse l'entree globale precisement
# pour eux.


def test_canonical_transition_scoped_series_02ml_accepted():
    # Positif : un autre carnet de la serie converge vers le canon 3.13.
    # Le representant est 2.14b, dont la version mesuree est bien 3.11.15 --
    # nommer ici un carnet a 3.10.19 aurait fait passer le test sur une base
    # que ce carnet n'a jamais portee (reserve NanoClaw du 2026-10-29).
    a = {"language_version": "3.11.15",
         "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.14",
         "kernelspec_name": "coursia-ml-training"}
    path = ("MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/"
            "2.14b-XAI-Shap-Attribution-Causal-Bridge.ipynb")
    assert ckd.accepted_canonical_transition(a, b, nb_path=path) is True
    # Sans chemin, la meme derive reste rouge : aucune entree GLOBALE n'a
    # ete ajoutee pour ce kernelspec.
    assert ckd.accepted_canonical_transition(a, b) is False
    # Et un changement de kernelspec reste rouge meme sous la portee serie
    # (le prefixe ne dispense pas de l'egalite de kernelspec).
    c = {"language_version": "3.13.14", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, c, nb_path=path) is False


def test_canonical_transition_scoped_series_02ml_310_accepted():
    # Positif, deuxieme direction (#23187) : a l'epoque de l'entree de serie,
    # 2.9d et 2.9g etaient a 3.10.19. La direction est devenue NOMINATIVE
    # (#23667) : 2.9d est le seul carnet admis -- ses sorties sont
    # re-executees -- et 2.9g reste rouge jusqu'a la livraison de sa tranche
    # (#23292).
    a = {"language_version": "3.10.19",
         "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.14",
         "kernelspec_name": "coursia-ml-training"}
    for name in ("2.9d-Features-Circulaires-Helice-Nombres.ipynb",):
        path = ("MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/"
                + name)
        assert ckd.accepted_canonical_transition(a, b, nb_path=path) is True
    # Sans chemin, la direction reste rouge (pas d'entree globale).
    assert ckd.accepted_canonical_transition(a, b) is False
    # Hors de la serie, 3.10 -> 3.13 reste rouge : le prefixe est le seul
    # elargissement, il ne fuit pas.
    assert ckd.accepted_canonical_transition(
        a, b,
        nb_path=("MyIA.AI.Notebooks/Complexity/"
                 "Complexity-07-KolmogorovBornee-Sequences-Python.ipynb"),
    ) is False


def test_canonical_transition_scoped_series_does_not_leak_outside():
    # Controle negatif de la portee serie (reserve #22979) : les carnets qui
    # partagent le kernelspec hors 02-ML-Cours gardent la direction rouge,
    # sinon l'entree globale refusee en revue rentrerait par la porte de
    # derriere. Le troisieme chemin verifie la frontiere du prefixe
    # (``02-ML-Cours-autre/`` n'est pas ``02-ML-Cours/``).
    a = {"language_version": "3.11.15",
         "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.14",
         "kernelspec_name": "coursia-ml-training"}
    for path in (
        "MyIA.AI.Notebooks/Complexity/"
        "Complexity-07-KolmogorovBornee-Sequences-Python.ipynb",
        "MyIA.AI.Notebooks/GameTheory/"
        "GameTheory-19b-Bilevel-PPO-Python.ipynb",
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours-autre/x.ipynb",
    ):
        assert ckd.accepted_canonical_transition(a, b, nb_path=path) is False


def test_canonical_transition_scoped_series_reverse_still_refused():
    # Le cliquet ne descend pas, meme sous la portee serie.
    a = {"language_version": "3.13.14",
         "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.11.15",
         "kernelspec_name": "coursia-ml-training"}
    path = ("MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/"
            "2.14b-XAI-Shap-Attribution-Causal-Bridge.ipynb")
    # L'assertion manquait depuis #23187 : la fonction calculait `path` et
    # ne controlait rien, donc ce controle negatif passait sans controler.
    assert ckd.accepted_canonical_transition(a, b, nb_path=path) is False


def test_canonical_transition_scoped_series_310_is_nominative():
    # #23667 : la direction 3.10 -> 3.13 n'est plus une PORTEE de serie,
    # elle est nominative (2.9d). Un carnet de la serie qui n'est pas 2.9d,
    # et dont les sorties n'ont pas ete re-executees, reste donc rouge --
    # quelle que soit sa place dans le repertoire. Le second chemin est un
    # carnet fictif de la serie : il controle que la PORTE, et pas seulement
    # le cas nomme 2.9g, est restee fermee.
    a = {"language_version": "3.10.19",
         "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.14",
         "kernelspec_name": "coursia-ml-training"}
    for path in (
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/"
        "2.9g-Geometrie-de-la-Verite.ipynb",
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/"
        "2.9h-Carnet-Inexistant-Sur-La-Serie.ipynb",
    ):
        assert ckd.accepted_canonical_transition(a, b, nb_path=path) is False


def test_canonical_transition_scoped_ml06_312_to_313_accepted():
    # #23426 : ML-06 est le seul carnet ML.Net sous kernel NOMME
    # (hors census #23379, kernel python3) -- sa convergence vers le canon
    # 3.13 exige une entree nominative, meme forme que 2.8c/2.9d.
    a = {"language_version": "3.12.13", "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.15", "kernelspec_name": "coursia-ml-training"}
    path = "MyIA.AI.Notebooks/ML/ML.Net/ML-06-ONNX-Python.ipynb"
    assert ckd.accepted_canonical_transition(a, b, nb_path=path) is True


def test_canonical_transition_scoped_ml06_does_not_leak():
    # La meme direction 3.12 -> 3.13 sous le meme kernelspec reste rouge
    # ailleurs : ni un autre carnet ML.Net, ni 2.8c (scope 3.11 -> 3.13).
    a = {"language_version": "3.12.13", "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.15", "kernelspec_name": "coursia-ml-training"}
    assert ckd.accepted_canonical_transition(a, b) is False
    assert ckd.accepted_canonical_transition(
        a, b,
        nb_path=("MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/"
                 "2.8c-Borne-Temoin-Concentration.ipynb")) is False


def test_canonical_transition_scoped_ml06_reverse_still_refused():
    # Direction inverse : rouge meme sur le chemin scope de ML-06.
    a = {"language_version": "3.13.15", "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.12.13", "kernelspec_name": "coursia-ml-training"}
    path = "MyIA.AI.Notebooks/ML/ML.Net/ML-06-ONNX-Python.ipynb"
    assert ckd.accepted_canonical_transition(a, b, nb_path=path) is False


# --- #23292 : le carnet 02-ML-Cours reste a 3.10.19 et re-execute --------
#
# La direction 3.10 -> 3.13 n'existait dans aucune des deux tables pour le
# kernelspec `coursia-ml-training` : mesure avant l'entree, sur le module
# d'avant-fix, `accepted_canonical_transition` rendait False avec ET sans
# chemin. Les tests ci-dessous portent la positive (2.9d, dont les sorties
# sont re-executees dans la meme PR) et les controles negatifs que
# l'acceptance de #23292 exige nominativement : un carnet hors serie
# partageant le kernelspec reste rouge, la direction inverse le reste aussi,
# et 2.9g -- dont la re-execution est due mais pas encore faite -- reste
# rouge tant que la mesure n'existe pas.

_02ML = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/"
_29D = _02ML + "2.9d-Features-Circulaires-Helice-Nombres.ipynb"
_29G = _02ML + "2.9g-Geometrie-de-la-Verite.ipynb"


def test_canonical_transition_scoped_02ml_310_to_313_accepted():
    # Voie 1 de #23292 : la re-execution sous le venv canon
    # `coursia-ml-training` (mesure a 3.13.15) est la convergence attendue
    # du carnet de la serie encore estampille 3.10.19.
    a = {"language_version": "3.10.19", "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.15", "kernelspec_name": "coursia-ml-training"}
    assert ckd.accepted_canonical_transition(a, b, nb_path=_29D) is True


def test_canonical_transition_scoped_29g_still_refused():
    # 2.9g partage la serie et la direction, mais pas la mesure : ses sorties
    # ne sont pas re-executees. Une entree accorde la permission de bouger la
    # version d'un carnet ; l'accorder avant la mesure laisserait passer un
    # hand-edit sous couvert de convergence. Le carnet reste donc rouge, et
    # ce test tombe le jour ou sa tranche est livree.
    a = {"language_version": "3.10.19", "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.15", "kernelspec_name": "coursia-ml-training"}
    assert ckd.accepted_canonical_transition(a, b, nb_path=_29G) is False


def test_canonical_transition_scoped_02ml_does_not_leak_outside_series():
    # Controle negatif de l'acceptance : un carnet HORS 02-ML-Cours qui
    # partage le kernelspec garde sa direction rouge (#22979 : 67 carnets
    # concernes), et la meme transition sans chemin reste rouge aussi.
    a = {"language_version": "3.10.19", "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.13.15", "kernelspec_name": "coursia-ml-training"}
    assert ckd.accepted_canonical_transition(
        a, b, nb_path="MyIA.AI.Notebooks/GenAI/Texte/01-Prompt-Eng.ipynb"
    ) is False
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_scoped_02ml_reverse_still_refused():
    # Le cliquet ne descend pas : 3.13 -> 3.10 reste rouge meme sur le
    # chemin scope.
    a = {"language_version": "3.13.15", "kernelspec_name": "coursia-ml-training"}
    b = {"language_version": "3.10.19", "kernelspec_name": "coursia-ml-training"}
    assert ckd.accepted_canonical_transition(a, b, nb_path=_29D) is False


def test_canonical_transition_python_313_to_311_refused():
    # Negatif 1 : la direction inverse est une regression du canon.
    a = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    b = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_python_311_to_310_refused():
    # Negatif 2 : retombada sur 3.10 apres adoption du canon 3.11.
    a = {"language_version": "3.11.9", "kernelspec_name": "python3"}
    b = {"language_version": "3.10.19", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_python_313_to_38_refused():
    # Negatif 3 : retomber de 3.13 a 3.8 reste rouge, meme si 3.8 -> 3.13
    # est accepte dans l'autre sens.
    a = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    b = {"language_version": "3.8.10", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_python_31213_to_3133_accepted():
    # Positif : la transition 3.12 -> 3.13 est couverte. Anticipation :
    # aucun carnet main n'exerce aujourd'hui le tuple (`python3`, `3.12`,
    # `3.13`) — le seul carnet a 3.12 mesure est ICT-47
    # (PainAxisDistillation), dont le kernelspec est `py310-gpu` (distinct
    # de `python3`), donc hors scope de ce tuple (le cliquet exige le meme
    # nom de kernel entre base et tete). L'entree est ajoutee pour
    # preparer la convergence d'un futur carnet `python3` a 3.12.x. Le
    # temoin effectif du test est le tuple synthetique ci-dessous, pas
    # ICT-47. Ajout a la demande du coordinateur (commentaire 5988053521,
    # 2026-10-05T04:22Z), oubli du dispatch initial qui ne listait pas
    # 3.12 dans les couverts.
    a = {"language_version": "3.12.13", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is True


def test_canonical_transition_python_313_to_312_refused():
    # Negatif : la direction inverse 3.13 -> 3.12 reste rouge (n'a pas
    # ete ajoutee a la table ; convention : la table n'accepte que les
    # convergences vers le canon, pas la descente).
    a = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    b = {"language_version": "3.12.13", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_python_kernelspec_change_refused():
    # Negatif 4 : un changement de kernelspec.name reste rouge, meme avec
    # des versions couvertes par la table.
    a = {"language_version": "3.11.9", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python311"}
    assert ckd.accepted_canonical_transition(a, b) is False


def _patched_run(monkeypatch, base_nb, head_nb):
    """Run _run() on one fake notebook pair, git fully stubbed."""
    import types
    monkeypatch.setattr(ckd, "resolve_base", lambda ref: "fake-base")
    monkeypatch.setattr(ckd, "changed_notebooks",
                        lambda base: ["Fake/Sudoku-1.ipynb"])
    monkeypatch.setattr(
        ckd, "read_blob",
        lambda ref, p, cwd=None: base_nb if ref == "fake-base" else head_nb)
    args = types.SimpleNamespace(base_ref="origin/main", json=False,
                                 explain=False)
    return ckd._run(args)


def test_run_cs12_to_cs13_is_green_end_to_end(monkeypatch):
    # Trajet COMPLET : la transition canon seule ne produit aucun finding
    # -- le ratchet ne rougit pas la convergence vers le canon.
    base_nb = _nb(".net-csharp", "12.0", ["total = 3\n"])
    head_nb = _nb(".net-csharp", "13.0", ["total = 3\n"])
    result = _patched_run(monkeypatch, base_nb, head_nb)
    assert result["findings"] == []


def test_run_cs13_to_cs12_is_red_end_to_end(monkeypatch):
    # Controle negatif du trajet : la direction inverse fait finding.
    base_nb = _nb(".net-csharp", "13.0", ["total = 3\n"])
    head_nb = _nb(".net-csharp", "12.0", ["total = 3\n"])
    result = _patched_run(monkeypatch, base_nb, head_nb)
    assert len(result["findings"]) == 1
    assert "language_info.version" in result["findings"][0]["kernel_diffs"][0]


def test_run_canonical_transition_does_not_mask_sig_drift(monkeypatch):
    # La table ne masque QUE la derive de version : une derive de
    # signature float coexistante reste un finding (elle releve de C.4).
    base_nb = _nb(".net-csharp", "12.0", ["[1.0, 1.0, 1.0]\n"])
    head_nb = _nb(".net-csharp", "13.0",
                  ["[1.0, 0.9999999999999998, 1.0]\n"])
    result = _patched_run(monkeypatch, base_nb, head_nb)
    assert len(result["findings"]) == 1
    f = result["findings"][0]
    assert f["kernel_diffs"] == []
    assert f["signature_drift_cells"]
    assert f["canonical_transition"] is True

# --- #19961 : tolerance numerique 1 ULP (decision bruit assume) ------------
# Tests consolides ici (fichier canonique du guard) : le pairage 1-ULP est
# du bruit, 2 ULP et plus restent du drift. Les fixtures historiques plus
# haut passent leurs valeurs derivees a 2 ULP pour la meme decision.

from check_kernel_drift import (  # noqa: E402
    _diff_signatures_ordinal,
    _signatures_equivalent,
    _within_ulp,
    diff_signatures,
    float_signatures,
)

ONE_ULP_BELOW_1 = 0.9999999999999999   # 1 nextafter step sous 1.0
TWO_ULP_BELOW_1 = 0.9999999999999998   # 2 steps


def _nb_ulp(*outputs_text, cell_id="c1"):
    return {
        "cells": [
            {
                "cell_type": "code",
                "id": cell_id,
                "outputs": [
                    {"output_type": "execute_result",
                     "data": {"text/plain": text}}
                    for text in outputs_text
                ],
            }
        ]
    }


class TestWithinUlp:
    def test_exact_equality(self):
        assert _within_ulp(1.0, 1.0)

    def test_one_ulp_is_noise(self):
        assert _within_ulp(1.0, ONE_ULP_BELOW_1)
        assert _within_ulp(ONE_ULP_BELOW_1, 1.0)

    def test_two_ulp_is_drift(self):
        assert not _within_ulp(1.0, TWO_ULP_BELOW_1)

    def test_nan_nan_accepted(self):
        assert _within_ulp(float("nan"), float("nan"))

    def test_nan_vs_value_refused(self):
        assert not _within_ulp(float("nan"), 1.0)

    def test_infinities_require_exact_sign(self):
        assert _within_ulp(float("inf"), float("inf"))
        assert not _within_ulp(float("inf"), float("-inf"))
        assert not _within_ulp(float("inf"), 1e308)

    def test_subnormal_one_step(self):
        assert _within_ulp(0.0, 5e-324)     # le plus petit sous-normal
        assert not _within_ulp(0.0, 1e-323)

    def test_complex_partwise(self):
        assert _within_ulp(complex(1.0, 2.0), complex(ONE_ULP_BELOW_1, 2.0))
        assert not _within_ulp(complex(1.0, 2.0), complex(1.0, 2.5))


class TestSignaturesEquivalent:
    def test_numpy2_repr_case_is_noise(self):
        """Le cas fondateur : NumPy 1.x imprime 1.0 la ou 2.x imprime
        0.9999999999999999 -- meme valeur a 1 ULP pres, pas de drift."""
        base = ("[1.0, 1.0, 1.0]",)
        head = (f"[1.0, {ONE_ULP_BELOW_1!r}, 1.0]",)
        assert base != head                      # byte-text DIFFERENT
        assert _signatures_equivalent(base, head)

    def test_beyond_one_ulp_stays_drift(self):
        base = ("[1.0, 1.0]",)
        head = (f"[{TWO_ULP_BELOW_1!r}, 1.0]",)
        assert not _signatures_equivalent(base, head)

    def test_different_value_stays_drift(self):
        assert not _signatures_equivalent(("[1.0, 2.0]",), ("[1.0, 2.1]",))

    def test_element_count_mismatch_stays_drift(self):
        assert not _signatures_equivalent(("[1.0, 1.0]",), ("[1.0]",))

    def test_array_count_mismatch_stays_drift(self):
        assert not _signatures_equivalent(("[1.0, 1.0]",), ())
        assert not _signatures_equivalent(
            ("[1.0, 1.0]",), ("[1.0, 1.0]", "[2.0, 3.0]"))

    def test_identical_text_short_circuits(self):
        assert _signatures_equivalent(("[1.0, 1.0]",), ("[1.0, 1.0]",))

    def test_unparseable_falls_back_to_text_fail_closed(self):
        """Une paire qui ne parse pas retombe sur l'egalite textuelle :
        jamais d'equivalence fabriquee sur une valeur non mesuree."""
        assert _signatures_equivalent(("[1.0, a.b]",), ("[1.0, a.b]",))
        assert not _signatures_equivalent(("[1.0, a.b]",), ("[1.0, c.d]",))


class TestDiffSignatures:
    def test_id_aligned_one_ulp_not_reported(self):
        base = _nb_ulp("[1.0, 1.0, 1.0]")
        head = _nb_ulp(f"[1.0, {ONE_ULP_BELOW_1!r}, 1.0]")
        b_sig, h_sig = float_signatures(base), float_signatures(head)
        assert b_sig != h_sig
        assert diff_signatures(b_sig, h_sig, base_nb=base, head_nb=head) == []

    def test_id_aligned_beyond_one_ulp_reported(self):
        base = _nb_ulp("[1.0, 1.0]")
        head = _nb_ulp(f"[{TWO_ULP_BELOW_1!r}, 1.0]")
        b_sig, h_sig = float_signatures(base), float_signatures(head)
        assert diff_signatures(b_sig, h_sig, base_nb=base, head_nb=head) == ["c1"]

    def test_ordinal_fallback_same_tolerance(self):
        # Notebooks sans ids : alignement ordinal legacy, meme tolerance.
        base = _nb_ulp("[1.0, 1.0]")
        base["cells"][0].pop("id")
        head = _nb_ulp(f"[1.0, {ONE_ULP_BELOW_1!r}]")
        head["cells"][0].pop("id")
        b_sig, h_sig = float_signatures(base), float_signatures(head)
        assert _diff_signatures_ordinal(b_sig, h_sig) == []
        head2 = _nb_ulp("[1.0, 2.0]")
        head2["cells"][0].pop("id")
        assert _diff_signatures_ordinal(b_sig, float_signatures(head2)) == [0]
