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
    # NumPy 1.x: [1.0, 1.0, ...]
    # NumPy 2.x: [1.0, 0.9999999999999999, 1.0, ...]
    a = (("[1.0, 1.0, 1.0, 1.0, 1.0]",),)
    b = (("[1.0, 0.9999999999999999, 1.0, 1.0, 1.0]",),)
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
    b = (("[-1.5e+00, 2.5000000000000004e-01, 3.14159]",),)
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
                "execution_count": 1,
                "outputs": ([] if text is None else
                            [{"output_type": "stream", "name": "stdout",
                              "text": text}]),
            }
            for cid, text in cells
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

    An added cell that really produces a float array is still a drift.
    """
    assert _id_aligned_diffs(
        [("c1", "[1.0, 1.0]\n")],
        [("c1", "[1.0, 1.0]\n"), ("c2", "[2.0, 2.0]\n")],
    ) == ["c2"]


def test_diff_signatures_added_empty_cell_does_not_mask_a_real_drift():
    """An empty added cell must not mask drift on a common cell."""
    assert _id_aligned_diffs(
        [("c1", "[1.0, 1.0]\n"), ("c2", "[2.0, 2.0]\n")],
        [("params-new", None), ("c1", "[1.0, 0.9999999999999999]\n"),
         ("c2", "[2.0, 2.0]\n")],
    ) == ["c1"]


def test_diff_signatures_added_mixed_only_float_ones_reported():
    """Among several added cells, only those carrying a signature report."""
    assert _id_aligned_diffs(
        [("c1", "ok\n")],
        [("c1", "ok\n"), ("injected", None), ("c3", "[3.0, 3.0]\n")],
    ) == ["c3"]



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
    # sont traites au cas par cas.
    a = {"language_version": "3.8.10", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


def test_canonical_transition_python_39_to_313_refused():
    # Negatif 6 : 3.9 -> 3.13 reste rouge (meme raison que 3.8).
    a = {"language_version": "3.9.0", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    assert ckd.accepted_canonical_transition(a, b) is False


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
    # Positif : la transition 3.12 -> 3.13 est couverte. ICT-47
    # (PainAxisDistillation) sur main est a language_info.version=3.12.13
    # (mesure directe, 2026-10-05) ; la flotte le rejeu en 3.13, donc
    # la transition est reelle. Ajout a la demande du coordinateur
    # (commentaire 5988053521, 2026-10-05T04:22Z), oubli du dispatch
    # initial qui ne listait pas 3.12 dans les couverts.
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
                  ["[1.0, 0.9999999999999999, 1.0]\n"])
    result = _patched_run(monkeypatch, base_nb, head_nb)
    assert len(result["findings"]) == 1
    f = result["findings"][0]
    assert f["kernel_diffs"] == []
    assert f["signature_drift_cells"]
    assert f["canonical_transition"] is True
