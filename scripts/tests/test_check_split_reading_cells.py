"""Tests du recensement des cellules de lecture scindees (#16762).

Fixtures synthetiques reproduisant les formes mesurees sur main :
pattern nominal user (« Lecture » puis « Lecture chiffree » consecutifs),
paire generique, paire separee par une cellule de code, temoins negatifs,
et le controle FP (deux lectures de signaux differents empilees ->
hit structurel mais recouvrement faible, le garde doit se fier a C, pas
a la seule structure).
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_split_reading_cells import cell_title, detect, main  # noqa: E402


def md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source, "metadata": {}}


def code(source: str = "1 + 1") -> dict:
    return {"cell_type": "code", "source": source, "metadata": {}, "outputs": []}


def write_nb(path, nb: dict) -> None:
    import json
    path.write_text(json.dumps(nb), encoding="utf-8")


def test_named_split_user_pattern():
    nb = {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** — le montant.\nL'age pese 0.37 et le montant 0.35, "
           "signes opposes : effet de correlation marginal."),
    ]}
    hits = detect(nb)
    assert len(hits) == 1
    h = hits[0]
    assert h["type"] == "named_split"
    assert h["cells"] == [1, 2]
    assert h["titles"][0].startswith("Lecture")
    assert "chiffree" in h["titles"][1]
    assert 0.0 <= h["jaccard"] <= 1.0
    assert h["shared_rare_words"] >= 1


def test_generic_pair_interpretation_titles():
    nb = {"cells": [
        md("### Lecture du resultat\nLa courbe converge apres 200 episodes."),
        md("### Analyse du modele\nLa courbe converge apres 200 episodes, "
           "le modele apprend la valeur."),
    ]}
    hits = detect(nb)
    assert [h["type"] for h in hits] == ["generic_pair"]


def test_separated_by_code_is_secondary():
    nb = {"cells": [
        md("### Lecture\nPremiere lecture du terrain."),
        code("df.head()"),
        md("### Lecture chiffree — les agregats\nSeconde lecture des agregats."),
    ]}
    hits = detect(nb)
    assert len(hits) == 1
    assert hits[0]["type"] == "separated_by_code"
    assert hits[0]["cells"] == [0, 2]


def test_clean_notebook_no_hit():
    nb = {"cells": [
        md("## Introduction\nLe contexte."),
        code("print('ok')"),
        md("### Lecture\nUne seule interpretation, pas de voisine."),
        md("## Conclusion\nEt suite du parcours."),
    ]}
    assert detect(nb) == []


def test_non_interpretation_consecutive_md_not_flagged():
    nb = {"cells": [
        md("### Exercice\nA vous de jouer."),
        md("### Indice\nPensez a la programmation dynamique."),
    ]}
    assert detect(nb) == []


def test_fp_control_different_signals_low_containment():
    """Deux lectures consecutives de signaux DIFFERENTS (temoin WS-00a) :
    le signal structurel reste (a instruire a l'oeil) mais C doit etre
    faible -- c'est la metrique qui evacue le faux positif du garde."""
    nb = {"cells": [
        md("### Lecture — Doppler\nLe chirp se dilate, la densite spectrale "
           "du signal doppler s'etale vers les basses frequences."),
        md("### Lecture — HeaviSine\nLa discontinuite du signal heavisine "
           "concentre l'energie sur les sauts brusques du champ."),
    ]}
    hits = detect(nb)
    assert [h["type"] for h in hits] == ["generic_pair"]
    assert hits[0]["rare_containment"] < 0.20


def test_cell_title_strips_markdown_noise():
    assert cell_title("### **Lecture chiffree — les agregats**") == \
        "Lecture chiffree — les agregats"
    assert cell_title("- `Lecture` du resultat") == "Lecture` du resultat"
    assert cell_title("") == ""


def test_directory_mode_findings_rc2_with_fail_on_findings(tmp_path, capsys):
    """Mode dossier : --fail-on-findings doit renvoyer 2 quand le dossier
    contient au moins un finding (reserve adjoint #16786 : le flag etait
    avale par scan_root, qui retournait toujours 0)."""
    write_nb(tmp_path / "notebook_a.ipynb", {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** — le montant.\nL'age pese 0.37 et le montant 0.35."),
    ]})
    rc = main([str(tmp_path), "--fail-on-findings"])
    capsys.readouterr()
    assert rc == 2


def test_directory_mode_clean_rc0(tmp_path, capsys):
    """Mode dossier sans findings : rc 0 meme avec --fail-on-findings."""
    write_nb(tmp_path / "notebook_clean.ipynb", {"cells": [
        md("## Introduction\nLe contexte."),
        code("print('ok')"),
        md("### Lecture\nUne seule interpretation, pas de voisine."),
    ]})
    rc = main([str(tmp_path), "--fail-on-findings"])
    capsys.readouterr()
    assert rc == 0


# --- #17044 : un carnet illisible ne doit pas annuler le recensement ---------


def test_scan_dossier_ne_avorte_pas_sur_carnet_illisible(tmp_path, capsys):
    """#17044 : `scan_root` faisait `return 1` sur le premier carnet illisible.

    Un seul carnet corrompu annulait TOUT le recensement (rc=1, zero finding --
    pas seulement un recensement degrade), donc l'organe etait incablable en
    cliquet : n'importe quel carnet corrompu du depot rougissait toute PR, pour
    une raison sans rapport avec elle. Il doit desormais le rapporter et
    continuer.

    Le carnet illisible est place ENTRE deux carnets sains : la preuve que le
    scan continue est que celui qui le SUIT est quand meme recense.
    """
    write_nb(tmp_path / "a_sain.ipynb", {"cells": [
        md("## Introduction\nRien a signaler ici."),
        code("print('ok')"),
    ]})
    (tmp_path / "b_corrompu.ipynb").write_text(
        "{ ceci n'est pas du JSON", encoding="utf-8")
    write_nb(tmp_path / "c_scinde.ipynb", {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** -- le montant.\nL'age pese 0.37."),
    ]})

    rc = main([str(tmp_path)])
    out, err = capsys.readouterr()

    assert rc == 0, "un carnet illisible ne doit pas faire rougir le recensement"
    assert "c_scinde" in out, "le carnet sain APRES le corrompu doit etre recense"
    assert "b_corrompu" in err, "le carnet saute doit etre nomme sur stderr"
    assert "illisible" in err, "le recensement doit se declarer PARTIEL"


def test_carnet_illisible_ne_masque_pas_un_finding(tmp_path, capsys):
    """Le carnet illisible ne doit ni avorter ni masquer un finding reel :
    avec --fail-on-findings, un vrai finding reste rc=2 (et non rc=1)."""
    (tmp_path / "a_corrompu.ipynb").write_text("not json at all", encoding="utf-8")
    write_nb(tmp_path / "b_scinde.ipynb", {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** -- le montant.\nL'age pese 0.37."),
    ]})

    rc = main([str(tmp_path), "--fail-on-findings"])
    capsys.readouterr()
    assert rc == 2, "le cliquet doit encore mordre malgre un carnet illisible"


def test_fichier_illisible_rc1_sans_traceback(tmp_path, capsys):
    """Contrat documente : un fichier DESIGNE illisible rend rc=1. Il etait
    rendu par une JSONDecodeError non rattrapee (traceback jusqu'a
    l'interpreteur) : meme code, rendu proprement."""
    p = tmp_path / "corrompu.ipynb"
    p.write_text("{ pas du json", encoding="utf-8")

    rc = main([str(p)])
    out, err = capsys.readouterr()
    assert rc == 1
    assert "ERREUR lecture" in err
