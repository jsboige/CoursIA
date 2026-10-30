"""Tests for scripts/notebook_tools/check_live_read_freshness.py -- #20049.

L'organe mesure un invariant : la sortie COMMITTEE d'une cellule declaree
live-read doit rester coherente avec l'etat COURANT du fichier qu'elle lit.
Les tests couvrent :

- l'extraction des invariants (compte de lignes accole au fichier, citations
  ``L<n>: <texte>``) depuis une sortie de cellule ;
- la semantique de comparaison (prefixe, ellipse, ligne hors fichier) ;
- le controle positif SYNTHETIQUE -- le document fondateur `Lean-16b` rend la
  meme forme de findings quand la ligne citee a bouge ;
- l'integrite du registre : chaque declaration pointe une cellule et un
  fichier qui existent reellement (un registre qui derive est un organe
  aveugle, pas un organe vert).

L'organe n'est volontairement PAS asserte ici sur l'etat de `main` : un carnet
qui doit etre resynchronise ferait rougir toute la suite au lieu de nommer la
cellule concernee. C'est la lane CI (`Live-read freshness`) qui porte ce
verdict, pas pytest.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from check_live_read_freshness import (  # noqa: E402
    REGISTRY,
    REPO_ROOT,
    audit_cell,
    cell_output_text,
    citation_matches,
    citations,
    count_claims,
    main,
    UNDECLARED_BASELINE,
    undeclared_live_read_cells,
)


# ---------------------------------------------------------------------------
# Extraction des invariants
# ---------------------------------------------------------------------------
def test_count_claims_scoped_to_basename():
    text = "Fichier : Conway/Life/Pillars.lean (246 lignes)\nLife.lean 253 lignes\n"
    assert count_claims(text, "Pillars.lean") == [(246, "Fichier : Conway/Life/Pillars.lean (246 lignes)")]


def test_count_claims_ignores_line_without_basename():
    assert count_claims("Life.lean            253 lignes", "Pillars.lean") == []


def test_count_claims_tolerates_reflowed_output():
    """#20076 reserve 2 : nom du fichier et compte sur deux lignes VOISINES."""
    text = "Fichier lu : Conway/Life/Pillars.lean\ncompte : 348 lignes\n"
    assert count_claims(text, "Pillars.lean") == [(348, "compte : 348 lignes")]


def test_count_claims_adjacent_line_naming_another_file_is_not_claimed():
    """La borne du repli : le compte d'un fichier VOISIN n'est pas attribue au
    fichier declare. Sans elle, « Life.lean 253 lignes » voisinerait le nom et
    serait confronte au mauvais fichier."""
    text = "Pillars.lean\nLife.lean            253 lignes\n"
    assert count_claims(text, "Pillars.lean") == []


def test_count_claims_does_not_read_a_decimal_as_a_filename():
    """Le garde de la borne ne doit pas prendre un decimal pour un fichier :
    sinon toute ligne voisine portant « 0.9326 » serait ecartee."""
    text = "Pillars.lean\nR^2 = 0.9326, soit 348 lignes\n"
    assert count_claims(text, "Pillars.lean") == [(348, "R^2 = 0.9326, soit 348 lignes")]


def test_citations_extract_line_and_text():
    text = "  L 87: | `otcametapixel.rle` | 2058 x 2058 |\n  L116: def otcaInitial : Grid := ([] : Grid)\n"
    assert citations(text) == [
        (87, "| `otcametapixel.rle` | 2058 x 2058 |"),
        (116, "def otcaInitial : Grid := ([] : Grid)"),
    ]


def test_citations_empty_when_output_has_none():
    assert citations("Statistiques des modules Life\n====") == []


def test_cell_output_text_reads_stream_and_execute_result():
    cell = {
        "outputs": [
            {"output_type": "stream", "text": ["ligne 1\n"]},
            {"output_type": "execute_result", "data": {"text/plain": ["ligne 2"]}},
        ]
    }
    assert cell_output_text(cell) == "ligne 1\n\nligne 2"


def test_cell_output_text_strips_ansi_before_matching():
    cell = {"outputs": [{"output_type": "stream", "text": ["\x1b[31mFichier : Pillars.lean (246 lignes)\x1b[0m"]}]}
    lines = ["a"] * 246
    assert audit_cell(lines, cell_output_text(cell), "Pillars.lean") == []


# ---------------------------------------------------------------------------
# Semantique de comparaison
# ---------------------------------------------------------------------------
def test_citation_matches_prefix_and_whitespace():
    assert citation_matches("def otcaInitial : Grid := ([] : Grid)", "def otcaInitial : Grid := ([] : Grid)")
    assert citation_matches("| `x.rle`   | 2058 |", "| `x.rle` | 2058 |")


def test_citation_matches_tolerates_ellipsis_truncation():
    assert citation_matches("evolveHashlifeFastMemo otcaGens otcaInitial = otcaTarget := by", "evolveHashlifeFastMemo otcaGens ...")


def test_citation_matches_rejects_moved_line():
    assert not citation_matches("def otcaInitial : Grid := ([] : Grid)", "def unitcellInitial : Grid := ([] : Grid)")


def test_citation_matches_requires_word_boundary_on_full_prefix():
    """#20076 (nit) : un symbole renomme en gardant le prefixe commun ne doit
    plus valider -- « theorem foo » ne doit pas attester « theorem foobar »."""
    assert not citation_matches("theorem foobar : True", "theorem foo")
    assert not citation_matches("def foo_bar := 1", "def foo")


def test_citation_matches_accepts_prefix_ending_at_word_boundary():
    assert citation_matches("theorem foo : True", "theorem foo")
    assert citation_matches("| a | 2058 |", "| a |")


def test_citation_matches_ellipsis_path_stays_lenient_mid_word():
    """Le chemin ellipse declare la troncature : une coupe a l'interieur d'un
    identifiant reste attestable (le residu est nomme, pas ferme)."""
    assert citation_matches("evolveHashlifeFastMemo helper := by", "evolveHashlifeFast...")


# ---------------------------------------------------------------------------
# audit_cell : le discriminant
# ---------------------------------------------------------------------------
SRC = ["alpha", "def unitcellInitial : Grid := ([] : Grid)", "| x | y |"]


@pytest.mark.parametrize("text", [
    "fichier (3 lignes)",           # compte juste
    "L2: def unitcellInitial",      # citation juste
    "L3: | x | y |",                # citation juste
    "L1: alpha ...",                # ellipse toleree
])
def test_audit_cell_fresh(text):
    assert audit_cell(SRC, text, "fichier") == []


@pytest.mark.parametrize("text", [
    "fichier (4 lignes)",           # compte faux
    "L2: def otcaInitial",          # la ligne 2 a bouge
    "L9: alpha",                    # citation hors du fichier
])
def test_audit_cell_stale(text):
    assert len(audit_cell(SRC, text, "fichier")) == 1


def test_audit_cell_positive_control_matches_founding_case_shape():
    """Forme exacte du cas #20019 : fichier de 348 lignes, cellule a 246."""
    src = ["x"] * 348
    text = "Fichier : Conway/Life/Pillars.lean (246 lignes)\n  L88: def unitcellInitial : Grid := ([] : Grid)"
    findings = audit_cell(src, text, "Pillars.lean")
    assert len(findings) == 2
    assert any(f.startswith("LINE_COUNT") for f in findings)
    assert any(f.startswith("LINE_CITATION") for f in findings)


# ---------------------------------------------------------------------------
# Registre
# ---------------------------------------------------------------------------
def test_registry_is_well_formed():
    reg = json.loads(REGISTRY.read_text(encoding="utf-8"))
    assert reg["cells"], "le registre est vide : l'organe ne verifie rien"


def test_registry_entries_resolve_to_real_artifacts():
    reg = json.loads(REGISTRY.read_text(encoding="utf-8"))
    for entry in reg["cells"]:
        nb = REPO_ROOT / entry["notebook"]
        src = REPO_ROOT / entry["source"]
        assert nb.is_file(), f"carnet introuvable : {entry['notebook']}"
        assert src.is_file(), f"fichier lu introuvable : {entry['source']}"
        data = json.loads(nb.read_text(encoding="utf-8"))
        ids = {c.get("id") for c in data["cells"]}
        assert entry["cell_id"] in ids, (
            f"cellule {entry['cell_id']} introuvable dans {nb.name} -- "
            "la declaration est perimee"
        )


def test_self_test_passes():
    assert main(["--self-test"]) == 0


# ---------------------------------------------------------------------------
# Invariant INVERSE (#22041, reserve 2) : carnets -> registre
# ---------------------------------------------------------------------------
def _cell(cell_id: str, source: str, output: str) -> dict:
    return {"cell_type": "code", "id": cell_id, "metadata": {},
            "execution_count": 1, "source": source,
            "outputs": [{"output_type": "stream", "name": "stdout",
                         "text": output}]}


def _tree(tmp_path: Path, cells: list[dict], declared: list[dict]) -> tuple[Path, Path]:
    """Un arbre minimal : un carnet sous MyIA.AI.Notebooks, une source, un registre."""
    root = tmp_path / "MyIA.AI.Notebooks"
    (root / "Serie").mkdir(parents=True)
    (tmp_path / "src").mkdir()
    (tmp_path / "src" / "Modele.lean").write_text("a\nb\nc\n", encoding="utf-8")
    (tmp_path / "src" / "Autre.lean").write_text("x\ny\n", encoding="utf-8")
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    (root / "Serie" / "Carnet.ipynb").write_text(
        json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    reg = tmp_path / "registre.json"
    reg.write_text(json.dumps({"version": 1, "cells": declared}), encoding="utf-8")
    return root, reg


LECTURE = "path = BASE / 'src' / 'Modele.lean'\nprint(path.read_text())\n"


def test_invariant_inverse_detecte_une_cellule_non_declaree(tmp_path):
    """Une cellule live-read absente du registre doit etre NOMMEE."""
    root, reg = _tree(tmp_path, [_cell("abc", LECTURE, "Modele.lean : 3 lignes\n")], [])
    found = undeclared_live_read_cells(notebook_root=root, registry_path=reg)
    assert [(f["notebook"], f["cell_id"]) for f in found] == [
        ("MyIA.AI.Notebooks/Serie/Carnet.ipynb", "abc")]


def test_invariant_inverse_est_satisfait_quand_la_cellule_est_declaree(tmp_path):
    """Controle negatif : la meme cellule declaree ne remonte plus."""
    cells = [_cell("abc", LECTURE, "Modele.lean : 3 lignes\n")]
    root, reg = _tree(tmp_path, cells, [{
        "notebook": "MyIA.AI.Notebooks/Serie/Carnet.ipynb",
        "cell_id": "abc", "source": "src/Modele.lean"}])
    assert undeclared_live_read_cells(notebook_root=root, registry_path=reg) == []


def test_invariant_inverse_ne_confond_pas_un_compte_non_rattache(tmp_path):
    """Controle negatif mesure : « 12 lignes » d'un tableau n'est pas une lecture.

    Cas reel qui a produit un faux positif (`m3_har_asymmetric_semivariance`) :
    la cellule nomme un script puis affiche un compte de LIGNES DE TABLEAU. Le
    compte doit nommer le fichier declare, comme le fait deja `count_claims`.
    """
    src = "s = Path('src/Autre.lean').read_text()\nprint('Resultats : 12 lignes')\n"
    root, reg = _tree(tmp_path, [_cell("abc", src, "Resultats : 12 lignes, 3 actifs\n")], [])
    assert undeclared_live_read_cells(notebook_root=root, registry_path=reg) == []


def test_invariant_inverse_resout_un_chemin_construit_par_segments(tmp_path):
    """La cellule declaree de GOL-01 n'a AUCUN chemin complet en litteral.

    `WIN_LEAN_PROJECT / 'Conway' / 'Life' / 'Pillars.lean'` : un detecteur qui
    n'accepterait que les chemins resolvables serait aveugle a la cellule qu'il
    protege. Le dernier segment suffit.
    """
    src = ("p = BASE / 'src' / 'Modele.lean'\n"
           "print(f'{p.name} -- declarations :')\n"
           "for i, l in enumerate(p.read_text().splitlines(), 1):\n"
           "    print(f'L{i}: {l}')\n")
    root, reg = _tree(tmp_path, [_cell("seg", src,
                                       "Modele.lean -- declarations :\nL1: a\n")], [])
    assert [f["cell_id"] for f in
            undeclared_live_read_cells(notebook_root=root, registry_path=reg)] == ["seg"]


def test_registre_complet_sur_l_arbre_reel():
    """Le ratchet qui retrecit : toute cellule live-read non declaree est vue.

    Le registre et l'organe vont registre -> cellule ; sans cet invariant,
    ajouter une cellule live-read ne rougit nulle part (#21899 par l'autre
    bout). Le socle est celui de l'organe lui-meme : ce test mesure que la
    realite n'a pas bouge sous lui, il ne redige pas une seconde liste.
    """
    found = {(f["notebook"], f["cell_id"]) for f in undeclared_live_read_cells()}
    assert found == UNDECLARED_BASELINE, (
        "cellules live-read non declarees inattendues : "
        f"{sorted(found - UNDECLARED_BASELINE)} ; declarees depuis : "
        f"{sorted(UNDECLARED_BASELINE - found)} (retrecir UNDECLARED_BASELINE)")


def test_une_cellule_hors_socle_rougit_l_organe(monkeypatch):
    """Le socle est un cliquet, pas un blanc-seing : une cellule nouvelle rougit."""
    import check_live_read_freshness as organe

    monkeypatch.setattr(organe, "undeclared_live_read_cells", lambda *a, **k: [
        {"notebook": "MyIA.AI.Notebooks/Serie/Nouveau.ipynb",
         "cell_id": "neuf", "literals": ["Modele.lean"]}])
    assert organe.main(["--check-declarations"]) == 1
