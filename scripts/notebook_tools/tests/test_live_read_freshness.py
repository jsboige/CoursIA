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
    signature_findings,
    stamp,
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


DEUX_FICHIERS = (
    "CHSH.lean : 2 lignes\n  L 1: a\n  L 2: b\n"
    "\n"
    "CHSHRandomized.lean : 3 lignes\n  L 1: x\n  L 2: y\n  L 3: z\n"
)


def test_citations_scopees_a_la_section_de_leur_fichier():
    """#22129 : une cellule qui lit DEUX fichiers voit chaque citation
    confrontee au fichier de SA section. Sans cette portee, les 19 citations de
    CHSHRandomized.lean sortaient « hors du fichier (88 lignes) » contre
    CHSH.lean, et la cellule ne pouvait jamais etre declaree fraiche."""
    assert citations(DEUX_FICHIERS, "CHSH.lean") == [(1, "a"), (2, "b")]
    assert citations(DEUX_FICHIERS, "CHSHRandomized.lean") == [
        (1, "x"), (2, "y"), (3, "z")]


def test_citations_hors_de_toute_section_restent_confrontees():
    """Fail-closed : sans en-tete, la citation n'est attribuable a personne --
    elle reste donc confrontee au fichier declare."""
    assert citations("L2: def unitcellInitial", "Modele.lean") == [
        (2, "def unitcellInitial")]


def test_une_mention_en_prose_ne_rouvre_pas_de_section():
    """Seul un en-tete (compte de lignes ou separateur) ouvre une section : une
    mention « voir Autre.lean » ne detourne pas les citations qui suivent."""
    text = ("Fichier : Modele.lean (2 lignes)\n  L 1: a\n"
            "Note : voir Autre.lean pour le detail.\n  L 2: b\n")
    assert citations(text, "Modele.lean") == [(1, "a"), (2, "b")]


def test_audit_cell_deux_sources_est_fraiche_pour_chacune():
    """Le discriminant complet sur la forme reelle de `chsh-code-inv`."""
    src_modele, src_autre = ["a", "b"], ["x", "y", "z"]
    assert audit_cell(src_modele, DEUX_FICHIERS, "CHSH.lean") == []
    assert audit_cell(src_autre, DEUX_FICHIERS, "CHSHRandomized.lean") == []
    # controle negatif : une ligne deplacee DANS sa propre section rougit
    assert len(audit_cell(["a", "z"], DEUX_FICHIERS, "CHSH.lean")) == 1


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
# ---------------------------------------------------------------------------
# Axe signature d'execution (#23390) -- opt-in, temoin negatif, deduplication
# ---------------------------------------------------------------------------
def _signed_notebook(source="x = 1\n"):
    """Carnet minimal portant une signature d'execution valide.

    ``stamp`` arrive par le module teste (qui l'importe explicitement) et non
    par un effet de bord d'ordre d'import -- reserve 4 de la review #24669.
    """
    nb = {
        "cells": [{"cell_type": "code", "id": "c1", "execution_count": 1,
                   "source": [source], "outputs": []}],
        "metadata": {"kernelspec": {"name": "python3",
                                    "display_name": "Python 3"}},
    }
    stamp(nb, {}, "2026-01-01T00:00:00Z")
    return nb


def test_signature_absente_est_ignoree():
    """Critere 3 : un carnet sans signature est ignore, pas declare non conforme."""
    assert signature_findings({"cells": [], "metadata": {}}) == []
    assert signature_findings({"cells": [], "metadata": {"kernelspec": {}}}) == []


def test_signature_fraiche_ne_produit_aucun_constat():
    """Critere 1 : l'introduction de l'axe ne rougit aucun carnet deja signe."""
    assert signature_findings(_signed_notebook()) == []


def test_source_editee_apres_execution_est_signalee():
    """Critere 2 : le temoin negatif de l'axe -- source editee apres attestation."""
    nb = _signed_notebook()
    nb["cells"][0]["source"] = ["x = 2\n"]
    findings = signature_findings(nb)
    assert len(findings) == 1
    assert findings[0].startswith("SIGNATURE_PERIMEE:")


def test_kernel_change_depuis_l_attestation_est_signale():
    nb = _signed_notebook()
    nb["metadata"]["kernelspec"]["name"] = ".net-csharp"
    assert any(f.startswith("KERNEL_INCOHERENT:")
               for f in signature_findings(nb))


def test_cellule_annexe_non_executee_rougit_le_carnet_entier():
    """Granularite de l'axe : le CARNET, pas la cellule declaree (reserve 2).

    ``verify`` atteste le carnet entier : une cellule annexe commise sans
    ``execution_count`` emet CELLULE_NON_EXECUTEE et rougit les declarations
    du carnet meme quand leur cellule est fraiche. Le comportement est
    assumi dans la docstring de ``signature_findings`` -- ce test l'epingle
    pour qu'il ne derive pas en silence.
    """
    nb = _signed_notebook()
    nb["cells"].append({"cell_type": "code", "id": "c2",
                        "execution_count": None,
                        "source": ["# annexe jamais executee\n"], "outputs": []})
    findings = signature_findings(nb)
    assert any(f.startswith("CELLULE_NON_EXECUTEE:") for f in findings)


def test_run_compte_les_carnets_perimes_au_niveau_carnet(tmp_path, monkeypatch):
    """``stale`` compte des declarations, ``signature_stale_notebooks`` des
    carnets -- les deux unites ne se confondent plus (reserve 1)."""
    import check_live_read_freshness as mod

    nb = _signed_notebook()
    nb["cells"][0]["outputs"] = [
        {"output_type": "stream", "text": ["f.lean (1 lignes)\nL1: alpha\n"]}]
    nb["cells"][0]["source"] = ["x = 2\n"]
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    (tmp_path / "f.lean").write_text("alpha\n", encoding="utf-8")
    (tmp_path / "reg.json").write_text(json.dumps({"version": 1, "cells": [
        {"notebook": "nb.ipynb", "cell_id": "c1", "source": "f.lean"},
        {"notebook": "nb.ipynb", "cell_id": "c1", "source": "f.lean"}]}),
        encoding="utf-8")
    monkeypatch.setattr(mod, "REGISTRY", tmp_path / "reg.json")
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

    report = mod.run()

    assert report["stale"] == 2, "une declaration perimee par entree"
    assert report["signature_stale_notebooks"] == 1, "un carnet perime, pas deux"


def test_run_pose_le_champ_signature_sur_les_sorties_precoces(tmp_path, monkeypatch):
    """Sortie precoce CELL_NOT_FOUND : le champ signature ne ment plus par
    defaut -- les constats de l'axe sont visibles meme sur une ligne deja
    rouge (reserve 3)."""
    import check_live_read_freshness as mod

    nb = _signed_notebook()
    nb["cells"][0]["source"] = ["x = 2\n"]  # perimee pour l'axe signature
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    (tmp_path / "reg.json").write_text(json.dumps({"version": 1, "cells": [
        {"notebook": "nb.ipynb", "cell_id": "absente", "source": "f.lean"}]}),
        encoding="utf-8")
    monkeypatch.setattr(mod, "REGISTRY", tmp_path / "reg.json")
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

    report = mod.run()

    assert report["rows"][0]["verdict"] == "CELL_NOT_FOUND"
    assert any(f.startswith("SIGNATURE_PERIMEE:")
               for f in report["rows"][0]["signature_findings"]), (
        "la ligne est deja rouge, le JSON ne doit pas cacher l'axe")


def test_run_herite_les_constats_et_ne_verifie_qu_une_fois(tmp_path, monkeypatch):
    """L'axe est porte par le CARNET : quatre entrees ne pesent qu'une verification.

    Chaque ligne du registre herite des constats, sinon la meme cellule
    apparaitrait verte ou rouge selon l'entree par laquelle on la lit.
    """
    import check_live_read_freshness as mod

    nb = _signed_notebook()
    nb["cells"][0]["outputs"] = [
        {"output_type": "stream", "text": ["f.lean (1 lignes)\nL1: alpha\n"]}]
    (tmp_path / "f.lean").write_text("alpha\n", encoding="utf-8")
    registry = {"version": 1, "cells": [
        {"notebook": "nb.ipynb", "cell_id": "c1", "source": "f.lean"},
        {"notebook": "nb.ipynb", "cell_id": "c1", "source": "f.lean"},
    ]}
    (tmp_path / "reg.json").write_text(json.dumps(registry), encoding="utf-8")
    # La source est editee APRES l'attestation : l'axe doit rougir, sans que
    # les invariants live-read (compte et citation) ne bougent.
    nb["cells"][0]["source"] = ["x = 2\n"]
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")

    calls = {"n": 0}
    real = mod.signature_findings

    def _count(notebook):
        calls["n"] += 1
        return real(notebook)

    monkeypatch.setattr(mod, "REGISTRY", tmp_path / "reg.json")
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(mod, "signature_findings", _count)

    report = mod.run()

    assert calls["n"] == 1, "une verification par carnet, pas par entree"
    assert report["signature_notebooks"] == 1
    assert report["stale"] == 2
    for row in report["rows"]:
        assert any(f.startswith("SIGNATURE_PERIMEE:") for f in row["findings"])


def test_run_desactive_l_axe_sur_demande(tmp_path, monkeypatch):
    """``--no-signature`` rend le comportement d'avant l'axe, a l'identique."""
    import check_live_read_freshness as mod

    nb = _signed_notebook()
    nb["cells"][0]["outputs"] = [
        {"output_type": "stream", "text": ["f.lean (1 lignes)\nL1: alpha\n"]}]
    nb["cells"][0]["source"] = ["x = 2\n"]
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    (tmp_path / "f.lean").write_text("alpha\n", encoding="utf-8")
    (tmp_path / "reg.json").write_text(json.dumps({"version": 1, "cells": [
        {"notebook": "nb.ipynb", "cell_id": "c1", "source": "f.lean"}]}),
        encoding="utf-8")
    monkeypatch.setattr(mod, "REGISTRY", tmp_path / "reg.json")
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

    report = mod.run(with_signature=False)

    assert report["signature_notebooks"] == 0
    assert report["stale"] == 0
    assert report["rows"][0]["verdict"] == "FRESH"


def test_registry_is_well_formed():
    reg = json.loads(REGISTRY.read_text(encoding="utf-8"))
    assert reg["cells"], "le registre est vide : l'organe ne verifie rien"


def test_registry_entries_resolve_to_real_artifacts():
    reg = json.loads(REGISTRY.read_text(encoding="utf-8"))
    for entry in reg["cells"]:
        nb = REPO_ROOT / entry["notebook"]
        # Le carnet et la cellule sont TOUJOURS reels, quelle que soit la
        # source : seule la SOURCE peut vivre hors du depot (source externe
        # epinglee, #23499).
        assert nb.is_file(), f"carnet introuvable : {entry['notebook']}"
        data = json.loads(nb.read_text(encoding="utf-8"))
        ids = {c.get("id") for c in data["cells"]}
        assert entry["cell_id"] in ids, (
            f"cellule {entry['cell_id']} introuvable dans {nb.name} -- "
            "la declaration est perimee"
        )
        if entry.get("source_kind", "repo") == "external":
            # Source externe : le fichier lu est dans un clone amont epingle,
            # pas dans le depot -- is_file() y est structurellement faux. Le
            # contrat de l'organe est le pin + l'empreinte (mirror de run(),
            # #23499), pas l'existence locale du chemin.
            assert str(entry.get("pin") or "").strip(), (
                f"source externe sans pin : {entry['source']}")
            assert str(entry.get("sha256") or "").strip(), (
                f"source externe sans sha256 : {entry['source']}")
        else:
            src = REPO_ROOT / entry["source"]
            assert src.is_file(), f"fichier lu introuvable : {entry['source']}"


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


# ---------------------------------------------------------------------------
# Source EXTERNE au depot (#23499 -- Pli 2 de l'EPIC #18205)
# ---------------------------------------------------------------------------
SHA = "a" * 64
PIN = "qinz1yang/differential-geometry@v0.1.3"
CHEMIN_AMONT = "DifferentialGeometry/Topology/ThreeManifold/Poincare.lean"


def _external_entry(**extra) -> dict:
    entry = {"notebook": "nb.ipynb", "cell_id": "c1", "source": CHEMIN_AMONT,
             "source_kind": "external", "pin": PIN, "sha256": SHA}
    entry.update(extra)
    return entry


def _external_run(tmp_path, monkeypatch, output: str, entry: dict) -> dict:
    """Joue l'organe sur une declaration de source externe."""
    import check_live_read_freshness as mod

    nb = {"cells": [_cell("c1", "print(1)\n", output)], "metadata": {}}
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    (tmp_path / "reg.json").write_text(
        json.dumps({"version": 1, "cells": [entry]}), encoding="utf-8")
    monkeypatch.setattr(mod, "REGISTRY", tmp_path / "reg.json")
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)
    return mod.run()


def test_source_externe_echellee_par_son_empreinte(tmp_path, monkeypatch):
    """Cas nominal : la cellule imprime le sha256 du fichier epingle qu'elle a lu.

    Le fichier lu est IMPUABLE (un tag ne bouge pas) : la fraicheur est
    deleguee au pin, et le lien entre la sortie commitee et le fichier lu est
    ferme par l'empreinte. Le verdict est FRESH, sans lecture du fichier.
    """
    report = _external_run(tmp_path, monkeypatch,
                           f"sha256: {SHA}\n", _external_entry())
    assert report["stale"] == 0
    assert report["rows"][0]["verdict"] == "FRESH"


def test_source_externe_sans_empreinte_rougit(tmp_path, monkeypatch):
    """Une source externe sans sha256 n'atteste rien : elle rougit."""
    entry = _external_entry()
    entry.pop("sha256")
    report = _external_run(tmp_path, monkeypatch, "Poincare.lean -- 23 lignes\n",
                           entry)
    assert report["stale"] == 1
    assert report["rows"][0]["verdict"] == "EXTERNAL_SANS_EMPREINTE"


def test_source_externe_sans_pin_rougit(tmp_path, monkeypatch):
    """Sans pin, la fraicheur serait deleguee a rien : elle rougit."""
    entry = _external_entry()
    entry.pop("pin")
    report = _external_run(tmp_path, monkeypatch, f"sha256: {SHA}\n", entry)
    assert report["stale"] == 1
    assert report["rows"][0]["verdict"] == "EXTERNAL_NON_ECINGLE"


def test_source_externe_empreinte_absente_de_la_sortie_rougit(tmp_path, monkeypatch):
    """La cellule doit prouver qu'elle a lu le fichier epingle : l'empreinte
    attendue doit apparaitre dans la sortie commitee."""
    report = _external_run(tmp_path, monkeypatch,
                           "Poincare.lean -- 23 lignes\n", _external_entry())
    assert report["stale"] == 1
    assert report["rows"][0]["verdict"] == "EXTERNAL_EMPREINTE_ABSENTE"


def test_registry_integrity_admet_une_source_externe(tmp_path, monkeypatch):
    """Le contrat d'integrite du registre admet une source EXTERNE.

    Controle par reinsertion (#23499) : la premiere entree externe REALE
    (carnet + cellule reels, source epinglee par pin + empreinte) doit
    satisfaire le test. Sans l'adaptation de
    ``test_registry_entries_resolve_to_real_artifacts``, ``is_file()`` sur le
    chemin AMONT -- absent du depot par construction -- la ferait rougir pour
    un motif qu'elle ne porte pas.
    """
    import sys

    mod = sys.modules[__name__]
    nb = {"cells": [_cell("c1", "print(1)\n", f"sha256: {SHA}\n")],
          "metadata": {}}
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    reg = tmp_path / "reg.json"
    reg.write_text(json.dumps({"version": 1, "cells": [
        {"notebook": "nb.ipynb", "cell_id": "c1", "source": CHEMIN_AMONT,
         "source_kind": "external", "pin": PIN, "sha256": SHA}]}),
        encoding="utf-8")
    monkeypatch.setattr(mod, "REGISTRY", reg)
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

    test_registry_entries_resolve_to_real_artifacts()  # ne doit pas lever


def test_registry_integrity_exige_pin_et_empreinte_sur_source_externe(
        tmp_path, monkeypatch):
    """Controle negatif : une source externe SANS pin ne satisfait PAS le
    contrat d'integrite -- le test la nomme, il ne la tolere pas."""
    import sys

    mod = sys.modules[__name__]
    nb = {"cells": [_cell("c1", "print(1)\n", "Poincare.lean -- 23 lignes\n")],
          "metadata": {}}
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    reg = tmp_path / "reg.json"
    reg.write_text(json.dumps({"version": 1, "cells": [
        {"notebook": "nb.ipynb", "cell_id": "c1", "source": CHEMIN_AMONT,
         "source_kind": "external", "sha256": SHA}]}),  # pin absent
        encoding="utf-8")
    monkeypatch.setattr(mod, "REGISTRY", reg)
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

    with pytest.raises(AssertionError):
        test_registry_entries_resolve_to_real_artifacts()


def test_une_entree_sans_source_kind_reste_repo(tmp_path, monkeypatch):
    """Le defaut reste la source du depot : une entree legacy ne change pas."""
    import check_live_read_freshness as mod

    nb = {"cells": [_cell("c1", "print(1)\n", "Modele.lean -- 3 lignes\n")],
          "metadata": {}}
    (tmp_path / "nb.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    (tmp_path / "reg.json").write_text(json.dumps({"version": 1, "cells": [
        {"notebook": "nb.ipynb", "cell_id": "c1",
         "source": "Modele.lean"}]}), encoding="utf-8")
    monkeypatch.setattr(mod, "REGISTRY", tmp_path / "reg.json")
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

    report = mod.run()

    assert report["rows"][0]["verdict"] == "SOURCE_MISSING"
