"""Tests for check_rich_output_as_text.py — un SVG imprime EN TEXTE (#26979).

Pinne le contrat de l'issue : une sortie dont le SVG ne vit que dans un
payload **textuel** (`stream`, ou `text/plain` d'un bundle sans
`image/svg+xml` ni `image/png`) est flaggee ; toute sortie rendue par une
representation native est exempte ; une chaine qui contient le mot « svg »
sans balise, et une balise `<svg …>` **non fermee**, ne sont pas des
defauts d'affichage.

Cas fondateur : #26921 (Concern user du 16/11/2026) — la cellule 9 de
`Dynamics-03-Sympathie-vs-Engagement-CSharp.ipynb` ecrit le SVG sur la
sortie standard. Le replay reel est dans `self_test()` (tete `f28443ae`).

La logique testee est pure (`svg_as_text_outputs` + cle d'ajout du
ratchet) -- pas de git, pas de kernel. Le seul test qui touche git est
`self_test()`, dont le replay est SKIPPE (et signale) quand le commit
fondateur est absent du clone.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_rich_output_as_text import (  # noqa: E402
    _SVG,
    _nb,
    _out,
    _stream,
    self_test,
    svg_as_text_outputs,
)


def _hits(outputs_by_cell):
    return svg_as_text_outputs(_nb(outputs_by_cell))


# ---------------------------------------------------------------------------
# controle positif
# ---------------------------------------------------------------------------

def test_positive_control_svg_imprime_en_texte_est_flagge():
    """Le cas fondateur : le SVG ecrit sur stdout -> flagge."""
    hits = _hits({"c9": [_stream(_SVG)]})
    assert len(hits) == 1
    assert hits[0]["cell_id"] == "c9"
    assert hits[0]["output_type"] == "stream"
    assert hits[0]["svg_bytes"] > 0


def test_un_text_plain_de_bundle_est_juge_comme_un_stream():
    """Un `text/plain` de bundle sans image est la meme classe."""
    hits = _hits({"c4": [_out({"text/plain": "prefixe\n" + _SVG})]})
    assert len(hits) == 1
    assert hits[0]["output_type"] == "display_data"


def test_une_cellule_sans_sortie_n_est_pas_une_occurrence():
    assert _hits({"c1": []}) == []


# ---------------------------------------------------------------------------
# controles negatifs
# ---------------------------------------------------------------------------

def test_un_svg_rendu_par_image_svg_plus_xml_est_exempt():
    """Le fix cible : le SVG double d'image/svg+xml est rendu, pas un defaut."""
    assert _hits({"c1": [_out({"image/svg+xml": _SVG,
                               "text/plain": _SVG})]}) == []


def test_un_fallback_image_png_est_exempt():
    assert _hits({"c1": [_out({"image/png": "iVBORw0KGgo=",
                               "text/plain": _SVG})]}) == []


def test_le_mot_svg_sans_balice_ne_declenche_nothing():
    """Une cellule qui parle de SVG n'est pas un defaut d'affichage."""
    assert _hits({"c1": [_stream("le mot svg apparait ici, sans balise")]}) == []


def test_un_svg_non_ferme_n_est_pas_une_occurrence():
    """L'element doit etre complet : une balise ouverte seule n'est rien."""
    assert _hits({"c1": [_stream("<svg width='10' height='10'>")]}) == []


def test_une_sortie_d_erreur_n_est_pas_jugee():
    """Une sortie `error` porte un traceback, pas un SVG."""
    erreur = {"output_type": "error", "ename": "ValueError",
              "evalue": "<svg>oops</svg>", "traceback": ["<svg>x</svg>"]}
    assert _hits({"c1": [erreur]}) == []


def test_un_markdown_sans_svg_ne_declenche_nothing():
    assert _hits({"c1": [_out({"text/markdown": "# titre",
                               "text/plain": "titre"})]}) == []


# ---------------------------------------------------------------------------
# cle d'occurrence (le diff base/head)
# ---------------------------------------------------------------------------

def test_la_cle_d_occurrence_ne_depend_pas_du_renumero_de_cellule():
    """Meme contenu, cellule renumerotee : la signature du contenu tient."""
    a = _hits({"c9": [_stream(_SVG)]})[0]
    b = _hits({"c42": [_stream(_SVG)]})[0]
    assert a["svg_sha1"] == b["svg_sha1"]
    assert a["cell_id"] != b["cell_id"]


def test_deux_svg_differents_ont_deux_signatures():
    autre = _SVG.replace("800", "640")
    a = _hits({"c1": [_stream(_SVG)]})[0]
    b = _hits({"c1": [_stream(autre)]})[0]
    assert a["svg_sha1"] != b["svg_sha1"]


# ---------------------------------------------------------------------------
# self-test (controles + replay du cas fondateur)
# ---------------------------------------------------------------------------

def test_le_self_test_passe():
    """Le self-test rejoue le cas fondateur reel quand le commit est la."""
    echecs = self_test()
    assert echecs == [], echecs


# ---------------------------------------------------------------------------
# cablage
# ---------------------------------------------------------------------------

def test_le_ratchet_signale_un_ajout_et_ignore_le_stock(tmp_path):
    """Le ratchet base-vs-PR, de bout en bout, sur un depot jetable.

    Le stock de main n'est pas juge : une occurrence deja presente a la base
    ne compte pas comme un ajout. C'est le contrat du ratchet (#11685) --
    un gate qui jugerait le stock condamnerait toutes les PRs tant que le
    stock n'est pas assaini.
    """
    import json
    import subprocess

    import check_rich_output_as_text as organ

    repo = tmp_path / "repo"
    repo.mkdir()
    def _git(*args):
        subprocess.run(["git", *args], cwd=str(repo), check=True,
                       capture_output=True, text=True, encoding="utf-8",
                       errors="replace")
    _git("init", "-q")
    _git("config", "user.email", "test@example.invalid")
    _git("config", "user.name", "test")
    _git("config", "commit.gpgsign", "false")

    cible = "MyIA.AI.Notebooks/Series/Un/carnet.ipynb"
    (repo / "MyIA.AI.Notebooks" / "Series" / "Un").mkdir(parents=True)
    notebook = repo / cible

    # 1. le carnet SANS defaut, puis commit
    notebook.write_text(json.dumps(_nb({"c1": []})), encoding="utf-8")
    _git("add", "-A")
    _git("commit", "-q", "-m", "carnet propre")
    # Le SHA, pas le nom `HEAD` : `HEAD` est evalue au moment de l'appel, et
    # il designerait alors le commit AVEC le defaut -- la base serait la tete
    # et le ratchet ne verrait rien (faux vert d'un test qui ne teste rien).
    propre = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(repo),
                             check=True, capture_output=True,
                             text=True, encoding="utf-8",
                             errors="replace").stdout.strip()

    # 2. le meme carnet AVEC le defaut, puis commit
    notebook.write_text(json.dumps(_nb({"c1": [_stream(_SVG)]})),
                        encoding="utf-8")
    _git("add", "-A")
    _git("commit", "-q", "-m", "svg imprime en texte")

    rapport = organ.ratchet(propre, cwd=str(repo))
    assert rapport["added_total"] == 1, rapport
    assert rapport["notebooks_flagged"] == 1
    assert rapport["rows"][0]["notebook"].endswith("carnet.ipynb")

    # 3. le meme etat, mais avec une base qui porte deja l'occurrence :
    # l'ajout disparait, le stock n'est pas re-flagge.
    rapport_stock = organ.ratchet("HEAD", cwd=str(repo))
    assert rapport_stock["added_total"] == 0, rapport_stock


def test_le_garde_est_declenche_dans_le_registre_de_la_voie_rapide():
    """L'organe est cable, en mode ADVISORY (blocking=False) d'abord."""
    racine = Path(__file__).resolve().parents[3]
    source = (racine / "scripts" / "ci" / "fast_lane_registry.py").read_text(
        encoding="utf-8", errors="replace")
    assert "check_rich_output_as_text.py" in source
    # Le garde de la famille SVG est advisory : `blocking=False`.
    idx = source.find("check_rich_output_as_text.py")
    fenetre = source[max(0, idx - 2000):idx + 2000]
    assert "blocking=False" in fenetre
    assert "needs_base=True" in fenetre
