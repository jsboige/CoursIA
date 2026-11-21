"""Tests de `scripts/notebook_tools/build_jupyterlite_site.py` (pli 2.2).

Ce que ces tests verrouillent :

1. **le lot vient du critere, pas d'une liste** -- un depot temporaire avec
   deux carnets eligibles et un carnet refuse (import absent) doit produire
   un lot qui ne contient que les eligibles ; ajouter un carnet ineligible
   ne doit rien changer au lot ;
2. **la pose est propre** -- `files/` est remis a zero avant la pose (un
   reste d'une construction anterieure ne doit pas rester en ligne), et deux
   carnets homonymes de series differentes font echouer la construction
   plutot que de publier l'un sous le nom de l'autre ;
3. **le site construit publie exactement le lot** -- un carnet manquant, un
   carnet en trop, un carnetrange dans un sous-repertoire sont signales ;
4. **les modules locaux de la serie voyagent avec le carnet** -- un carnet
   qui importe un module de sa serie le voit poser a cote de lui (sans lui,
   le carnet publie echoue a l'import en navigation) ; deux modules
   homonymes de series differentes font echouer la construction ;
5. **les URLs publiques sont bien formees** -- `lab` ouvre le carnet,
   `files` sert le carnet brut, les deux sous le prefixe du site.

Aucun test ne construit de site JupyterLite (cela demande l'outillage
navigateur) ni ne touche le reseau.

Issue #27550 (pli 2.2 de l'Epic #27543).
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import build_jupyterlite_site as bjs  # noqa: E402
from pyodide_eligibility import NotebookVerdict  # noqa: E402


def _nb(cells_sources, kernel="python3", language="python"):
    """Notebook minimal : cellules de code + metadonnees de noyau."""
    return {
        "cells": [
            {"cell_type": "code", "source": [src], "metadata": {}, "outputs": [],
             "execution_count": 1}
            for src in cells_sources
        ],
        "metadata": {
            "kernelspec": {"name": kernel, "display_name": kernel},
            "language_info": {"name": language},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write(root: Path, rel: str, nb: dict) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _verdict(path="MyIA.AI.Notebooks/SerieA/carnet.ipynb", series="SerieA",
             eligible=True, code_cells=2):
    return NotebookVerdict(
        path=path, series=series, subseries=series, kernel="python3",
        eligible=eligible, language="python", code_cells=code_cells)


# --- 1. le lot vient du critere --------------------------------------------

def _depot(tmp_path: Path, carnets):
    """Depot git minimal contenant les carnets donnes (rel -> notebook)."""
    root = tmp_path / "depot"
    root.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(["git", "config", "user.email", "t@t"], cwd=root, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=root, check=True)
    for rel, nb in carnets.items():
        _write(root, rel, nb)
    subprocess.run(["git", "add", "-A"], cwd=root, check=True)
    subprocess.run(["git", "commit", "-qm", "carnets"], cwd=root, check=True)
    return root


def test_le_lot_vient_du_critere_et_non_d_une_liste(tmp_path):
    """Deux carnets eligibles et un carnet refuse (import absent).

    Le lot contient les deux eligibles, pas le refuse : la selection passe
    par le critere d'eligibilite, pas par une liste maintenue a la main.
    """
    root = _depot(tmp_path, {
        "MyIA.AI.Notebooks/SerieA/a.ipynb": _nb(["import math", "print(math.pi)"]),
        "MyIA.AI.Notebooks/SerieB/b.ipynb": _nb(["import json", "print(json.dumps({}))"]),
        "MyIA.AI.Notebooks/SerieC/c.ipynb": _nb(["import paquet_inexistant_xyz"]),
    })
    lot = bjs.lot(root, 8)
    chemins = sorted(v.path for v in lot)
    assert chemins == ["MyIA.AI.Notebooks/SerieA/a.ipynb",
                       "MyIA.AI.Notebooks/SerieB/b.ipynb"]


def test_un_carnet_ineligible_ne_change_pas_le_lot(tmp_path):
    """Ajouter un carnet refuse ne deplace aucun carnet du lot.

    Le lot est une **selection**, pas un ordre : la regle de l'organe de
    critere (une serie par tour, series par ordre alphabetique) tient
    independamment de ce que le depot contient par ailleurs.
    """
    root = _depot(tmp_path, {
        "MyIA.AI.Notebooks/SerieA/a.ipynb": _nb(["import math"]),
    })
    lot_avant = [v.path for v in bjs.lot(root, 8)]
    _write(root, "MyIA.AI.Notebooks/SerieZ/z.ipynb", _nb(["import paquet_inexistant_xyz"]))
    subprocess.run(["git", "add", "-A"], cwd=root, check=True)
    subprocess.run(["git", "commit", "-qm", "z"], cwd=root, check=True)
    assert [v.path for v in bjs.lot(root, 8)] == lot_avant


def test_un_carnet_hors_famille_python_n_entre_pas_dans_le_lot(tmp_path):
    """La famille se lit sur `language_info.name` : un carnet .NET n'est pas
    un candidat Pyodide, meme s'il n'a aucun import interdit."""
    root = _depot(tmp_path, {
        "MyIA.AI.Notebooks/SerieA/a.ipynb": _nb(["import math"]),
        "MyIA.AI.Notebooks/SerieD/d.ipynb": _nb(["var x = 1;"], kernel="dotnet",
                                                language="csharp"),
    })
    chemins = [v.path for v in bjs.lot(root, 8)]
    assert chemins == ["MyIA.AI.Notebooks/SerieA/a.ipynb"]


# --- 2. la pose est propre -------------------------------------------------

def test_la_pose_met_a_zero_le_repertoire_de_contenus(tmp_path):
    """Un reste de construction anterieure ne doit pas rester en ligne."""
    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb", _nb(["import math"]))
    source = tmp_path / "site"
    (source / "files").mkdir(parents=True)
    (source / "files" / "ancien.ipynb").write_text("{}", encoding="utf-8")
    poses = bjs.stage(root, [(_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb"), [])],
                      source)
    assert poses["carnets"] == ["a.ipynb"]
    assert (source / "files" / "a.ipynb").is_file()
    assert not (source / "files" / "ancien.ipynb").exists()


def test_deux_carnets_homonymes_font_echouer_la_construction(tmp_path):
    """Deux carnets de series differentes, meme nom : la construction
    echoue au lieu de publier l'un des deux sous le nom de l'autre."""
    root = tmp_path / "depot"
    root.mkdir()
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    (root / "MyIA.AI.Notebooks" / "SerieB").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/meme.ipynb", _nb(["import math"]))
    _write(root, "MyIA.AI.Notebooks/SerieB/meme.ipynb", _nb(["import json"]))
    source = tmp_path / "site"
    with pytest.raises(ValueError):
        bjs.stage(root, [(_verdict("MyIA.AI.Notebooks/SerieA/meme.ipynb", "SerieA"), []),
                         (_verdict("MyIA.AI.Notebooks/SerieB/meme.ipynb", "SerieB"), [])],
                  source)


def test_un_carnet_du_lot_absent_du_depot_est_signale(tmp_path):
    """Un carnet annonce mais absent du depot est une erreur, pas un silence."""
    root = tmp_path / "depot"
    root.mkdir()
    with pytest.raises(FileNotFoundError):
        bjs.stage(root, [(_verdict(), [])], tmp_path / "site")


# --- 3. le site construit publie exactement le lot --------------------------

def test_le_site_construit_doit_publier_le_lot_entier(tmp_path):
    """Un carnet du lot absent du site construit est signale."""
    output = tmp_path / "_output"
    (output / "files").mkdir(parents=True)
    (output / "files" / "a.ipynb").write_text("{}", encoding="utf-8")
    anomalies = bjs.verifier_contenu(output, ["a.ipynb", "b.ipynb"])
    assert len(anomalies) == 1
    assert "b.ipynb" in anomalies[0]


def test_un_carnet_hors_lot_est_signale(tmp_path):
    """Un carnet en trop -- reste d'une construction anterieure -- est signale."""
    output = tmp_path / "_output"
    (output / "files").mkdir(parents=True)
    (output / "files" / "a.ipynb").write_text("{}", encoding="utf-8")
    (output / "files" / "ancien.ipynb").write_text("{}", encoding="utf-8")
    anomalies = bjs.verifier_contenu(output, ["a.ipynb"])
    assert len(anomalies) == 1
    assert "ancien.ipynb" in anomalies[0]


def test_un_carnet_range_dans_un_sous_repertoire_est_signale(tmp_path):
    """Meme nom de fichier, mais range : le site publie plus que le lot."""
    output = tmp_path / "_output"
    (output / "files" / "MyIA.AI.Notebooks").mkdir(parents=True)
    (output / "files" / "a.ipynb").write_text("{}", encoding="utf-8")
    (output / "files" / "MyIA.AI.Notebooks" / "a.ipynb").write_text("{}", encoding="utf-8")
    anomalies = bjs.verifier_contenu(output, ["a.ipynb"])
    assert len(anomalies) == 1
    assert "MyIA.AI.Notebooks/a.ipynb" in anomalies[0]


def test_un_site_sans_repertoire_de_contenus_est_signale(tmp_path):
    """Pas de `files/` dans la sortie : rien n'est publie."""
    anomalies = bjs.verifier_contenu(tmp_path / "_output", ["a.ipynb"])
    assert len(anomalies) == 1
    assert "files/" in anomalies[0]


# --- 4. les modules locaux de la serie voyagent avec le carnet ---------------

def _depot_avec_organe(tmp_path, source_module, notebook_sources=None):
    """Depot minimal : un carnet qui importe `mon_organe`, et l'organe."""
    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb",
           _nb(notebook_sources or ["import mon_organe", "print(mon_organe.VALEUR)"]))
    (root / "MyIA.AI.Notebooks" / "SerieA" / "mon_organe.py").write_text(
        source_module, encoding="utf-8")
    return root


def test_un_module_local_de_la_serie_est_embarque_avec_le_carnet(tmp_path):
    """Un carnet qui importe un module de sa serie ne doit pas etre publie
    seul : sans le module, le carnet echoue a l'import en navigation
    (mesure : `ModuleNotFoundError: dowhy_iv_organs`).

    Le critere d'eligibilite declare ces modules **embarquables** : le
    deploiement doit les embarquer pour de vrai.
    """
    root = _depot_avec_organe(tmp_path, "VALEUR = 1\n")
    publie, refus = bjs.suffisance(root, [_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                                   {}, set())
    assert refus == []
    poses = bjs.stage(root, publie, tmp_path / "site")
    assert poses["modules"] == {"mon_organe.py": "MyIA.AI.Notebooks/SerieA/mon_organe.py"}
    assert (tmp_path / "site" / "files" / "mon_organe.py").is_file()
    assert poses["modules_par_carnet"]["MyIA.AI.Notebooks/SerieA/a.ipynb"] == \
        ["mon_organe.py"]


def test_un_carnet_qui_importe_un_module_local_non_satisfaisant_n_est_pas_publie(tmp_path):
    """Un module local dont une dependance est absente de la distribution
    rend le carnet impropre au bundle : le carnet n'est pas publie.

    Mesure : le carnet `Causalite-06` importe `dowhy_iv_organs`, qui importe
    `dowhy` -- absent de la distribution Pyodide. Le carnet echoue en
    navigation ; le deploiement l'ecarte, avec le motif.
    """
    root = _depot_avec_organe(tmp_path, "import dowhy\nVALEUR = 1\n")
    publie, refus = bjs.suffisance(root, [_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                                   {"numpy": "2.4.6"}, set())
    assert publie == []
    assert len(refus) == 1
    chemin, motifs = refus[0]
    assert chemin == "MyIA.AI.Notebooks/SerieA/a.ipynb"
    assert any("dowhy" in motif and "absent de la distribution" in motif
               for motif in motifs)


def test_une_dependance_presente_dans_la_distribution_est_satisfaisante(tmp_path):
    """Un module local dont les dependances sont dans la distribution ne
    fait pas refuser le carnet."""
    root = _depot_avec_organe(tmp_path, "import numpy as np\nVALEUR = 1\n")
    publie, refus = bjs.suffisance(root, [_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                                   {"numpy": "2.4.6"}, set())
    assert refus == []
    assert len(publie) == 1


def test_un_import_du_carnet_absent_de_la_distribution_refuse_le_carnet(tmp_path):
    """Le bundle publie des fichiers et n'installe rien : un import que la
    distribution ne fournit pas n'est pas satisfait.

    Le critere, lui, accepte une roue pure presente dans son cache -- le
    deploiement est plus strict, et c'est lui qui publie.
    """
    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb", _nb(["import nashpy"]))
    publie, refus = bjs.suffisance(root, [_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                                   {}, set())
    assert publie == []
    assert len(refus) == 1
    assert any("nashpy" in motif and "absent de la distribution" in motif
               for motif in refus[0][1])


def test_un_carnet_qui_installe_lui_meme_la_roue_est_publie(tmp_path):
    """Le carnet peut installer une roue pure a l'execution : cette trace
    la rend disponible, donc l'import est satisfait."""
    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb",
           _nb(["await micropip.install(\"nashpy\")", "import nashpy"]))
    publie, refus = bjs.suffisance(root, [_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                                   {}, set())
    assert refus == []
    assert len(publie) == 1


def test_un_module_hors_serie_refuse_le_carnet(tmp_path):
    """Le bundle ne livre que la serie du carnet : un module d'une autre
    serie ne sera pas dans le site, l'import echouerait en navigation."""
    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    (root / "AutresSeries").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb", _nb(["import module_partout"]))
    (root / "AutresSeries" / "module_partout.py").write_text(
        "VALEUR = 1\n", encoding="utf-8")
    publie, refus = bjs.suffisance(root, [_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                                   {}, set())
    assert publie == []
    assert len(refus) == 1
    assert any("hors serie" in motif for motif in refus[0][1])


def test_le_deploiement_dit_la_meme_chose_que_le_critere(tmp_path):
    """Le deploiement n'a pas sa propre regle : il **importe** celle du critere.

    Le meme carnet passe par le critere (organe de 2.1) et par le deploiement
    (2.2) : meme verdict, memes motifs, dans le meme ordre. C'est ce qui rend
    impossible un ecart entre ce que le critere accepte et ce que le
    deploiement publie -- les deux sharing la meme fonction.
    """
    from pyodide_eligibility import analyse_notebook

    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb", _nb(["import nashpy"]))
    cache = {"nashpy": {"pure_wheel": True, "version": "1.0"}}

    verdict = analyse_notebook(root, "MyIA.AI.Notebooks/SerieA/a.ipynb",
                               {}, cache, set(), False)
    assert "suffisance" in verdict.motifs
    assert verdict.eligible is False

    publie, refus = bjs.suffisance(root, [verdict], {}, set(), cache)
    assert publie == []
    assert len(refus) == 1
    assert refus[0][0] == "MyIA.AI.Notebooks/SerieA/a.ipynb"
    assert refus[0][1] == [p["detail"] for p in verdict.to_dict()["problemes"]]


def test_un_import_inconnu_ne_stage_aucun_module(tmp_path):
    """Un import qui n'est pas un module de la serie n'embarque rien.

    C'est le critere d'eligibilite qui refuse un tel carnet (import absent) ;
    le deploiement, lui, n'a rien a poser.
    """
    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb", _nb(["import paquet_absent_xyz"]))
    publie, refus = bjs.suffisance(root, [_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                                   {}, set())
    poses = bjs.stage(root, publie, tmp_path / "site")
    assert poses["modules"] == {}


def test_deux_modules_locaux_homonymes_dans_le_lot_font_echouer(tmp_path):
    """Deux series qui fournissent le meme nom de module : on ne publie pas
    l'un des deux sous le nom de l'autre."""
    root = tmp_path / "depot"
    (root / "MyIA.AI.Notebooks" / "SerieA").mkdir(parents=True)
    (root / "MyIA.AI.Notebooks" / "SerieB").mkdir(parents=True)
    _write(root, "MyIA.AI.Notebooks/SerieA/a.ipynb", _nb(["import mon_organe"]))
    _write(root, "MyIA.AI.Notebooks/SerieB/b.ipynb", _nb(["import mon_organe"]))
    (root / "MyIA.AI.Notebooks" / "SerieA" / "mon_organe.py").write_text(
        "VALEUR = 1\n", encoding="utf-8")
    (root / "MyIA.AI.Notebooks" / "SerieB" / "mon_organe.py").write_text(
        "VALEUR = 2\n", encoding="utf-8")
    publie, _refus = bjs.suffisance(
        root, [_verdict("MyIA.AI.Notebooks/SerieA/a.ipynb", "SerieA"),
               _verdict("MyIA.AI.Notebooks/SerieB/b.ipynb", "SerieB")], {}, set())
    with pytest.raises(ValueError):
        bjs.stage(root, publie, tmp_path / "site")


def test_un_module_local_absent_du_site_construit_est_signale(tmp_path):
    """Le module embarque doit se retrouver dans le site construit."""
    output = tmp_path / "_output"
    (output / "files").mkdir(parents=True)
    (output / "files" / "a.ipynb").write_text("{}", encoding="utf-8")
    anomalies = bjs.verifier_contenu(output, ["a.ipynb"], {"mon_organe.py": "x.py"})
    assert len(anomalies) == 1
    assert "mon_organe.py" in anomalies[0]


def test_le_manifeste_nomme_les_modules_embarques(tmp_path):
    """Le manifeste dit quel module est livre avec quel carnet."""
    data = bjs.manifeste([_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                         "/CoursIA",
                         {"MyIA.AI.Notebooks/SerieA/a.ipynb": ["mon_organe.py"]})
    assert data["carnets"][0]["modules_locaux"] == ["mon_organe.py"]


# --- 5. les URLs publiques --------------------------------------------------

def test_un_prefixe_de_site_converti_par_msys_est_refuse():
    """Sous Git Bash, `--base-url /CoursIA` devient un chemin Windows.

    Un manifeste publie avec un tel prefixe porterait des URL de la forme
    `C:/Program Files/Git/CoursIA/...` : des liens morts que le garde
    rapporterait comme casses, pour une cause etrangere au lot. La
    construction refuse ce prefixe.
    """
    with pytest.raises(ValueError):
        bjs.verifier_base_url("C:/Program Files/Git/CoursIA")
    with pytest.raises(ValueError):
        bjs.verifier_base_url("CoursIA")


def test_un_prefixe_de_site_valide_est_normalise():
    """Un prefixe d'origine-racine est accepte, sans barre oblique finale."""
    assert bjs.verifier_base_url("/CoursIA") == "/CoursIA"
    assert bjs.verifier_base_url("/CoursIA/") == "/CoursIA"
    assert bjs.verifier_base_url("") == ""


def test_les_urls_publiques_portent_le_prefixe_du_site():
    """Les deux URLs sont relatives au prefixe du site publie."""
    urls = bjs.urls("/CoursIA", "a.ipynb")
    assert urls["lab"] == "/CoursIA/jupyterlite/lab/index.html?path=a.ipynb"
    assert urls["files"] == "/CoursIA/jupyterlite/files/a.ipynb"


def test_les_urls_sans_prefixe_ne_portent_pas_de_slash_final():
    """Un prefixe vide donne une URL qui commence par le sous-dossier."""
    urls = bjs.urls("", "a.ipynb")
    assert urls["lab"] == "/jupyterlite/lab/index.html?path=a.ipynb"
    assert bjs.urls("/CoursIA/", "a.ipynb")["files"] == "/CoursIA/jupyterlite/files/a.ipynb"


def test_le_manifeste_porte_le_chemin_d_origine_et_les_urls():
    """Le manifeste fait la correspondance nom de fichier -> carnet du depot."""
    data = bjs.manifeste([_verdict(path="MyIA.AI.Notebooks/SerieA/a.ipynb")],
                          "/CoursIA")
    assert data["taille"] == 1
    carnet = data["carnets"][0]
    assert carnet["chemin"] == "MyIA.AI.Notebooks/SerieA/a.ipynb"
    assert carnet["fichier"] == "a.ipynb"
    assert carnet["serie"] == "SerieA"
    assert carnet["files"].endswith("/CoursIA/jupyterlite/files/a.ipynb")
    assert "path=a.ipynb" in carnet["lab"]
    assert data["source"] == "critere-pyodide-2.1"


def test_le_manifeste_est_ecrit_en_utf8_sans_bom(tmp_path):
    """Le manifeste est lu par le garde post-deploiement : pas de BOM."""
    chemin = bjs.ecrire_manifeste({"carnets": []}, tmp_path / "manifest.json")
    octets = chemin.read_bytes()
    assert not octets.startswith(b"\xef\xbb\xbf")
    assert json.loads(octets.decode("utf-8")) == {"carnets": []}
