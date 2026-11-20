"""Tests de la garde de fraicheur et des lectures de services (#27572).

Ces tests couvrent les quatre gestes demandes par la revue de #27572 :
la lecture de ``tool.coursia.pinned_env``, la resolution d'un port ecrit dans
une constante, la lecture du fichier de code qu'un carnet cite, et le mode
``--check`` de l'organe.
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import dependency_manifest as dm


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _notebook(kernel: str, language: str, source: str) -> str:
    return json.dumps(
        {
            "cells": [
                {
                    "cell_type": "code",
                    "execution_count": 1,
                    "outputs": [],
                    "source": source,
                }
            ],
            "metadata": {"kernelspec": {"name": kernel, "language": language}},
        }
    )


def _commit(repo: Path) -> None:
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
    subprocess.run(
        ["git", "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "init"],
        cwd=repo,
        check=True,
    )


@pytest.fixture()
def fake_repo(tmp_path: Path) -> Path:
    """Un depot git minimal : une serie, un carnet, la politique du depot."""
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "scripts/notebook_tools").mkdir(parents=True)
    _write(
        repo / dm.POLICY_RELPATH,
        (Path(dm.__file__).resolve().parent / "dependency_manifest_policy.json")
        .read_text(encoding="utf-8"),
    )
    _write(repo / "MyIA.AI.Notebooks/Search/requirements.txt", "numpy>=1.24\n")
    _write(
        repo / "MyIA.AI.Notebooks/Search/A-01.ipynb",
        _notebook("python3", "python", "import numpy\n"),
    )
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    _commit(repo)
    return repo


def test_pinned_env_prime_sur_project(fake_repo: Path):
    """L'env de la serie prime sur le plancher d'installation du paquet.

    Le cas ICT : ``project.requires-python`` dit ``>=3.9`` (coeur installable
    partout), mais l'env que les carnets traversent est epingle ``<3.10`` par
    ``tool.coursia.pinned_env``. Lire le seul premier champ ferait passer la
    serie pour compatible avec un noyau 3.13.
    """
    _write(
        fake_repo / "MyIA.AI.Notebooks/IIT/ICT-Series/pyproject.toml",
        "[project]\n"
        'name = "ict"\n'
        'requires-python = ">=3.9"\n'
        "\n"
        "[tool.coursia.pinned_env]\n"
        'requires-python = ">=3.9,<3.10"\n',
    )
    _write(
        fake_repo / "MyIA.AI.Notebooks/IIT/ICT-Series/A-04.ipynb",
        _notebook("python3", "python", "print('ict')\n"),
    )
    _commit(fake_repo)
    manifest = dm.build_manifest(fake_repo)
    groups = {group["group"]: group for group in manifest["groups"]}
    ict = groups["MyIA.AI.Notebooks/IIT/ICT-Series"]
    assert ict["requires_python"] == ">=3.9,<3.10"
    assert "pinned_env" in ict["requires_python_source"]
    fields = {row["field"] for row in ict["requires_python_constraints"]}
    assert "tool.coursia.pinned_env.requires-python" in fields
    assert any(
        "conflit de versions d'interpreteur" in motif["text"] for motif in ict["motifs"]
    )


def test_port_lu_dans_une_constante_du_carnet(fake_repo: Path):
    """Le port d'un service peut etre une constante du carnet.

    Le carnet ecrit ``FD_API_PORT = 8200`` puis ``f"http://localhost:{FD_API_PORT}"`` :
    l'URL ne porte aucun port en dur, mais le service est la.
    """
    _write(
        fake_repo / "MyIA.AI.Notebooks/Search/A-02.ipynb",
        _notebook(
            "python3",
            "python",
            "FD_API_PORT = 8200\n"
            "import urllib.request\n"
            "resp = urllib.request.urlopen(f'http://localhost:{FD_API_PORT}/health')\n",
        ),
    )
    _commit(fake_repo)
    manifest = dm.build_manifest(fake_repo)
    groups = {group["group"]: group for group in manifest["groups"]}
    search = groups["MyIA.AI.Notebooks/Search"]
    assert "planners-fast-downward" in search["needs"]["network_services"]
    assert "localhost:8200" in search["needs"]["local_endpoints"]


def test_service_lu_dans_le_fichier_que_le_carnet_cite(fake_repo: Path):
    """Le carnet cite son moteur : le service que le moteur appelle est un besoin.

    Cas Planners : le carnet C# cite ``FastDownwardBackend.cs``, et c'est ce
    fichier qui porte l'URL du service Docker.
    """
    _write(
        fake_repo / "MyIA.AI.Notebooks/SymbolicAI/Planners/FastDownwardBackend.cs",
        "public const string ServiceUrl = \"http://localhost:8200\";\n",
    )
    _write(
        fake_repo / "MyIA.AI.Notebooks/SymbolicAI/Planners/A-03.ipynb",
        _notebook(
            ".net-csharp",
            "csharp",
            "// voir FastDownwardBackend.cs pour le pont HTTP\n",
        ),
    )
    _commit(fake_repo)
    manifest = dm.build_manifest(fake_repo)
    groups = {group["group"]: group for group in manifest["groups"]}
    planners = groups["MyIA.AI.Notebooks/SymbolicAI/Planners"]
    assert "planners-fast-downward" in planners["needs"]["network_services"]
    assert any(
        "FastDownwardBackend.cs" in name
        for name in planners["needs"]["companion_files"]
    )


def test_appel_de_service_sans_url_lisible_est_compte(fake_repo: Path):
    """Un appel de service dont l'URL n'est pas sur la ligne est compte a part.

    L'appel existe ; le service qu'il vise ne peut pas etre nomme. L'organe
    le dit plutot que de pretendre que la serie est autonome.
    """
    _write(
        fake_repo / "MyIA.AI.Notebooks/Search/A-04.ipynb",
        _notebook(
            "python3",
            "python",
            "import requests\n"
            "def charger(url):\n"
            "    return requests.post(url, timeout=30)\n",
        ),
    )
    _commit(fake_repo)
    manifest = dm.build_manifest(fake_repo)
    groups = {group["group"]: group for group in manifest["groups"]}
    search = groups["MyIA.AI.Notebooks/Search"]
    assert search["needs"]["service_call_count"] >= 1
    assert search["needs"]["dynamic_service_calls"] >= 1
    assert any(
        motif["policy"] == "dynamic_service_calls" for motif in search["motifs"]
    )


def test_check_signale_un_manifeste_perime(fake_repo: Path, tmp_path: Path):
    """``--check`` repond frais sur des sorties fraiches, perime apres un ajout."""
    out = tmp_path / "out"
    assert dm.main(["--repo-root", str(fake_repo), "--out-dir", str(out), "--write"]) == 0
    etat, ecarts = dm.check_freshness(fake_repo, out)
    assert etat == "frais", ecarts

    _write(
        fake_repo / "MyIA.AI.Notebooks/Search/A-05.ipynb",
        _notebook("python3", "python", "import numpy\n"),
    )
    _commit(fake_repo)
    etat, ecarts = dm.check_freshness(fake_repo, out)
    assert etat == "perime"
    assert ecarts


def test_check_ignore_le_sha_et_le_compte_de_fichiers(fake_repo: Path, tmp_path: Path):
    """Le SHA de generation et le compte de fichiers suivis ne sont pas des ecarts.

    Les deux decrivent l'etat du depot, pas le contenu du manifeste : les
    ignorer evite un garde rouge sur chaque commit sans raison de fond.
    """
    out = tmp_path / "out"
    assert dm.main(["--repo-root", str(fake_repo), "--out-dir", str(out), "--write"]) == 0
    charge = json.loads((out / "manifeste-dependances.json").read_text(encoding="utf-8"))
    charge["generated_from"] = "0" * 40
    charge["counts"]["tracked_files"] = 999999
    (out / "manifeste-dependances.json").write_text(
        json.dumps(charge, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    etat, ecarts = dm.check_freshness(fake_repo, out)
    assert etat == "frais", ecarts


def test_check_incident_quand_la_sortie_est_absente(fake_repo: Path, tmp_path: Path):
    """Une sortie absente est un **verdict inconnu**, pas un verdict de perimetre."""
    etat, ecarts = dm.check_freshness(fake_repo, tmp_path / "vide")
    assert etat == "incident"
    assert ecarts



def test_check_ignore_le_sha_de_generation_dans_le_markdown(
    fake_repo: Path, tmp_path: Path
):
    """Le Markdown porte le SHA de generation : il est neutralise lui aussi.

    Le JSON et le Markdown sont deux sorties du meme organe : si le SHA est
    ignore dans l'un et pas dans l'autre, la garde rougirait sur un commit
    qui n'a rien change de fond.
    """
    out = tmp_path / "out"
    assert dm.main(["--repo-root", str(fake_repo), "--out-dir", str(out), "--write"]) == 0
    chemin = out / "manifeste-dependances.md"
    sha = dm.build_manifest(fake_repo)["generated_from"]
    chemin.write_text(
        chemin.read_text(encoding="utf-8").replace(sha, "1" * 40), encoding="utf-8"
    )
    etat, ecarts = dm.check_freshness(fake_repo, out)
    assert etat == "frais", ecarts


def test_mode_check_rend_son_code_de_sortie(fake_repo: Path, tmp_path: Path):
    """Le contrat CLI : 0 frais, 1 perime, 2 incident.

    Un code de sortie documente est ce que le cablage de la voie rapide
    consomme : sans lui, un garde ne peut pas distinguer « perime » de
    « l'organe n'a pas pu conclure ».
    """
    out = tmp_path / "out"
    assert dm.main(["--repo-root", str(fake_repo), "--out-dir", str(out), "--write"]) == 0
    assert dm.main(["--repo-root", str(fake_repo), "--out-dir", str(out), "--check"]) == 0
    assert dm.main(["--repo-root", str(fake_repo), "--out-dir", str(out / "rien"), "--check"]) == 2
    _write(
        fake_repo / "MyIA.AI.Notebooks/Search/A-05.ipynb",
        _notebook("python3", "python", "import numpy\n"),
    )
    _commit(fake_repo)
    assert dm.main(["--repo-root", str(fake_repo), "--out-dir", str(out), "--check"]) == 1


# --- Hermes : trois mesures fausses, trois tests qui ferment la porte -------


def test_chemin_accentue_inventorie(fake_repo: Path):
    """Un chemin accentue reste un chemin (defaut 1 de la revue).

    ``git ls-files`` C-quote les chemins non-ASCII : le chemin ressort entre
    guillemets avec des echappements octaux, ne finit plus par ``.ipynb``,
    et disparait de l'inventaire. La mesure des carnets etait donc fausse
    sur les noms accentues.
    """
    _write(
        fake_repo / "MyIA.AI.Notebooks/Search/Créateur de mail personnalisé.ipynb",
        _notebook("python3", "python", "print('mail')\n"),
    )
    _write(
        fake_repo / "MyIA.AI.Notebooks/Données/requirements.txt",
        "pandas>=2.0\n",
    )
    _commit(fake_repo)
    manifest = dm.build_manifest(fake_repo)
    assert manifest["counts"]["notebooks"] == 2
    groups = {group["group"]: group for group in manifest["groups"]}
    assert groups["MyIA.AI.Notebooks/Search"]["notebook_count"] == 2
    assert "MyIA.AI.Notebooks/Données" in groups
    assert groups["MyIA.AI.Notebooks/Données"]["dependency_files"] == [
        "MyIA.AI.Notebooks/Données/requirements.txt"
    ]


def test_groupe_sans_carnet_n_est_pas_exclu(fake_repo: Path):
    """Un groupe sans carnet n'est pas un groupe « non-Python » (defaut 2).

    L'absence de carnet est une **absence de mesure** : elle ne peut pas
    exclure le groupe, sinon ses paquets reels disparaissent du manifeste
    consolide (cas `cross-series/matching-cv`, `SymbolicAI/Lean/agent_tests`).
    """
    _write(
        fake_repo / "MyIA.AI.Notebooks/cross-series/matching-cv/requirements.txt",
        "flask>=3.0\n",
    )
    _commit(fake_repo)
    manifest = dm.build_manifest(fake_repo)
    groups = {group["group"]: group for group in manifest["groups"]}
    matching = groups["MyIA.AI.Notebooks/cross-series/matching-cv"]
    assert matching["verdict"] == "inclus"
    assert matching["kernel_families_source"] == "non mesure"
    motif = next(
        motif
        for motif in matching["motifs"]
        if motif["policy"] == "kernel_family_unmeasured"
    )
    assert motif["origin"] == "declaration"
    consolidated = {record["package"] for record in manifest["consolidated_manifest"]}
    assert "flask" in consolidated


def test_famille_heritee_des_sous_repertoires(fake_repo: Path):
    """Un repertoire sans carnet direct lit sa famille dans ses enfants.

    Le groupe parent porte les dependances ; ses carnets vivent un niveau
    plus bas. La famille se lit donc dans les sous-repertoires : c'est une
    mesure, pas une supposition.
    """
    _write(
        fake_repo / "MyIA.AI.Notebooks/Series/requirements.txt",
        "numpy>=1.24\n",
    )
    _write(
        fake_repo / "MyIA.AI.Notebooks/Series/Sub/A-01.ipynb",
        _notebook("python3", "python", "import numpy\n"),
    )
    _commit(fake_repo)
    manifest = dm.build_manifest(fake_repo)
    groups = {group["group"]: group for group in manifest["groups"]}
    parent = groups["MyIA.AI.Notebooks/Series"]
    assert parent["verdict"] == "inclus"
    assert parent["kernel_families"] == ["Python"]
    assert parent["kernel_families_source"] == "herite"


def test_entete_du_manifeste_reconnu_par_le_garde_prose(fake_repo: Path):
    """Le Markdown genere se declare genere devant le garde `prose-counts`.

    Le garde est bloquant sur les compteurs ecrits a la main : un fichier
    genere qui ne se declare pas tel est traite comme de la prose et
    bloque la PR sans raison de fond. L'en-tete doit porter le motif que
    l'organe sait lire.
    """
    import importlib.util

    organe = Path(dm.__file__).resolve().parent / "check_prose_quantitative_claims.py"
    spec = importlib.util.spec_from_file_location("cpq", organe)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    manifest = dm.build_manifest(fake_repo)
    markdown = dm.render_markdown(manifest)
    assert module._declares_generated(markdown)


def test_repli_de_normalisation_divulgue(fake_repo: Path, monkeypatch):
    """Un repli de normalisation est compte, pas tait en silence.

    Sans l'organe natif des versions, le repli compare les chaines brutes
    et invente des conflits : il doit etre visible dans les compteurs.
    """
    monkeypatch.setattr(dm, "version_key", None)
    manifest = dm.build_manifest(fake_repo)
    assert manifest["counts"]["version_normalization_fallbacks"] > 0
    markdown = dm.render_markdown(manifest)
    assert "Repli de normalisation" in markdown

