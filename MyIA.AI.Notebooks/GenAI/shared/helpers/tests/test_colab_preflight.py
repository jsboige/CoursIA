"""Prevol Colab : trois garanties verifiees par le test.

Le module `colab_preflight.py` observe un runtime et nomme un etat par
element. Ce test fixe les trois garanties que le module promet :

1. **aucune valeur de secret rendue** -- ni la cle, ni un fragment de cle,
   ni dans le texte, ni dans le JSON ;
2. **aucun appel de modele** -- le module n'importe ni SDK de modele ni ne
   lance de commande d'appel ;
3. **un etat nomme par element** -- chaque element porte exactement un etat
   parmi `OK` / `ACTION` / `INFO`, et un `ACTION` porte toujours un remede.

Les valeurs de cle employees sont **fictives** et n'apparaissent dans aucune
assertion de sortie ; elles servent uniquement a verifier qu'elles ne fuient
pas.

Aucune valeur reelle n'est lue : le test injecte un faux `genai_helpers`.
"""

from __future__ import annotations

import ast
import json
import subprocess
import sys
import types
from pathlib import Path

import pytest

FICHIER_MODULE = Path(__file__).resolve().parents[1] / "colab_preflight.py"

CLE_FICTIVE = "sk-fictif-ne-pas-filer-0123456789"


# --- Import du module --------------------------------------------------------

def _charger_module():
    """Charge `colab_preflight` depuis son chemin, hors dependances du depot."""
    import importlib.util

    spec = importlib.util.spec_from_file_location("colab_preflight_test", FICHIER_MODULE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def preflight():
    return _charger_module()


@pytest.fixture
def faux_organe(monkeypatch):
    """Installe un faux `genai_helpers` dans `sys.modules` et rend sa config."""
    module = types.ModuleType("genai_helpers")

    class Config:
        provider = "openai"
        key_source = "env:OPENAI_API_KEY"
        model = "gpt-5-mini"
        api_key = CLE_FICTIVE

    def resolve_openai_config(required=True, env=None):
        if required:
            return Config()
        return Config()

    module.resolve_openai_config = resolve_openai_config
    module.is_colab = lambda: False
    monkeypatch.setitem(sys.modules, "genai_helpers", module)
    return module


# --- Garantie 1 : aucune valeur de secret rendue ----------------------------

def test_la_valeur_de_cle_n_apparait_pas_dans_le_rendu(preflight, faux_organe, capsys):
    """La cle resolue ne doit apparaitre ni dans le texte ni dans le JSON."""
    rapport = preflight.preflight("all")
    texte = preflight.render(rapport)
    capture = capsys.readouterr()

    assert CLE_FICTIVE not in texte
    assert CLE_FICTIVE not in capture.out
    assert CLE_FICTIVE not in capture.err
    # pas meme un fragment significatif
    assert "sk-fictif" not in texte


def test_le_rendu_json_ne_contient_pas_de_cle(preflight, faux_organe):
    """La serialisation JSON ne doit pas non plus porter la valeur."""
    rapport = preflight.preflight("all")
    rendu = json.dumps(rapport, ensure_ascii=False)
    assert CLE_FICTIVE not in rendu
    assert "sk-fictif" not in rendu


def test_le_code_ne_mentionne_aucune_variable_de_cle_brute(preflight):
    """Le module ne doit lire `os.environ` d'une variable de cle qu'a travers
    l'organe partage : un `os.getenv('OPENAI_API_KEY')` local dupliquerait la
    configuration -- c'est ce que la regle d'organe-fixe interdit."""
    arbre = ast.parse(FICHIER_MODULE.read_text(encoding="utf-8"))
    lectures_directes = []
    for noeud in ast.walk(arbre):
        if not isinstance(noeud, ast.Call):
            continue
        fonction = noeud.func
        if not isinstance(fonction, ast.Attribute):
            continue
        if fonction.attr != "getenv":
            continue
        if noeud.args and isinstance(noeud.args[0], ast.Constant):
            if isinstance(noeud.args[0].value, str) and "API_KEY" in noeud.args[0].value:
                lectures_directes.append(noeud.args[0].value)
    assert lectures_directes == [], (
        "lecture directe d'une variable de cle : %s" % ", ".join(lectures_directes)
    )


def test_la_resolution_de_cle_est_deleguee_a_l_organe(preflight, faux_organe):
    """L'element de cle est construit depuis `resolve_openai_config`."""
    elements = preflight.check_semantic_kernel()
    element_cle = [e for e in elements if e["element"].endswith("/ cle")]
    assert len(element_cle) == 1
    element = element_cle[0]
    assert element["etat"] == preflight.OK
    assert "env:OPENAI_API_KEY" in element["detail"]
    assert "openai" in element["detail"]


def test_absence_d_organe_rend_un_action_nomme(preflight, monkeypatch):
    """Sans `genai_helpers`, l'element de cle est un `ACTION` avec remede."""
    monkeypatch.setitem(sys.modules, "genai_helpers", None)
    elements = preflight.check_semantic_kernel()
    element = [e for e in elements if e["element"].endswith("/ cle")][0]
    assert element["etat"] == preflight.ACTION
    assert element["remede"], "un ACTION doit toujours porter un remede"


def test_sans_semantic_kernel_l_etat_de_cle_est_tout_de_meme_rendu(
    preflight, faux_organe, monkeypatch
):
    """SDK absent : l'installation est un `ACTION`, et la cle est quand meme verifiee.

    Mesure fondatrice : le workflow `genai-helpers-tests.yml` tourne sur
    `ubuntu-latest` avec `numpy requests python-dotenv pillow librosa pytest`
    seulement -- pas `semantic-kernel`. Un retour premature apres le constat
    d'installation cachait l'element de cle, et les deux tests de cle
    echouaient la-bas alors qu'ils passent sur un poste ou le SDK est installe.
    """
    monkeypatch.setitem(sys.modules, "semantic_kernel", None)
    elements = preflight.check_semantic_kernel()
    installation = [e for e in elements if e["element"] == "sk / installation"][0]
    assert installation["etat"] == preflight.ACTION
    element_cle = [e for e in elements if e["element"].endswith("/ cle")]
    assert len(element_cle) == 1
    assert element_cle[0]["etat"] == preflight.OK


# --- Garantie 2 : aucun appel de modele --------------------------------------

def test_le_module_n_importe_aucun_sdk_de_modele(preflight):
    """Ni `openai`, ni `anthropic`, ni `semantic_kernel` au niveau module.

    Seuls les imports de **niveau module** sont vérifiés : les imports de
    fonction (le SDK `semantic_kernel` est justement probed par le controle
    de cablage) sont hors du contrat -- ce qui compte est qu'aucun SDK ne
    soit charge au moment ou le module est importe.
    """
    arbre = ast.parse(FICHIER_MODULE.read_text(encoding="utf-8"))
    interdits = {"openai", "anthropic", "semantic_kernel", "google.generativeai"}
    importes = set()
    for noeud in arbre.body:
        if isinstance(noeud, ast.Import):
            for alias in noeud.names:
                importes.add(alias.name.split(".")[0])
        elif isinstance(noeud, ast.ImportFrom) and noeud.module:
            importes.add(noeud.module.split(".")[0])
    assert not (importes & interdits), (
        "import de SDK de modele au niveau module : %s" % ", ".join(sorted(importes & interdits))
    )


def test_la_cli_ne_declenche_aucun_appel_de_modele(preflight, faux_organe, monkeypatch):
    """La commande `claude` n'est lancee qu'en mode `--version`.

    Un appel de modele (`claude -p`) serait facture : le module ne doit le
    faire que si l'appelant le demande explicitement, et il ne le fait pas.
    """
    appels = []

    def faux_run(cmd, *args, **kwargs):
        appels.append(cmd)
        class Resultat:
            returncode = 0
            stdout = "2.1.332 (fictif)"
            stderr = ""
        return Resultat()

    monkeypatch.setattr(preflight.subprocess, "run", faux_run)
    preflight.check_claude_cli()
    for cmd in appels:
        assert "--version" in cmd, "commande non-version lancee : %s" % cmd


# --- Garantie 3 : un etat nomme par element ----------------------------------

def test_chaque_element_porte_un_etat_de_la_liste(preflight, faux_organe):
    """Chaque element porte exactement un etat parmi les trois."""
    rapport = preflight.preflight("all")
    for element in rapport["elements"]:
        assert element["etat"] in (preflight.OK, preflight.ACTION, preflight.INFO), element
        assert element["detail"], "element sans detail : %s" % element


def test_tout_action_porte_un_remede(preflight, faux_organe):
    """Un `ACTION` sans remede serait un constat sans porte de sortie."""
    rapport = preflight.preflight("all")
    for element in rapport["elements"]:
        if element["etat"] == preflight.ACTION:
            assert element["remede"], "ACTION sans remede : %s" % element["element"]


def test_le_rendu_annonce_le_compte_par_etat(preflight, faux_organe):
    """Le rendu se termine par un decompte qui somme le nombre d'elements."""
    rapport = preflight.preflight("all")
    texte = preflight.render(rapport)
    total = len(rapport["elements"])
    compte = {preflight.OK: 0, preflight.ACTION: 0, preflight.INFO: 0}
    for element in rapport["elements"]:
        compte[element["etat"]] += 1
    assert "%d OK, %d ACTION, %d INFO" % (
        compte[preflight.OK], compte[preflight.ACTION], compte[preflight.INFO]
    ) in texte
    assert total == sum(compte.values())


# --- Comportement des parcours ----------------------------------------------

def test_un_parcours_inconnu_leve_une_erreur(preflight):
    """Un parcours mal orthographie est refuse, pas ignore."""
    with pytest.raises(ValueError):
        preflight.preflight("sk-plus")


def test_le_parcours_all_couvre_les_trois(preflight, faux_organe):
    """`all` couvre les trois parcours de #23276."""
    rapport = preflight.preflight("all")
    noms = " ".join(e["element"] for e in rapport["elements"])
    assert "claude-cli" in noms
    assert "sk /" in noms
    assert "ft /" in noms


def test_un_parcours_unique_ne_rend_que_ses_elements(preflight, faux_organe):
    """`sk` ne parle que du parcours Semantic Kernel."""
    rapport = preflight.preflight("sk")
    noms = " ".join(e["element"] for e in rapport["elements"])
    assert "ft /" not in noms
    assert "claude-cli /" not in noms
    assert "sk /" in noms


# --- Detection du cas "installe mais hors du PATH" ----------------------------

def test_le_binaire_hors_path_est_nomme_avec_son_remede(preflight, monkeypatch, tmp_path):
    """Le cas mesure sous Colab : installe, mais hors du PATH du kernel.

    Le module doit nommer le cas **et** donner le remede exact (rejouer le
    PATH dans `os.environ`), pas se contenter de dire "absent".
    """
    monkeypatch.setattr(preflight.shutil, "which", lambda nom: None)
    monkeypatch.setattr(preflight, "COLAB_NPM_BIN_DIR", str(tmp_path))
    monkeypatch.setattr(
        preflight.Path, "exists", lambda self: True, raising=False
    )

    elements = preflight.check_claude_cli()
    binaire = [e for e in elements if e["element"] == "claude-cli / binaire"][0]
    assert binaire["etat"] == preflight.ACTION
    assert "hors du PATH" in binaire["detail"]
    assert "os.environ['PATH']" in binaire["remede"]


def test_un_binaire_absent_donne_la_commande_d_installation(preflight, monkeypatch, tmp_path):
    """Absent des deux cotes, le remede est la commande npm mesuree."""
    monkeypatch.setattr(preflight.shutil, "which", lambda nom: None)
    monkeypatch.setattr(preflight, "COLAB_NPM_BIN_DIR", str(tmp_path))
    monkeypatch.setattr(preflight.Path, "exists", lambda self: False, raising=False)

    elements = preflight.check_claude_cli()
    binaire = [e for e in elements if e["element"] == "claude-cli / binaire"][0]
    assert binaire["etat"] == preflight.ACTION
    assert "npm install -g @anthropic-ai/claude-code" in binaire["remede"]


# --- Execution en ligne de commande -------------------------------------------

def test_la_cli_rend_un_json_exploitable(preflight, faux_organe):
    """`python colab_preflight.py sk --json` rend un JSON parseable."""
    resultat = subprocess.run(
        [sys.executable, str(FICHIER_MODULE), "sk", "--json"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )
    assert resultat.returncode == 0, resultat.stderr
    rapport = json.loads(resultat.stdout)
    assert rapport["parcours"] == "sk"
    assert rapport["elements"]
    assert CLE_FICTIVE not in resultat.stdout


def test_la_cli_refuse_un_parcours_inconnu(preflight):
    """argparse refuse une valeur hors liste, avec un code de sortie non nul."""
    resultat = subprocess.run(
        [sys.executable, str(FICHIER_MODULE), "inexistant"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )
    assert resultat.returncode != 0
