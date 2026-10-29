"""Contrat de resolution de la cle : le carnet et l'organe doivent choisir
le meme fournisseur.

Contexte
--------

`MyIA.AI.Notebooks/GenAI/Texte/02_PromptEngineering.ipynb` porte un **repli
autonome** de resolution de la cle, pour le cas ou le carnet est telecharge
seul dans Colab et que l'organe de la serie
(`GenAI/shared/helpers/genai_helpers.py`, fonction `resolve_openai_config`)
n'est pas sous la main. Le repli doit **honorer le meme contrat** que
l'organe : c'est ce que dit sa documentation, et c'est ce que la sonde ci-dessous
verifie.

L'ecart mesure par l'adjoint (2026-10-29) : le repli du carnet ordonnait les
sources **par emplacement** (env OPENAI, env OPENROUTER, Colab OPENAI, Colab
OPENROUTER) alors que l'organe les ordonne **par fournisseur** (env OPENAI,
Colab OPENAI, env OPENROUTER, Colab OPENROUTER). Avec une cle
`OPENROUTER_API_KEY` dans l'environnement ET un Secret Colab `OPENAI_API_KEY`,
le carnet retenait le fournisseur *openrouter* et l'organe le fournisseur
*openai* -- le meme carnet, deux fournisseurs, selon que l'organe soit
importable ou non.

Ce que fait cette sonde
-----------------------

Elle **n'ecrit pas le contrat dans le test** : elle extrait la fonction du
carnet tel qu'il est commite (extraction AST depuis la cellule), l'execute
dans un espace de noms ou les Secrets Colab sont simules, et compare le
resultat a l'attendu. Une modification de la cellule qui reordonne les sources
fait donc echouer ce test -- c'est le but.

Aucune valeur de cle reelle n'est employee : les valeurs sont des chaines
fictives, et rien n'est imprime.

La seconde moitie du fichier verifie la **parite** avec l'organe, quand
l'organe est importable (il est livre par #23269) : les deux doivent choisir
le meme fournisseur et la meme source pour les memes entrees.
"""

from __future__ import annotations

import ast
import importlib.util
import json
import sys
import types
from pathlib import Path

import pytest

# --- Localisation des artefacts ------------------------------------------------

FICHIER_TEST = Path(__file__).resolve()


def _racine_depot() -> Path:
    """Remonte jusqu'a la racine du depot (celle qui contient MyIA.AI.Notebooks)."""
    for candidat in FICHIER_TEST.parents:
        if (candidat / "MyIA.AI.Notebooks").is_dir():
            return candidat
    raise RuntimeError("racine de depot introuvable depuis %s" % FICHIER_TEST)


CARNET = (
    _racine_depot()
    / "MyIA.AI.Notebooks"
    / "GenAI"
    / "Texte"
    / "02_PromptEngineering.ipynb"
)

VARIABLES = (
    "OPENAI_API_KEY",
    "OPENROUTER_API_KEY",
    "OPENAI_BASE_URL",
    "OPENAI_MODEL",
    "OPENAI_REASONING_MODEL",
)


# --- Extraction de la fonction du carnet ---------------------------------------

def _source_de_la_cellule(nom_fonction: str) -> str:
    """Source de la cellule qui definit `nom_fonction`."""
    if not CARNET.is_file():
        pytest.skip("carnet absent : %s" % CARNET)
    carnet = json.loads(CARNET.read_text(encoding="utf-8"))
    for cellule in carnet["cells"]:
        if cellule.get("cell_type") != "code":
            continue
        source = "".join(cellule.get("source") or [])
        if ("def %s(" % nom_fonction) in source:
            return source
    pytest.skip("la cellule definissant %s est introuvable" % nom_fonction)


def _replis_du_carnet() -> dict:
    """Execute les replis du carnet et retourne leur espace de noms.

    L'extraction est AST : on ne recopie **rien** du code dans le test. Seuls
    les noeuds qui definissent le repli sont retenus (les deux fonctions et le
    texte d'aide), compiles et executes dans un espace de noms qui ne contient
    que `os` -- le module de la cellule fait le reste.
    """
    source = _source_de_la_cellule("_resoudre_config_autonome")
    arbre = ast.parse(source)
    retenus = []
    for noeud in arbre.body:
        if isinstance(noeud, ast.FunctionDef) and noeud.name in (
            "_lire_secret_colab",
            "_resoudre_config_autonome",
        ):
            retenus.append(noeud)
        elif isinstance(noeud, ast.Assign) and any(
            getattr(cible, "id", None) == "AIDE_CLE" for cible in noeud.targets
        ):
            retenus.append(noeud)
    noms = {getattr(n, "name", None) for n in retenus}
    assert "_resoudre_config_autonome" in noms, (
        "la fonction _resoudre_config_autonome n'a pas ete extraite de la cellule"
    )
    module = ast.Module(body=retenus, type_ignores=[])
    ast.fix_missing_locations(module)
    espace = {"os": __import__("os")}
    exec(compile(module, "<cellule-02_PromptEngineering>", "exec"), espace)
    return espace


# --- Faux Secrets Colab (aucune valeur reelle) --------------------------------

def _installer_secrets_colab(monkeypatch, secrets: dict) -> None:
    """Simule `google.colab.userdata` avec un dictionnaire de Secrets fictifs."""
    google = types.ModuleType("google")
    colab = types.ModuleType("google.colab")
    userdata = types.ModuleType("google.colab.userdata")

    def get(nom):
        if nom in secrets:
            return secrets[nom]
        raise RuntimeError("Secret not found: %s" % nom)

    userdata.get = get
    colab.userdata = userdata
    google.colab = colab
    monkeypatch.setitem(sys.modules, "google", google)
    monkeypatch.setitem(sys.modules, "google.colab", colab)
    monkeypatch.setitem(sys.modules, "google.colab.userdata", userdata)


def _vider_environ(monkeypatch) -> None:
    for nom in VARIABLES:
        monkeypatch.delenv(nom, raising=False)


# --- Les cas ------------------------------------------------------------------
# (variables d'environnement, Secrets Colab, source attendue, fournisseur attendu)

CAS = [
    pytest.param(
        {"OPENAI_API_KEY": "fictif-env-openai"},
        {},
        "env:OPENAI_API_KEY",
        "openai",
        id="env-openai-seul",
    ),
    pytest.param(
        {"OPENROUTER_API_KEY": "fictif-env-openrouter"},
        {},
        "env:OPENROUTER_API_KEY",
        "openrouter",
        id="env-openrouter-seul",
    ),
    pytest.param(
        {},
        {"OPENAI_API_KEY": "fictif-colab-openai"},
        "colab:OPENAI_API_KEY",
        "openai",
        id="colab-openai-seul",
    ),
    pytest.param(
        {},
        {"OPENROUTER_API_KEY": "fictif-colab-openrouter"},
        "colab:OPENROUTER_API_KEY",
        "openrouter",
        id="colab-openrouter-seul",
    ),
    pytest.param(
        # LE CAS CROISE : une cle OpenRouter dans l'environnement ET un Secret
        # Colab OpenAI. L'ordre par fournisseur tranche pour OpenAI ; l'ordre
        # par emplacement tranchait pour OpenRouter, et le carnet et l'organe
        # divergeaient.
        {"OPENROUTER_API_KEY": "fictif-env-openrouter"},
        {"OPENAI_API_KEY": "fictif-colab-openai"},
        "colab:OPENAI_API_KEY",
        "openai",
        id="croise-env-openrouter-et-colab-openai",
    ),
    pytest.param(
        {"OPENAI_API_KEY": "fictif-env-openai"},
        {"OPENROUTER_API_KEY": "fictif-colab-openrouter"},
        "env:OPENAI_API_KEY",
        "openai",
        id="croise-env-openai-et-colab-openrouter",
    ),
]


@pytest.mark.parametrize("env, secrets, source_attendue, fournisseur_attendu", CAS)
def test_le_repli_du_carnet_choisit_le_meme_fournisseur(
    monkeypatch, env, secrets, source_attendue, fournisseur_attendu
):
    """Le repli autonome du carnet suit l'ordre par fournisseur."""
    _vider_environ(monkeypatch)
    for nom, valeur in env.items():
        monkeypatch.setenv(nom, valeur)
    _installer_secrets_colab(monkeypatch, secrets)

    espace = _replis_du_carnet()
    config = espace["_resoudre_config_autonome"]()

    assert config["provider"] == fournisseur_attendu, config["key_source"]
    assert config["key_source"] == source_attendue, config["key_source"]


def test_absence_de_cle_donne_le_message_d_aide(monkeypatch):
    """Sans aucune cle, le repli leve l'aide -- il ne devine pas de fournisseur."""
    _vider_environ(monkeypatch)
    _installer_secrets_colab(monkeypatch, {})

    espace = _replis_du_carnet()
    with pytest.raises(ValueError) as exc:
        espace["_resoudre_config_autonome"]()
    assert "OPENAI_API_KEY" in str(exc.value)


def test_les_valeurs_de_cle_ne_sont_jamais_printed(monkeypatch, capsys):
    """La sonde n'imprime aucune valeur de cle : le repli ne les expose pas."""
    _vider_environ(monkeypatch)
    monkeypatch.setenv("OPENAI_API_KEY", "fictif-a-ne-pas-imprimer")
    _installer_secrets_colab(monkeypatch, {})

    espace = _replis_du_carnet()
    espace["_resoudre_config_autonome"]()
    capture = capsys.readouterr()
    assert "fictif-a-ne-pas-imprimer" not in capture.out
    assert "fictif-a-ne-pas-imprimer" not in capture.err


# --- Parite avec l'organe de la serie -----------------------------------------

def _organe():
    """L'organe de la serie, ou None quand il n'est pas compose sur ce checkout.

    Deux echecs distincts, et les confondre est le defaut que cette borne
    repare (#23288) : un module **absent** du checkout (la composition #23269
    n'a pas ete faite) est un skip honnete ; un module **present dont l'import
    leve** est un import casse, et il doit faire echouer le test au lieu de
    disparaitre derriere un skip.

    `find_spec` tranche l'absence **sans importer** -- c'est ce qui permet de
    separer les deux cas. `import_module` laisse donc remonter tout ce qui
    casse, au lieu de l'avaler.
    """
    if importlib.util.find_spec("genai_helpers") is None:
        return None
    return importlib.import_module("genai_helpers")


def test_absence_de_l_organe_rend_none(monkeypatch):
    """L'absence du module est le SEUL cas ou la sonde de parite se saute."""
    monkeypatch.setattr(importlib.util, "find_spec", lambda nom: None)
    assert _organe() is None


def test_un_import_casse_fait_echouer_au_lieu_de_skipper(monkeypatch, tmp_path):
    """CONTROLE NEGATIF : un module present dont l'import leve ne se cache pas.

    Sans ce controle, la borne de `_organe()` ne prouverait rien : un helper qui
    rend `None` sur toute exception produirait exactement le meme skip, et un
    import casse resterait invisible. Le faux module est place devant le vrai
    par `syspath_prepend`, et purge de `sys.modules` pour qu'il soit reellement
    importe.
    """
    (tmp_path / "genai_helpers.py").write_text(
        "raise ImportError('dependance absente : import casse simule')\n",
        encoding="utf-8",
    )
    monkeypatch.syspath_prepend(str(tmp_path))
    monkeypatch.delitem(sys.modules, "genai_helpers", raising=False)
    importlib.invalidate_caches()

    with pytest.raises(ImportError, match="import casse simule"):
        _organe()


@pytest.mark.parametrize("env, secrets, source_attendue, fournisseur_attendu", CAS)
def test_parite_avec_l_organe_de_la_serie(
    monkeypatch, env, secrets, source_attendue, fournisseur_attendu
):
    """Le repli du carnet et l'organe de la serie tranchent pareil."""
    organe = _organe()
    if organe is None:
        pytest.skip("genai_helpers absent du checkout : composition #23269 non faite")
    if not hasattr(organe, "resolve_openai_config"):
        pytest.skip("genai_helpers present mais sans resolve_openai_config : #23269 pas livre")

    _vider_environ(monkeypatch)
    for nom, valeur in env.items():
        monkeypatch.setenv(nom, valeur)

    def _secret_factice(nom):
        if nom in secrets:
            return secrets[nom]
        return None

    monkeypatch.setattr(organe, "read_colab_secret", _secret_factice)

    _installer_secrets_colab(monkeypatch, secrets)
    espace = _replis_du_carnet()
    config_carnet = espace["_resoudre_config_autonome"]()
    config_organe = organe.resolve_openai_config(required=True)

    assert config_carnet["provider"] == config_organe.provider, (
        "fournisseur different : carnet=%s organe=%s"
        % (config_carnet["provider"], config_organe.provider)
    )
    assert config_carnet["key_source"] == config_organe.key_source, (
        "source differente : carnet=%s organe=%s"
        % (config_carnet["key_source"], config_organe.key_source)
    )
