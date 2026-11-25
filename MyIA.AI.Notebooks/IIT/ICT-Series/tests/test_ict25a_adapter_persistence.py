"""#5105 -- l adaptateur QLoRA de la campagne ICT-25a doit etre persistable.

Mesure du 24/11 : le runner `ict25a_scaleup_grpo.py` entrainait en QLoRA
(`peft_config=lora`) mais ne persistait **jamais** l adaptateur
(`save_strategy="no"`, aucun `save_pretrained`). Aucun adaptateur de la
campagne 2B du 20/11 n existe sur le disque : le bloc `trained` de la lecture
SAE (`extract_sae_traces.py --variant trained`) n a donc rien a recharger, et
la moitie « panel persona » de la Gate 21 n a pas d instrument. Le verdict
`RECOVERABLE-MACHINE` de `docs/ict/ict25a-2b-resultats-2b.md` attribuait la
cause a un environnement bf16 non monte : la cause mesuree est plus profonde.

Ce test verifie deux choses :

* le **comportement** du module de persistance (`ict25a_adapter.py`, stdlib
  pur) -- empreinte, chemin publie, ecriture ;
* l'**existence** du chemin dans le runner, lue sur son AST : le runner
  importe torch au niveau module (script GPU), l importer ici ferait
  planter la collecte sur le runner CI ubuntu sans torch (convention serie,
  cf `test_sae_traces_layout.py`).
"""

import ast
import hashlib
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS))

LAUNCHER = SCRIPTS / "ict25a_scaleup_grpo.py"


def _arbre() -> ast.Module:
    return ast.parse(LAUNCHER.read_text(encoding="utf-8"))


def _fonction(nom: str) -> ast.FunctionDef:
    for noeud in ast.walk(_arbre()):
        if isinstance(noeud, ast.FunctionDef) and noeud.name == nom:
            return noeud
    raise AssertionError(f"fonction absente : {nom}")


def test_le_module_de_persistance_certifie_un_fichier(tmp_path):
    from ict25a_adapter import chemin_publie, sha256_fichier

    p = tmp_path / "adapter_model.safetensors"
    p.write_bytes(b"poids factices")
    attendu = hashlib.sha256(b"poids factices").hexdigest()
    assert sha256_fichier(p) == attendu
    # Un artefact commite ne porte jamais de chemin de machine : hors de la
    # base, seul le nom de fichier survit.
    assert chemin_publie(p, base=tmp_path) == "adapter_model.safetensors"
    assert chemin_publie(tmp_path / "sous" / "a.bin", base=tmp_path) == "sous/a.bin"


def test_sauver_adaptateur_ecrit_le_poids_et_le_certifie(tmp_path):
    from ict25a_adapter import sauver_adaptateur

    ecrits = {}

    class FauxModele:
        def save_pretrained(self, chemin, safe_serialization=True):
            ecrits["chemin"] = chemin
            ecrits["safe"] = safe_serialization
            (Path(chemin) / "adapter_model.safetensors").write_bytes(b"poids")

    dest = tmp_path / "N_s0"
    info = sauver_adaptateur(FauxModele(), dest, base=tmp_path)
    assert ecrits["safe"] is True
    assert info["fichier"] == "N_s0/adapter_model.safetensors"
    assert info["sha256"] == hashlib.sha256(b"poids").hexdigest()


def test_le_lanceur_expose_l_option_de_persistance():
    drapeaux = {a.args[0].value for a in ast.walk(_arbre())
                if isinstance(a, ast.Call) and isinstance(a.func, ast.Attribute)
                and a.func.attr == "add_argument" and a.args
                and isinstance(a.args[0], ast.Constant)}
    assert "--save-adapter" in drapeaux


def test_l_adaptateur_est_persiste_apres_l_entrainement():
    """L adaptateur doit etre ecrit APRES `trainer.train()`.

    Avant l entrainement, l adaptateur est vide : la sauvegarde porterait sur
    des poids qui n existent pas encore.
    """
    corps = _fonction("run_seed")
    lignes = {}
    for noeud in ast.walk(corps):
        if isinstance(noeud, ast.Call):
            if isinstance(noeud.func, ast.Attribute):
                nom = noeud.func.attr
                if nom == "train" and isinstance(noeud.func.value, ast.Name) \
                        and noeud.func.value.id == "trainer":
                    lignes["train"] = noeud.lineno
            elif isinstance(noeud.func, ast.Name) and noeud.func.id == "sauver_adaptateur":
                lignes["save"] = noeud.lineno
    assert "train" in lignes and "save" in lignes
    assert lignes["save"] > lignes["train"]


def test_le_module_de_persistance_appelle_save_pretrained():
    """L ecriture effective du poids passe par `save_pretrained`."""
    arbre = ast.parse((SCRIPTS / "ict25a_adapter.py").read_text(encoding="utf-8"))
    appels = {n.func.attr for n in ast.walk(arbre)
              if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)}
    assert "save_pretrained" in appels


def test_l_artefact_porte_la_certification_de_l_adaptateur():
    """Le dict de graine doit porter la cle `adapter`.

    Sans elle, l artefact ne dit pas quels poids ont produit la lecture :
    la lecture SAE ne serait pas reproductible ni auditable.
    """
    corps = _fonction("run_seed")
    cles = set()
    for noeud in ast.walk(corps):
        if isinstance(noeud, ast.Dict):
            for cle in noeud.keys:
                if isinstance(cle, ast.Constant) and isinstance(cle.value, str):
                    cles.add(cle.value)
    assert "adapter" in cles


@pytest.mark.parametrize("fichier", ["ict25a_scaleup_grpo.py", "ict25a_adapter.py"])
def test_le_fichier_existe(fichier):
    assert (SCRIPTS / fichier).is_file()
