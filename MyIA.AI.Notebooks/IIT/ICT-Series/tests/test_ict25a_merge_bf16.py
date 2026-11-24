"""Tests du rebasculement bf16 (fusion d'adaptateur) de la campagne ICT-25a.

Le module `scripts/ict25a_merge_bf16.py` confine `torch` / `transformers` /
`peft` a l'interieur de la fonction de fusion : il reste donc importable sur
le runner CI, qui n'a pas de torch. Les gardes pures (empreinte, publication
des chemins, certification, refus d'un modele quantifie) sont verifiees
comportementalement ; le contrat de la fusion (chargement bf16, fusion
reelle, ecriture du tokenizer) est verifie par lecture de l'AST, comme le
fait la suite voisine pour le lanceur d'entrainement.
"""
from __future__ import annotations

import ast
import hashlib
import json
import sys
from pathlib import Path

import pytest

SERIE = Path(__file__).resolve().parent.parent
SCRIPTS = SERIE / "scripts"
sys.path.insert(0, str(SERIE))
sys.path.insert(0, str(SCRIPTS))

import ict25a_merge_bf16 as m  # noqa: E402


# --------------------------------------------------------------------------
# Fonctions pures
# --------------------------------------------------------------------------

def test_sha256_fichier_conforme_a_un_hash_connu(tmp_path):
    f = tmp_path / "poids.bin"
    f.write_bytes(b"poids de test")
    attendu = hashlib.sha256(b"poids de test").hexdigest()
    assert m.sha256_fichier(f) == attendu


def test_chemin_publie_est_relatif_sous_la_base(tmp_path):
    base = tmp_path / "artefact"
    fichier = base / "sous" / "poids.safetensors"
    fichier.parent.mkdir(parents=True)
    fichier.write_bytes(b"x")
    assert m.chemin_publie(fichier, base) == "sous/poids.safetensors"


def test_chemin_publie_ne_porte_jamais_une_arborescence(tmp_path):
    fichier = tmp_path / "poids.safetensors"
    fichier.write_bytes(b"x")
    publie = m.chemin_publie(fichier, tmp_path / "ailleurs")
    assert publie == "poids.safetensors"
    assert "/" not in publie


def test_poids_uniques_dans_le_repertoire(tmp_path):
    (tmp_path / "model.safetensors").write_bytes(b"a")
    (tmp_path / "model-00001-of-00002.safetensors").write_bytes(b"b")
    trouves = m.poids_du_repertoire(tmp_path)
    assert {p.name for p in trouves} == {"model.safetensors",
                                         "model-00001-of-00002.safetensors"}


def test_poids_par_pieces_suivent_l_index(tmp_path):
    (tmp_path / "model-00001-of-00002.safetensors").write_bytes(b"a")
    (tmp_path / "model-00002-of-00002.safetensors").write_bytes(b"b")
    (tmp_path / "model.safetensors.index.json").write_text(
        json.dumps({"weight_map": {"a": "model-00001-of-00002.safetensors",
                                   "b": "model-00002-of-00002.safetensors"}}),
        encoding="utf-8")
    trouves = m.poids_du_repertoire(tmp_path)
    assert len(trouves) == 2


def test_poids_absents_refuses(tmp_path):
    (tmp_path / "config.json").write_text("{}", encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        m.poids_du_repertoire(tmp_path)


def test_piece_manquante_refusee(tmp_path):
    (tmp_path / "model.safetensors.index.json").write_text(
        json.dumps({"weight_map": {"a": "model-00001-of-00002.safetensors"}}),
        encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        m.poids_du_repertoire(tmp_path)


# --------------------------------------------------------------------------
# Certification
# --------------------------------------------------------------------------

def _modele(tmp_path, config: dict) -> Path:
    d = tmp_path / "fusionne"
    d.mkdir(parents=True, exist_ok=True)
    (d / "config.json").write_text(json.dumps(config), encoding="utf-8")
    (d / "model.safetensors").write_bytes(b"poids fusionnes")
    return d


def test_certificat_refuse_un_modele_quantifie(tmp_path):
    d = _modele(tmp_path, {"dtype": "bfloat16",
                           "quantization_config": {"quant_method": "nf4"}})
    with pytest.raises(ValueError):
        m.certificater(d, "Qwen/Qwen3.5-2B-Base", "adapter", tmp_path)


def test_certificat_refuse_sans_config(tmp_path):
    d = tmp_path / "vide"
    d.mkdir()
    with pytest.raises(FileNotFoundError):
        m.certificater(d, "base", "adapter", tmp_path)


def test_certificat_certifie_le_poids_et_publie_le_chemin(tmp_path):
    d = _modele(tmp_path, {"dtype": "bfloat16"})
    cert = m.certificater(d, "Qwen/Qwen3.5-2B-Base", "adaptateur/N_s0", tmp_path)
    assert cert["base"] == "Qwen/Qwen3.5-2B-Base"
    assert cert["quantized_readout"] is False
    assert cert["sha256_poids"]["model.safetensors"] == hashlib.sha256(
        b"poids fusionnes").hexdigest()
    assert cert["poids"]["model.safetensors"] == "fusionne/model.safetensors"
    assert len(cert["sha256_dossier"]) == 64


# --------------------------------------------------------------------------
# Contrat de la fusion (lecture de l'AST)
# --------------------------------------------------------------------------

_SOURCE = (SCRIPTS / "ict25a_merge_bf16.py").read_text(encoding="utf-8")
_ARBRE = ast.parse(_SOURCE)


def _fonction(nom: str) -> ast.FunctionDef:
    for noeud in ast.walk(_ARBRE):
        if isinstance(noeud, ast.FunctionDef) and noeud.name == nom:
            return noeud
    raise AssertionError(f"fonction absente : {nom}")


def _appels(fonction: ast.FunctionDef) -> list[str]:
    noms = []
    for noeud in ast.walk(fonction):
        if isinstance(noeud, ast.Call):
            f = noeud.func
            if isinstance(f, ast.Attribute):
                noms.append(f.attr)
            elif isinstance(f, ast.Name):
                noms.append(f.id)
    return noms


def test_le_module_n_importe_pas_torch_au_niveau_module():
    for noeud in _ARBRE.body:
        if isinstance(noeud, (ast.Import, ast.ImportFrom)):
            modulos = ([a.name for a in noeud.names] if isinstance(noeud, ast.Import)
                       else [noeud.module or ""])
            assert not any(m.split(".")[0] in {"torch", "transformers", "peft"}
                           for m in modulos), (
                "torch/transformers/peft doivent rester importes dans la "
                "fonction de fusion, sinon le module n'est plus importable "
                "sans torch (le runner CI n'en a pas).")


def test_la_fusion_charge_la_base_en_bf16():
    src = ast.get_source_segment(_SOURCE, _fonction("fusionner")) or ""
    assert "torch.bfloat16" in src
    assert "dtype=torch.bfloat16" in src.replace(" ", "")


def test_la_fusion_fusionne_reellement_l_adaptateur():
    assert "merge_and_unload" in _appels(_fonction("fusionner"))


def test_la_fusion_ecrit_les_poids_et_le_tokenizer():
    appels = _appels(_fonction("fusionner"))
    assert "save_pretrained" in appels
    assert "from_pretrained" in appels
    src = ast.get_source_segment(_SOURCE, _fonction("fusionner")) or ""
    assert "tokenizer.save_pretrained" in src


def test_la_certification_appelle_la_garde_bf16():
    src = ast.get_source_segment(_SOURCE, _fonction("certificater")) or ""
    assert "assert_bf16_readout" in src


def test_la_garde_bf16_est_importee_de_la_bibliotheque_de_la_serie():
    assert "from ict.sae_traces import assert_bf16_readout" in _SOURCE
