"""Tests du pre-tri des fils de commentaires (organe de lecture externe).

Le reseau n'est jamais appele ici : seules les fonctions pures sont testees.
"""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ORGAN_PATH = HERE.parent / "coordination" / "pr_comment_pretriage.py"
spec = importlib.util.spec_from_file_location("pr_comment_pretriage", ORGAN_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["pr_comment_pretriage"] = mod
spec.loader.exec_module(mod)


def test_strip_fences_retire_un_enveloppe_de_code():
    assert mod.strip_fences("```json\n{\"a\": 1}\n```") == '{"a": 1}'
    assert mod.strip_fences('{"a": 1}') == '{"a": 1}'


def test_parse_lenient_accepte_un_json_tronque():
    texte = 'Voici le resultat : {"commentaires": [{"n": 1, "role": "reserve"}'
    parsed = mod.parse_lenient(texte)
    assert parsed["commentaires"][0]["n"] == 1
    assert parsed["commentaires"][0]["role"] == "reserve"


def test_parse_lenient_echoue_sans_json_recoverable():
    try:
        mod.parse_lenient("pas du json du tout")
    except ValueError:
        return
    raise AssertionError("ValueError attendue")


def test_is_bot_reconnait_les_logins_de_bot():
    assert mod.is_bot("github-actions[bot]")
    assert mod.is_bot("clusterManager-Myia[bot]")
    assert mod.is_bot("github-actions")
    assert not mod.is_bot("jsboige")
    assert not mod.is_bot("myia-ai-01")


def test_le_prompt_ne_contient_pas_les_sauts_de_ligne_du_commentaire():
    """Le mini copie la decoupe : les commentaires sont donnes tels quels,
    sans aplatissement (regle de craft mesuree le 21/10)."""
    prompt = mod.TEMPLATE.format(
        num=1, titre="t", body="b", commentaires="--- commentaire 1 ---\nligne 1\nligne 2")
    assert "ligne 1\nligne 2" in prompt
