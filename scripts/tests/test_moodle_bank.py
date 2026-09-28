#!/usr/bin/env python3
"""Banque de QCM : la passe de test exigee par #18223.

Ce que ce fichier garde
-----------------------
La banque `MyIA.AI.Notebooks/cross-series/qcm/` est un artefact commis, produit par
`scripts/notebook_tools/moodle_bank.py convert` depuis les exports XML Moodle
du Drive. Deux familles de derives sont possibles apres coup, et chacune a son
test :

- **une main edite la banque a la main** (question retiree, option cassee,
  bonne reponse effacee) : le format se casse sans que rien ne rougisse, car
  rien ne re-execute le convertisseur -- la source vit hors depot ;
- **le convertisseur derive** (regle de classification modifiee, cle de
  dedoublonnage affaiblie) : les comptes par theme bougent alors que la table
  de decision du mainteneur (28/09, issue #18223) est figee : 147 publiees,
  64 exclues C#, 29 differrees Big Data.

Le test verifie donc les invariants de FORMAT via l'organe `check` du
convertisseur lui-meme (une seule definition de la validite, pas deux), et les
COMPTES figes par la decision du mainteneur. Une re-conversion legitimate
(nouvelles questions publiees) fait bouger les comptes : le test se met a jour
dans la meme PR, avec l'explication du delta.

Le scanner se valide par ses faux negatifs
------------------------------------------
Les compteurs ne testent pas seulement le total : un theme qui perd une
question au profit d'un autre (classification deplacee) laisse le total a 147
et le test aveugle. Les comptes par theme sont donc assertes individuellement,
d'apres la table de l'issue (15/36/19/24/21 + 32).
"""

import os
import re
import sys

import pytest
import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BANK = os.path.join(ROOT, "MyIA.AI.Notebooks", "cross-series", "qcm")
sys.path.insert(0, os.path.join(ROOT, "scripts", "notebook_tools"))

from moodle_bank import THEME_ID_PREFIX, check  # noqa: E402

# Table de decision du mainteneur (28/09) -- issue #18223. Le total publie
# (147) est la somme de ces comptes : un delta ici est un evenement a expliquer,
# pas un bruit.
EXPECTED_PER_THEME = {
    "dl-evaluation-seance": 32,
    "ia-1-introduction-agents": 15,
    "ia-2-resolution-problemes": 36,
    "ia-3-logique-bases-connaissances": 19,
    "ia-4-systemes-probabilistes": 24,
    "ia-5-apprentissage": 21,
}
EXPECTED_TOTAL = sum(EXPECTED_PER_THEME.values())  # 147


def load_bank() -> dict[str, list[dict]]:
    bank = {}
    for fname in sorted(os.listdir(BANK)):
        if fname.endswith(".yaml"):
            with open(os.path.join(BANK, fname), encoding="utf-8") as fh:
                bank[fname[:-5]] = yaml.safe_load(fh) or []
    return bank


def test_bank_exists_with_expected_themes():
    bank = load_bank()
    assert set(bank) == set(EXPECTED_PER_THEME), (
        f"themes de la banque = {sorted(bank)} != decision mainteneur {sorted(EXPECTED_PER_THEME)}")


def test_counts_match_maintainer_decision_table():
    bank = load_bank()
    for theme, expected in EXPECTED_PER_THEME.items():
        assert len(bank[theme]) == expected, (
            f"{theme}: {len(bank[theme])} questions != {expected} (table #18223)")
    total = sum(len(qs) for qs in bank.values())
    assert total == EXPECTED_TOTAL


def test_check_organ_passes_on_committed_bank(capsys):
    """L'organe check du convertisseur doit valider la banque commise.

    Invariants portes par check() : identifiant unique, enonce non vide, source
    presente, >=2 options dont >=1 correcte, exactement 1 correcte si
    choix_unique, appariements complets, images referencees presentes.
    """
    rc = check(BANK)
    out = capsys.readouterr().out
    assert rc == 0, f"check() a rendu {rc} :\n{out}"


def test_check_flags_source_duplicate_options_as_attention(capsys):
    """Les options dupliquees a cles contradictoires (defaut de SOURCE Moodle,
    cf RELECTURE-2026-09.md) sont signalees en ATTENTION sans faire echouer
    l'organe : la banque reste fidele a la source.
    """
    rc = check(BANK)
    out = capsys.readouterr().out
    assert rc == 0, f"check() a rendu {rc} :\n{out}"
    for qid in ("ia2-008", "ia5-002"):
        assert qid in out, f"{qid} attendu en ATTENTION :\n{out}"
    assert "cles contradictoires" in out


def test_ids_stable_pattern_and_unique():
    bank = load_bank()
    ids = [q["id"] for qs in bank.values() for q in qs]
    assert len(ids) == len(set(ids)), "identifiants dupliques"
    prefix_by_theme = THEME_ID_PREFIX
    for theme, qs in bank.items():
        for i, q in enumerate(qs, start=1):
            expected = f"{prefix_by_theme[theme]}-{i:03d}"
            assert q["id"] == expected, (
                f"{theme}: id {q['id']} != sequence stable attendue {expected}")


def test_no_published_csharp_or_bigdata():
    """Les lots exclus (C#) et differs (Big Data) ne doivent jamais fuiter
    dans la banque : ni par theme, ni par contenu de categorie dans la source."""
    bank = load_bank()
    for theme, qs in bank.items():
        assert "csharp" not in theme and "big-data" not in theme
        for q in qs:
            assert not re.search(r"C#|Big Data", q.get("enonce", "") or ""), (
                f"{q['id']}: enonce C#/Big Data dans un theme publie ({theme})")


def test_types_reconcile_with_inventory():
    """14 vrai/faux (tous evaluation de seance) et 1 appariement distinct --
    les << 3 appariements >> de l'inventaire initial etaient 3 occurrences
    verbatim de la meme question dans l'export JSBoige (mesure, issue #18223)."""
    bank = load_bank()
    all_q = [q for qs in bank.values() for q in qs]
    tf = [q for q in all_q if q["type"] == "truefalse"]
    matching = [q for q in all_q if q["type"] == "matching"]
    assert len(tf) == 14
    assert all(q["theme"] == "dl-evaluation-seance" for q in tf)
    assert len(matching) == 1
    assert matching[0]["theme"] == "ia-1-introduction-agents"
    assert len(matching[0]["appariements"]) >= 3


@pytest.mark.parametrize("theme", sorted(EXPECTED_PER_THEME))
def test_every_question_carries_verifier_contract(theme):
    """Contrat #18207 : la banque doit nourrir verifier(...) sans conversion.
    Champs minimaux par question, types Python corrects."""
    bank = load_bank()
    for q in bank[theme]:
        assert isinstance(q["enonce"], str) and q["enonce"].strip()
        assert isinstance(q["source"], str) and q["source"].strip()
        if q["type"] in ("multichoice", "truefalse"):
            assert isinstance(q["choix_unique"], bool)
            assert isinstance(q["options"], list) and len(q["options"]) >= 2
            for o in q["options"]:
                assert isinstance(o["texte"], str) and o["texte"].strip()
                assert isinstance(o["correcte"], bool)
