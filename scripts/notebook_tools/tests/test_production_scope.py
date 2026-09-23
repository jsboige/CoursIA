#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests du tampon PRODUCTION (#14831, sign-off user 2026-09-21).

`PRODUCTION` ne decrit pas une propriete du fichier : il dit que le responsable
pedagogique a appose son tampon, et juge le notebook finalise pour etre utilise
en cours **par d'autres**. Aucune combinaison d'axes ne peut produire ce fait.

Ce que ces tests epinglent, par ordre de degat s'ils cassent :

1. **Une colonne vide ne signe rien.** C'est l'etat reel du document aujourd'hui,
   et c'est l'etat correct : non tranche = BETA. Un parser qui signerait par
   defaut fabriquerait la signature qu'on vient de retirer de l'agregat.
2. **Une ligne qui signe mais ne resout aucun groupe est RENDUE.** C'est la panne
   mesuree pendant la conception : un join par repertoire sous-signait
   silencieusement (90 chemins sur 99, SmartContracts s'etalant sur deux
   sous-repertoires). Une ligne qui signe zero notebook sans le dire est
   indiscernable d'une ligne non repondue.
3. **Une exclusion nommee l'emporte sur la signature de sa serie.** L'inverse
   transformerait une reserve en approbation.
4. **Le document reel se lit.** Les 13 lignes resolvent leur groupe, les 99
   chemins de strate A existent. Sans ce controle, le parser pourrait rendre 0
   parce que le document a change de forme, et ce zero se lirait comme
   « personne n'a encore signe ».

Run: python -m pytest scripts/notebook_tools/tests/test_production_scope.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from generate_catalog import (  # noqa: E402
    PRODUCTION_SCOPE_PATH,
    _load_production_scope,
    production_is_signed,
)

REPO_ROOT = Path(__file__).resolve().parents[3]

DOC = """# Perimetre

## La passe par serie

| Série | Cours | Tête de série | N proposés | Verdict |
|-------|-------|---------------|------------|---------|
| Alpha | Cours A | `A-01-Tete.ipynb` | 2 | {verdict_a} |
| Beta | Cours B | `B-01-Tete.ipynb` | 2 | {verdict_b} |

## Strate A — proposés pour signature (4)

<!-- MyIA.AI.Notebooks/Alpha -->

- [{tick_a1}] `MyIA.AI.Notebooks/Alpha/A-01-Tete.ipynb`
- [ ] `MyIA.AI.Notebooks/Alpha/sub/A-02-Autre.ipynb`

<!-- MyIA.AI.Notebooks/Beta -->

- [ ] `MyIA.AI.Notebooks/Beta/B-01-Tete.ipynb`
- [ ] `MyIA.AI.Notebooks/Beta/B-02-Autre.ipynb`

## Strate B — hors proposition v1 (1)

<!-- MyIA.AI.Notebooks/Gamma -->

- [ ] `MyIA.AI.Notebooks/Gamma/G-01.ipynb`
"""


def write_doc(tmp_path, verdict_a="", verdict_b="", tick_a1=" "):
    p = tmp_path / "production-scope.md"
    p.write_text(
        DOC.format(verdict_a=verdict_a, verdict_b=verdict_b, tick_a1=tick_a1),
        encoding="utf-8",
    )
    return p


# --- 1. une colonne vide ne signe rien ---------------------------------------

def test_une_colonne_vide_ne_signe_rien(tmp_path):
    scope = _load_production_scope(write_doc(tmp_path))
    assert scope["signed"] == set()
    assert scope["unresolved"] == []
    assert production_is_signed(scope, "MyIA.AI.Notebooks/Alpha/A-01-Tete.ipynb") is False


def test_un_verdict_non_reconnu_ne_signe_rien(tmp_path):
    """Fail-CLOSED : « à voir », « peut-être », un point d'interrogation — rien
    de tout cela n'est une signature."""
    for bidon in ("à voir", "peut-être", "?", "non", "TODO"):
        scope = _load_production_scope(write_doc(tmp_path, verdict_a=bidon))
        assert scope["signed"] == set(), bidon


def test_un_document_absent_ne_leve_pas_et_ne_signe_rien(tmp_path):
    scope = _load_production_scope(tmp_path / "inexistant.md")
    assert scope["signed"] == set()


# --- le controle positif : sans lui, tout ce qui precede est satisfait par un
#     parser qui ne signe JAMAIS rien --------------------------------------

def test_un_oui_signe_toute_la_serie(tmp_path):
    scope = _load_production_scope(write_doc(tmp_path, verdict_a="oui"))
    assert scope["signed"] == {
        "MyIA.AI.Notebooks/Alpha/A-01-Tete.ipynb",
        "MyIA.AI.Notebooks/Alpha/sub/A-02-Autre.ipynb",
    }
    assert production_is_signed(scope, "MyIA.AI.Notebooks/Alpha/A-01-Tete.ipynb") is True
    assert production_is_signed(scope, "MyIA.AI.Notebooks/Beta/B-01-Tete.ipynb") is False


def test_le_groupe_porte_les_sous_repertoires(tmp_path):
    """La raison d'etre du join par commentaire de groupe : `A-02-Autre.ipynb`
    vit dans `Alpha/sub/`, pas dans le repertoire de la tete de serie. Un join
    par repertoire l'aurait manque -- c'est la panne mesuree sur SmartContracts
    (90 chemins signes sur 99)."""
    scope = _load_production_scope(write_doc(tmp_path, verdict_a="oui"))
    assert production_is_signed(scope, "MyIA.AI.Notebooks/Alpha/sub/A-02-Autre.ipynb") is True


def test_la_strate_b_n_est_jamais_signee(tmp_path):
    """La strate B n'est pas soumise a decision (non tranche = BETA)."""
    scope = _load_production_scope(write_doc(tmp_path, verdict_a="oui", verdict_b="oui"))
    assert not any("Gamma" in p for p in scope["signed"])


# --- 2. une ligne qui ne resout rien est RENDUE ------------------------------

def test_une_tete_de_serie_introuvable_est_rendue_pas_tue(tmp_path):
    doc = write_doc(tmp_path, verdict_a="oui")
    doc.write_text(
        doc.read_text(encoding="utf-8").replace("`A-01-Tete.ipynb`", "`A-1-Tete.ipynb`"),
        encoding="utf-8",
    )
    scope = _load_production_scope(doc)
    assert scope["signed"] == set(), "une ligne non resolue ne signe rien"
    assert len(scope["unresolved"]) == 1, "et elle le DIT"
    assert "Alpha" in scope["unresolved"][0]


# --- 3. une exclusion nommee l'emporte ---------------------------------------

def test_oui_sauf_exclut_le_notebook_nomme(tmp_path):
    scope = _load_production_scope(write_doc(tmp_path, verdict_a="oui sauf `A-02-Autre.ipynb`"))
    assert scope["signed"] == {"MyIA.AI.Notebooks/Alpha/A-01-Tete.ipynb"}


def test_oui_sauf_accepte_plusieurs_exclusions(tmp_path):
    scope = _load_production_scope(
        write_doc(tmp_path, verdict_a="oui sauf A-01-Tete.ipynb, A-02-Autre.ipynb"))
    assert scope["signed"] == set()


# --- la case cochee est le meme geste, pose notebook par notebook ------------

def test_une_case_cochee_signe_ce_notebook_seul(tmp_path):
    scope = _load_production_scope(write_doc(tmp_path, tick_a1="x"))
    assert scope["signed"] == {"MyIA.AI.Notebooks/Alpha/A-01-Tete.ipynb"}


# --- la comparaison de chemins ne se rabat pas sur le nom de fichier ---------

def test_un_homonyme_d_une_autre_serie_n_est_pas_signe(tmp_path):
    """Se rabattre sur le basename signerait les homonymes -- et les series de
    ce depot en regorgent (`01-1-...`, `Search-01-...`)."""
    scope = _load_production_scope(write_doc(tmp_path, verdict_a="oui"))
    assert production_is_signed(scope, "MyIA.AI.Notebooks/Autre/A-01-Tete.ipynb") is False


def test_les_separateurs_windows_sont_normalises(tmp_path):
    scope = _load_production_scope(write_doc(tmp_path, verdict_a="oui"))
    assert production_is_signed(scope, "MyIA.AI.Notebooks\\Alpha\\A-01-Tete.ipynb") is True


# --- 4. le document REEL se lit ----------------------------------------------

def test_le_document_reel_se_lit_et_ne_signe_encore_rien():
    """Contrat avec le document reel, dans les deux sens.

    **Il ne signe rien** : les 13 verdicts sont vides, le user n'a pas encore
    repondu, et `PRODUCTION = 0` est le verdict correct.

    **Et aucune ligne n'echoue a se resoudre** : c'est ce qui separe « personne
    n'a signe » de « le parser ne trouve plus le document ». Sans cette seconde
    assertion, la premiere serait satisfaite par un parser casse.
    """
    if not PRODUCTION_SCOPE_PATH.exists():
        import pytest
        pytest.skip("production-scope.md absent de cet arbre")
    scope = _load_production_scope()
    assert scope["signed"] == set(), (
        "des notebooks sont signes : mettre a jour ce test ET verifier que le "
        "user a bien repondu, la signature ne se derive de rien d'autre"
    )
    assert scope["unresolved"] == [], (
        "une ligne de decision ne resout plus son groupe de strate A : %s"
        % scope["unresolved"]
    )


def test_les_treize_lignes_de_decision_resolvent_leur_groupe():
    """Controle positif du test precedent : on force les 13 verdicts a « oui »
    sur une COPIE, et on verifie que la couverture est exactement la strate A.

    Sans ca, `unresolved == []` serait aussi vrai d'un parser qui ne lit aucune
    ligne. C'est la lecon du zero d'instrument aveugle : un zero ne prouve rien
    tant qu'on n'a pas montre que l'instrument sait rendre autre chose.
    """
    import re
    if not PRODUCTION_SCOPE_PATH.exists():
        import pytest
        pytest.skip("production-scope.md absent de cet arbre")
    text = PRODUCTION_SCOPE_PATH.read_text(encoding="utf-8")
    # remplir la derniere colonne des seules lignes a 5 cellules
    out = []
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("|") and not s.startswith("|--"):
            cells = [c.strip() for c in s.strip("|").split("|")]
            if len(cells) == 5 and cells[0].lower() not in ("serie", "série") and not cells[4]:
                cells[4] = "oui"
                line = "| " + " | ".join(cells) + " |"
        out.append(line)
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "scope.md"
        p.write_text("\n".join(out), encoding="utf-8")
        scope = _load_production_scope(p)

    strate_a = set()
    strate = None
    for line in text.splitlines():
        s = line.strip()
        m = re.match(r"^##\s+Strate\s+([ABC])\b", s)
        if m:
            strate = m.group(1)
            continue
        if s.startswith("## "):
            strate = None
            continue
        m = re.match(r"^- \[[ xX]\]\s*`([^`]+)`", s)
        if m and strate == "A":
            strate_a.add(m.group(1))

    assert scope["unresolved"] == [], scope["unresolved"]
    assert scope["signed"] == strate_a, (
        "un « oui » partout doit couvrir exactement la strate A : %d signes, "
        "%d attendus, ecart %s"
        % (len(scope["signed"]), len(strate_a),
           sorted(strate_a ^ scope["signed"])[:5])
    )


def test_tous_les_chemins_de_strate_a_existent_sur_disque():
    """Un chemin de strate A qui n'existe pas serait un notebook signable et
    introuvable — la signature porterait sur du vide."""
    import re
    if not PRODUCTION_SCOPE_PATH.exists():
        import pytest
        pytest.skip("production-scope.md absent de cet arbre")
    text = PRODUCTION_SCOPE_PATH.read_text(encoding="utf-8")
    strate = None
    absents = []
    for line in text.splitlines():
        s = line.strip()
        m = re.match(r"^##\s+Strate\s+([ABC])\b", s)
        if m:
            strate = m.group(1)
            continue
        if s.startswith("## "):
            strate = None
            continue
        m = re.match(r"^- \[[ xX]\]\s*`([^`]+)`", s)
        if m and strate == "A" and not (REPO_ROOT / m.group(1)).exists():
            absents.append(m.group(1))
    assert absents == [], "chemins de strate A absents du disque : %s" % absents[:5]
