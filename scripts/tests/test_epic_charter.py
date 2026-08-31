#!/usr/bin/env python3
"""Controles positifs de `scripts/check_epic_charter.py` (#13420).

Le docstring de l'organe promettait ces controles ; ce fichier les livre.

Pourquoi ils sont obligatoires, et pas decoratifs : la passe du 2026-08-29 sur
les 52 EPICs ouverts a rendu **zero** `PARITE-ABSENTE`. Les 7 defauts trouves
etaient tous sur la jambe faible (redaction). Un garde qui ne trouve aucune
instance de sa classe de defaut principale est *indiscernable* d'un garde
incapable de la detecter -- c'est exactement le mode d'echec de
`handrolled-pattern-set-undercounts-silently` : un motif absent ne leve pas
d'erreur, il rend un chiffre plus petit et plus propre.

Les tests ci-dessous fabriquent donc l'instance que le corpus n'a pas fournie,
et exigent que chaque forme de chaque motif morde individuellement -- une
alternative perdue rougit ici au lieu de sous-compter en silence.
"""

import os
import re
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_epic_charter import (  # noqa: E402
    EXPANSION_MIN,
    _CONSO_PLEDGE_RE,
    _STOP_RE,
    audit_epic,
    children_of,
    is_epic,
)

# Un corps d'EPIC qui satisfait LES DEUX exigences de redaction, pour que la
# jambe A (parite) puisse etre observee seule. Sans cet isolement, un test de
# parite verrait trois defauts et ne prouverait pas lequel a mordu.
BODY_REDACTION_OK = (
    "Regle d'arret : cet EPIC s'arrete a 12 notebooks dans la serie.\n"
    "Chaque tranche d'expansion appelle une issue de consolidation.\n"
)


def _issue(number, title, body="", state="OPEN", labels=None):
    return {
        "number": number,
        "title": title,
        "body": body,
        "state": state,
        "labels": labels or [],
    }


def _child(number, parent, title, state="OPEN"):
    """Fille qui DECLARE son ascendance dans la forme que `parent_issue` lit."""
    return _issue(number, title, "Enfant de l'Epic #%d.\n" % parent, state)


def _expansion(number, parent, state="OPEN"):
    return _child(number, parent, "Nouveau notebook %d de la serie" % number,
                  state)


def _consolidation(number, parent, state="OPEN"):
    return _child(number, parent, "Renumerotation de la sous-serie", state)


def _neutral(number, parent, state="OPEN"):
    return _child(number, parent, "Ajuster le libelle du titre", state)


# --------------------------------------------------------------------------
# Jambe A -- la mesure. Le controle que le corpus reel n'a pas fourni.
# --------------------------------------------------------------------------

def test_parite_absente_fires_on_synthetic_epic():
    """>= EXPANSION_MIN filles d'expansion, ZERO consolidation -> defaut.

    C'est LE controle positif de la jambe forte. Il fabrique la situation que
    le mandat user decrit -- un EPIC qui alimente une serie sans jamais
    engendrer le grain qui la range -- et exige que l'organe la nomme.
    """
    epic = _issue(20000, "[EPIC] Serie qui gonfle", BODY_REDACTION_OK)
    pool = [_expansion(20000 + i, 20000) for i in range(1, EXPANSION_MIN + 1)]

    row = audit_epic(epic, pool)

    assert row["measured"] is True
    assert len(row["expansion"]) == EXPANSION_MIN
    assert row["consolidation"] == []
    assert "PARITE-ABSENTE" in row["defects"]
    # L'isolement doit tenir : la redaction est correcte, donc PAS de defaut
    # de redaction. Si ceux-ci apparaissaient, le test ci-dessus ne prouverait
    # plus que la jambe A a mordu.
    assert row["defects"] == ["PARITE-ABSENTE"]


def test_parite_satisfaite_par_une_seule_consolidation():
    """UNE fille de consolidation suffit a eteindre le defaut de parite.

    Le seuil de l'organe est `not con` -- pas un ratio. Ce test fige ce choix :
    si quelqu'un durcit en `len(con) >= len(exp)`, il rougit ici et doit le
    declarer, au lieu de changer la semantique en silence.
    """
    epic = _issue(20100, "[EPIC] Serie equilibree", BODY_REDACTION_OK)
    pool = [_expansion(20100 + i, 20100) for i in range(1, EXPANSION_MIN + 1)]
    pool.append(_consolidation(20190, 20100))

    row = audit_epic(epic, pool)

    assert row["consolidation"] == [20190]
    assert "PARITE-ABSENTE" not in row["defects"]
    assert row["verdict"] == "OK"


def test_parite_muette_sous_le_seuil():
    """EXPANSION_MIN - 1 filles d'expansion : pas encore un rollout."""
    epic = _issue(20200, "[EPIC] Debut de serie", BODY_REDACTION_OK)
    pool = [_expansion(20200 + i, 20200) for i in range(1, EXPANSION_MIN)]

    row = audit_epic(epic, pool)

    assert len(row["expansion"]) == EXPANSION_MIN - 1
    assert row["defects"] == []


def test_seuil_configurable_deplace_bien_la_frontiere():
    """`expansion_min` n'est pas decoratif : le baisser doit faire mordre."""
    epic = _issue(20300, "[EPIC] Deux instances", BODY_REDACTION_OK)
    pool = [_expansion(20300 + i, 20300) for i in range(1, 3)]

    assert audit_epic(epic, pool)["defects"] == []
    assert "PARITE-ABSENTE" in audit_epic(epic, pool, expansion_min=2)["defects"]


# --------------------------------------------------------------------------
# NON-MESURE -- le vert dangereux que l'organe refuse de rendre.
# --------------------------------------------------------------------------

def test_epic_sans_fille_declaree_est_non_mesure_pas_ok():
    """Aucune ascendance declaree -> NON-MESURE, jamais OK.

    Rendre `OK` ferait passer une absence de mesure pour une absence de
    defaut. Le test fige la distinction.
    """
    epic = _issue(20400, "[EPIC] Sans filles declarees", "Corps quelconque.")
    pool = [_issue(20401, "Nouveau notebook orphelin", "Aucune ascendance.")]

    row = audit_epic(epic, pool)

    assert row["measured"] is False
    assert row["verdict"] == "NON-MESURE"
    assert row["defects"] == []
    assert row["children"] == 0


def test_reference_nue_ne_vaut_pas_ascendance():
    """`#20500` en prose n'est pas une declaration de filiation."""
    epic = _issue(20500, "[EPIC] Cite ailleurs", BODY_REDACTION_OK)
    pool = [_issue(20501, "Nouveau notebook", "Voir aussi #20500 pour contexte.")]

    assert children_of(20500, pool) == []
    assert audit_epic(epic, pool)["verdict"] == "NON-MESURE"


# --------------------------------------------------------------------------
# Jambe B -- la redaction. Chaque alternative se prouve individuellement.
# --------------------------------------------------------------------------

def _alternatives(pattern):
    """Decoupe un motif sur ses `|` de premier niveau.

    Les `|` internes -- `criteri(?:on|a)` -- sont proteges par la profondeur de
    parenthese. Deriver les alternatives du motif VIVANT plutot que les
    recopier ici est ce qui rend les deux invariants ci-dessous honnetes : une
    copie divergerait en silence, exactement le defaut que ces tests existent
    pour empecher.
    """
    parts, depth, cur = [], 0, []
    for ch in pattern:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "|" and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur))
    return parts


STOP_ALTERNATIVES = _alternatives(_STOP_RE.pattern)

# Une phrase par alternative, chacune ecrite pour n'en declencher QU'UNE.
# L'isolement n'est pas cosmetique : "Regle d'arret : 12 notebooks." matche
# AUSSI `arret :`, donc perdre l'alternative `regle d'arret` ne l'aurait pas
# fait rougir -- le controle serait passe pour la mauvaise raison. Mesure du
# 2026-08-29 : 3 des 5 controles d'apostrophe etaient confondus ainsi.
STOP_PHRASES = [
    "Regle d'arret fixee a 12 notebooks.",
    "Critere d'arret defini par la couverture.",
    "Condition d'arret atteinte a 12 instances.",
    "Regle de sortie definie plus bas.",
    "Critere de sortie, audit vert.",
    "Stopping rule, the series caps at 12 notebooks.",
    "Exit criterion, coverage complete.",
    "Exit criteria, coverage complete.",
    "On sait quand s'arrete la serie.",
    "Cet EPIC s'arrete des que la serie est renumerotee.",
    "Arret : 12 notebooks.",
    "Borne : 12 instances au maximum.",
    "Plafond : 12 notebooks.",
]


@pytest.mark.parametrize("phrase", STOP_PHRASES)
def test_stop_re_reconnait_chaque_forme(phrase):
    """Chaque phrase declenche `_STOP_RE`, et par UNE SEULE alternative.

    Une alternative perdue par une reecriture ne casse rien de visible : elle
    fait simplement rougir a tort des EPICs correctement rediges. Ce
    parametrage rend la perte bruyante -- a condition que chaque phrase soit
    isolee, sans quoi une alternative voisine la couvre et la perte reste
    muette.
    """
    assert _STOP_RE.search(phrase), phrase
    touchees = [a for a in STOP_ALTERNATIVES if re.search(a, phrase, re.I)]
    assert len(touchees) == 1, "%r declenche %d alternatives : %s" % (
        phrase, len(touchees), touchees)


def test_chaque_alternative_de_stop_re_a_son_controle():
    """Ajouter une alternative sans controle positif doit rougir ici.

    C'est l'invariant qui rend la couverture auto-portante : sans lui, la
    promesse "chaque forme est couverte" se perime au premier ajout, en
    silence.
    """
    couvertes = {a for a in STOP_ALTERNATIVES
                 for p in STOP_PHRASES if re.search(a, p, re.I)}
    manquantes = [a for a in STOP_ALTERNATIVES if a not in couvertes]
    assert not manquantes, "alternatives sans phrase de controle : %s" % manquantes


# L'apostrophe typographique U+2019 est ecrite ici par `chr` plutot qu'en
# litteral : un editeur ou un outil de reformatage qui la normaliserait en
# apostrophe droite retirerait le controle sans que rien ne rougisse -- le test
# passerait alors en testant l'autre forme, deja couverte.
APOS_TYPO = chr(8217)


@pytest.mark.parametrize("modele", [
    "Regle d{a}arret fixee a 12 notebooks.",
    "Critere d{a}arret defini par la couverture.",
    "Condition d{a}arret atteinte a 12 instances.",
    "On sait quand s{a}arrete la serie.",
    "Cet EPIC s{a}arrete des que la serie est renumerotee.",
])
def test_stop_re_accepte_l_apostrophe_typographique(modele):
    """Les deux apostrophes valent, sinon le motif sous-compte en silence.

    Mesure du 2026-08-29 : 2 des 52 EPICs ouverts ecrivent deja leur corps
    avec `U+2019`. Aucune regle d'arret n'etait ratee ce jour-la -- la forme
    est simplement vivante dans le corpus, et le jour ou elle portera une
    borne, l'organe la manquerait sans rien signaler.
    """
    assert _STOP_RE.search(modele.format(a=APOS_TYPO)), modele


@pytest.mark.parametrize("phrase", [
    "Cet EPIC couvre la serie GenAI/Texte.",
    "Les filles arrivent au fil des cycles.",
    "Objectif : enrichir chaque notebook de la serie.",
])
def test_stop_re_ne_mord_pas_sur_de_la_prose_ordinaire(phrase):
    """Controle negatif : sans regle d'arret ecrite, rien ne doit matcher."""
    assert not _STOP_RE.search(phrase), phrase


@pytest.mark.parametrize("phrase", [
    "Une issue de consolidation par tranche.",
    "Prevoir la renumerotation en fin de serie.",
    "Il faudra renumeroter la serie.",
    "Fusionner les notebooks 3 et 4.",
    "Fusion notebooks redondants prevue.",
    "Regrouper les variantes en une seule instance.",
    "Un regroupement est prevu.",
    "La sous-serie sera extraite ensuite.",
])
def test_conso_pledge_re_reconnait_chaque_forme(phrase):
    assert _CONSO_PLEDGE_RE.search(phrase), phrase


@pytest.mark.parametrize("phrase", [
    "Ajouter un notebook par semaine.",
    "Chaque fille couvre une nouvelle famille.",
])
def test_conso_pledge_re_ne_mord_pas_sur_de_l_expansion(phrase):
    assert not _CONSO_PLEDGE_RE.search(phrase), phrase


def test_arret_non_declare_ne_se_pose_que_sur_un_epic_qui_alimente():
    """Zero fille d'expansion -> exiger une regle d'arret serait du bruit."""
    epic = _issue(20600, "[EPIC] Rangement pur", "Corps sans borne ecrite.")
    pool = [_consolidation(20601, 20600), _neutral(20602, 20600)]

    row = audit_epic(epic, pool)

    assert row["feeds_series"] is False
    assert "ARRET-NON-DECLARE" not in row["defects"]
    assert row["verdict"] == "OK"


def test_arret_non_declare_mord_des_la_premiere_expansion():
    epic = _issue(20700, "[EPIC] Alimente sans borne",
                  "Une issue de consolidation suivra.")
    pool = [_expansion(20701, 20700), _consolidation(20702, 20700)]

    row = audit_epic(epic, pool)

    assert row["feeds_series"] is True
    assert row["defects"] == ["ARRET-NON-DECLARE"]


def test_regle_d_arret_ecrite_dans_le_TITRE_seul_est_vue():
    """Concern 2 de la review NanoClaw sur #13539 : la jambe B lisait `body`
    seul, donc une borne ecrite uniquement dans l intitule passait inapercue.

    Controle NEGATIF apparie juste en dessous : sans la borne, le meme EPIC
    mord. Sans cette moitie, le test passerait aussi avec une jambe B qui ne
    mord plus jamais -- c est la seule facon de distinguer « vue » de
    « eteinte ».
    """
    epic = _issue(20750, "[EPIC] Serie X -- regle d'arret : 12 notebooks",
                  "Corps sans aucune borne ecrite. Une consolidation suivra.")
    pool = [_expansion(20751, 20750), _consolidation(20752, 20750)]

    row = audit_epic(epic, pool)

    assert row["feeds_series"] is True
    assert "ARRET-NON-DECLARE" not in row["defects"], (
        "la borne est dans le titre, la jambe B doit la voir")


def test_controle_negatif_titre_sans_borne_mord_toujours():
    epic = _issue(20760, "[EPIC] Serie X -- suite du rollout",
                  "Corps sans aucune borne ecrite. Une consolidation suivra.")
    pool = [_expansion(20761, 20760), _consolidation(20762, 20760)]

    assert audit_epic(epic, pool)["defects"] == ["ARRET-NON-DECLARE"]


def test_pendant_non_declare_isole_de_l_arret():
    """Rollout sans engagement de consolidation ECRIT, mais borne declaree."""
    epic = _issue(20800, "[EPIC] Borne mais sans pendant",
                  "Regle d'arret : 12 notebooks.")
    pool = [_expansion(20800 + i, 20800) for i in range(1, EXPANSION_MIN + 1)]
    pool.append(_consolidation(20890, 20800))

    row = audit_epic(epic, pool)

    assert row["defects"] == ["PENDANT-NON-DECLARE"]


# --------------------------------------------------------------------------
# Classement des filles et etats.
# --------------------------------------------------------------------------

def test_les_trois_polarites_sont_ventilees():
    epic = _issue(20900, "[EPIC] Melange", BODY_REDACTION_OK)
    pool = [
        _expansion(20901, 20900),
        _consolidation(20902, 20900),
        _neutral(20903, 20900),
    ]

    row = audit_epic(epic, pool)

    assert row["expansion"] == [20901]
    assert row["consolidation"] == [20902]
    assert row["neutral"] == [20903]
    assert row["children"] == 3


def test_les_filles_fermees_comptent_dans_la_mesure():
    """Le recensement porte sur TOUS les etats -- c'est le point de #13420.

    Les filles d'expansion sont consommees vite ; ne compter que les ouvertes
    mesurerait la file d'attente restante, pas ce que l'EPIC a engendre. Un
    organe qui ne verrait que les ouvertes rendrait un verdict rassurant sur
    l'EPIC meme qui a motive le mandat.
    """
    epic = _issue(21000, "[EPIC] Filles consommees", BODY_REDACTION_OK)
    pool = [_expansion(21000 + i, 21000, state="CLOSED")
            for i in range(1, EXPANSION_MIN + 1)]

    row = audit_epic(epic, pool)

    assert row["children"] == EXPANSION_MIN
    assert row["open_children"] == 0
    assert "PARITE-ABSENTE" in row["defects"]


def test_forme_mesuree_sur_12373_ne_rougit_pas_en_parite():
    """Ancrage sur la mesure firsthand du 2026-08-29 : 4 expansion / 5 conso.

    #12373 (MGS vs mealpy) est l'EPIC le plus fourni du corpus ; il portait
    `ARRET-NON-DECLARE` mais PAS `PARITE-ABSENTE`. Ce test fige cette forme :
    un durcissement futur de la parite se declarera ici.
    """
    epic = _issue(21100, "[EPIC] MGS vs mealpy (forme reproduite)",
                  "Corps sans borne ecrite, avec consolidation prevue.")
    pool = [_expansion(21101 + i, 21100) for i in range(4)]
    pool += [_consolidation(21201 + i, 21100) for i in range(5)]
    pool += [_neutral(21301 + i, 21100) for i in range(4)]

    row = audit_epic(epic, pool)

    assert (len(row["expansion"]), len(row["consolidation"])) == (4, 5)
    assert row["children"] == 13
    assert "PARITE-ABSENTE" not in row["defects"]
    assert row["defects"] == ["ARRET-NON-DECLARE"]


# --------------------------------------------------------------------------
# Reconnaissance d'un EPIC.
# --------------------------------------------------------------------------

@pytest.mark.parametrize("issue", [
    {"title": "[EPIC] Serie GenAI", "labels": []},
    {"title": "EPIC: serie GenAI", "labels": []},
    {"title": "epic serie GenAI", "labels": []},
    {"title": "Serie GenAI", "labels": [{"name": "EPIC"}]},
    {"title": "Serie GenAI", "labels": ["umbrella"]},
    {"title": "Serie GenAI", "labels": [{"name": "ombrelle"}]},
])
def test_is_epic_positif(issue):
    assert is_epic(issue)


@pytest.mark.parametrize("issue", [
    {"title": "Nouveau notebook pour la serie", "labels": []},
    {"title": "Corriger la serie", "labels": [{"name": "bug"}]},
    {"title": "", "labels": []},
])
def test_is_epic_negatif(issue):
    assert not is_epic(issue)
