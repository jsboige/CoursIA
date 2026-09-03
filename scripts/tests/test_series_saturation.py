#!/usr/bin/env python3
"""Tests de rattachement de `series_saturation.py` (#13435).

Le defaut vise : `_DECL_RE` comptait un renvoi purement referentiel
(`voir #N`, bare `EPIC #N`) comme une declaration de travail -- la PR se
voyait rattachee a la zone dominante de l'issue citee, ce qui amortissait le
poids d'une issue neutre et gonflait l'expansion apparente d'une zone deja
saturee (reserve Hermes sur #13419, mesure : 19/459 rattachements sur la
fenetre 14 j du 2026-08-29).

Un detecteur se valide par ses faux negatifs (anti-regression.md) : les
controles ci-dessous epinglent les DEUX sens -- le renvoi de contexte NE
rattache PAS, la declaration (et la forme structurelle) rattache.

Extension #13507 : `parent_issue` applique la meme distinction declaration vs
renvoi -- le motif nu `EPIC #N` ne rattache qu'en tete de corps, jamais au
fil du texte.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import series_saturation as ss  # noqa: E402


def _pr(body: str = "", title: str = "", number: int = 9999) -> dict:
    return {"body": body, "title": title, "number": number}


def test_context_ref_voir_does_not_attach():
    """Controle positif du fix : `voir #N` seul ne rattache pas (#13435)."""
    cited = ss.cited_issues(_pr(body="Contexte historique : voir #12373 pour le recit."))
    assert 12373 not in cited, f"`voir #N` ne doit pas rattacher, cite={cited}"


def test_context_bare_epic_does_not_attach():
    """Un bare `EPIC #N` en prose ne declare pas servir la zone."""
    cited = ss.cited_issues(_pr(body="Pourquoi ce bump etait attendu. L'EPIC #4960 suit son cours ailleurs."))
    assert 4960 not in cited, f"bare `EPIC #N` ne doit pas rattacher, cite={cited}"


def test_context_ombrelle_does_not_attach():
    cited = ss.cited_issues(_pr(body="Cadre general (ombrelle #11268), hors perimetre de cette PR."))
    assert 11268 not in cited, f"`ombrelle #N` ne doit pas rattacher, cite={cited}"


def test_declaration_see_attaches():
    """La classe declaration rattache toujours (regression guard du split)."""
    cited = ss.cited_issues(_pr(body="Contribution partielle. See #12373."))
    assert 12373 in cited, f"`See #N` doit rattacher, cite={cited}"


def test_declaration_closes_attaches():
    cited = ss.cited_issues(_pr(body="Closes #11168."))
    assert 11168 in cited


def test_declaration_refs_attaches():
    cited = ss.cited_issues(_pr(body="Refs : #12373 (epic)."))
    assert 12373 in cited, "`Refs :` doit rattacher meme suivi de `(epic)` en parenthese"


def test_structural_enfant_de_attaches():
    """Les formes structurelles restent des declarations (via _PARENT_RE)."""
    cited = ss.cited_issues(_pr(body="Enfant de l'Epic #12373, paire 4/9."))
    assert 12373 in cited, f"`Enfant de l'Epic #N` doit rattacher, cite={cited}"


def test_structural_paire_de_attaches():
    cited = ss.cited_issues(_pr(body="Paire 3/9 de l'EPIC #12373."))
    assert 12373 in cited, f"`Paire N/N de l'EPIC #N` doit rattacher, cite={cited}"


def test_title_ref_still_attaches():
    """Les refs du titre ne dependent pas du split (_REF_RE inchange)."""
    cited = ss.cited_issues(_pr(body="Rien de special.", title="fix(mgs,#12373): livraison"))
    assert 12373 in cited


def test_prev_grain_line_masked():
    """La clause `prev:` du tag Grain reste masquee (adjacence != sujet)."""
    cited = ss.cited_issues(_pr(body="Grain: MED/lean -- lane x:y -- prev: MED/lean #10999\n\nCloses #12373."))
    assert 10999 not in cited, "prev: ne doit jamais rattacher"
    assert 12373 in cited


def test_saturation_does_not_map_zone_from_context_ref():
    """Integration : une PR `voir #N` seule ne cree pas d'entree issue->zone."""
    prs = [{
        "number": 4242,
        "title": "feat(x): unrelated work",
        "body": "Incidemment, voir #12373 pour le contexte.",
        "files": [{"path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/Foo.ipynb",
                   "additions": 10, "deletions": 0}],
    }]
    zones, i2f = ss.saturation(prs)
    assert 12373 not in i2f, f"renvoi contexte ne doit pas mapper l'issue a une zone, i2f={i2f}"
    assert "MyIA.AI.Notebooks/Search/Part4-Metaheuristics" in zones


def test_saturation_maps_zone_from_declaration():
    """Integration miroir : `See #N` + depot dans la zone rattache #N."""
    prs = [{
        "number": 4243,
        "title": "feat(x): work",
        "body": "See #12373.",
        "files": [{"path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/Foo.ipynb",
                   "additions": 10, "deletions": 0}],
    }]
    zones, i2f = ss.saturation(prs)
    assert i2f.get(12373) == "MyIA.AI.Notebooks/Search/Part4-Metaheuristics"


# --- Emballement : la MAGNITUDE que la polarite ne voit pas -----------------
# Les deux premiers tests sont les DEUX zones reelles mesurees le 2026-08-29 :
# c'est leur ecart qui definit le critere, et non l'inverse. Si un jour le
# seuil devait bouger, c'est ce couple qui doit continuer a se separer.


def _slot(landed, exp, con):
    return {"new_notebooks": landed, ss.EXPANSION: exp,
            ss.CONSOLIDATION: con, ss.NEUTRAL: 0}


def test_runaway_fires_on_dswa_shape():
    """DataScienceWithAgents mesure : 11 arrivees, 3 consolidations ouvertes.

    Le verdict de POLARITE la disait OK -- trois remedes ouverts pour deux
    expansions ouvertes. C'est exactement la zone que le user a nommee comme
    symptomatique. La parite ne suffit pas : elle ne compte pas ce qui est
    deja tombe.
    """
    slot = _slot(11, 2, 3)
    assert ss.zone_verdict(slot) == ss.BALANCED, "la polarite reste OK -- c'est le point"
    assert ss.is_runaway(slot), "11 arrivees pour 3 consolidations = emballement"


def test_runaway_silent_on_mgs_shape():
    """Search/Part4-Metaheuristics mesure : 6 arrivees, 3 consolidations.

    Zone signalee en premier par le user, mais dont la consolidation est
    engagee (EPIC #12373). Un critere qui la ferait rougir sanctionnerait le
    remede en cours -- le meme defaut que l'amortissement aveugle corrige la
    veille.
    """
    slot = _slot(6, 1, 3)
    assert not ss.is_runaway(slot), "consolidation engagee : ne pas sanctionner"


def test_runaway_ignores_small_zones():
    """Trois notebooks sans aucun remede, c'est petit -- pas emballe.

    `SANS REMEDE` dit deja ce qu'il faut en faire. Qualifier ca d'emballement
    diluerait le mot sur le cas ou il n'apporte rien.
    """
    slot = _slot(3, 0, 0)
    assert ss.zone_verdict(slot) == ss.NO_REMEDY
    assert not ss.is_runaway(slot)


def test_runaway_fires_with_zero_consolidation():
    """Le plancher a 1 evite la division par zero ET tient le cas le pire.

    Six arrivees et aucun remede ouvert doit rougir : c'est le cas ou personne
    n'a encore ouvert la contrepartie.
    """
    assert ss.is_runaway(_slot(6, 4, 0))


def test_runaway_is_orthogonal_to_polarity():
    """Une zone peut etre DESEQUILIBREE sans etre emballee, et l'inverse.

    Les deux mesures repondent a deux questions differentes ; les fondre en
    une seule ferait perdre celle qui manquait.
    """
    petite_desequilibree = _slot(2, 5, 0)
    assert ss.zone_verdict(petite_desequilibree) == ss.IMBALANCED
    assert not ss.is_runaway(petite_desequilibree)

    grosse_ok = _slot(12, 0, 1)
    assert ss.zone_verdict(grosse_ok) == ss.BALANCED
    assert ss.is_runaway(grosse_ok)


# --- Polarity : forme [<tag> N/M] (#13533) --------------------------------
# Bug #13533 : la sous-fille EPIC #12373 utilise la forme compacte
# `paire 4/9` precede d'une etiquette (ex. `[MGS-vs-mealpy 4/9]`).
# Le pattern originel `paire \d+\s*/\s*\d+` ne matche pas cette forme,
# et la sous-fille tombe en `consolidation` par defaut, ce qui fausse
# la parite de `Search/Part4-Metaheuristics` : 5 expansions mesuerees
# comme `consolidation` (vs parite reelle 6/5 OK).
# Le pattern etendu doit :
#   1. Rattraper la forme bracket-tag exact -- sans bruit sur les autres.
#   2. Ne pas reclasser `consolidation` ni `neutral` (sanity guards).
#   3. Rattraper la forme `paire N/M` SANS etiquette (le pattern originel).


def test_polarity_bracket_tag_pattern_is_expansion():
    """#13533 -- `paire N/M` precede d'un tag [<...>] est expansion."""
    title = "[MGS-vs-mealpy 4/9] Algorithme genetique vs metaheuristique"
    assert ss.polarity(title, "") == ss.EXPANSION, (
        f"forme bracket-tag classee {ss.polarity(title, '')!r}, "
        f"attendue {ss.EXPANSION!r}"
    )


def test_polarity_bracket_tag_variations_all_expansion():
    """Variations reelles mesurees sur les 5 sous-filles #12373."""
    for title in (
        "[MGS-vs-mealpy 4/9] titre",
        "[MGS-vs-mealpy  4 / 9 ] titre",
        "[autre-tag 1/12] titre",
        "[foo bar 7/42] titre",
    ):
        assert ss.polarity(title, "") == ss.EXPANSION, (
            f"variation {title!r} classee {ss.polarity(title, '')!r}"
        )


def test_polarity_bracket_tag_does_not_regress_consolidation():
    """Sanity guard -- le pattern ne doit pas reclasser une consolidation.

    Si `_EXPANSION_RE` mange un ratio qui suit un mot-cle consolidation
    (ex. `consolidation 4/9`), la polarite bascule. Verifier que
    l'ordre `_CONSOLIDATION_RE` -> `_EXPANSION_RE` tient.
    """
    title = "consolidation 4/9 vers une seule paire"
    assert ss.polarity(title, "") == ss.CONSOLIDATION, (
        f"consolidation classee {ss.polarity(title, '')!r} -- regression"
    )


def test_polarity_bracket_tag_does_not_match_neutral():
    r"""Sanity guard -- un titre neutre sans aucune paire ne doit pas matcher.

    Si le pattern etait trop large (ex. `[\d+\s*/\s*\d+]`), il mangerait
    `4/9` isoles. Le pattern exige un tag texte (non-vide) avant le ratio.
    """
    assert ss.polarity("note de release", "") == ss.NEUTRAL
    assert ss.polarity("ratio 4/9 hors bracket-tag", "") == ss.NEUTRAL


def test_zone_verdict_matches_legacy_inline_logic():
    """Le verdict extrait doit rendre EXACTEMENT ce que le picker rendait.

    `SANS REMEDE` a un effet de bord -- il retient des grains hors tirage.
    Extraire la logique sans la reproduire au bit pres changerait le tirage
    en silence.
    """
    for landed in (0, 3, 9):
        for exp in range(4):
            for con in range(4):
                slot = _slot(landed, exp, con)
                if exp == 0 and con == 0:
                    attendu = "SANS REMEDE"
                elif con >= exp:
                    attendu = "OK"
                else:
                    attendu = "DESEQUILIBRE"
                assert ss.zone_verdict(slot) == attendu, (landed, exp, con)


def test_zone_umbrellas_names_the_feeding_epic():
    """Nommer l'EPIC : sans lui, le lecteur du verdict doit le chercher."""
    pool = [
        {"number": 1, "parent": 12373, "title": "a", "body": ""},
        {"number": 2, "parent": 12373, "title": "b", "body": ""},
        {"number": 3, "parent": 999, "title": "c", "body": ""},
        {"number": 4, "parent": None, "title": "d", "body": ""},
    ]
    i2f = {1: "Z", 2: "Z", 3: "Z", 4: "Z"}
    out = ss.zone_umbrellas(i2f, pool)
    assert out["Z"] == {12373: 2, 999: 1}, out


def test_zone_umbrellas_empty_when_no_parent_declared():
    """Zone chaude sans EPIC : le cas le PLUS grave, pas le plus propre.

    Il doit rendre un vide explicite, que l'appelant rend en clair -- personne
    n'y est comptable de la contrepartie.
    """
    pool = [{"number": 1, "parent": None, "title": "a", "body": ""}]
    assert ss.zone_umbrellas({1: "Z"}, pool) == {}


# --- Attribution : ce qui empechait de NOMMER l'EPIC -----------------------


def test_family_from_text_prefers_frequency_over_length():
    """Le sujet est ce que l'issue REPETE, pas sa plus longue citation.

    Cas reel : l'EPIC #13504 nomme deux fois `ML/DataScienceWithAgents` et
    cite une fois `Search/Part4-Metaheuristics` dans un tableau de
    comparaison. Le second est plus LONG (45 vs 44). Sous l'ancien
    tie-break, l'EPIC ouvert pour declarer une zone se rattachait a l'autre
    -- l'organe repondait le contraire de ce qui venait d'etre ecrit.
    """
    fams = ["MyIA.AI.Notebooks/ML/DataScienceWithAgents",
            "MyIA.AI.Notebooks/Search/Part4-Metaheuristics"]
    txt = ("MyIA.AI.Notebooks/ML/DataScienceWithAgents est la zone chaude. "
           "La suivante, MyIA.AI.Notebooks/Search/Part4-Metaheuristics, est "
           "a 6. Voir MyIA.AI.Notebooks/ML/DataScienceWithAgents.")
    assert ss.family_from_text(txt, fams) == fams[0]


def test_family_from_text_length_still_breaks_ties():
    """A frequence egale, la longueur departage -- le garde d'origine tient."""
    fams = ["MyIA.AI.Notebooks/GenAI/Texte", "GenAI"]
    assert ss.family_from_text("MyIA.AI.Notebooks/GenAI/Texte", fams) == fams[0]


def test_distinctive_segment_matches_identifiers_not_words():
    """Un identifiant se cherche seul ; un mot francais courant, jamais.

    C'est la condition qui permet a un TITRE de rattacher une zone : personne
    n'ecrit le chemin complet dans un titre. Le refus total protegeait de
    `Texte`, il coutait `DataScienceWithAgents`.
    """
    for mot in ("Texte", "Audio", "Video", "Search", "ML"):
        assert not ss._is_distinctive(mot), mot
    for ident in ("DataScienceWithAgents", "Part4-Metaheuristics",
                  "ML-Training-Pipeline", "Argument_Analysis", "ICT-Series"):
        assert ss._is_distinctive(ident), ident


def test_family_from_title_alone_resolves_a_distinctive_zone():
    """Integration : le titre reel de #13505 doit suffire."""
    fams = ["MyIA.AI.Notebooks/ML/DataScienceWithAgents"]
    titre = ("consolidation(DataScienceWithAgents): absorber 2.8c dans "
             "2.8b/2.8d")
    assert ss.family_from_text(titre, fams) == fams[0]


def test_family_from_text_does_not_match_common_word_zone_by_leaf():
    """Miroir : `Texte` en prose ne doit rattacher aucune zone."""
    fams = ["MyIA.AI.Notebooks/GenAI/Texte"]
    assert ss.family_from_text("On corrige le texte de la conclusion.",
                               fams) is None


def test_issue_zone_is_a_series_not_a_script_path():
    """Une zone est une SERIE de notebooks, pas `scripts/<fichier>.py`.

    Cas reel : mes propres PRs de picker citent #12373 (l'EPIC MGS) en prose
    et ne touchent que des scripts. `i2f[12373]` valait donc
    `scripts/series_saturation.py`, et TOUTE fille de cet EPIC heritait de la
    zone d'un script au lieu de sa serie.
    """
    prs = [
        {"number": 1, "title": "tooling", "body": "See #12373.",
         "files": [{"path": "scripts/series_saturation.py",
                    "additions": 40, "deletions": 2}]},
        {"number": 2, "title": "notebook", "body": "See #12373.",
         "files": [{"path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/"
                            "MGS-30.ipynb", "additions": 900, "deletions": 0}]},
    ]
    _, i2f = ss.saturation(prs)
    assert i2f[12373] == "MyIA.AI.Notebooks/Search/Part4-Metaheuristics", i2f


def test_series_attribution_is_not_overwritten_by_a_later_script_pr():
    """La promotion va dans UN sens : serie remplace non-serie, jamais l'inverse."""
    prs = [
        {"number": 2, "title": "notebook", "body": "See #12373.",
         "files": [{"path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/"
                            "MGS-30.ipynb", "additions": 900, "deletions": 0}]},
        {"number": 3, "title": "tooling", "body": "See #12373.",
         "files": [{"path": "scripts/pick_idle_grain.py",
                    "additions": 40, "deletions": 2}]},
    ]
    _, i2f = ss.saturation(prs)
    assert i2f[12373] == "MyIA.AI.Notebooks/Search/Part4-Metaheuristics"


def test_is_series_rejects_tooling_paths():
    assert ss._is_series("MyIA.AI.Notebooks/ML/DataScienceWithAgents")
    for p in ("scripts/series_saturation.py", ".github/workflows/x.yml",
              "docs/reference/y.md"):
        assert not ss._is_series(p), p
def test_parent_issue_prose_renvoi_mid_body_returns_none():
    """Controle positif du fix #13507 : la phrase REELLE du corps de #13504.

    #13504 se voyait attribuer parent=12373 sur ce seul renvoi de comparaison
    mi-corps : "dont l'EPIC #12373 porte la consolidation".
    """
    body_13504 = (
        "## La zone\n\nDecrire `ML/DataScienceWithAgents`.\n\nC'est la difference exacte avec "
        "`Part4-Metaheuristics`, qui recoit vite **aussi** mais dont l'EPIC #12373 porte la "
        "consolidation."
    )
    assert ss.parent_issue(body_13504) is None


def test_parent_issue_structural_formulations_anywhere():
    """Les formulations REELLES des filles de #12373 rattachent, quelle que soit la position."""
    assert ss.parent_issue("Enfant de l'Epic #12373.") == 12373
    assert ss.parent_issue("Paire 9/9 de l'EPIC #12373 (MGS vs mealpy).") == 12373
    assert ss.parent_issue("Paire 8/9 de l'EPIC #12373.") == 12373
    assert ss.parent_issue("Intro longue.\n\nPuis du recit.\n\nEnfin : Fille de l'EPIC #5081.") == 5081


def test_parent_issue_naked_epic_head_declares():
    """Le motif nu garde sa valeur de declaration en TETE de corps.

    Formes reelles mesurees sur les issues ouvertes : #13436, #12915, #12607.
    """
    assert ss.parent_issue("## Contexte\nSous-grain de l'EPIC #1454.") == 1454
    assert ss.parent_issue("## Contexte\nTranche T5 de l'EPIC #12904.") == 12904
    assert ss.parent_issue("Fils techniques de l'axe 5 de l'Epic #12373.") == 12373


def test_parent_issue_naked_epic_mid_body_returns_none():
    """Le MEME motif nu, mi-corps, ne rattache plus (frontiere des 3 lignes)."""
    body = (
        "Un long sujet.\n\nUne premiere etape.\n\nUne deuxieme etape.\n\n"
        "Pour finir : l'EPIC #1621 a corrige ce point ailleurs."
    )
    assert ss.parent_issue(body) is None


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))


# --- Zone d'un EPIC : le vote de ses enfants (#12373 / #13268) -------------
#
# `saturation()` fige une issue sur la zone de la PREMIERE PR mergee qui la
# cite. Pour un EPIC -- un tracker cite par tout ce qui l'outille -- cela le
# fige sur un chemin de script, zone qui ne portera jamais de notebook. Ses
# filles sans PR citante propre heritent alors d'un frein NUL. Mesure du
# 2026-08-29 : #13268 prenait x1.00 la ou sa soeur #13394, meme EPIC et meme
# zone saturee, prenait x0.33.
#
# Un detecteur se valide par ses faux negatifs : les trois controles epinglent
# les deux sens -- le vote comble l'absente ET la muette, et n'ecrase JAMAIS
# une attribution deja informative ni n'invente une zone.

NB_A = "MyIA.AI.Notebooks/Search/Part4-Metaheuristics"
NB_B = "MyIA.AI.Notebooks/GenAI/Texte"
SCRIPT_ZONE = "scripts/series_saturation.py"


def test_parent_vote_replaces_a_zone_that_holds_no_notebook():
    """L'EPIC fige sur un chemin de script recoit la zone de ses enfants."""
    zones = {NB_A: {"new_notebooks": 6}, SCRIPT_ZONE: {"new_notebooks": 0}}
    i2f = {12373: SCRIPT_ZONE, 13394: NB_A, 12607: NB_A}
    pool = [{"number": 13394, "parent": 12373},
            {"number": 12607, "parent": 12373},
            {"number": 13268, "parent": 12373}]
    out = ss.enrich_parent_families(pool, i2f, zones)
    assert out[12373] == NB_A


def test_parent_vote_never_overwrites_an_informative_zone():
    """Une attribution qui porte deja des notebooks reste intacte."""
    zones = {NB_A: {"new_notebooks": 4}, NB_B: {"new_notebooks": 9}}
    i2f = {1: NB_A, 2: NB_B}
    out = ss.enrich_parent_families([{"number": 2, "parent": 1}], i2f, zones)
    assert out[1] == NB_A


def test_parent_vote_invents_nothing_without_an_informative_child():
    """Aucun enfant informatif : la carte est rendue telle quelle."""
    zones = {SCRIPT_ZONE: {"new_notebooks": 0}}
    i2f = {10: SCRIPT_ZONE}
    out = ss.enrich_parent_families([{"number": 99, "parent": 10}], i2f, zones)
    assert out[10] == SCRIPT_ZONE


def test_resolve_family_walks_past_a_zone_without_notebooks():
    """La cascade ne s'arrete pas sur une source qui n'informe pas le frein."""
    zones = {NB_B: {"new_notebooks": 4}, SCRIPT_ZONE: {"new_notebooks": 0}}
    item = {"number": 77, "parent": 10,
            "title": "GenAI/Texte : renumerotation", "body": ""}
    fam = ss.resolve_family(item, {10: SCRIPT_ZONE}, tuple(zones), zones)
    assert fam == NB_B


def test_resolve_family_keeps_legacy_answer_without_zones():
    """Sans `zones` on ne sait rien : comportement anterieur preserve."""
    item = {"number": 77, "parent": 10, "title": "x", "body": ""}
    assert ss.resolve_family(item, {10: SCRIPT_ZONE}, ()) == SCRIPT_ZONE

def test_informative_is_false_on_an_empty_candidate_list():
    """Le cas qui a casse les appelants a trois arguments.

    `_informative` raccourcit sur `zones is None` pour ne pas degrader
    l'existant. Sans garde prealable, ce raccourci repondait True sur une
    liste VIDE -- donc `resolve_family` croyait tenir une source informative
    la ou elle n'en avait aucune, et sautait le repli par le texte. Trois
    tests de `test_family_resolution.py` rendaient alors None.

    Une liste vide n'informe jamais, avec ou sans `zones`.
    """
    assert ss._informative([], None) is False
    assert ss._informative([], {}) is False
    assert ss._informative(["X"], None) is True
