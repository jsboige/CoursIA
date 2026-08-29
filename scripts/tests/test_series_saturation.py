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
"""
from __future__ import annotations

import sys
from pathlib import Path

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


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
