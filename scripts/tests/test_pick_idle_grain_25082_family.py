"""La zone du grain, resolue dans le TAPIS (issue #25082, point C).

Le fait mesure (issue #25082, mesure 4) : sur 50 tirages de `--belt`,
`family` valait `null` sur 50. La cause n'est pas une correspondance qui
manque : c'est que la resolution de zone vivait dans `weight()`, c'est-a-dire
dans la voie PONDEREE, et que le tapis (`--belt`) trie et retient sans jamais
passer par `weight()`. Aucun grain du tapis n'avait donc de zone, et le
facteur de saturation -- le seul endroit ou la polarite `consolidation` pese
-- ne jouait sur rien.

Ces tests couvrent l'instrument (point C) : la zone est resolue, elle est
COMPTEE, et l'absence de zone se distingue de l'absence de mesure. Ils ne
touchent pas au tirage : la repondersion qui consommera ces zones (points A
et B) est une autre PR, et celle-ci n'eprouve que la mesure.

Aucun appel reseau : la resolution est une fonction pure sur des dicts.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402

TEXTE = "MyIA.AI.Notebooks/GenAI/Texte"
CHAINES = "MyIA.AI.Notebooks/GameTheory/Chaines"


def _issue(number: int, title: str, body: str = "", parent: int | None = None) -> dict:
    return {"number": number, "title": title, "body": body, "parent": parent,
            "labels": [], "polarity": "neutral", "klass": "grain"}


def _ponderee(number: int, title: str) -> dict:
    """Un grain complet pour `weight()` : la voie ponderee lit des champs
    de surface que le grain du tapis porte aussi."""
    it = _issue(number, title)
    it.update({"age": 30.0, "idle": 30.0, "idle_since_delivery": 30.0,
               "genre": "notebook-python", "genre_confident": True})
    return it


def _series(**kwargs) -> dict:
    base = {"prs": 3, "new_notebooks": 2, "numbers": [1, 2]}
    base.update(kwargs)
    return base


# --- la resolution ------------------------------------------------------------


def test_le_titre_qui_nomme_la_serie_resout_la_zone():
    """Le grain nomme sa zone dans son titre : la zone est resolue."""
    pool = [_issue(1, "GenAI/Texte : renumerotation du carnet 04")]
    signal = pig.resolve_belt_families(pool, {}, {TEXTE: _series()})
    assert pool[0]["family"] == TEXTE
    assert pool[0]["family_new_notebooks"] == 2
    assert signal["resolved"] == 1
    assert signal["total"] == 1
    assert signal["measured"] is True


def test_le_corps_sert_quand_le_titre_est_muet():
    """Le titre muet ne condamne pas la resolution : le corps parle aussi."""
    pool = [_issue(2, "Consolidation de la serie", body=f"travail sur {TEXTE}")]
    pig.resolve_belt_families(pool, {}, {TEXTE: _series()})
    assert pool[0]["family"] == TEXTE


def test_une_pr_mergee_attribue_la_zone_a_l_issue_quelle_cite():
    """L'attribution par PR mergee prime : elle est factuelle."""
    pool = [_issue(3, "Un titre muet")]
    pig.resolve_belt_families(pool, {3: CHAINES}, {CHAINES: _series()})
    assert pool[0]["family"] == CHAINES


def test_le_parent_herite_de_la_zone_de_l_epic():
    """Un grain sans PR citante herite de la zone de son EPIC parent."""
    pool = [_issue(4, "Grain fils", parent=900)]
    pig.resolve_belt_families(pool, {900: TEXTE}, {TEXTE: _series()})
    assert pool[0]["family"] == TEXTE


def test_une_zone_absente_est_comptee_comme_absente_et_non_comme_une_erreur():
    """Mesure faite, zone introuvable : c'est une MESURE, pas un echec."""
    pool = [_issue(5, "Un grain qui ne nomme aucune serie")]
    signal = pig.resolve_belt_families(pool, {}, {TEXTE: _series()})
    assert pool[0]["family"] is None
    assert pool[0]["family_new_notebooks"] == 0
    assert signal["measured"] is True
    assert signal["resolved"] == 0
    assert signal["ratio"] == 0.0


def test_une_mesure_non_faite_est_distinguee_d_une_zone_absente():
    """L'organe amont n'a pas repondu : la zone est absente PARCE QUE RIEN n'a
    ete mesure. Le signal doit le dire, sinon il se lit comme « le grain ne
    porte aucune zone »."""
    pool = [_issue(6, "GenAI/Texte : renumerotation")]
    signal = pig.resolve_belt_families(pool, {}, {}, measured=False)
    assert signal["measured"] is False
    assert signal["resolved"] == 0
    assert signal["total"] == 1


def test_un_pool_vide_ne_donne_pas_un_ratio_inexistant():
    signal = pig.resolve_belt_families([], {}, {TEXTE: _series()})
    assert signal["total"] == 0
    assert signal["ratio"] is None


# --- l'accord avec la voie ponderee -------------------------------------------


def test_le_tapis_et_la_voie_ponderee_resolvent_la_meme_zone():
    """C'est l'ACCORD qui prouve la reparation : les deux voies doivent
    nommer la meme zone pour le meme grain. Une voie qui repond `null` et
    l'autre une zone, c'est le bug d'origine."""
    item = _ponderee(7, "GenAI/Texte : consolidation")
    series = {TEXTE: _series()}
    i2f = {}
    ponderee = dict(item)
    pig.weight(ponderee, None, None, series, i2f)
    pig.resolve_belt_families([item], i2f, series)
    assert item["family"] == ponderee["family"] == TEXTE
    assert item["family_new_notebooks"] == ponderee["family_new_notebooks"]


def test_le_tapis_ne_change_aucun_tirage():
    """L'instrument ne doit pas deplacer le grain servi : c'est une mesure,
    pas une repondersion (la repondersion est le point A/B, une autre PR)."""
    items = [
        {"number": 10, "title": "a", "last_delivery_stamp": "2026-01-01T00:00:00Z",
         "created_at": "2026-01-01T00:00:00Z"},
        {"number": 11, "title": "b", "last_delivery_stamp": None,
         "created_at": "2026-02-01T00:00:00Z"},
    ]
    avant = [set(it) for it in items]
    numeros = [it["number"] for it in items]
    pig.resolve_belt_families(items, {}, {TEXTE: _series()})
    assert [it["number"] for it in items] == numeros
    # Le seul ajout est la zone (et son compteur) -- rien d'autre.
    for it, cles_avant in zip(items, avant):
        assert set(it) - cles_avant == {"family", "family_new_notebooks"}


@pytest.mark.parametrize("titre,attendu", [
    ("GenAI/Texte : renumerotation", TEXTE),
    ("GameTheory/Chaines : paire 9", CHAINES),
])
def test_chaque_serie_connue_a_son_issue(titre, attendu):
    """Le texte ne distingue pas les series par la longueur de la chaine
    citee une fois : ce qui REPETE est le sujet."""
    pool = [_issue(20, titre)]
    series = {TEXTE: _series(), CHAINES: _series()}
    pig.resolve_belt_families(pool, {}, series)
    assert pool[0]["family"] == attendu
