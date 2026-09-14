"""Tests de l'admission sous restriction de secheresse (G-VAR-1).

La restriction de secheresse (#13086) donnait une probabilite **exactement
nulle** aux items dont le genre n'est pas CONTENU. Deux de ses exclusions
portaient sur un verdict de genre que l'organe ne pouvait pas soutenir :

1. les **umbrellas** -- tirer une Epic veut dire creer un sous-grain dedans
   (R5 de proactive-coordination), donc le genre de l'Epic ne decrit jamais
   le livrable ;
2. les items dont le genre vient du **repli** de `infer_genre` (aucune regle
   de titre matchee, defaut `docs`) -- une absence de signal n'est pas un
   verdict META.

Mesure du 2026-09-12, 322 issues ouvertes : 72 des 115 umbrellas classees
META l'etaient par ce repli, et la restriction retirait **34 Epics sur 64**
du tirage des lanes en secheresse -- dont #15475 (ICT Toolkit), #15397
(Thom), #13992 (Matrix Profile), #13924-26 (ADK / BigQuery), #14467 (reward
hacking), #4588 (IIT -> ICT). Aucune n'est de la documentation.

Un detecteur se valide par ses faux negatifs : le controle positif ci-dessous
(les genres META reellement annonces restent exclus) est AUSSI obligatoire
que le reste. Sans lui, ce fichier serait vert alors meme que la correction
aurait desarme G-VAR-1 -- ce qui rendrait au picker la monoculture que le
garde existe pour briser.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pick_idle_grain import (  # noqa: E402
    CONTENU,
    META,
    drought_admits,
    genre_signal_present,
    infer_genre,
)


def item(genre, klass="grain", confident=True):
    return {"genre": genre, "klass": klass, "genre_confident": confident}


# --------------------------------------------------------------------------
# Controle POSITIF -- les dents du garde sont conservees
# --------------------------------------------------------------------------

@pytest.mark.parametrize("genre", sorted(META))
def test_positive_control_declared_meta_grain_stays_excluded(genre):
    """Un grain META dont le genre est SOUTENU reste exclu. C'est la
    raison d'etre du garde : sans cette ligne, la correction le desarme."""
    assert drought_admits(item(genre, confident=True)) is False


@pytest.mark.parametrize("title", [
    "ci(infra): variance 3-4x du pool self-hosted coursia-ephemeral",
    "tooling(#5081): inventaire canonique des noms, kernels, cibles",
    "docs(symboliclearning): reconcilier catalogue, compteurs et structure",
    "guard(#5081): securiser les renames -- collisions, suffixes",
    "fix(ci): le sentinel d'arret gracieux survit au reboot",
])
def test_positive_control_real_meta_titles_carry_a_signal(title):
    """Mesure du 2026-09-12 : le travail META reel ANNONCE son genre.

    La sequence guard -> tooling -> docs -> test que ce garde existe pour
    briser reste donc exclue : ces titres matchent une regle, leur genre
    est soutenu, et le test precedent les exclut."""
    assert genre_signal_present(title, []) is True
    assert infer_genre(title, []) in META
    assert drought_admits(item(infer_genre(title, []), confident=True)) is False


# --------------------------------------------------------------------------
# Les trois cas d'admission
# --------------------------------------------------------------------------

@pytest.mark.parametrize("genre", sorted(CONTENU))
def test_content_genre_is_admitted(genre):
    """Cas d'origine, inchange."""
    assert drought_admits(item(genre)) is True


@pytest.mark.parametrize("genre", sorted(META))
def test_umbrella_is_admitted_whatever_its_own_genre(genre):
    """Une Epic est admise quel que soit SON genre : le livrable est le
    sous-grain cree dedans, pas l'Epic. L'obligation de contenu n'est pas
    levee, elle se deplace -- et la banniere le dit."""
    assert drought_admits(item(genre, klass="umbrella")) is True


@pytest.mark.parametrize("genre", sorted(META))
def test_fallback_genre_is_admitted(genre):
    """Genre non soutenu (repli de l'inference) : admis. Une absence de
    signal ne vaut pas un verdict META."""
    assert drought_admits(item(genre, klass="grain", confident=False)) is True


@pytest.mark.parametrize("title", [
    "[EPIC][ICT] Toolkit multi-instrument de mesure et d'interventions causales",
    "[EPIC] Thom -- langage, agents transparents et singularites",
    "ML-11 (Python) : Matrix Profile multidimensionnel -- detection",
    "feat(adk): migrer Track2 vers le vrai runtime Google ADK",
    "Reward hacking : mesurer la forme forte de Goodhart sans nouveau run",
])
def test_buried_content_titles_fall_through_and_are_admitted(title):
    """Les titres mesures que la restriction enterrait. `infer_genre` les
    rend `docs` **par defaut**, sans qu'aucune regle ne matche."""
    assert genre_signal_present(title, []) is False
    assert infer_genre(title, []) == "docs"
    it = item(infer_genre(title, []), klass="grain", confident=False)
    assert drought_admits(it) is True


# --------------------------------------------------------------------------
# Le defaut de repli lui-meme
# --------------------------------------------------------------------------

def test_fallback_default_is_a_meta_genre():
    """La cause racine : le defaut de `infer_genre` est `docs`, un genre
    META. Si ce defaut changeait de classe, ce fichier devrait etre relu."""
    assert infer_genre("zzzz aucun mot-cle de genre zzzz", []) == "docs"
    assert "docs" in META


def test_genre_confident_absent_defaults_to_soutenu():
    """Fail vers l'exclusion quand la cle manque : un appelant qui ne pose
    pas `genre_confident` ne doit pas elargir le tirage par inadvertance."""
    assert drought_admits({"genre": "docs", "klass": "grain"}) is False


def test_positive_control_the_old_predicate_buried_these_epics():
    """Controle positif du DEFAUT lui-meme.

    L'ancien predicat etait `it["genre"] in CONTENU` seul. Sans cette
    ligne, rien dans ce fichier ne prouve que la correction corrige
    quelque chose : les tests ci-dessus passeraient a l'identique sur un
    organe qui n'aurait jamais eu le defaut.
    """
    def ancien_predicat(it):
        return it["genre"] in CONTENU

    enterrees = [
        "[EPIC][ICT] Toolkit multi-instrument de mesure et d'interventions causales",
        "[EPIC] Thom -- langage, agents transparents et singularites",
        "ML-11 (Python) : Matrix Profile multidimensionnel -- detection",
    ]
    for title in enterrees:
        it = item(infer_genre(title, []), klass="umbrella", confident=False)
        assert ancien_predicat(it) is False, f"le defaut ne se reproduit pas : {title}"
        assert drought_admits(it) is True, f"la correction ne mord pas : {title}"
