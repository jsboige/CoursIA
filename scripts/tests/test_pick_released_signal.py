"""Tests du signal de livraison par `[RELEASED]` (#20351).

Le marqueur `[RELEASED]` a deux sens dans la flotte :

- une lane rend la main sur un item qu'elle n'a pas livre, bloque par une
  barriere reelle -> l'item **doit rester servi** par le tapis ;
- une lane rend la main en constatant que l'acceptance de l'item est **deja
  couverte** par un travail livre -> l'item **ne doit plus remonter**.

La sonde pleine (`_delivered_state`) ne lisait que `[INFO] candidate-delivered` :
le second cas gardait une « derniere visite » ancienne et l'item revenait en
tete du tapis indefiniment (11 tetes de tapis mortes mesurees le 2026-10-11,
lane myia-po-2027:CoursIA).

Ce fichier verifie la REPARTITION des deux sens. Un detecteur se valide par
ses faux NEGATIFS : le cas « barriere » doit rester servi, et surtout les
livraisons de SOUS-GRAIN (une tranche, un carnet, un grain d'un item plus
large) ne doivent pas ecarter un item encore actionnable.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pick_idle_grain import (  # noqa: E402
    _delivered_state,
    _released_covers_acceptance,
)


def test_released_avec_acceptance_couverte_est_une_livraison():
    """Cas nominal de #20351 : l'acceptance est deja couverte."""
    bodies = [
        "[RELEASED] lane myia-po-2027:CoursIA -- acceptance deja couverte "
        "(verifie firsthand), rien de reparable par cette lane",
    ]
    assert _released_covers_acceptance(bodies[0]) is True
    assert _delivered_state(bodies) is True


def test_released_sans_motif_de_couverture_ne_livre_pas():
    """Faux negatif central : `[RELEASED]` nu = barriere, l'item reste servi."""
    bodies = [
        "[RELEASED] lane myia-po-2026:CoursIA -- levee du claim epic-wide : "
        "le grain part sur po-2024",
    ]
    assert _released_covers_acceptance(bodies[0]) is False
    assert _delivered_state(bodies) is False


def test_released_avec_negation_ne_livre_pas():
    """« l'acceptance n'est pas couverte » = l'autre cas : on rend la main."""
    bodies = [
        "[RELEASED] lane myia-po-2026:CoursIA -- l'acceptance n'est pas "
        "couverte ici, on rend la main au tapis",
    ]
    assert _released_covers_acceptance(bodies[0]) is False
    assert _delivered_state(bodies) is False


def test_negation_generic_ne_trip_pas_le_motif():
    """« pas de travail restant » n'est pas une negation du motif.

    Un garde-fou trop grossier (chercher « pas » partout) ecarterait des
    livraisons legitimes -- c'est un faux NEGATIF de la correction.
    """
    bodies = [
        "[RELEASED] lane myia-po-2027:CoursIA -- acceptance deja couverte, "
        "pas de travail restant",
    ]
    assert _released_covers_acceptance(bodies[0]) is True
    assert _delivered_state(bodies) is True


def test_accents_et_variantes_de_motif():
    for line in (
        "[RELEASED] lane x:y -- acceptance déjà couverte",
        "[RELEASED] lane x:y -- l'acceptance est couverte",
        "[RELEASED] lane x:y -- acceptance deja satisfaite",
        "[RELEASED] lane x:y -- acceptance deja livree",
        "[RELEASED] lane x:y -- rien à réparer ici",
    ):
        assert _released_covers_acceptance(line) is True, line


def test_livraison_de_sous_grain_ne_livre_pas():
    """Faux positif mesure (pool 512 issues) : une TRANCHE livree ne clot pas
    l'item qui en contient d'autres (#17578 : « la Tranche A est deja livree »
    alors que « Tranche B libre pour reprise »)."""
    bodies = [
        "[RELEASED] #17578 -- lane myia-po-2024:CoursIA -- claim Tranche A "
        "pose ce soir, libere sans edition : la Tranche A est deja livree sur "
        "main par PR #17582 (MERGED)",
    ]
    assert _released_covers_acceptance(bodies[0]) is False
    assert _delivered_state(bodies) is False


def test_perimetre_de_sous_item_rejete():
    for line in (
        "[RELEASED] lane x:y -- le carnet 03 est deja livre et enrichi sur main",
        "[RELEASED] lane x:y -- grain deja livre par la lane myia-po-2024",
        "[RELEASED] lane x:y -- la migration PT-05 est DEJA livree (#10487)",
    ):
        assert _released_covers_acceptance(line) is False, line


def test_scope_de_lane_rejete():
    """« aucune tranche restante POUR CETTE LANE » : les autres lanes peuvent
    encore servir l'item (#18767 : 4 sous-modules sur 5 a couvrir)."""
    bodies = [
        "[RELEASED] lane myia-po-2027:CoursIA -- levee du claim epic-wide : la "
        "substance (bump Argumentum) est livree et mergee (PR #21320) ; "
        "aucune tranche restante pour cette lane.",
    ]
    assert _released_covers_acceptance(bodies[0]) is False
    assert _delivered_state(bodies) is False


def test_mention_en_prose_ne_livre_pas():
    """L'en-tete doit etre en debut de ligne (convention du protocole)."""
    bodies = [
        "Je note ici que la forme [RELEASED] acceptance deja couverte est "
        "employee par d'autres lanes, mais ce commentaire n'est pas un marqueur.",
    ]
    assert _released_covers_acceptance(bodies[0]) is False
    assert _delivered_state(bodies) is False


def test_retractation_posterieure_desarme_la_livraison():
    """L'etat reste ordonne : une retractation posterieure desarme."""
    bodies = [
        "[RELEASED] lane myia-po-2027:CoursIA -- acceptance deja couverte",
        "[NOT-DELIVERED] lane myia-ai-01:CoursIA -- livraison partielle, "
        "l'item revient sur le tapis",
    ]
    assert _delivered_state(bodies) is False


def test_marqueur_posterieur_rearme_la_livraison():
    bodies = [
        "[RELEASED] lane myia-po-2027:CoursIA -- acceptance deja couverte",
        "[NOT-DELIVERED] lane myia-ai-01:CoursIA -- livraison partielle",
        "[INFO] candidate-delivered lane myia-po-2027:CoursIA -- preuve en "
        "commentaire",
    ]
    assert _delivered_state(bodies) is True


def test_couverture_dans_un_commentaire_ulterieur_est_vue():
    """L'ordre ne doit pas cacher une couverture posee plus tard."""
    bodies = [
        "Un commentaire sans marqueur.",
        "[RELEASED] lane myia-po-2027:CoursIA -- acceptance deja couverte",
    ]
    assert _delivered_state(bodies) is True
