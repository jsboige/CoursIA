#!/usr/bin/env python3
"""Les temoins de la FAMINE, mesures sur le LOT PUBLIC (revue du 19/11).

Le peer a mesure deux famines sur la voie publique :

- **cas A** : un pool de 80 grains, priorite decroissante, taille 40, un
  seul candidat lu par tour -> **4 numeros lus sur 80** en 400 tours ;
- **cas B** : 6 grains et 2 conteneurs, taille 2, un lu par tour ->
  6/6 grains mais **0/2 conteneurs** (le conteneur etait exilie en fin de
  lot, il n'avait donc jamais de tour).

Ces deux temoins sont **la** regression : ils se rejouent ici sur le lot
public (`coordination.tapis_public`), pas sur une reconstruction de la
mesure -- un temoin qui ne teste pas la voie reelle ne prouve rien.
"""
import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import (tapis_ancre, tapis_citations, tapis_equilibre,
                         tapis_leger, tapis_public, tapis_universel,
                         tapis_verdict)

LANE = "test:famine"
MAINTENANT = datetime(2026, 11, 19, 12, 0, tzinfo=UTC)


class Grain:
    """Le minimum qu'un grain doit porter pour composer un lot."""

    def __init__(self, numero: int, conteneur: bool = False):
        self.numero = numero
        self.conteneur = conteneur


def _tour(grains: list, conteneurs: list, n_grains: int, taille: int,
          budget: int) -> list[int]:
    """Un tour de lecture sur le lot PUBLIC : proposition, lecture, verdict."""
    lot, _ = tapis_public.lot_public(LANE, grains, conteneurs, n_grains,
                                      taille, MAINTENANT)
    lus = [g.numero for g in lot][:budget]
    tapis_verdict.avancer(LANE, {n: object() for n in lus}, {})
    return lus


def test_le_lot_public_couvre_le_pool_entier(monkeypatch, tmp_path):
    """Cas A : les 80 numeros du pool sont lus (le peer mesurait 4/80)."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    pool = [Grain(n) for n in range(80, 0, -1)]
    lus: list[int] = []
    for _ in range(400):
        lus.extend(_tour(pool, [], 40, 40, 1))
    assert len(set(lus)) == 80, \
        f"le pool n'est pas couvert : {len(set(lus))}/80 lus en 400 tours"


def test_le_lot_public_donne_un_creneau_a_chaque_classe(monkeypatch, tmp_path):
    """Cas B : les 6 grains ET les 2 conteneurs sont lus (le peer mesurait 0/2)."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    grains = [Grain(n) for n in range(1, 7)]
    conteneurs = [Grain(101 + n, conteneur=True) for n in range(2)]
    lus: list[int] = []
    for _ in range(40):
        lus.extend(_tour(grains, conteneurs, 2, 2, 1))
    lus = set(lus)
    assert {n for n in lus if n <= 6} == set(range(1, 7)), \
        "un grain n'a pas ete lu"
    assert {n for n in lus if n > 100} == {101, 102}, \
        "un conteneur n'a pas de creneau de lecture"


# --- L'EQUITE DU DISPATCH : une racine deja servie ne repasse pas devant ----
# (mission du coordinateur du 19/11, cas reel #27338)

def _meta(n: int, titre: str, cree: str = "2026-02-01T00:00:00Z") -> dict:
    return {"number": n, "title": titre, "labels": [], "created_at": cree}


def test_le_lot_ordinaire_ne_ressert_pas_une_racine_deja_servie(monkeypatch, tmp_path):
    """Le cas reel #27338 : huit PRs ouvertes, douze issues anciennes a zero.

    L'umbrella #27338 a ete servie huit fois dans la journee (huit PRs
    distinctes sur huit carnets). Le lot **ordinaire** ne doit pas la
    resservir avant que les issues a premiere visite aient ete servies :
    c'est le mandement d'equite du 16/11, et le cas que le user a signale.

    Le compteur est celui de la voie reelle : les huit PRs ouvertes qui la
    citent sont comptees par `tapis_citations` -- pas un score prepare.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    anciennes = [11698, 11703, 14528, 14529, 14769, 14926, 15002, 15293,
                 17845, 19280, 4362, 4427]
    metas = [_meta(n, "Ancienne issue") for n in anciennes]
    metas.append(_meta(27338, "Umbrella des passages", cree="2026-11-19T05:41:02Z"))
    prs = [{"number": 900 + k, "title": "PR", "body": "Part of #27338",
            "created_at": "2026-11-19T06:00:00Z",
            "updated_at": "2026-11-19T12:00:00Z"} for k in range(8)]
    etats = tapis_universel.etats_leger(metas, {}, MAINTENANT, prs)
    par_num = {e.numero: e for e in etats}
    assert par_num[27338].visites == 8, "les huit PRs ouvertes ne sont pas vues"
    assert par_num[27338].cle_service == "2026-11-19T06:00:00Z",         "la cle de service n'est pas la date de la derniere PR qui couvre"
    assert all(par_num[n].visites == 0 for n in anciennes)
    grains_, conteneurs = tapis_leger._ordre(etats, "test:famine", MAINTENANT, "g")
    lot, _ = tapis_public.lot_public("test:famine", grains_, conteneurs,
                                      len(metas), len(metas), MAINTENANT)
    nums = [g.numero for g in lot]
    assert set(nums[:len(anciennes)]) == set(anciennes), \
        "une premiere visite a ete sautee"
    assert nums.index(27338) == len(anciennes), \
        "la racine deja servie repasse devant les premieres visites"


def test_la_racine_servie_plusieurs_fois_passe_derriere_une_issue_servie_une_fois(
        monkeypatch, tmp_path):
    """Le temoin DISCRIMINANT de la famine, dans le modele de la CLE.

    Mandat du 19/11 : l'ordre est la date de la derniere PR qui **couvre** le
    grain. Une racine servie huit fois AUJOURD'HUI passe donc derriere une
    issue servie HIER -- meme si la racine est plus ancienne.

    Le temoin rejoue les deux colonnes : sans les PRs ouvertes, la racine,
    jamais servie, passe devant (l'inversion est presente) ; avec elles, elle
    passe derriere. Un temoin qui ne rejouerait qu'une colonne ne prouverait
    rien.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    metas = [_meta(27338, "Racine des passages", cree="2026-01-01T00:00:00Z"),
             _meta(27399, "Issue servie hier", cree="2026-01-02T00:00:00Z")]
    cite_merges = {27399: [{"sha": "abc1234", "date": "2026-11-18T09:00:00Z",
                             "sujet": "Closes #27399", "ferme": True,
                             "canonique": True}]}
    prs = [{"number": 900 + k, "title": "PR", "body": "Part of #27338",
            "created_at": "2026-11-19T06:00:00Z",
            "updated_at": "2026-11-19T12:00:00Z"} for k in range(8)]

    def _rangs(les_prs):
        etats = tapis_universel.etats_leger(metas, cite_merges, MAINTENANT, les_prs)
        ordre = tapis_equilibre.ordre(etats, etats, "g", MAINTENANT,
                                       rotation=False)
        nums = [e.numero for e in ordre]
        return nums.index(27338), nums.index(27399)

    avant_racine, avant_servie = _rangs([])
    assert avant_racine < avant_servie,         "le temoin ne reproduit plus l'inversion : il ne prouve plus rien"

    apres_racine, apres_servie = _rangs(prs)
    assert apres_servie < apres_racine,         "la racine servie huit fois repasse devant une issue servie une fois"
