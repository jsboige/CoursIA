"""Les VAGUES de la prise en charge : la file se remplit, ou le pool est vide.

Ce que ces tests prouvent :

- la qualification **ouvre la vague suivante** tant que la file n'est pas
  pleine (le cas mesure du 18/11 : les 24 candidats de la vague 0 sont tous
  ecartes -- servir 0 grain alors que le pool en contient serait un echec de
  methode) ;
- une vague est le **bloc suivant** du pool classe : sur un pool d'un multiple
  du bloc, deux vagues successives sont disjointes (la vague herite le
  retour-au-debut de la rotation, comme la fenetre) ;
- la file pleine **arrete** le balayage, et le plafond de vagues tient ;
- le **mur** (l'echeance) arrete les vagues comme il arrete la qualification :
  un refus, jamais un demi-resultat.

Aucun test ne touche le reseau : l'organe de qualification est simule.
"""
from __future__ import annotations

import sys
import tempfile
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_age, tapis_ancre, tapis_rotation, tapis_vagues  # noqa: E402
from coordination import tapis_qualification as tq  # noqa: E402
from coordination.tapis_preuve import Preuve  # noqa: E402


pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 18, 17, 20, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
GRAINS = 8
TAILLE = 24  # le bloc servi : 3 x grains, comme le tirage leger


class _Grain:
    """Un grain minimal : l'ordre classe ne lit que son numero."""

    def __init__(self, numero: int):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.visites = 0
        self.conteneur = False
        self.notes: list[str] = []


def _simule(accepte: set[int], arrete: bool = False):
    """Un organe de qualification simule : il refuse tout sauf `accepte`.

    Il note aussi les candidats recus, vague par vague : les tests verifient
    ainsi que les vagues sont disjointes.
    """
    vus: list[list[int]] = []

    def _q(candidats, lane, maintenant, jours, prs, citations, run,
           echeance=None, lot=50, horloge=None, debut=None, preuve=None):
        vus.append(list(candidats))
        servis = [_Grain(n) for n in candidats if n in accepte]
        ecartes = {n: {"numero": n, "code": "LABEL", "motif": "simule"}
                   for n in candidats if n not in accepte}
        chrono = {"secondes": 0.1,
                  "premier_servable_s": 0.1 if servis else None}
        return servis, ecartes, [], arrete, 1, chrono

    _q.vus = vus
    return _q


def _ordre(n: int) -> list[_Grain]:
    return [_Grain(1000 + i) for i in range(n)]


def _vagues(accepte: set[int], monkeypatch, max_vagues: int = 4,
            arrete: bool = False, pool: int = 48, grains: int = GRAINS):
    """Les vagues sur un pool de `pool` grains, sans reseau.

    L'etat d'ancre est ISOLE (un repertoire temporaire par appel) : sinon la
    file d'attente accumulee par les tests precedents -- ou par les tours
    reels de la lane -- separe le pool et le nombre de vagues change.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT,
                       tempfile.mkdtemp(prefix="tapis-vagues-"))
    simule = _simule(accepte, arrete)
    monkeypatch.setattr(tapis_vagues.tq, "qualifier", simule)
    servis, ecartees, rapport = tapis_vagues.vagues(
        _ordre(pool), [], LANE, MAINTENANT, 45, [], None, grains,
        max_vagues, taille=TAILLE, echeance=None, debut=0.0)
    return servis, ecartees, rapport, simule


def test_la_vague_suivante_ouvre_la_file(monkeypatch):
    """La vague 0 entierement ecartee ouvre la vague 1 : la file se remplit.

    Les vagues suivent la selection par AGE (mandat du 22/11) : la vague 1
    est le bloc SUIVANT de l'ordre d'age, pas un retour au debut de la
    rotation par numero.
    """
    grains = _ordre(48)
    bloc1, _ = tapis_rotation.bloc(grains, [], GRAINS, TAILLE, LANE,
                                     MAINTENANT, bloc_suivant=1,
                                     ages_g=tapis_age.trier(grains, MAINTENANT),
                                     exclus_g=set())
    accepte = {bloc1[0].numero}
    services, ecartees, rapport, _ = _vagues(accepte, monkeypatch, grains=1)
    assert rapport["vagues"][0]["servis"] == 0
    assert rapport["vagues"][1]["servis"] == 1
    assert [s.numero for s in services] == [bloc1[0].numero]
    assert ecartees, "les ecarts restent affiches"


def test_le_plafond_de_vagues_tient_la_file(monkeypatch):
    """Une file qui ne se remplit pas s'arrete au plafond : 4 vagues au plus."""
    _, _, rapport, _ = _vagues({1000}, monkeypatch, pool=192)
    assert rapport["vagues_jouees"] == rapport["vagues_max"] == 4


def test_les_vagues_sont_disjointes(monkeypatch):
    """Sur un pool de trois blocs, trois vagues ne se recouvrent pas."""
    _, _, _, simule = _vagues(set(), monkeypatch, max_vagues=3, pool=72)
    vus = simule.vus
    assert len(vus) == 3
    for i in range(len(vus) - 1):
        assert not set(vus[i]) & set(vus[i + 1]), "deux vagues se recouvrent"


def test_la_file_pleine_arrete_le_balayage(monkeypatch):
    """Des que la file est pleine, aucune vague supplementaire n'est ouverte."""
    services, _, rapport, _ = _vagues(set(range(1000, 1100)), monkeypatch)
    assert rapport["vagues_jouees"] == 1
    assert len(services) >= GRAINS


def test_le_plafond_de_vagues_tient(monkeypatch):
    """Un pool qui ne donne rien ne fait pas balayer le pool entier."""
    services, ecartees, rapport, _ = _vagues(set(), monkeypatch, max_vagues=3,
                                              pool=192)
    assert rapport["vagues_jouees"] == 3
    assert rapport["vagues_max"] == 3
    assert services == []
    assert ecartees, "les refus restent affiches"


def test_le_mur_arrete_les_vagues(monkeypatch):
    """Le mur (l'echeance) arrete les vagues : un refus, pas un demi-resultat."""
    _, _, rapport, _ = _vagues(set(), monkeypatch, arrete=True)
    assert rapport["vagues_jouees"] == 1
    assert rapport["vagues"][0]["servis"] == 0


# --- LA PREUVE DE DIFF SUR LA VOIE DES VAGUES (revue du peer, 19/11) ----
#
# La voie des vagues QUALIFIE : elle fait passer le lot par le meme organe
# que la voie nominative. Un marqueur `[DELIVERED]` y DESIGNE une PR a
# verifier ; la preuve, c'est le diff de cette PR. Un marqueur SANS diff
# probant n'est pas une livraison : le grain reste servable.

MARQUEUR = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242 -- "
            "paths: scripts/coordination/tapis_diff.py")
#: Le marqueur SANS perimetre : les regles d'ecart le prennent pour une
#: livraison. C'est lui que la preuve doit contredire.
MARQUEUR_SANS_PATHS = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242"
ATTRIBUTION = ("[CLAIMED] lane myia-ai-01:CoursIA-2 -- paths: "
               "scripts/coordination/tapis_diff.py")
FICHIER = "scripts/coordination/tapis_diff.py"


def _issue_7(marqueur: str = MARQUEUR, autres: list[str] | None = None) -> dict:
    """L'issue qui porte le marqueur de livraison et son attribution."""
    commentaires = [{"created_at": "2026-11-10T00:00:00Z", "author": "jsboige",
                     "body": marqueur}]
    for i, autre in enumerate(autres or []):
        commentaires.append({"created_at": f"2026-11-1{i}T00:00:00Z",
                             "author": "jsboige", "body": autre})
    return {"number": 7, "title": "Grain 7", "body": "",
            "created_at": "2026-11-01T00:00:00Z",
            "comments": commentaires,
            "comments_total": len(commentaires), "labels": []}


def _vague_avec_lecture(monkeypatch, tmp_path, preuve_gh,
                        marqueur: str = MARQUEUR,
                        autres: list[str] | None = None):
    """Les vagues sur un grain reellement lu, avec la preuve du diff voulue.

    La lecture est simulee (aucun reseau) ; la qualification, elle, est la
    vraie : c'est elle qui applique la preuve.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    issue = _issue_7(marqueur, autres)
    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier",
                        lambda run, depot, numeros=None: {7: issue})
    monkeypatch.setattr(tq.tapis_fenetre, "fil_complet",
                        lambda numero: issue["comments"])
    monkeypatch.setattr(tapis_vagues.tapis_diff, "preuve_gh",
                        lambda run: preuve_gh)
    return tapis_vagues.vagues([_Grain(7)], [], LANE, MAINTENANT, 45, [],
                                None, 1, 1, taille=1, echeance=None,
                                debut=0.0)


def test_un_marqueur_sans_diff_probant_n_est_pas_une_livraison(monkeypatch,
                                                               tmp_path):
    """TEMOIN (revue du peer, 19/11) : la voie des vagues refuse le marqueur.

    Le marqueur, sans perimetre, est pris pour une livraison par les regles
    d'ecart. La preuve est absente (le diff n'est pas lisible) : le grain
    n'est donc pas ecarte LIVREE, il reste **servable** -- il revient dans
    la file.
    """
    servis, ecartees, rapport = _vague_avec_lecture(
        monkeypatch, tmp_path, lambda pr: None,
        marqueur=MARQUEUR_SANS_PATHS)
    assert 7 not in ecartees, "un marqueur sans diff n'est pas une livraison"
    assert [e.numero for e in servis] == [7], "le grain reste servable"


def test_un_diff_probant_livre_le_grain_par_la_vague(monkeypatch, tmp_path):
    """Le CONTRE-TEMOIN : avec la preuve, le meme grain est livre.

    Meme voie, meme perimetre : la seule difference est la preuve. Sans
    elle le grain reste dans la file ; avec elle, il sort.
    """
    preuve = Preuve((FICHIER,), "CLOSED", True)
    servis, ecartees, rapport = _vague_avec_lecture(
        monkeypatch, tmp_path, lambda pr: preuve,
        marqueur=MARQUEUR, autres=[ATTRIBUTION])
    assert [e.numero for e in servis] == [], "une livraison prouvee n'est pas servie"
    assert ecartees[7]["code"] == "LIVREE"
    assert "couvre" in ecartees[7]["motif"]
