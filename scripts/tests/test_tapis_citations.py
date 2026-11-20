"""Le travail EN COURS compte comme une visite (famine du 19/11/2026).

Le classement leger ne comptait que les commits **merges** : une issue sur
laquelle huit PRs sont ouvertes -- pas encore mergees -- restait a
`visites = 0`, donc en tete de rotation. Le tapis la resservait alors que le
travail etait deja fait : l'umbrella #27338, cree le matin, a ete servie
sept fois dans la journee pendant que des issues anciennes n'attendaient
aucune PR.

Le correctif compte les citations des PRs **ouvertes** avec la meme regle
que les commits merges : une mention `#N` dans le corps. La date retenue est
la derniere activite de la PR : une PR abandonnee depuis des mois ne tient
pas une issue en tete.
"""
import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_citations
from coordination import tapis_universel as tu

NOW = datetime(2026, 11, 19, 12, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


def _meta(n: int, titre: str = "Grain") -> dict:
    return {"number": n, "title": titre, "labels": [],
            "created_at": "2026-01-01T00:00:00Z"}


def _pr(n: int, corps: str, jour: str = "2026-11-19T09:00:00Z") -> dict:
    return {"number": n, "title": "PR", "body": corps,
            "created_at": jour, "updated_at": jour}


def test_une_pr_ouverte_qui_cite_une_issue_compte_une_visite():
    cites = tapis_citations.des_prs_ouvertes([_pr(900, "See #42")])
    assert list(cites) == [42]
    assert cites[42][0]["date"] == "2026-11-19T09:00:00Z"


def test_une_pr_ne_se_cite_pas_elle_meme():
    """L'auto-reference est exclue : une PR ne se cite pas elle-meme."""
    assert tapis_citations.des_prs_ouvertes([_pr(900, "See #900")]) == {}


def test_le_classement_leger_voit_le_travail_en_cours():
    """Sans les PRs ouvertes, l'issue travailsee reste a zero visite."""
    metas = [_meta(1, "Ancienne issue"), _meta(2, "Issue travaillee")]
    etats = tu.etats_leger(metas, {}, NOW)
    par_num = {e.numero: e for e in etats}
    assert par_num[2].visites == 0, "seuls les commits merges comptent"


def test_deux_prs_ouvertes_font_deux_visites():
    metas = [_meta(1, "Ancienne issue"), _meta(2, "Issue travaillee")]
    cites = tapis_citations.des_prs_ouvertes([_pr(901, "See #2"),
                                               _pr(902, "Part of #2")])
    etats = tu.etats_leger(metas, {}, NOW, cites)
    par_num = {e.numero: e for e in etats}
    assert par_num[1].visites == 0
    assert par_num[2].visites == 2, "deux PRs ouvertes = deux visites"


def test_l_issue_en_cours_recule_derriere_une_issue_jamais_servie():
    """L'issue travaillee sort de la tete : une issue jamais servie passe devant."""
    metas = [_meta(1, "Ancienne issue"), _meta(2, "Issue travaillee")]
    cites = tapis_citations.des_prs_ouvertes([_pr(901, "See #2"),
                                               _pr(902, "Part of #2"),
                                               _pr(903, "See #2")])
    etats = tu.etats_leger(metas, {}, NOW, cites)
    file = tu.rotation_universelle(etats, LANE, NOW, 2, "g")
    assert [e.numero for e in file] == [1, 2], "l'issue en cours recule"


def test_une_pr_abandonnee_ne_tient_pas_une_issue_en_tete():
    """La date retenue est la derniere ACTIVITE : une PR vieille de trois mois
    ne compte pas dans la fenetre du tour."""
    metas = [_meta(1, "Ancienne issue"), _meta(2, "Issue travaillee")]
    cites = tapis_citations.des_prs_ouvertes(
        [_pr(901, "See #2", "2026-08-01T09:00:00Z")])
    etats = tu.etats_leger(metas, {}, NOW, cites)
    par_num = {e.numero: e for e in etats}
    assert par_num[2].visites == 0, "hors fenetre du tour"
    assert par_num[2].visites_total == 1, "mais elle reste comptee au total"
