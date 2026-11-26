"""Temoins de la VOIE D'ECRITURE du balayage de suspicion (#28454).

Le balayage (`scripts/coordination/tapis_livraison.py`) pose un marqueur dans
le fil et un label candidat sur l'issue. La voie `--apply` ecrit -- c'est la
seule voie qui mute, et elle est donc la seule qui doit appliquer le VETO
HUMAIN : si une personne a retire le label candidat, le balayage ne peut pas
le reposer (il poserait sous le login partage, et sa pose deviendrait le
dernier evenement humain, effacant le veto du classificateur).

Ces temoins regardent les **ecritures** (marqueur + label), pas la
detection : la detection a ses propres temoins
(`test_candidate_delivered_chemins.py`).

Aucun test ne touche le reseau : `gh` est un faux.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_livraison as tl

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

REPO = "jsboige/CoursIA"

ISSUE = {"number": 42, "title": "Grain 42", "body": "Un grain ordinaire",
         "labels": [], "createdAt": "2026-11-01T00:00:00Z"}

SUSPECT = {"chemin": "docs/reference/exemple.md", "statut": "modified",
           "date": "2026-11-20T10:00:00Z", "sujet": "Fix: cite #42"}


def _balayage(monkeypatch, fil_=None, evenements_=None) -> list[str]:
    """Prepare un balayage a faux et rend la liste des ECRITURES vues."""
    ecritures: list[str] = []

    monkeypatch.setattr(tl.chemins, "touches_main",
                        lambda depot: {"docs/reference/exemple.md": {}})
    monkeypatch.setattr(tl, "pool", lambda repo, limit: [ISSUE])
    monkeypatch.setattr(tl, "prs_ouverts", lambda repo, limit=300: set())
    monkeypatch.setattr(tl, "suspecter",
                        lambda issue, touches, commentaires: [SUSPECT])
    monkeypatch.setattr(tl, "fil", lambda repo, number: fil_)
    monkeypatch.setattr(tl, "evenements", lambda repo, number: evenements_)
    monkeypatch.setattr(tl, "poster",
                        lambda repo, number, corps: ecritures.append(f"marqueur:{number}"))
    monkeypatch.setattr(tl, "poser_label",
                        lambda repo, number: ecritures.append(f"label:{number}"))
    return ecritures


def test_le_balayage_pose_le_marqueur_et_le_label_quand_nothing_ne_l_interdit(monkeypatch):
    """TEMOIN DE CONTROLE POSITIF : sans veto ni lecture incomplete, le
    balayage ecrit bien les deux choses.

    Sans ce temoin, les temoins « zero ecriture » ne prouveraient rien : ils
    passeraient aussi sur un balayage qui n'ecrit jamais.
    """
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=[])
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == ["marqueur:42", "label:42"], ecritures


def test_une_lecture_incomplete_du_fil_empêche_toute_ecriture(monkeypatch, capsys):
    """Le fil illisible -> ZERO ecriture (ni marqueur, ni label)."""
    ecritures = _balayage(monkeypatch, fil_=None, evenements_=[])
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "LECTURE INCOMPLETE" in capsys.readouterr().out


def test_une_lecture_incomplete_des_evenements_empêche_toute_ecriture(monkeypatch, capsys):
    """La timeline illisible -> ZERO ecriture."""
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=None)
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "LECTURE INCOMPLETE" in capsys.readouterr().out


def test_un_retrait_humain_du_label_empêche_toute_ecriture(monkeypatch, capsys):
    """Une personne a retire le label -> ZERO ecriture (le veto prime)."""
    evenements = [{"event": "unlabeled", "actor": "jsboige",
                   "created_at": "2026-11-22T10:00:00Z"}]
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=evenements)
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "VETO" in capsys.readouterr().out.upper()


def test_un_evenement_de_pose_humain_ne_bloque_pas_le_balayage(monkeypatch):
    """CONTROLE NEGATIF du veto : une pose humaine (et non un retrait) ne
    veto pas -- seule la pose sous le login partage est un risque, et c'est
    le RETRAIT qui fait veto."""
    evenements = [{"event": "labeled", "actor": "jsboige",
                   "created_at": "2026-11-22T10:00:00Z"}]
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=evenements)
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == ["marqueur:42", "label:42"], ecritures


# ---------------------------------------------------------------------------
# Les PAGES multiples de `gh api --paginate` (reserve du coordinateur du
# 26/11 sur #28454)
#
# `gh api --paginate` imprime un document JSON PAR PAGE : la sortie d'un fil
# ou d'une timeline de deux pages est `[{...}][{...}]`, qui n'est pas un JSON
# valide. Un `json.loads` unique levait `Extra data`, et la lecture rendait
# `None` -- donc un veto sur une reponse parfaitement correcte de GitHub.
#
# Ces temoins eprouvent les LECTEURS REELS : seul `gh` est factice (la
# reponse est choisie PAR APPEL). Les temoins precedents remplacaient
# `fil`/`evenements` par des listes -- ils ne pouvaient donc pas voir ce
# defaut.
# ---------------------------------------------------------------------------

#: Deux pages de commentaires (page 1 puis page 2).
PAGES_FIL = ('[{"created_at": "2026-11-20T10:00:00Z", "body": "premier"}]'
             '[{"created_at": "2026-11-21T10:00:00Z", "body": "second"}]')

#: Deux pages de timeline, sans retrait humain.
PAGES_TIMELINE = (
    '[{"event": "labeled", "label": {"name": "candidate-delivered"}, '
    '"actor": {"login": "jsboige"}, "created_at": "2026-11-20T10:00:00Z"}]'
    '[{"event": "labeled", "label": {"name": "candidate-delivered"}, '
    '"actor": {"login": "jsboige"}, "created_at": "2026-11-21T10:00:00Z"}]')

#: Deux pages de timeline, dont le RETRAIT du label est sur la seconde page.
PAGES_TIMELINE_RETRAIT = (
    '[{"event": "labeled", "label": {"name": "candidate-delivered"}, '
    '"actor": {"login": "jsboige"}, "created_at": "2026-11-20T10:00:00Z"}]'
    '[{"event": "unlabeled", "label": {"name": "candidate-delivered"}, '
    '"actor": {"login": "jsboige"}, "created_at": "2026-11-22T10:00:00Z"}]')


class _Reponse:
    """La sortie d'un `gh` factice."""

    def __init__(self, stdout: str, returncode: int = 0) -> None:
        self.stdout = stdout
        self.stderr = ""
        self.returncode = returncode


class _Subprocess:
    """Un module `subprocess` de substitution : seul `run` est utilise."""

    def __init__(self, run) -> None:
        self.run = run


def _gh_faux(ecritures: list[str], **reponses: str):
    """Un `gh` factice : la reponse est choisie PAR APPEL.

    `reponses` mappe un motif present dans la ligne de commande vers la sortie
    rendue. Un appel sans reponse declenche une erreur explicite : un temoin
    qui n'exerce pas le lecteur qu'il pretend eprouver ne prouve rien.
    """
    def run(args, **kwargs):
        cmd = [str(a) for a in args]
        if cmd and cmd[0] == "gh":
            cmd = cmd[1:]
        ligne = " ".join(cmd)
        for motif, sortie in reponses.items():
            if motif in ligne:
                return _Reponse(sortie)
        if cmd[:2] == ["issue", "comment"]:
            ecritures.append("marqueur")
            return _Reponse("")
        if cmd[:2] == ["issue", "edit"]:
            ecritures.append("label")
            return _Reponse("")
        raise AssertionError(f"appel gh inattendu : {ligne}")
    return run


def _balayage_complet(monkeypatch, **reponses: str) -> list[str]:
    """Un balayage ou les LECTEURS sont les vrais : seul `gh` est factice.

    `suspecter` et la lecture de `main` sont factices (ils ne sont pas
    l'objet de la reserve) ; `fil`, `evenements`, `pool` et `prs_ouverts`
    sont les VRAIS, avec un `gh` qui repond en plusieurs pages.
    """
    ecritures: list[str] = []
    monkeypatch.setattr(tl.chemins, "touches_main",
                        lambda depot: {"docs/reference/exemple.md": {}})
    monkeypatch.setattr(tl, "suspecter",
                        lambda issue, touches, commentaires: [SUSPECT])
    monkeypatch.setattr(tl, "subprocess",
                        _Subprocess(_gh_faux(ecritures, **reponses)))
    return ecritures


def test_un_fil_de_deux_pages_est_lu_comme_un_fil_de_deux_commentaires(monkeypatch):
    """TEMOIN DE LECTURE : le fil de deux pages n'est plus une lecture ratee."""
    monkeypatch.setattr(tl, "subprocess", _Subprocess(_gh_faux(
        [], **{"issues/42/comments": PAGES_FIL})))
    lus = tl.fil(REPO, 42)
    assert isinstance(lus, list), f"lecture incomplete sur un fil lisible : {lus}"
    assert len(lus) == 2, lus
    assert [c["body"] for c in lus] == ["premier", "second"], lus


def test_une_timeline_de_deux_pages_est_lue_comme_une_timeline_de_deux_evenements(monkeypatch):
    """TEMOIN DE LECTURE : la timeline de deux pages n'est plus une lecture ratee."""
    monkeypatch.setattr(tl, "subprocess", _Subprocess(_gh_faux(
        [], **{"issues/42/timeline": PAGES_TIMELINE})))
    lus = tl.evenements(REPO, 42)
    assert isinstance(lus, list), f"lecture incomplete sur une timeline lisible : {lus}"
    assert len(lus) == 2, lus


def test_deux_pages_sans_veto_posent_le_marqueur_et_le_label(monkeypatch):
    """TEMOIN DE CONTROLE POSITIF, sur le CHEMIN REEL.

    Le fil et la timeline tiennent sur deux pages : le balayage doit quand
    meme ecrire. Sur le code d'avant, les deux lectures rendaient `None`
    (sortie multi-pages illisible) et le balayage refusait d'ecrire -- un
    veto fabrique sur une reponse correcte de GitHub.
    """
    ecritures = _balayage_complet(monkeypatch, **{
        "issue list": json.dumps([ISSUE]),
        "pr list": "[]",
        "issues/42/comments": PAGES_FIL,
        "issues/42/timeline": PAGES_TIMELINE,
    })
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == ["marqueur", "label"], ecritures


def test_le_retrait_humain_au_second_page_empêche_toute_ecriture(monkeypatch, capsys):
    """Le retrait est sur la PAGE 2 de la timeline : il doit primer.

    Temoin jumeau du precedent : les deux pages sont lisibles, donc le veto
    ne peut pas etre un artefact de lecture.
    """
    ecritures = _balayage_complet(monkeypatch, **{
        "issue list": json.dumps([ISSUE]),
        "pr list": "[]",
        "issues/42/comments": PAGES_FIL,
        "issues/42/timeline": PAGES_TIMELINE_RETRAIT,
    })
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "VETO" in capsys.readouterr().out.upper()


def test_le_pool_des_prs_ouvertes_illisible_est_inconnu(monkeypatch):
    """Une lecture ratee des PRs ouvertes rend `None`, PAS un ensemble vide.

    Un ensemble vide se lit comme « aucune PR ouverte » -- donc comme une
    issue sans travail en cours, qu'on peut soupconner.
    """
    monkeypatch.setattr(tl, "subprocess", _Subprocess(_gh_faux(
        [], **{"pr list": ""})))
    assert tl.prs_ouverts(REPO) is None


def test_le_plafond_du_pool_des_prs_ouvertes_est_inconnu(monkeypatch):
    """Le plafond de 300 PRs rend le pool INCONNU (page coupee ou pile ?)."""
    prs = json.dumps([{"number": i, "title": "", "body": ""} for i in range(300)])
    monkeypatch.setattr(tl, "subprocess", _Subprocess(_gh_faux(
        [], **{"pr list": prs})))
    assert tl.prs_ouverts(REPO) is None


def test_le_pool_des_prs_ouvertes_lisible_donne_les_issues_citees(monkeypatch):
    """TEMOIN DE CONTROLE POSITIF : une lecture complete rend les cites."""
    prs = json.dumps([{"number": 7, "title": "Fix(#42)", "body": "voir #43"}])
    monkeypatch.setattr(tl, "subprocess", _Subprocess(_gh_faux(
        [], **{"pr list": prs})))
    cites = tl.prs_ouverts(REPO)
    assert cites == {42, 43}, cites


def test_le_pool_ouvert_illisible_est_inconnu(monkeypatch):
    """Meme distinction pour le pool des issues ouvertes."""
    monkeypatch.setattr(tl, "subprocess", _Subprocess(_gh_faux(
        [], **{"issue list": ""})))
    assert tl.pool(REPO, 600) is None


def test_le_mode_apply_refuse_d_ecrire_sur_un_pool_de_prs_incomplet(monkeypatch, capsys):
    """La voie d'ecriture REFUSE sur une lecture incomplete du pool.

    Ce qui est en cours est INCONNU, pas absent : soupconner une issue dont
    une PR ouverte la cite, ce serait un fail-OPEN sur une lecture
    incomplete. Le code de sortie vaut 2, et rien n'est ecrit.
    """
    ecritures = _balayage_complet(monkeypatch, **{
        "issue list": json.dumps([ISSUE]),
        "pr list": "",
        "issues/42/comments": PAGES_FIL,
        "issues/42/timeline": PAGES_TIMELINE,
    })
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 2
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "LECTURE INCOMPLETE" in capsys.readouterr().out


def test_le_mode_apply_refuse_d_ecrire_sur_un_pool_ouvert_incomplet(monkeypatch, capsys):
    """Meme refus pour le pool des issues ouvertes."""
    ecritures = _balayage_complet(monkeypatch, **{
        "issue list": "",
        "pr list": "[]",
        "issues/42/comments": PAGES_FIL,
        "issues/42/timeline": PAGES_TIMELINE,
    })
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 2
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "LECTURE INCOMPLETE" in capsys.readouterr().out


def test_le_rapport_nomme_la_lecture_incomplete_sans_ecrire(monkeypatch, capsys):
    """En mode rapport, la lecture incomplete est NOMMEE, et rien n'est ecrit."""
    ecritures = _balayage_complet(monkeypatch, **{
        "issue list": json.dumps([ISSUE]),
        "pr list": "",
        "issues/42/comments": PAGES_FIL,
        "issues/42/timeline": PAGES_TIMELINE,
    })
    rc = tl.main(["--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "LECTURE INCOMPLETE" in capsys.readouterr().out
