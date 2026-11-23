"""Tests de `scripts/ci/replay_dwell_floors.py`.

Hors reseau : les fonctions testees sont PURES. Le controle cle est le
**controle d'emetteur** : le message du minuteur est produit par
`merge_dwell.evaluate` (l'emetteur), puis relu par le parseur de l'emetteur
aussi -- jamais par une copie de la forme. Une copie deriverait en silence et
le minuteur redeviendrait invisible, ce qui est exactement le piege documente
dans `merge_dwell`.
"""

from __future__ import annotations

import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
CI_DIR = Path(__file__).resolve().parents[1]
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import merge_dwell  # noqa: E402
from replay_dwell_floors import (  # noqa: E402
    decide,
    dwell_floor,
    is_dwell_timer,
    job_ref,
)

HEAD_AT = datetime(2026, 11, 18, 18, 57, 52, tzinfo=timezone.utc)


def _pending_title(dwell_min: float = 120.0, age_min: float = 10.0) -> str:
    """Message du minuteur produit par l'EMETTEUR (merge_dwell.evaluate)."""
    _ok, _remaining, message = merge_dwell.evaluate(
        committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=age_min),
        dwell_min=dwell_min)
    return message


def test_plancher_brut_est_la_tete_plus_le_dwell():
    floor = dwell_floor(HEAD_AT, 120.0)
    assert floor == HEAD_AT + timedelta(minutes=120)
    assert floor.strftime("%Y-%m-%dT%H:%M:%SZ") == "2026-11-18T20:57:52Z"


def test_le_minuteur_est_reconnu_par_le_parseur_de_l_emetteur():
    assert is_dwell_timer(_pending_title()) is True


def test_un_plancher_ecoule_n_est_pas_un_minuteur():
    """Quand le plancher est passe, le message change de forme : ce n'est plus
    une attente de minuteur, et l'organe ne doit pas rejouer sur ce texte."""
    _ok, _remaining, message = merge_dwell.evaluate(
        committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=200), dwell_min=120.0)
    assert "dwell ecoule" in message
    assert is_dwell_timer(message) is False


def test_un_rouge_reel_n_est_pas_un_minuteur():
    assert is_dwell_timer("3 tests ont echoue : assertion false") is False


def test_legende_verte_ignoree():
    action, motif = decide(conclusion="success", title="", committed_at=HEAD_AT,
                           now=HEAD_AT + timedelta(hours=3))
    assert action == "ignorer"
    assert "verte" in motif


def test_rouge_reel_jamais_rejoue():
    action, motif = decide(conclusion="failure", title="3 tests ont echoue",
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3))
    assert action == "ignorer"
    assert "reel" in motif


def test_derogation_par_label_ignoree():
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           waived=True)
    assert action == "ignorer"
    assert merge_dwell.WAIVER_LABEL in motif


def test_plancher_non_passe_attente():
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=30))
    assert action == "attendre"
    assert "pas encore passe" in motif


def test_plancher_passe_rejoue():
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=121))
    assert action == "rejouer"
    assert "2026-11-18T20:57:52Z" in motif


def test_egalite_au_plancher_rejoue():
    """Le plancher passe a l'instant exact : la limite est inclusive."""
    action, _motif = decide(conclusion="failure", title=_pending_title(),
                            committed_at=HEAD_AT, now=dwell_floor(HEAD_AT, 120.0))
    assert action == "rejouer"


def test_jambe_en_cours_n_est_pas_un_rouge_reel():
    """Une jambe EN COURS porte un titre vide (GitHub ne l'ecrit qu'a la fin du
    job) : sans test de `status`, elle tombait dans « pas le minuteur » et le
    verdict devenait « rouge reel ». Mesure : #26989 (18/11 20:45:34Z)."""
    action, motif = decide(conclusion="", title="", committed_at=HEAD_AT,
                           now=HEAD_AT + timedelta(hours=3), status="in_progress")
    assert action == "attendre"
    assert "en cours" in motif
    assert "reel" not in motif


def test_jembe_en_cours_n_est_jamais_rejouee():
    """Meme au-dela du plancher : une jambe qui tourne n'est pas rejouee."""
    action, _motif = decide(conclusion="", title="", committed_at=HEAD_AT,
                            now=HEAD_AT + timedelta(hours=3), status="queued")
    assert action == "attendre"


def test_le_minuteur_reconnu_passe_meme_si_la_jambe_echoue():
    """Le cas inverse : le minuteur reste detectable sur une jambe terminee."""
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           status="completed")
    assert action == "rejouer"
    assert "2026-11-18T20:57:52Z" in motif


def test_un_statut_absent_ne_rejoue_jamais():
    """Un `status` ABSENT n'est pas « terminee » : la reponse est incomplete.

    Fail-CLOSED : le minuteur etait lisible, le plancher etait ecoule, et
    l'organe pouvait rejouer sur une reponse qui n'avait pas tout dit
    (relire du coordinateur, 19/11 00:05Z)."""
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           status="")
    assert action == "attendre"
    assert "absent" in motif


def test_une_conclusion_autre_qu_un_echec_ne_rejoue_jamais():
    """Une jambe terminee mais conclue autrement (annulee, ignoree, neutre) :
    ce n'est pas un echec, il n'y a rien a rejouer."""
    for conclusion in ("cancelled", "skipped", "neutral", ""):
        action, motif = decide(conclusion=conclusion, title=_pending_title(),
                               committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                               status="completed")
        assert action == "ignorer", conclusion
        assert "rien a rejouer" in motif


def test_horloge_en_arriere_ou_future_ne_passe_pas():
    """Une tete datee dans le futur (decalage de machine) ne doit pas etre
    lue comme un plancher ecoule : fail-CLOSED.

    Le deccalage se lit desormais dans le message de l'**emetteur** (`head_at`),
    puisque c'est lui qui porte le plancher : c'est la date que l'emetteur a
    ecrite qui doit etre dans le futur, pas une date recomputee.
    """
    future = HEAD_AT + timedelta(days=1)
    _ok, _rem, message = merge_dwell.evaluate(
        committed_at=future, now=HEAD_AT + timedelta(hours=3), dwell_min=120.0)
    action, motif = decide(conclusion="failure", title=message,
                           committed_at=future, now=HEAD_AT + timedelta(hours=3))
    assert action == "attendre"
    assert "fail-CLOSED" in motif


def test_le_plancher_vient_de_l_emetteur_pas_de_la_date_de_tete():
    """Controle NEGATIF de l'update-branch sans conflit (c3271).

    Apres un `update-branch` **sans conflit**, la tete est un commit de fusion
    dont la date est **plus recente**, mais le contenu du cote PR n'a pas
    change : le rafraichissement est *prouve* content-free, donc l'emetteur ne
    rearme pas le plancher (`head_at` reste l'ancienne date). Un organe qui
    recalculait le plancher depuis la date de tete disait « attendre » la ou
    l'emetteur disait deja « plancher ecoule ».

    Ici la date de tete est de **2 h** plus recente que le `head_at` du
    message : si l'organe recalculait, il dirait « attendre » (plancher
    22:57:52Z > maintenant 21:57:52Z). Il doit dire « rejouer ».
    """
    tete_plus_recente = HEAD_AT + timedelta(hours=2)
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=tete_plus_recente,
                           now=HEAD_AT + timedelta(hours=3))
    assert action == "rejouer"
    assert "2026-11-18T20:57:52Z" in motif


def test_le_dwell_de_l_emetteur_prime_sur_le_dwell_par_defaut():
    """Le `dwell_min` du message est celui que l'emetteur a applique : il
    prime sur le defaut du module (l'emetteur peut en choisir un autre)."""
    _ok, _rem, message = merge_dwell.evaluate(
        committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=10), dwell_min=60.0)
    action, motif = decide(conclusion="failure", title=message,
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=90),
                           dwell_min=120.0)
    assert action == "rejouer"
    assert "2026-11-18T19:57:52Z" in motif


def test_un_brouillon_n_est_jamais_rejoue():
    """Une PR en brouillon n'est pas mergeable : sa jambe n'est jamais rejouee,
    et elle est separee de l'inventaire des PRs mergeables."""
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           draft=True)
    assert action == "ignorer"
    assert "brouillon" in motif


def test_une_derogation_n_est_annoncee_que_si_les_labels_ont_ete_lus():
    """Sans lecture des labels, aucune derogation n'est annoncee : le verdict
    reste celui du minuteur (point 7 du coordinateur, c3271)."""
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           waived=False)
    assert action == "rejouer"
    assert "derogation" not in motif
    action2, motif2 = decide(conclusion="failure", title=_pending_title(),
                             committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                             waived=True)
    assert action2 == "ignorer"
    assert "derogation" in motif2


def test_dwell_desactive_rejoue_tout():
    """`--dwell-min <= 0` desactive le plancher : la jambe n'est plus un
    minuteur, donc elle ne se rejoue pas sur le critere du plancher."""
    action, motif = decide(conclusion="failure", title=_pending_title(dwell_min=0.0),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           dwell_min=0.0)
    assert action == "ignorer"


def test_job_ref_extrait_run_et_job():
    ref = job_ref("https://github.com/jsboige/CoursIA/actions/runs/44375592255/job/135053807477")
    assert ref == ("44375592255", "135053807477")


def test_job_ref_none_si_url_inconnue():
    assert job_ref("https://example.invalid/nope") is None


@pytest.mark.parametrize("dwell_min", [60.0, 120.0, 240.0])
def test_le_plancher_suit_le_dwell(dwell_min):
    assert dwell_floor(HEAD_AT, dwell_min) == HEAD_AT + timedelta(minutes=dwell_min)


# --------------------------------------------------------------------------
# Pagination de la liste des PR ouvertes (correction c3271)
# --------------------------------------------------------------------------

def test_open_pr_numbers_pagine_jusqu_a_epuisement(monkeypatch):
    """`--all` doit voir TOUTES les PRs ouvertes, pas la premiere page.

    Mesure du 2026-11-18 : le depot comptait 194 PRs ouvertes ; la lecture
    d'une seule page (`per_page=100`, sans pagination) n'en voyait que 100
    -- les plus recentes -- alors que l'aide de l'organe annoncait « examine
    toutes les PR ouvertes du depot ». La promesse non tenue est le defaut.
    """
    import replay_dwell_floors

    pages = {
        1: [{"number": n} for n in range(1, 101)],
        2: [{"number": n} for n in range(101, 195)],
    }
    appels = []

    def faux_gh_json(path):
        appels.append(path)
        return pages.get(int(path.split("&page=")[1]), [])

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    nums = replay_dwell_floors.open_pr_numbers("jsboige/CoursIA")
    assert len(nums) == 194
    assert nums[0] == 1 and nums[-1] == 194
    assert len(appels) == 2


def test_open_pr_numbers_ne_boucle_pas_sur_une_page_pleine(monkeypatch):
    """Une page exactement pleine force une page de plus : la page vide qui
    suit doit arreter la lecture (et non la faire boucler)."""
    import replay_dwell_floors

    appels = []

    def faux_gh_json(path):
        appels.append(path)
        page = int(path.split("&page=")[1])
        if page == 1:
            return [{"number": n} for n in range(1, 101)]
        return []

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    nums = replay_dwell_floors.open_pr_numbers("jsboige/CoursIA")
    assert len(nums) == 100
    assert len(appels) == 2


# --------------------------------------------------------------------------
# Collecteur de check-runs, lecture des labels, et rc de sortie (c3271)
# --------------------------------------------------------------------------

def test_le_collecteur_de_check_runs_refuse_une_couverture_incomplete(monkeypatch):
    """Au-dela de `per_page` check-runs, la liste est tronquee : la jambe
    `PR gate` peut manquer, et « pas de check-run trouve » n'est **pas** une
    absence. La lecture tronquee est un **refus** (c3272) : plus de verdict
    « incomplete », plus de couple `(run, complete)` a mal lire."""
    import replay_dwell_floors

    def faux_gh_json(path):
        # une page pleine a chaque fois -> le plafond de pages est atteint
        return {"check_runs": [{"name": "PR gate", "id": i, "started_at": "2026-11-18T20:00:00Z"}
                               for i in range(100)]}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.gate_check_run(
            "jsboige/CoursIA", "deadbeef", per_page=100, max_pages=2)


def test_le_collecteur_de_check_runs_signale_la_couverture_complete(monkeypatch):
    """Une page finale courte signe la fin de la liste : la couverture est
    complete et la lecture est fiable."""
    import replay_dwell_floors

    appels = []

    def faux_gh_json(path):
        appels.append(path)
        page = int(path.split("&page=")[1])
        if page == 1:
            return {"check_runs": [{"name": "PR gate", "id": 1,
                                    "started_at": "2026-11-18T20:00:00Z"}] * 100}
        return {"check_runs": [{"name": "Autre", "id": 2,
                                "started_at": "2026-11-18T20:01:00Z"}]}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    run = replay_dwell_floors.gate_check_run("jsboige/CoursIA", "deadbeef")
    assert run is not None
    assert run["id"] == 1
    assert len(appels) == 2


def test_pr_info_lit_les_labels_et_le_statut_de_brouillon(monkeypatch):
    """Les labels et le `draft` viennent de la meme charge utile que la tete :
    une derogation n'est annoncee respectee que si les labels ont ete lus."""
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"},
                "labels": [{"name": "merge-dwell-waived"}, {"name": "bug"}],
                "draft": True, "state": "open"}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    info = replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)
    assert info["sha"] == "abc123"
    assert info["draft"] is True
    assert "merge-dwell-waived" in info["labels"]


def test_un_rejeu_refuse_sort_en_rc_non_nul(monkeypatch):
    """Un geste rate doit etre visible par le consommateur : l'organe sortait
    0 meme apres un refus (point 4 du coordinateur, c3271)."""
    import replay_dwell_floors

    monkeypatch.setattr(replay_dwell_floors, "inspect_pr", lambda *a, **k: {
        "pr": 1, "action": "rejouer", "motif": "plancher brut passe",
        "run_id": "42", "job_id": "43", "draft": False})
    monkeypatch.setattr(replay_dwell_floors, "gh_rerun",
                        lambda *a, **k: (1, "refuse"))
    monkeypatch.setattr(sys, "argv",
                        ["replay_dwell_floors.py", "--pr", "1", "--apply", "--json"])
    rc = replay_dwell_floors.main()
    assert rc == 1


def test_le_rejeu_prend_le_repo_en_argument(monkeypatch):
    """`gh run rerun` sans `--repo` agit sur le depot du repertoire courant
    de l'appelant (point 3 du coordinateur, c3271)."""
    import replay_dwell_floors

    argv_vus = {}

    def faux_run(cmd, *args, **kwargs):
        argv_vus["cmd"] = cmd
        class R:
            returncode = 0
            stdout = ""
            stderr = ""
        return R()

    monkeypatch.setattr(replay_dwell_floors.subprocess, "run", faux_run)
    rc, _out = replay_dwell_floors.gh_rerun("42", "43", "jsboige/CoursIA")
    assert rc == 0
    assert "--repo" in argv_vus["cmd"]
    assert argv_vus["cmd"][argv_vus["cmd"].index("--repo") + 1] == "jsboige/CoursIA"


# --------------------------------------------------------------------------
# Lecture STRICTE : une reponse cassee est un refus, pas une valeur par
# defaut (c3272 -- demande du coordinateur sur #27273)
# --------------------------------------------------------------------------

def test_des_labels_absents_sont_un_refus_pas_une_liste_vide(monkeypatch):
    """CONTROLE NEGATIF : `labels` absent ne vaut PAS `[]`.

    L'ancien comportement transformait un champ absent en liste vide, et
    `inspect_pr` ecrivait alors `labels_lus = True` : une reponse **cassee**
    se lisait « pas de derogation », c'est-a-dire un **fait** affirme sur une
    lecture qui n'avait pas eu lieu.
    """
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"}, "draft": False}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)


def test_des_labels_mal_formes_sont_un_refus(monkeypatch):
    """`labels` qui n'est pas une liste, ou un element sans `name` : refus."""
    import replay_dwell_floors

    def faux_labels_non_liste(path):
        return {"head": {"sha": "abc123"}, "labels": {"name": "bug"}, "draft": False}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_labels_non_liste)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)

    def faux_labels_sans_nom(path):
        return {"head": {"sha": "abc123"}, "labels": [{"id": 7}], "draft": False}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_labels_sans_nom)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)


def test_un_draft_absent_est_un_refus_pas_False(monkeypatch):
    """CONTROLE NEGATIF : `draft` absent ne vaut PAS `False`.

    Un `draft` absent se lisait « PR mergeable » -- une **absence** due a une
    lecture cassee, lue comme un fait.
    """
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"}, "labels": []}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)


def test_un_draft_non_booleen_est_un_refus(monkeypatch):
    """Un `draft` qui n'est pas un booleen est une lecture cassee."""
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"}, "labels": [], "draft": "false"}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)


def test_une_tete_absente_est_un_refus(monkeypatch):
    """Sans `head.sha`, l'organe n'a pas de tete : pas de lecture."""
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"labels": [], "draft": False}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)


def test_labels_lus_n_est_annonce_qu_apres_une_lecture_reelle(monkeypatch):
    """`labels_lus` vaut `True` quand les labels ont ete lus -- et la lecture
    refuse des lors qu'ils n'ont pas pu l'etre."""
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"}, "labels": [{"name": "bug"}], "draft": False,
                "state": "open"}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    info = replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)
    assert info["labels_lus"] is True
    assert info["labels"] == ["bug"]
    assert info["draft"] is False


def test_des_check_runs_de_forme_invalide_sont_un_refus(monkeypatch):
    """CONTROLE NEGATIF : `check_runs` absent ou non-liste.

    L'ancien comportement lisait une forme invalide comme une liste VIDE,
    donc comme « aucune check-run `PR gate` sur cette tete » -- une absence
    deduite d'une lecture cassee.
    """
    import replay_dwell_floors

    def faux_absent(path):
        return {"total_count": 0}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_absent)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.gate_check_run("jsboige/CoursIA", "deadbeef")

    def faux_pas_liste(path):
        return {"check_runs": {"name": "PR gate"}}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_pas_liste)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.gate_check_run("jsboige/CoursIA", "deadbeef")


def test_le_plafond_de_pagination_des_prs_ouvertes_est_un_refus(monkeypatch):
    """Un inventaire tronque ne se lit pas « toutes les PRs ouvertes »."""
    import replay_dwell_floors

    def faux_gh_json(path):
        return [{"number": n} for n in range(1, 101)]

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.open_pr_numbers("jsboige/CoursIA", per_page=100,
                                             max_pages=2)


def test_une_liste_de_prs_de_forme_invalide_est_un_refus(monkeypatch):
    """Une liste de PRs qui n'est pas une liste (ou un element sans `number`)
    est une lecture cassee : pas d'inventaire."""
    import replay_dwell_floors

    def faux_pas_liste(path):
        return {"message": "Not Found"}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_pas_liste)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.open_pr_numbers("jsboige/CoursIA")

    def faux_element_mal_forme(path):
        return [{"number": 1}, "deux"]

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_element_mal_forme)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.open_pr_numbers("jsboige/CoursIA")


def test_un_refus_de_lecture_ne_produit_aucun_verdict(monkeypatch):
    """Le refus remonte jusqu'a la sortie : action `incomplet`, rc 2.

    Un verdict sur une lecture cassee serait un **fait** affirme sur une
    absence : l'organe distingue l'echec de geste (rc 1) de l'inventaire
    incomplet (rc 2).
    """
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"}, "labels": [], "draft": False, "state": "open"}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    monkeypatch.setattr(sys, "argv",
                        ["replay_dwell_floors.py", "--pr", "27273", "--json"])
    rc = replay_dwell_floors.main()
    assert rc == 2


def test_le_refus_de_l_organe_est_distinct_de_l_echec_de_geste(monkeypatch):
    """Lecture cassee -> rc 2 ; echec de geste -> rc 1. Deux causes, deux
    codes : un consommateur ne peut pas les confondre."""
    import replay_dwell_floors

    monkeypatch.setattr(replay_dwell_floors, "inspect_pr", lambda *a, **k: {
        "pr": 1, "action": "rejouer", "motif": "plancher brut passe",
        "run_id": "42", "job_id": "43", "draft": False})
    monkeypatch.setattr(replay_dwell_floors, "gh_rerun",
                        lambda *a, **k: (1, "refuse"))
    monkeypatch.setattr(sys, "argv",
                        ["replay_dwell_floors.py", "--pr", "1", "--apply", "--json"])
    assert replay_dwell_floors.main() == 1


# --------------------------------------------------------------------------
# PERIMETRE et FRAICHEUR (reserve du coordinateur du 19/11 01:32Z, #27273)
# --------------------------------------------------------------------------

def test_une_pr_fermee_n_est_jamais_rejouee():
    """CONTROLE NEGATIF : une PR fermee est hors perimetre du rejeu.

    `pr_info` ne lisait pas `state` : `--pr N --apply` pouvait relancer un
    ancien minuteur sur une PR **fermee**, et `--all` pouvait rencontrer une
    fermeture apres son inventaire. Fermer une PR ne rend pas sa jambe
    rejouable : la decision porte sur l'etat de la PR, pas sur celui du
    minuteur.
    """
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT,
                           now=HEAD_AT + timedelta(minutes=200),
                           state="closed")
    assert action == "ignorer"
    assert "fermee" in motif


def test_une_pr_ouverte_est_rejouable():
    """Témoin positif : la meme jambe, sur une PR ouverte, se rejoue."""
    action, _motif = decide(conclusion="failure", title=_pending_title(),
                            committed_at=HEAD_AT,
                            now=HEAD_AT + timedelta(minutes=200),
                            state="open")
    assert action == "rejouer"


def test_un_state_absent_est_un_refus_pas_ouverte(monkeypatch):
    """CONTROLE NEGATIF : `state` absent ne vaut PAS « ouverte ».

    Meme piege que `labels` et `draft` : une reponse cassee ne se lit pas
    « ouverte » -- elle se refuse.
    """
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"}, "labels": [], "draft": False}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)


def test_un_state_non_chaine_est_un_refus(monkeypatch):
    """Un `state` qui n'est pas une chaine est une lecture cassee."""
    import replay_dwell_floors

    def faux_gh_json(path):
        return {"head": {"sha": "abc123"}, "labels": [], "draft": False,
                "state": 42}

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    with pytest.raises(replay_dwell_floors.LectureIncomplete):
        replay_dwell_floors.pr_info("jsboige/CoursIA", 27273)


def _inv(**extra):
    """Un inventaire minimal : l'etat de depart du rejeu."""
    base = {"head_sha": "abc123", "gate_id": 1, "draft": False,
            "derogation": False}
    base.update(extra)
    return base


def _frais(**extra):
    """Un etat relu minimal, identique a l'inventaire."""
    base = {"sha": "abc123", "state": "open", "gate_id": 1,
            "status": "completed", "conclusion": "failure",
            "draft": False, "derogation": False}
    base.update(extra)
    return base


def test_le_geste_est_refuse_si_la_tete_a_change():
    """La tete a bouge entre l'inventaire et le geste : le minuteur lu
    n'est plus celui de la tete courante."""
    import replay_dwell_floors

    inv = _inv()
    frais = _frais(sha="def456")
    ok, motif = replay_dwell_floors.verifie_fraicheur(inv, frais)
    assert ok is False
    assert "tete changee" in motif


def test_le_geste_est_refuse_si_la_pr_a_ete_fermee_entre_temps():
    import replay_dwell_floors

    inv = _inv()
    frais = _frais(state="closed")
    ok, motif = replay_dwell_floors.verifie_fraicheur(inv, frais)
    assert ok is False
    assert "fermee" in motif


def test_le_geste_est_refuse_si_le_controle_selectionne_a_change():
    """La jambe `PR gate` selectionnee n'est plus celle lue : un tiers a
    rejoue, ou une nouvelle tete a produit une autre jambe."""
    import replay_dwell_floors

    inv = _inv()
    frais = _frais(gate_id=2)
    ok, motif = replay_dwell_floors.verifie_fraicheur(inv, frais)
    assert ok is False
    assert "change" in motif


def test_le_geste_est_refuse_si_la_jambe_n_est_plus_terminee_en_echec():
    """La jambe relue n'est plus terminee, ou plus en echec : plus rien a
    rejouer."""
    import replay_dwell_floors

    inv = _inv()
    for status, conclusion in (("in_progress", "failure"),
                                ("completed", "success"),
                                ("completed", "cancelled")):
        frais = _frais(status=status, conclusion=conclusion)
        ok, _motif = replay_dwell_floors.verifie_fraicheur(inv, frais)
        assert ok is False


def test_un_rejeu_autorise_passe_quand_etat_relu_est_identique():
    """Témoin positif : etat relu identique -> le geste est autorise."""
    import replay_dwell_floors

    inv = _inv()
    frais = _frais()
    ok, _motif = replay_dwell_floors.verifie_fraicheur(inv, frais)
    assert ok is True


def test_le_geste_ne_part_pas_quand_la_relecture_est_impossible():
    """Fail-CLOSED : une relecture impossible n'est jamais « rien n'a
    change »."""
    import replay_dwell_floors

    inv = _inv()
    ok, _motif = replay_dwell_floors.verifie_fraicheur(inv, {})
    assert ok is False


def test_un_rejeu_refuse_par_fraicheur_ne_appelle_pas_gh(monkeypatch):
    """Le geste refuse par la relecture **ne part pas** : `gh run rerun`
    n'est pas appele, et la commande sort en rc 1 (geste rate)."""
    import replay_dwell_floors

    appele = {"gh": False}

    monkeypatch.setattr(replay_dwell_floors, "inspect_pr", lambda *a, **k: {
        "pr": 1, "action": "rejouer", "motif": "plancher brut passe",
        "run_id": "42", "job_id": "43", "draft": False, "state": "open",
        "head_sha": "abc123", "gate_id": 1, "derogation": False})

    def faux_relit(repo, number):
        return {"sha": "autre", "state": "open", "gate_id": 1,
                "status": "completed", "conclusion": "failure",
                "draft": False, "derogation": False}

    def faux_gh_rerun(*a, **k):
        appele["gh"] = True
        return 0, ""

    monkeypatch.setattr(replay_dwell_floors, "relit_etat", faux_relit)
    monkeypatch.setattr(replay_dwell_floors, "gh_rerun", faux_gh_rerun)
    monkeypatch.setattr(sys, "argv",
                        ["replay_dwell_floors.py", "--pr", "1", "--apply", "--json"])
    assert replay_dwell_floors.main() == 1
    assert appele["gh"] is False
