"""Tests du plafond de WIP par lane (Q41, mandat user 2026-09-22).

Le garde rouge ne compte que les PRs BLOQUEES : une PR VERTE en attente de
dossier ou de merge ne declenche rien (volontaire, #12108). Mais le temps de
passage est WIP / debit (loi de Little) -- mesurable au 2026-09-22 : 323 PRs
ouvertes, dont 91 pour la seule lane myia-po-2026:CoursIA. Le plafond borne
l'encours lui-meme : au-dela, la lane recoit SA file (reparation/
consolidation), la plus ancienne d'abord, memes convention de sortie et code
de retour que le garde rouge.

Controles pins ici, par le meme principe que la suite rouge (un detecteur se
valide par ses faux negatifs) : brouillons comptes (convertir en draft
n'echappe pas au plafond), PRs d'autres lanes et PRs sans tag NON comptees,
plafond desactivable, echappatoire auditee (--ignore-wip exige
--wip-reason, distincte de --admit-reason qui leverait aussi le garde
d'admission), et composition avec le garde rouge -- aucun des deux gardes
ne masque l'autre.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402

LANE = "myia-po-2026:CoursIA"
OTHER_LANE = "myia-po-2023:CoursIA-2"


def _pr(n, lane, age_hours, *, draft=False):
    """Meme fixture que la suite rouge : corps porte le tag, age pilote la file."""
    created = (pig.NOW - pig.dt.timedelta(hours=age_hours)).strftime("%Y-%m-%dT%H:%M:%SZ")
    body = f"Grain: MED/guard -- lane {lane}\n" if lane else "pas de tag\n"
    return {"number": n, "title": f"pr {n}", "body": body,
            "createdAt": created, "isDraft": draft}


def _state_red(number=1):
    """Etat GraphQL d'une PR rouge, forme rendue par fetch_pr_states."""
    return {"number": number, "mergeable": "MERGEABLE",
            "reviews": {"nodes": []},
            "commits": {"nodes": [{"commit": {"statusCheckRollup": {"contexts": {"nodes": [
                {"name": "PR gate", "conclusion": "FAILURE", "isRequired": True,
                 "completedAt": "2026-08-20T00:00:00Z"}]}}}}]}}


def _patch_guard(monkeypatch, prs, states=None, nits=None):
    """Meme neutralisation reseau que _patch_backlog de la suite principale."""
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    states = states or {}
    monkeypatch.setattr(pig, "fetch_pr_states",
                        lambda nums: {n: states[n] for n in nums if n in states})
    monkeypatch.setattr(pig, "unaddressed_review_points", lambda nums: dict(nits or {}))
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **k: ([], None))
    monkeypatch.setattr(pig, "fetch_main_head_probe", lambda *a, **k: None)


def _patch_draw(monkeypatch):
    """Le tirage APRES les gardes parle a gh : payloads vides, hermetique.

    Les fetchers du chemin de tirage sont remplaces par des rendus vides
    de la bonne arite -- le test ne traverse le garde que pour verifier
    qu'il laisse passer, pas pour verifier le tirage lui-meme.
    `fetch_merged_grains` (secheresse de substance) est un appel gh de
    plus, neutralise pour la meme raison.
    """
    monkeypatch.setattr(pig, "fetch_pool", lambda **k: ([], None))
    monkeypatch.setattr(pig, "fetch_visits", lambda *a, **k: ({}, None))
    monkeypatch.setattr(pig, "fetch_series_visits", lambda **k: ([], {}, None))
    monkeypatch.setattr(pig, "fetch_merged", lambda *a, **k: ([], None))
    monkeypatch.setattr(pig, "fetch_merged_grains", lambda *a, **k: ([], None))


# --- comptage : qui entre dans le WIP, qui n'y entre pas --------------------


def test_wip_counts_drafts_and_excludes_other_lanes_and_untagged(monkeypatch):
    """Le compte mesure l'ENCOURS de la lane : brouillon oui, etranger non.

    Le garde rouge ignore les brouillons a bon droit (pas de checks a
    reparer) ; le plafond, lui, doit les compter -- sinon convertir en
    draft devient l'echappatoire du plafond. Controles negatifs : une PR
    d'une autre lane et une PR sans tag lisible ne comptent pas.
    """
    _patch_guard(monkeypatch, [
        _pr(1, LANE, 30),
        _pr(2, LANE, 5, draft=True),      # brouillon : compte pour le WIP
        _pr(3, OTHER_LANE, 30),           # autre lane : non
        _pr(4, None, 30),                 # sans tag : non
    ])
    out = pig.red_backlog(LANE, 24, count_threshold=3)
    assert out["wip_count"] == 2
    assert [e["number"] for e in out["wip_prs"]] == [1, 2]  # oldest first
    assert out["wip_prs"][1]["is_draft"] is True
    assert out["wip_triggered"] is False  # 2 < 15 : le garde ne declenche pas


def test_lane_open_prs_sorts_oldest_first():
    """La file a drainer se lit de la plus ancienne a la plus recente."""
    prs = [_pr(7, LANE, 2), _pr(8, LANE, 50), _pr(9, LANE, 20)]
    out = pig.lane_open_prs(LANE, prs)
    assert [e["number"] for e in out] == [8, 9, 7]
    assert out[0]["age_hours"] == 50


def test_red_causes_are_reported_on_the_wip_queue(monkeypatch):
    """La file WIP dit POURQUOI chaque PR attend quand la cause est connue.

    Une PR rouge de la lane entre dans la file WIP AVEC ses causes (deja
    calculees par le garde rouge, pas de second etat GraphQL) ; une PR
    verte entre avec causes vides -- c'est exactement la population que le
    garde rouge ne voyait pas.
    """
    red = _state_red()
    _patch_guard(monkeypatch, [
        _pr(1, LANE, 30),
        _pr(2, LANE, 5),
    ], {1: red})
    out = pig.red_backlog(LANE, 24, count_threshold=3)
    by_number = {e["number"]: e for e in out["wip_prs"]}
    assert by_number[1]["causes"], "la rouge porte ses causes dans la file WIP"
    assert by_number[2]["causes"] == [], "la verte n'a pas de cause fabriquee"


# --- declenchement : au plafond, la lane recoit sa file --------------------


def _fleet(n, first_age=50):
    """n PRs de la lane, ages distincts decroissants : la plus ancienne est #1."""
    return [_pr(i + 1, LANE, first_age - i) for i in range(n)]


def test_at_the_cap_the_lane_gets_its_queue_not_a_draw(monkeypatch, capsys):
    """15 PRs ouvertes (toutes vertes) : assignation, pas de grain neuf.

    C'est le cas que le garde rouge ne pouvait pas voir : aucune PR
    bloquee, la lane attend des dossiers/merges -- et le temps de passage
    croit avec l'encours (loi de Little). Memes conventions que le garde
    rouge : sortie 0, en-tete FILE DE REPARATION, aucune occurrence du mot
    refus, plafond ET compte mesures nommes, file oldest first.
    """
    _patch_guard(monkeypatch, _fleet(pig.WIP_CAP_DEFAULT))
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0, f"le chemin assignation doit rendre 0, got {rc}"
    head = out.splitlines()[0]
    assert "FILE DE REPARATION" in head
    assert "REFUS" not in head.upper()
    assert f"plafond de WIP = {pig.WIP_CAP_DEFAULT}" in out, "le plafond doit etre nomme"
    assert f"porte {pig.WIP_CAP_DEFAULT} PR(s) ouverte(s)" in out, "le compte mesure doit etre nomme"
    # File oldest first : la plus ancienne (#1, 50 h) est listee en premier.
    listed = [line for line in out.splitlines() if "ouverte depuis" in line]
    assert len(listed) == pig.WIP_CAP_DEFAULT
    assert "#1" in listed[0] and "50 h" in listed[0]


def test_at_the_cap_the_json_assignation_carries_the_queue(monkeypatch, capsys):
    """Le consommateur machine lit mode repair + assignment + grain, pas un refus."""
    _patch_guard(monkeypatch, _fleet(pig.WIP_CAP_DEFAULT))
    rc = pig.main(["--lane", LANE, "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["mode"] == "repair"
    assert payload["assignment"] == "drainer-son-wip"
    assert payload["grain"]["number"] == 1  # la plus ancienne de la file
    assert payload["wip_triggered"] is True
    assert payload["wip_count"] == pig.WIP_CAP_DEFAULT
    assert "refus" not in payload


def test_below_the_cap_the_draw_proceeds(monkeypatch, capsys):
    """Controle positif : 14 PRs ouvertes, le tirage passe les gardes.

    Sans ce temoin, un plafond bloque-a-l'allumage serait indiscernable
    d'un plafond qui marche : toute lane active serait immobilisee et
    --ignore-wip deviendrait la voie ordinaire.
    """
    _patch_guard(monkeypatch, _fleet(pig.WIP_CAP_DEFAULT - 1))
    _patch_draw(monkeypatch)
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" not in out
    assert "plafond de WIP" not in out
    assert "Pool ouvert" in out  # le chemin de tirage a bien etre atteint


def test_drafts_count_toward_the_cap(monkeypatch, capsys):
    """Le brouillon qui complete le plafond declenche l'assignation.

    14 PRs regulieres + 1 brouillon = 15 : convertir la 15e en draft ne
    doit pas echapper au plafond. Le brouillon est liste ET marque.
    """
    prs = _fleet(pig.WIP_CAP_DEFAULT - 1)
    prs.append(_pr(99, LANE, 1, draft=True))
    _patch_guard(monkeypatch, prs)
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" in out
    assert "[brouillon]" in out
    assert "#99" in out


def test_other_lanes_prs_do_not_count_toward_the_cap(monkeypatch, capsys):
    """Controle negatif : 14 PRs a moi + 5 a une autre lane = pas d'assignation.

    L'unite d'attribution est le TAG de lane, jamais l'auteur ni le total
    du depot -- sinon toutes les lanes paieraient l'encours de la plus
    chargee.
    """
    prs = _fleet(pig.WIP_CAP_DEFAULT - 1)
    prs += [_pr(500 + i, OTHER_LANE, 30) for i in range(5)]
    _patch_guard(monkeypatch, prs)
    _patch_draw(monkeypatch)
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" not in out


def test_untagged_prs_do_not_count_toward_the_cap(monkeypatch, capsys):
    """Controle negatif : une PR sans tag lisible n'est imputable a personne."""
    prs = _fleet(pig.WIP_CAP_DEFAULT - 1)
    prs += [_pr(600 + i, None, 30) for i in range(3)]
    _patch_guard(monkeypatch, prs)
    _patch_draw(monkeypatch)
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" not in out


# --- reglages et echappatoire -----------------------------------------------


def test_wip_cap_zero_disables_the_guard(monkeypatch, capsys):
    """--wip-cap 0 desactive le garde : 20 PRs ouvertes, le tirage passe.

    Meme convention que --dwell-hours 0 : un garde reglable doit pouvoir
    etre eteint proprement (kill switch), pas contourne par --ignore-wip.
    """
    _patch_guard(monkeypatch, _fleet(20))
    _patch_draw(monkeypatch)
    rc = pig.main(["--lane", LANE, "--wip-cap", "0"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" not in out
    assert "plafond de WIP" not in out


def test_wip_cap_is_overridable_downward(monkeypatch, capsys):
    """--wip-cap N resserre le plafond sans attendre un changement de defaut."""
    _patch_guard(monkeypatch, _fleet(3))
    rc = pig.main(["--lane", LANE, "--wip-cap", "3"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" in out
    assert "plafond de WIP = 3" in out


def test_ignore_wip_without_wip_reason_is_an_error(monkeypatch, capsys):
    """L'echappatoire du plafond est AUDITEE : --wip-reason exigee.

    Contrairement a --ignore-red (justification ECRITE sur la PR concernee,
    verifiee par le merge-gate), le plafond n'a pas de PR particuliere ou
    poser la justification : elle vit dans --wip-reason ou ne se prend
    pas. argparse ap.error = sortie 2, meme convention que --lane requis.
    """
    with pytest.raises(SystemExit) as excinfo:
        pig.main(["--lane", LANE, "--ignore-wip"])
    assert excinfo.value.code == 2
    assert "--wip-reason" in capsys.readouterr().err


def test_admit_reason_does_not_satisfy_ignore_wip(monkeypatch, capsys):
    """--admit-reason ne vaut PAS justification du plafond.

    --admit-reason leve le garde d'admission (claims, DWELL) : l'accepter
    pour --ignore-wip ouvrirait en silence les issues retenues, alors que
    la lane n'a demande qu'a passer le plafond.
    """
    with pytest.raises(SystemExit) as excinfo:
        pig.main(["--lane", LANE, "--ignore-wip", "--admit-reason", "x"])
    assert excinfo.value.code == 2
    assert "--wip-reason" in capsys.readouterr().err


def test_wip_reason_without_ignore_wip_is_an_error(monkeypatch, capsys):
    with pytest.raises(SystemExit) as excinfo:
        pig.main(["--lane", LANE, "--wip-reason", "x"])
    assert excinfo.value.code == 2
    assert "--ignore-wip" in capsys.readouterr().err


def test_ignore_wip_with_wip_reason_lets_the_draw_proceed(monkeypatch, capsys):
    """--ignore-wip --wip-reason passe le plafond -- et le dit en epilogue.

    Le passage outre ne se prend pas en silence : l'epilogue du tirage
    doit nommer le compte qui reste au-dessus du plafond.
    """
    _patch_guard(monkeypatch, _fleet(pig.WIP_CAP_DEFAULT))
    _patch_draw(monkeypatch)
    rc = pig.main(["--lane", LANE, "--ignore-wip",
                   "--wip-reason", "gel coordinateur, file entiere tenue"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" not in out
    assert "!! --ignore-wip" in out
    assert f"plafond {pig.WIP_CAP_DEFAULT}" in out
    assert "gel coordinateur, file entiere tenue" in out
    # le garde d'admission n'est PAS leve par le passage outre du plafond
    assert "!! --admit-reason" not in out


# --- composition avec le garde rouge ----------------------------------------


def test_red_and_wip_are_both_reported(monkeypatch, capsys):
    """Rouge ET plafond declenches : les deux motifs rendus, aucun masque.

    La lane porte 15 PRs dont une rouge de 30 h : l'en-tete vient du garde
    rouge (c'est la reparation la plus urgente), le plafond est rendu en
    PLUS avec sa propre file -- un garde qui en masquerait un autre
    laisserait la lane croire qu'un seul travail l'attend.
    """
    red = _state_red()
    prs = _fleet(pig.WIP_CAP_DEFAULT)
    states = {1: red}  # la plus ancienne est aussi la rouge
    _patch_guard(monkeypatch, prs, states)
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0
    head = out.splitlines()[0]
    assert "FILE DE REPARATION" in head
    assert "reparer ses propres PRs" in out      # motif rouge
    assert "drainer son WIP" in out or "PLAFOND DE WIP" in out  # motif WIP
    assert "check requis en echec" in out        # la cause rouge est bien la
    assert f"plafond de WIP = {pig.WIP_CAP_DEFAULT}" in out or \
        f"plafond = {pig.WIP_CAP_DEFAULT}" in out


def test_red_and_wip_json_composes_the_assignment(monkeypatch, capsys):
    """En sortie machine aussi : assignment compose, grain = premier rouge."""
    red = _state_red()
    prs = _fleet(pig.WIP_CAP_DEFAULT)
    _patch_guard(monkeypatch, prs, {1: red})
    rc = pig.main(["--lane", LANE, "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["mode"] == "repair"
    assert payload["assignment"] == "reparer-son-rouge+drainer-son-wip"
    assert payload["grain"]["number"] == 1
    assert payload["wip_triggered"] is True


def test_wip_guard_survives_a_fetch_failure(monkeypatch, capsys):
    """Panne reseau : le garde WIP ne bloque pas, mais le compte rendu le DIT.

    Meme principe que le garde rouge : un garde qui ne peut pas mesurer ne
    doit pas immobiliser la lane -- mais wip_count None (et non 0) pour
    qu'un zero d'absence de mesure ne se lise pas comme une ardoise vide.
    """
    def boom():
        raise OSError("gh injoignable")

    monkeypatch.setattr(pig, "fetch_open_prs", boom)
    monkeypatch.setattr(pig, "unaddressed_review_points", lambda nums: {})
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **k: ([], None))
    _patch_draw(monkeypatch)
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0
    assert "FILE DE REPARATION" not in out
    assert "indisponible" in out
