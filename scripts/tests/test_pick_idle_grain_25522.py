"""#25522 : classer les PRs rouges par QUI PEUT AGIR.

La fixture est l'etat de la lane `myia-po-2028:CoursIA` mesure le
2026-11-09 (issue #25522, section « Constat mesure » du body) :

- 4 PRs de la pile Chaines (#25028, #25029, #25033, #25036), **gelee par le
  coordinateur** -- leur age alimente `aged` et `count` ;
- des reserves de `clusterManager-Myia` (verdicts `CHANGES_REQUESTED
  (review-state)`, `LGTM (review-body)`, `VOIX-SANS-VERDICT (review-body)`) ;
- une jambe `PR gate` CANCELLED pendant la famine de runners, deja rejouee
  et en file.

Les PRs sont decrites ici, sans reseau : le test doit etre rejouable hors
ligne, et son verdict doit dependre du CLASSEMENT, pas de l'etat du
GitHub du jour.

Le marquage du gel est pose comme le coordinateur le pose
(`[FROZEN] <motif> -- <autorite>`, cf #24516) : au 09/11, les PRs de la
pile Chaines ne portaient pas encore de marqueur -- le gel y etait exprime
en prose sur l'issue mere #25013. C'est ce que le controle negatif 3
protege : un `[FROZEN]` d'une lane NON habilitee ne classe rien en `gel`.
"""

import subprocess
import sys
import types
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402

#: Le `subprocess.run` REEL, capture a l'import -- avant que la sentinelle
#: du module (`forbid_shell_escape`) ne le remplace. Le test de
#: `stale_picker` a besoin de lancer `git` pour de vrai ; il ne laisse
#: passer que `git`, et refuse tout le reste.
_REAL_RUN = subprocess.run

LANE = "myia-po-2028:CoursIA"

RESERVE_AT = "2026-11-05T09:00:00Z"
ASK_AFTER = "2026-11-05T10:00:00Z"
ASK_BEFORE = "2026-11-05T08:00:00Z"

FROZEN_BY_COORDINATOR = (
    "[FROZEN] gel coordinateur c2794 -- ai-01\n\n"
    "Pile Chaines gelee par le coordinateur (veto mainteneur).")
FROZEN_BY_FOREIGN_LANE = (
    "[FROZEN] accord de coordination -- lane myia-po-2027:CoursIA\n\n"
    "Gel pose par une lane qui n'est pas habilitee.")
ASK_BY_LANE = (
    "[ASK] lane myia-po-2028:CoursIA -- reserve tierce du 05/11, en attente "
    "de levee par ai-01 (le gate refuse de lever sous un autre login).")


def _pr(number, lane=LANE, age_hours=2.0):
    created = (pig.NOW - pig.dt.timedelta(hours=age_hours)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")
    return {"number": number, "title": f"pr {number}",
            "body": f"Grain: MED/notebook-python -- lane {lane}\n",
            "createdAt": created, "isDraft": False}


def _state(*, checks=(), mergeable="MERGEABLE", rollup_state="SUCCESS"):
    """Etat GraphQL d'une PR, forme rendue par `fetch_pr_states`.

    `checks` : tuples `(name, conclusion, is_required)` ou
    `(name, conclusion, is_required, started_at, completed_at)`.
    """
    nodes = []
    for check in checks:
        name, conclusion, required = check[0], check[1], check[2]
        started = check[3] if len(check) > 3 else "2026-11-08T09:00:00Z"
        completed = check[4] if len(check) > 4 else "2026-11-08T10:00:00Z"
        nodes.append({"name": name, "conclusion": conclusion,
                      "state": conclusion, "isRequired": required,
                      "startedAt": started, "completedAt": completed})
    return {"number": 1, "mergeable": mergeable,
            "reviews": {"nodes": []},
            "commits": {"nodes": [{"commit": {"statusCheckRollup": {
                "state": rollup_state, "contexts": {"nodes": nodes}}}}]}}


GREEN = _state(checks=[("PR gate", "SUCCESS", True)])
FAILED = _state(checks=[("PR gate", "FAILURE", True)])
#: Une jambe CANCELLED dont le rejeu est DEJA en vol : le geste est un rejeu,
#: pas une correction de diff (classe `infra`).
CANCELLED_WITH_RERUN = _state(
    checks=[("PR gate", "CANCELLED", True,
             "2026-11-08T09:00:00Z", "2026-11-08T10:00:00Z"),
            ("PR gate (requeue)", "", True, "2026-11-08T11:00:00Z",
             "2026-11-08T11:00:00Z")],
    rollup_state="PENDING")


def _nits(count=0, authors=(), verdict=None, surface="review-body",
          last_reserve_at=None):
    return {"count": count, "authors": list(authors), "verdict": verdict,
            "verdict_surface": surface, "last_reserve_at": last_reserve_at}


def _patch(monkeypatch, prs, states, nits, comments):
    """Neutralise les sources reseau et installe la fixture."""
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    monkeypatch.setattr(pig, "fetch_pr_states",
                        lambda nums: {n: states[n] for n in nums if n in states})
    monkeypatch.setattr(pig, "unaddressed_review_points_detail",
                        lambda nums: {k: v for k, v in nits.items()
                                      if k in nums})
    # Le fil de chaque PR : c'est la que sont le marqueur `[FROZEN]` et la
    # declaration `[ASK]`.
    monkeypatch.setattr(pig, "_red_pr_comments",
                        lambda n: list(comments.get(n, [])))
    # Sources annexes du garde rouge (memes raisons que dans le fichier de
    # tests historique) : la sonde de la tete de `main` et la lecture des
    # annotations d'un check-run.
    monkeypatch.setattr(pig, "fetch_main_head_probe", lambda *a, **k: None)
    monkeypatch.setattr(pig, "fetch_check_dwell", lambda rid: None)
    monkeypatch.setattr(pig, "fetch_check_organs", lambda rid: [])


def _fixture_po2028():
    """L'etat mesure de la lane po-2028 le 09/11 (issue #25522).

    Le gel est pose par le coordinateur (`-- ai-01`), la declaration
    `[ASK]` par la lane elle-meme, posterieure a la reserve.
    """
    prs = [
        _pr(25028, age_hours=66), _pr(25029, age_hours=65),
        _pr(25033, age_hours=65), _pr(25036, age_hours=64),
        _pr(25444, age_hours=24), _pr(25461, age_hours=24),
        _pr(25459, age_hours=2),
    ]
    states = {25028: GREEN, 25029: GREEN, 25033: GREEN, 25036: GREEN,
              25444: GREEN, 25461: CANCELLED_WITH_RERUN, 25459: FAILED}
    nits = {
        25028: _nits(1, ["clusterManager-Myia"], "CHANGES_REQUESTED",
                     "review-state", RESERVE_AT),
        25029: _nits(1, ["clusterManager-Myia"], "LGTM", "review-body",
                     RESERVE_AT),
        25033: _nits(1, ["clusterManager-Myia"], "LGTM", "review-body",
                     RESERVE_AT),
        25036: _nits(1, ["clusterManager-Myia"], "LGTM", "review-body",
                     RESERVE_AT),
        25444: _nits(1, ["clusterManager-Myia"], "LGTM", "review-body",
                     RESERVE_AT),
        25461: _nits(0),
        25459: _nits(0),
    }
    comments = {
        25028: [{"created_at": "2026-11-04T09:00:00Z",
                 "body": FROZEN_BY_COORDINATOR}],
        25029: [{"created_at": "2026-11-04T09:05:00Z",
                 "body": FROZEN_BY_COORDINATOR}],
        25033: [{"created_at": "2026-11-04T09:10:00Z",
                 "body": FROZEN_BY_COORDINATOR}],
        25036: [{"created_at": "2026-11-04T09:15:00Z",
                 "body": FROZEN_BY_COORDINATOR}],
        25444: [{"created_at": ASK_AFTER, "body": ASK_BY_LANE}],
    }
    return prs, states, nits, comments


def test_positif_la_file_ne_retain_plus_les_prs_gelees_ni_les_ask(monkeypatch):
    """Controle POSITIF de #25522 : le tapis est servi.

    Sur l'etat mesure de po-2028 du 09/11, la file de reparation ne
    retient plus les 4 PRs Chaines gelees, ni la PR declaree `[ASK]` en
    attente d'ai-01, ni la jambe d'infra : il ne reste que la PR que la
    lane peut reellement reparer.
    """
    prs, states, nits, comments = _fixture_po2028()
    _patch(monkeypatch, prs, states, nits, comments)
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert [r["number"] for r in out["red"]] == [25459]
    assert out["triggers"] == []
    waiting = {item["number"]: item["class"] for item in out["waiting_others"]}
    assert waiting == {25028: "gel", 25029: "gel", 25033: "gel",
                       25036: "gel", 25444: "coordinateur", 25461: "infra"}
    # Les classes sont rendues avec leur motif : la lane doit pouvoir les
    # recopier dans son [DONE] sans les re-deriver.
    assert all(item.get("reason") for item in out["waiting_others"])
    # Le JSON porte les classes, avec les numeros en chaines (cles JSON).
    assert set(out["red_classes"]) == {"25028", "25029", "25033", "25036",
                                       "25444", "25459", "25461"}


def test_sans_le_classement_les_memes_prs_retenaient_la_file(monkeypatch):
    """Le CONTRASTE du controle positif : meme fixture, sans marqueurs.

    Sans le gel du coordinateur et sans la declaration `[ASK]`, les PRs
    retombent en `lane` (fail-closed) et la file se referme : c'est
    exactement ce que #25522 corrige. Sans ce temoin, un `triggers == []`
    obtenu par une erreur de classement passerait pour un succes.
    """
    prs, states, nits, comments = _fixture_po2028()
    _patch(monkeypatch, prs, states, nits, {})
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert [r["number"] for r in out["red"]] == [25028, 25029, 25033, 25036,
                                                  25444, 25459]
    assert "nits" in out["triggers"]
    assert "aged" in out["triggers"]


def test_negatif_1_vrai_failure_reste_lane_et_bloque(monkeypatch):
    """Controle NEGATIF 1 : un vrai FAILURE reste `lane`, et il bloque.

    Un `FAILURE` sur un check REQUIS est un defaut de code : c'est la
    lane qui le repare, et la file doit la retenir (PR de 30 h : `aged`).
    """
    _patch(monkeypatch, [_pr(25459, age_hours=30)], {25459: FAILED},
           {25459: _nits(0)}, {})
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert [r["number"] for r in out["red"]] == [25459]
    assert out["red_classes"]["25459"]["class"] == "lane"
    assert "aged" in out["triggers"]


def test_negatif_2_reserve_tierce_sans_ask_reste_lane(monkeypatch):
    """Controle NEGATIF 2 : une reserve tierce sans `[ASK]` reste `lane`.

    La declaration `[ASK]` de la lane est ce qui fait basculer la PR en
    `coordinateur`. Sans elle -- ou posee AVANT la reserve -- la lane doit
    encore repondre a la reserve : fail-closed.
    """
    prs = [_pr(25444, age_hours=24)]
    states = {25444: GREEN}
    nits = {25444: _nits(1, ["clusterManager-Myia"], "LGTM", "review-body",
                            RESERVE_AT)}
    # (a) aucune declaration
    _patch(monkeypatch, prs, states, nits, {})
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert out["red_classes"]["25444"]["class"] == "lane"
    assert "nits" in out["triggers"]
    # (b) une declaration posee AVANT la reserve : elle ne repond pas a la
    # reserve, posee apres.
    _patch(monkeypatch, prs, states, nits,
           {25444: [{"created_at": ASK_BEFORE, "body": ASK_BY_LANE}]})
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert out["red_classes"]["25444"]["class"] == "lane"
    # (c) une declaration d'une AUTRE lane : elle ne dit rien de notre
    # reserve (le login GitHub est partage).
    _patch(monkeypatch, prs, states, nits,
           {25444: [{"created_at": ASK_AFTER,
                     "body": "[ASK] lane myia-po-2027:CoursIA -- en attente"}]})
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert out["red_classes"]["25444"]["class"] == "lane"


def test_negatif_3_frozen_d_une_lane_non_habilitee_ne_classe_pas_gel(monkeypatch):
    """Controle NEGATIF 3 : un `[FROZEN]` d'une lane tierce ne gele rien.

    Le login GitHub est partage : l'autorite d'un gel se lit dans le
    MARQUEUR, pas dans l'auteur du commentaire. Un gel pose par une lane
    qui n'est pas habilitee laisse la PR dans la file de la lane.
    """
    prs = [_pr(25028, age_hours=66)]
    states = {25028: GREEN}
    nits = {25028: _nits(1, ["clusterManager-Myia"], "CHANGES_REQUESTED",
                          "review-state", RESERVE_AT)}
    _patch(monkeypatch, prs, states, nits,
           {25028: [{"created_at": "2026-11-04T09:00:00Z",
                     "body": FROZEN_BY_FOREIGN_LANE}]})
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert out["red_classes"]["25028"]["class"] != "gel"
    assert [r["number"] for r in out["red"]] == [25028]


def test_le_gel_du_coordinateur_est_classe_gel_quelle_queue_soit_la_forme(monkeypatch):
    """Les DEUX formes d'autorite sont acceptees, et rien d'autre.

    La forme courte (`-- ai-01`) et la forme complete
    (`-- lane myia-ai-01:CoursIA`) sont les deux formes en usage dans la
    flotte (#24516) ; une autorite tierce ne l'est pas.
    """
    prs = [_pr(25028, age_hours=66)]
    states = {25028: GREEN}
    nits = {25028: _nits(1, ["clusterManager-Myia"], "CHANGES_REQUESTED",
                          "review-state", RESERVE_AT)}
    for marker in ("[FROZEN] gel -- ai-01",
                   "[FROZEN] gel -- lane myia-ai-01:CoursIA",
                   "[FROZEN] gel -- lane myia-po-2025:CoursIA-2"):
        _patch(monkeypatch, prs, states, nits,
               {25028: [{"created_at": "2026-11-04T09:00:00Z",
                         "body": marker}]})
        out = pig.red_backlog(LANE, 24, count_threshold=6)
        assert out["red_classes"]["25028"]["class"] == "gel", marker
        assert out["red"] == []


def test_un_degel_habilite_reclasse_la_pr_en_lane():
    """Un degel HABILITE ferme le gel qu'il suit : la PR revient en `lane`.

    Le fil se lit DANS L'ORDRE, comme `_issue_is_frozen`. Sans cela, une PR
    degelee qui porte un vrai `FAILURE` quittait la file de sa lane pour
    toujours : c'est un fail-open a rebours du contrat fail-closed.
    """
    comments = [
        {"created_at": "2026-11-08T10:00:00Z", "body": FROZEN_BY_COORDINATOR},
        {"created_at": "2026-11-09T10:00:00Z",
         "body": "[UNFROZEN] lane myia-ai-01:CoursIA -- pile degelee"},
    ]
    out = pig.classify_red_pr(
        lane="myia-po-2028:CoursIA", body="Grain: x",
        causes=["check requis en echec : Scripts Tests (FAILURE)"],
        nits={}, comments=comments)
    assert out["class"] == "lane", out
    # Le meme fil, lu par le lecteur d'issue, ne voit pas de gel non plus.
    assert pig._issue_is_frozen("Grain: x", comments) is None


def test_un_degel_d_une_lane_non_habilitee_laisse_le_gel(monkeypatch):
    """Un degel d'une lane NON habilitee ne ferme rien : la PR reste `gel`.

    Le login GitHub est partage : l'autorite du degel se lit dans la lane
    DECLAREE dans le marqueur, pas dans l'auteur du commentaire.
    """
    comments = [
        {"created_at": "2026-11-08T10:00:00Z", "body": FROZEN_BY_COORDINATOR},
        {"created_at": "2026-11-09T10:00:00Z",
         "body": "[UNFROZEN] lane myia-po-2027:CoursIA -- pile degelee"},
    ]
    out = pig.classify_red_pr(
        lane="myia-po-2028:CoursIA", body="Grain: x",
        causes=["check requis en echec : Scripts Tests (FAILURE)"],
        nits={}, comments=comments)
    assert out["class"] == "gel", out


def test_un_gel_pose_dans_le_body_suit_la_regle_a():
    """Un gel de BODY : seul le retrait de la ligne le leve.

    Un `[UNFROZEN]` habilite dans le fil ne le ferme pas -- c'est la regle A
    de la grammaire du gel (#24516).
    """
    body = ("Grain: MED/notebook-python -- lane myia-po-2028:CoursIA\n\n"
            "[FROZEN] gel coordinateur -- ai-01\n")
    comments = [{"created_at": "2026-11-09T10:00:00Z",
                 "body": "[UNFROZEN] lane myia-ai-01:CoursIA -- pile degelee"}]
    out = pig.classify_red_pr(
        lane="myia-po-2028:CoursIA", body=body,
        causes=["check requis en echec : Scripts Tests (FAILURE)"],
        nits={}, comments=comments)
    assert out["class"] == "gel", out


def test_la_classe_infra_ne_retient_pas_le_tapis(monkeypatch):
    """Une jambe CANCELLED deja rejouee est `infra` : le geste est un rejeu.

    Elle est RENDUE (la lane la recopie dans son [DONE]) et elle ne retient
    pas le tapis.
    """
    prs = [_pr(25461, age_hours=24)]
    _patch(monkeypatch, prs, {25461: CANCELLED_WITH_RERUN},
           {25461: _nits(0)}, {})
    out = pig.red_backlog(LANE, 24, count_threshold=6)
    assert out["red_classes"]["25461"]["class"] == "infra"
    assert out["red"] == []
    assert [item["number"] for item in out["waiting_others"]] == [25461]


# --- #25522 point 4 : la fenetre de service s'etend par tranches ----------


def _belt_item(number, klass="grain"):
    """Un candidat du tapis, forme minimale (comme `_make_item` du fichier
    de tests du tapis)."""
    return {"number": number, "klass": klass, "age": 5, "idle": 1,
            "genre": "docs", "labels": [], "title": f"issue #{number}",
            "created_at": "2026-11-01T00:00:00Z",
            "last_delivery_stamp": None}


def _belt_args(grains=4):
    return types.SimpleNamespace(grains=grains, include_delivered=False,
                                  lane=LANE)


def _no_probe(n, lane=None):
    return False


def test_la_fenetre_s_etend_par_tranches_et_trouve_le_grain_au_dela():
    """Controle POSITIF du point 4 : quota non rempli + du temps -> fenetre
    etendue.

    Le pool du 09/11 : 70 positions parcourues, 0 retenu, et rien ne disait
    si le grain servable etait plus loin. La fenetre s'etend par tranches
    (70 -> 140 -> 210...) tant que la lane a moins de grains que demandes
    (11/11 : plus seulement quand elle n'en a aucun) ET qu'il reste du temps
    sous le mur ; le grain est alors servi.
    """
    args = _belt_args(grains=4)
    pool = [_belt_item(1000 + i) for i in range(150)]
    claims = {it["number"]: (pig.CLAIM_CODE_BLOCKED, "claim d'une autre lane")
              for it in pool[:80]}
    claims[pool[80]["number"]] = (pig.CLAIM_CODE_FREE, "libre")
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, claims, args, probe_budget=8,
        delivered_probe=_no_probe,
        merged_pr_probe=_no_probe,
        claims_probe=lambda numbers: {
            n: (pig.CLAIM_CODE_BLOCKED, "claim d'une autre lane")
            for n in numbers})
    assert [p["number"] for p in picks] == [pool[80]["number"]]
    assert state["service_window_extended"] is True
    # Un seul grain trouve sur 4 demandes : la fenetre continue de s'etendre
    # jusqu'au bout du pool (140 -> 150), au lieu de s'arreter a la tranche
    # ou le premier grain est apparu.
    assert state["service_window"] == 150
    assert state["service_positions"] == 150


def test_le_mur_de_temps_arrete_l_extension_de_la_fenetre():
    """Le mur prime sur l'extension : sans temps, la fenetre ne bouge pas.

    L'extension ne sert qu'a trouver un grain que la lane aurait pu
    prendre. Sous le mur, aucune sonde ne peut etre emise : la boucle
    s'arrete a la fenetre normale et le dit.
    """
    args = _belt_args(grains=4)
    pool = [_belt_item(2000 + i) for i in range(150)]
    claims = {it["number"]: (pig.CLAIM_CODE_BLOCKED, "claim d'une autre lane")
              for it in pool}
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, claims, args, probe_budget=8, time_budget_s=0,
        delivered_probe=_no_probe, merged_pr_probe=_no_probe)
    assert picks == []
    assert state["service_window_extended"] is False
    assert state["service_positions"] == 70


def test_un_pool_vide_ne_produit_ni_grain_ni_extension():
    """Controle NEGATIF du point 4 : un pool vraiment vide rend 0, et le dit.

    L'extension ne doit pas transformer un pool vide en boucle : le
    controle negatif est ce qui distingue « le pool n'a rien » de « le
    picker n'a rien cherché ».
    """
    picks, withheld, state = pig.belt_pick_with_replacements(
        [], {}, _belt_args(grains=4), probe_budget=8,
        delivered_probe=_no_probe, merged_pr_probe=_no_probe)
    assert picks == []
    assert withheld == []
    assert state["service_positions"] == 0
    assert state["service_window_extended"] is False
    assert state["pending_deliveries"] == 0


def test_la_sortie_nome_les_positions_parcourues_et_les_livraisons_en_attente():
    """Les deux nombres du point 4 sont RENDUS, pas calcules en silence.

    « 0 retenu » doit dire ce que la boucle a couvert : sans ces deux
    nombres, la lane ne peut pas distinguer un pool vide d'une fenetre
    de positions toutes livrees.
    """
    args = _belt_args(grains=4)
    pool = [_belt_item(3000 + i) for i in range(4)]
    claims = {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in pool}
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, claims, args, probe_budget=8,
        delivered_probe=lambda n, lane=None: n == 3000,
        merged_pr_probe=_no_probe)
    assert state["service_positions"] == 4
    assert state["pending_deliveries"] == 1
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[3000].startswith("LIVRAISON")


def _git_only_run(argv, *args, **kwargs):
    """Laisse passer `git`, refuse tout le reste (sentinelle du module)."""
    if isinstance(argv, (list, tuple)) and argv and str(argv[0]) == "git":
        return _REAL_RUN(argv, *args, **kwargs)
    raise AssertionError(f"processus non simule : {argv}")


def _make_repo(tmp_path):
    """Un depot jetable avec un `origin/main` local et un picker script."""
    repo = tmp_path / "repo"
    (repo / "scripts").mkdir(parents=True)
    script = repo / "scripts" / "pick_idle_grain.py"
    script.write_text("# version 1\n", encoding="utf-8")
    _REAL_RUN(["git", "init", "-q", str(repo)], check=True,
              capture_output=True)
    _REAL_RUN(["git", "-C", str(repo), "add", "-A"], check=True,
              capture_output=True)
    _REAL_RUN(["git", "-C", str(repo), "-c", "user.email=t@t", "-c",
               "user.name=t", "commit", "-q", "-m", "init"], check=True,
              capture_output=True)
    _REAL_RUN(["git", "-C", str(repo), "update-ref",
               "refs/remotes/origin/main", "HEAD"], check=True,
              capture_output=True)
    return repo, script


def test_stale_picker_faux_si_le_picker_est_identique_a_origin_main(tmp_path,
                                                                   monkeypatch):
    """`stale_picker` est faux quand le fichier local est celui d'origin/main."""
    repo, script = _make_repo(tmp_path)
    monkeypatch.setattr(subprocess, "run", _git_only_run)
    state = pig.picker_stale_state(script)
    assert state["stale"] is False
    assert state["local"] and state["origin_main"]
    assert state["local"] == state["origin_main"]


def test_stale_picker_vrai_si_le_picker_diffe_d_origin_main(tmp_path,
                                                           monkeypatch):
    """`stale_picker` est vrai des que le fichier local differe.

    C'est la mesure du 09/11 : `main` fige a 15:48Z, correctif du mur de
    boucle sur `main` depuis 16:16Z, et des tirages rendus avec l'ancien
    contrat sans que rien ne le signale.
    """
    repo, script = _make_repo(tmp_path)
    monkeypatch.setattr(subprocess, "run", _git_only_run)
    script.write_text("# version 2 -- le contrat a change\n", encoding="utf-8")
    state = pig.picker_stale_state(script)
    assert state["stale"] is True
    assert state["local"] != state["origin_main"]
    assert "origin/main" in state["reason"]
