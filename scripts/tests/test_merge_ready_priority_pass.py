"""Temoins de la priorite de service DANS LA PASSE ``merge_ready`` (#28009).

Second module des temoins de la lecture GROUPEE des approbations. Le
premier, ``test_merge_ready_priority.py``, porte le temoin de l'ORDRE, le
canon, la requete et les pannes de la lecture, et definit les faux (serveur
GraphQL, runner, constructeurs). Celui-ci reprend ces faux et verifie ce que
la priorite fait a la passe ENTIERE :

- UNE lecture a l'ouverture, apres la liste des PRs et avant la premiere
  vue -- jamais une par PR ;
- le bilan nomme les approuvees et les lectures incompletes, ou le motif
  d'une lecture non mesuree (cas reel du 27/11 : seau GraphQL epuise) ;
- la priorite est un renseignement d'ORDRE : gardes et verdicts inchanges,
  aucune fusion sur la foi de la seule lecture d'ordre ;
- le curseur tourne aussi dans le groupe approuve, et le reste est servi
  des que ce groupe laisse la place.

Les fixtures autouse sont PAR MODULE (un import ne les apporte pas) : elles
sont reposees ici, a l'identique du premier module. Aucun reseau, la aussi.
"""

import pytest

import scripts.tests.test_merge_ready as organ
from scripts.tests.test_merge_ready import ScriptedRunner, default_view, run_organ
from scripts.tests.test_merge_ready_priority import (
    HEAD,
    HEAD_MOVED,
    HUMAIN,
    ORG,
    QUOTA_GRAPHQL,
    PriorityRunner,
    ServeurPriorite,
    _fusions,
    _index_de_pile_vide,
    _lectures,
    _noeud,
    _page,
    _revue,
    _serveur,
    _vues,
)


@pytest.fixture(autouse=True)
def _porte_stack_mesuree(monkeypatch):
    """Porte STACK injectee (comme dans `test_merge_ready.py`) : aucun git."""
    monkeypatch.setattr(ORG.gate, "default_stack_index", _index_de_pile_vide)


@pytest.fixture(autouse=True)
def _construction_de_pile_vierge(monkeypatch):
    """Chaque test repart d'une construction VIERGE (etat du module execute)."""
    monkeypatch.setattr(
        ORG, "_PILE_CONSTRUCTION",
        {"evenement": None, "resultat": None, "echeance": None},
        raising=False,
    )


# --- dans la passe : une lecture a l'ouverture, jamais une par PR ------------------


def test_une_seule_lecture_a_l_ouverture_avant_toute_vue_de_pr(tmp_path):
    serveur = ServeurPriorite({
        None: _page(
            [_noeud(101), _noeud(102, {HUMAIN: [_revue()]})], suite=True, curseur="c1"
        ),
        "c1": _page([_noeud(103, {HUMAIN: [_revue()]})]),
    })
    runner = PriorityRunner(
        serveur=serveur, prs=(101, 102, 103), views=_vues((101, 102, 103), {102, 103})
    )

    rc, lines, _ = run_organ(tmp_path, runner)

    assert rc == 0
    assert [row["pr"] for row in lines] == [102, 103, 101]
    lectures = _lectures(runner)
    assert len(lectures) == 2, "une requete par page, aucune par PR"
    liste = next(
        rang for rang, (cmd, _) in enumerate(runner.calls)
        if cmd[:3] == ["gh", "pr", "list"]
    )
    premiere_vue = min(
        rang for rang, (cmd, _) in enumerate(runner.calls)
        if cmd[:3] == ["gh", "pr", "view"]
    )
    assert liste < lectures[0][0] <= lectures[-1][0] < premiere_vue


def test_une_pr_approuvee_absente_de_la_file_ne_derange_pas_la_passe(tmp_path):
    """Entre la liste et la lecture, une PR a pu se fermer : elle est ignoree."""
    runner = PriorityRunner(
        serveur=ServeurPriorite({None: _page([
            _noeud(101), _noeud(102), _noeud(999, {HUMAIN: [_revue()]}),
        ])}),
        prs=(101, 102), views=_vues((101, 102)),
    )

    rc, lines, _ = run_organ(tmp_path, runner, extra=("--json",))

    assert rc == 0
    assert [row["pr"] for row in lines] == [101, 102]


def test_le_bilan_nomme_les_approuvees_et_les_lectures_incompletes(tmp_path, capsys):
    runner = PriorityRunner(
        serveur=ServeurPriorite({None: _page([
            _noeud(101), _noeud(102, {HUMAIN: [_revue()]}),
            _noeud(103, {HUMAIN: [_revue()]}, tete=""),
        ])}),
        prs=(101, 102, 103), views=_vues((101, 102, 103), {102}),
    )

    rc, _, _ = run_organ(tmp_path, runner, extra=("--json",))

    assert rc == 0
    assert organ._payload(capsys)["priority"] == {
        "read": "measured",
        "approved": [102],
        "truncated": [103],
        "pages": 1,
        "read_prs": 3,
    }


def test_une_lecture_non_mesuree_laisse_l_ordre_du_curseur_et_le_dit(tmp_path, capsys):
    """Le runner ne sert pas la lecture : priorite NON MESUREE, ordre inchange."""
    runner = ScriptedRunner(prs=(101, 102, 103), views=_vues((101, 102, 103), {102}))

    rc, lines, _ = run_organ(tmp_path, runner, extra=("--json",))

    assert rc == 0
    assert [row["pr"] for row in lines] == [101, 102, 103]
    priorite = organ._payload(capsys)["priority"]
    assert priorite["read"] == "unreadable"
    assert priorite["reason"].startswith("AssertionError : commande non scriptee")

    runner = ScriptedRunner(prs=(101, 102), views=_vues((101, 102)))
    rc, _, _ = run_organ(tmp_path, runner)
    resume = capsys.readouterr().out
    assert rc == 0
    ligne = next(l for l in resume.splitlines() if l.startswith("priorite :"))
    assert ligne.startswith("priorite : NON MESUREE (AssertionError : commande non scriptee")
    assert ligne.endswith("-- ordre du curseur seul")


def test_un_quota_graphql_epuise_est_nomme_dans_le_bilan_et_l_ordre_tient(tmp_path, capsys):
    """Le cas reel du 27/11 : seau GraphQL epuise pour le jeton partage de la flotte.

    La passe continue sur l'ordre du curseur -- aucune PR approuvee n'est
    servie en premier, puisque la lecture n'a rien etabli -- et son bilan dit
    POURQUOI.
    """
    def runner_a_quota() -> PriorityRunner:
        serveur = _serveur({102})
        serveur.rc[None] = 1
        serveur.stderr = QUOTA_GRAPHQL
        return PriorityRunner(
            serveur=serveur, prs=(101, 102, 103), views=_vues((101, 102, 103), {102}),
        )

    rc, lines, _ = run_organ(tmp_path, runner_a_quota(), extra=("--json",))

    assert rc == 0
    assert [row["pr"] for row in lines] == [101, 102, 103]
    assert organ._payload(capsys)["priority"] == {
        "read": "unreadable", "reason": "page 1 rc=1 : " + QUOTA_GRAPHQL,
    }

    rc, _, _ = run_organ(tmp_path, runner_a_quota())
    resume = capsys.readouterr().out

    assert rc == 0
    ligne = next(l for l in resume.splitlines() if l.startswith("priorite :"))
    assert ligne == "priorite : NON MESUREE (page 1 rc=1 : " + QUOTA_GRAPHQL + ")" \
        " -- ordre du curseur seul"


# --- la priorite est un renseignement d'ORDRE : gardes et verdicts inchanges -------


def test_une_pr_priorisee_mais_sale_est_sautee_et_rien_n_est_fusionne(tmp_path):
    runner = PriorityRunner(
        serveur=_serveur({102}), prs=(101, 102), views=_vues((101, 102), {102}),
        pulls=[{"mergeable_state": "dirty", "head": {"sha": HEAD}}],
    )

    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    rows = {row["pr"]: row for row in lines}
    assert rc == 0
    assert [row["pr"] for row in lines] == [102, 101], "servie en premier quand meme"
    assert rows[102]["verdict"] == "skipped"
    assert rows[102]["reason"] == "mergeable-state:dirty"
    assert rows[101]["reason"] == "no-coordinator-approval"
    assert not _fusions(runner)


def test_la_priorite_ne_cree_jamais_une_approbation(tmp_path):
    """La lecture groupee dit « approuvee », la lecture TYPEE de l'etape 2ter dit non.

    Le verdict releve de l'etape 2ter, sur la tete EVALUEE : la PR est servie
    en premier, et sautee comme avant.
    """
    runner = PriorityRunner(
        serveur=_serveur({102}), prs=(101, 102), views=_vues((101, 102), set())
    )

    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    rows = {row["pr"]: row for row in lines}
    assert rc == 0
    assert [row["pr"] for row in lines] == [102, 101]
    assert rows[102]["verdict"] == "skipped"
    assert rows[102]["reason"] == "no-coordinator-approval"
    assert not _fusions(runner)


def test_le_verdict_releve_de_la_lecture_typee_pas_de_la_lecture_groupee(tmp_path):
    """La lecture groupee dit « approuvee a la tete » ; la vue EVALUEE dit non.

    Entre les deux lectures, la derniere voix du coordinateur a pu changer, ou
    la tete a bouger : l'etape 2ter relit les reviews sur la tete evaluee. Une
    approbation qui ne couvre pas cette tete est perime ou inverifiable --
    jamais une fusion sur la foi de la seule lecture d'ordre.
    """
    vues = _vues((101, 102), {102})
    vues[102] = default_view(pr=102, coordinator=HEAD_MOVED)
    runner = PriorityRunner(serveur=_serveur({102}), prs=(101, 102), views=vues)

    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    rows = {row["pr"]: row for row in lines}
    assert rc == 0
    assert [row["pr"] for row in lines] == [102, 101]
    assert rows[102]["verdict"] == "skipped"
    assert rows[102]["reason"].startswith("coordinator-approval-")
    assert not _fusions(runner)


# --- le curseur tourne aussi dans le groupe approuve -------------------------------


def test_le_curseur_tourne_dans_le_groupe_approuve(tmp_path, monkeypatch):
    """Trois approuvees, deux par passe : chacune attend son tour, aucune ne meurt de faim.

    Sans ordre du curseur DANS le groupe, chaque passe repartirait des deux
    premieres approuvees et la troisieme ne serait jamais evaluee -- le defaut
    meme que le curseur ferme pour la file entiere.
    """
    monkeypatch.setattr(ORG, "_clock", organ._fake_clock(100.0))
    prs = tuple(range(101, 111))
    approuvees = {102, 104, 106}
    journal = tmp_path / "journal.jsonl"
    passes = []
    for _ in range(4):
        # Le journal CUMULE les passes : on ne lit que les lignes de celle-ci.
        deja = (
            len(journal.read_text(encoding="utf-8").splitlines())
            if journal.is_file() else 0
        )
        runner = PriorityRunner(
            serveur=_serveur(approuvees, pool=prs), prs=prs, views=_vues(prs, approuvees)
        )
        rc, lines, _ = run_organ(tmp_path, runner, extra=("--pass-budget-s", "250"))
        assert rc == 0
        passes.append(lines[deja:])

    tour = [[row["pr"] for row in passe] for passe in passes]
    assert [passe[:2] for passe in tour] == [
        [102, 104], [106, 102], [104, 106], [102, 104]
    ]
    # Les non-approuvees attendent : la passe n'evalue que deux PRs.
    assert all(
        row["verdict"] == ORG.VERDICT_NOT_EVALUATED
        for passe in passes for row in passe[2:]
    )
    # Le curseur de reprise est la derniere PR evaluee -- dans le groupe approuve.
    assert ORG.read_pass_cursor(journal) == 104


def test_le_reste_est_servi_des_que_le_groupe_approuve_laisse_la_place(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(ORG, "_clock", organ._fake_clock(100.0))
    prs = tuple(range(101, 107))

    runner = PriorityRunner(
        serveur=_serveur({103}, pool=prs), prs=prs, views=_vues(prs, {103})
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--pass-budget-s", "250"))

    assert rc == 0
    evaluees = [row["pr"] for row in lines if row["verdict"] != ORG.VERDICT_NOT_EVALUATED]
    assert evaluees == [103, 101]

