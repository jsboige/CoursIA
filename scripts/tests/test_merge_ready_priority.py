"""Temoins de la PRIORITE DE SERVICE de l'organe `merge_ready` (#28009).

Ordre du coordinateur : la passe evalue d'abord les PRs approuvees par
`myia-ai-01` a la TETE EXACTE, puis les autres -- chaque groupe dans l'ordre
du curseur de reprise. Une PR approuvee est la seule qui puisse etre
fusionnee : quand la passe s'arrete sur son budget de duree, elle ne doit pas
attendre derriere des PRs qui ne peuvent pas l'etre.

Ce que ces temoins verrouillent, et pourquoi :

- le TEMOIN de l'ordre : une PR approuvee au-dessus du curseur, derriere six
  PRs non approuvees dans l'ordre de la passe, est servie EN PREMIER. Sans la
  priorite, la passe s'arrete sur son budget avant de l'atteindre et la
  journalise `unevaluated` ;
- la lecture est GROUPEE : UNE lecture GraphQL paginee a l'ouverture de la
  passe, jamais une par PR (le jeton du coordinateur est partage) ;
- l'incompletude est NOMMEE : une lecture en panne ne vaut jamais « aucune PR
  approuvee » -- l'ordre du curseur s'applique seul, et le bilan le dit ;
- la priorite est un renseignement d'ORDRE : elle ne cree ni approbation ni
  fusion. Le verdict de chaque PR reste decide par l'etape 2ter (lecture
  TYPEE, sur la tete evaluee) et par les gardes.

Aucun reseau : la lecture groupee est servie par un faux serveur GraphQL,
page par VALEUR du curseur. Une requete qui ne porte pas le curseur sous le
nom de la variable de la requete recoit la premiere page -- le defaut mesure
le 27/11 sur le pool reel (garde de 20 pages atteinte au premier essai).
"""

import json

import pytest

import scripts.tests.test_merge_ready as organ
from scripts.tests.test_merge_ready import ScriptedRunner, default_view, run_organ

#: Le module que ``run_organ`` execute (charge par chemin, pas par son nom).
ORG = organ.mr
HEAD = organ.HEAD
HEAD_MOVED = organ.HEAD_MOVED
#: Login humain du coordinateur.
HUMAIN = "myia-ai-01"
#: Voix App du coordinateur, en orthographe canonique (suffixe compris).
APP = "coursia-coord-ai01[bot]"
#: Le meme login, nu, comme le serveur GraphQL le rend sur une ligne.
NU = "coursia-coord-ai01"
#: Login -> alias sous lequel la requete demande cette voix. Ecrit en dur ici :
#: le faux serveur repond a la FORME de la requete, il ne la deduit pas de
#: l'organe -- ainsi le temoin d'ordre echoue sur l'ORDRE quand la priorite
#: manque, pas sur un attribut absent. Le test
#: ``test_les_alias_du_faux_sont_ceux_de_la_requete`` recoupe les deux.
ALIAS = {APP: "voix0", HUMAIN: "voix1"}


def _index_de_pile_vide() -> dict:
    """Index de pile vide : porte MESUREE, aucun appel git reel."""
    return {}


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


# --- le faux serveur GraphQL ------------------------------------------------------


def _revue(
    *,
    login: str = HUMAIN,
    type_auteur: str = "User",
    etat: str = "APPROVED",
    oid: str = HEAD,
    date: str = "2026-11-27T10:00:00Z",
    corps: str = "",
) -> dict:
    """Une review, forme GraphQL : le TYPE de l'auteur est porte par la ligne."""
    return {
        "state": etat,
        "body": corps,
        "submittedAt": date,
        "author": {"login": login, "__typename": type_auteur},
        "commit": {"oid": oid},
    }


def _noeud(
    pr: int,
    voix: dict[str, list[dict]] | None = None,
    *,
    tete: str = HEAD,
    totaux: dict[str, int] | None = None,
) -> dict:
    """Un noeud PR tel que la requete le demande : une connexion par voix."""
    noeud: dict = {"number": pr, "headRefOid": tete}
    for login, alias in ALIAS.items():
        revues = list((voix or {}).get(login) or [])
        noeud[alias] = {
            "totalCount": (totaux or {}).get(login, len(revues)),
            "nodes": revues,
        }
    return noeud


def _page(noeuds: list[dict], *, suite: bool = False, curseur: str | None = None) -> dict:
    return {"data": {"repository": {"pullRequests": {
        "pageInfo": {"hasNextPage": suite, "endCursor": curseur},
        "nodes": list(noeuds),
    }}}}


class ServeurPriorite:
    """Le serveur GraphQL, tel qu'il repond a la lecture groupee.

    Une page par VALEUR du curseur ``after`` ; une requete sans curseur recoit
    la premiere. Un curseur inconnu rend une erreur GraphQL, comme le vrai
    serveur ; ``rc`` rend une page ILLISIBLE (quota, 5xx) pour un curseur donne.
    """

    def __init__(self, pages: dict[str | None, object]) -> None:
        self.pages = pages
        self.rc: dict[str | None, int] = {}
        #: Valeur du curseur de chaque requete recue, dans l'ordre.
        self.appels: list[str | None] = []

    def repondre(self, cmd: list[str]):
        apres = next(
            (arg[len("after="):] for arg in cmd if arg.startswith("after=")), None
        )
        self.appels.append(apres)
        if apres in self.rc:
            return ORG.RunResult(self.rc[apres], "", "gh: HTTP 500")
        if apres not in self.pages:
            return ORG.RunResult(0, json.dumps(
                {"errors": [{"message": "INVALID_CURSOR_ARGUMENTS"}]}
            ), "")
        page = self.pages[apres]
        brut = page if isinstance(page, str) else json.dumps(page)
        return ORG.RunResult(0, brut, "")


class PriorityRunner(ScriptedRunner):
    """Le runner scripte de l'organe, qui sert en plus ``gh api graphql``.

    ``serveur=None`` : la lecture groupee n'est pas scriptee, et le runner
    leve comme le fait ``ScriptedRunner`` pour toute commande inattendue.
    Il MEMORISE les budgets poses par l'organe.
    """

    def __init__(self, *, serveur: ServeurPriorite | None = None, **kwargs) -> None:
        super().__init__(**kwargs)
        self.serveur = serveur
        self.budgets: list[float | None] = []

    def set_pr_budget(self, budget_s) -> None:
        self.budgets.append(budget_s)

    def run(self, cmd: list[str], env: dict | None = None):
        if cmd[:3] == ["gh", "api", "graphql"] and self.serveur is not None:
            self.calls.append((list(cmd), env))
            return self.serveur.repondre(cmd)
        return super().run(cmd, env)


def _serveur(approuvees=(), *, pool=None) -> ServeurPriorite:
    """UNE page : les approuvees portent un APPROVED du coordinateur a la tete."""
    noeuds = []
    for pr in (pool if pool is not None else sorted(approuvees)):
        voix = {HUMAIN: [_revue()]} if pr in approuvees else None
        noeuds.append(_noeud(pr, voix))
    return ServeurPriorite({None: _page(noeuds)})


def _vues(prs, approuvees=()) -> dict[int, dict]:
    """Vues ``gh pr view`` : l'approbation du coordinateur a la tete, ou aucune."""
    return {
        pr: default_view(pr=pr, coordinator=None if pr not in approuvees else HEAD)
        for pr in prs
    }


def _lectures(runner: ScriptedRunner) -> list[tuple[int, list[str]]]:
    """Rang et commande de chaque lecture groupee dans la trace du runner."""
    return [
        (rang, cmd) for rang, (cmd, _) in enumerate(runner.calls)
        if cmd[:3] == ["gh", "api", "graphql"]
    ]


def _fusions(runner: ScriptedRunner) -> list[list[str]]:
    return [cmd for cmd in runner.cmds() if cmd[:3] == ["gh", "pr", "merge"]]


# --- LE TEMOIN de l'ordre (celui demande par le coordinateur) ----------------------
#
# Dix PRs, UNE approuvee (#105). Le curseur de reprise est sur #108 : l'ordre
# de la passe est 109, 110, puis 101 a 108 -- la PR approuvee attend derriere
# SIX PRs non approuvees. Budget de 250 s, horloge de 100 s par lecture : la
# passe evalue deux PRs, puis s'arrete sur son budget.

PRS_TEMOIN = tuple(range(101, 111))
CURSEUR_TEMOIN = 108


def _temoin(tmp_path, monkeypatch, runner: ScriptedRunner, mode: str):
    monkeypatch.setattr(ORG, "_clock", organ._fake_clock(100.0))
    journal = tmp_path / "journal.jsonl"
    ORG.write_pass_cursor(journal, CURSEUR_TEMOIN)
    extra = ("--pass-budget-s", "250") + (("--apply",) if mode == "apply" else ())
    return run_organ(tmp_path, runner, extra=extra)


@pytest.mark.parametrize("mode", ("dry-run", "apply"))
def test_une_pr_approuvee_derriere_des_prs_non_approuvees_est_servie_en_premier(
    tmp_path, monkeypatch, mode
):
    """La PR approuvee est EVALUEE EN PREMIER, malgre le budget de la passe.

    Falsification : sans la priorite, la passe evalue 109 et 110, s'arrete sur
    son budget, et #105 reste `unevaluated` -- une PR prete a fusionner qui
    attend derriere des PRs qui ne le peuvent pas. C'est le controle
    `test_sans_priorite_mesuree_...` ci-dessous.
    """
    runner = PriorityRunner(
        serveur=_serveur({105}, pool=PRS_TEMOIN),
        prs=PRS_TEMOIN, views=_vues(PRS_TEMOIN, {105}),
    )
    rc, lines, _ = _temoin(tmp_path, monkeypatch, runner, mode)

    assert rc == 0
    ordre = [row["pr"] for row in lines]
    assert ordre[:2] == [105, 109], "la PR approuvee doit etre servie EN PREMIER"
    assert ordre == [105, 109, 110, 101, 102, 103, 104, 106, 107, 108]
    assert lines[0]["verdict"] == ("merged" if mode == "apply" else "would-merge")
    assert lines[0]["review"] == ORG.APPROVED_EXACT_HEAD
    assert organ._evaluated(runner, 105)
    non_evaluees = [
        row["pr"] for row in lines if row["verdict"] == ORG.VERDICT_NOT_EVALUATED
    ]
    assert non_evaluees == [110, 101, 102, 103, 104, 106, 107, 108]
    assert [cmd[3] for cmd in _fusions(runner)] == (["105"] if mode == "apply" else [])


def test_sans_priorite_mesuree_la_meme_file_laisse_la_pr_approuvee_non_evaluee(
    tmp_path, monkeypatch
):
    """CONTROLE du temoin : lecture non mesuree = ordre du curseur seul.

    Ici le runner ne sert pas la lecture groupee : la priorite n'est pas
    mesuree, et la file se comporte comme avant -- la PR approuvee attend.
    Ce controle passe AVANT le correctif : il prouve que le temoin ci-dessus
    echoue pour la raison qu'il nomme.
    """
    runner = ScriptedRunner(prs=PRS_TEMOIN, views=_vues(PRS_TEMOIN, {105}))
    rc, lines, _ = _temoin(tmp_path, monkeypatch, runner, "dry-run")

    assert rc == 0
    assert [row["pr"] for row in lines][:2] == [109, 110]
    non_evaluees = [
        row["pr"] for row in lines if row["verdict"] == ORG.VERDICT_NOT_EVALUATED
    ]
    assert non_evaluees == [101, 102, 103, 104, 105, 106, 107, 108]
    assert not organ._evaluated(runner, 105)


# --- la fonction d'ordre -----------------------------------------------------------


def test_l_ordre_est_une_partition_stable_par_numero():
    source = [104, 101, 102, 103]
    assert ORG._ordonner_par_priorite(source, {102}) == [102, 104, 101, 103]
    # Sans approuvee, ou toutes approuvees : l'ordre recu, a l'identique.
    assert ORG._ordonner_par_priorite(source, set()) == source
    assert ORG._ordonner_par_priorite(source, set(source)) == source
    # Une approuvee hors de la file (fermee entre les deux lectures) est ignoree.
    assert ORG._ordonner_par_priorite(source, {999}) == source
    # La liste recue n'est jamais mutee.
    assert source == [104, 101, 102, 103]


# --- le canon : seule une approbation REELLE a la tete exacte priorise --------------


@pytest.mark.parametrize(
    ("cas", "noeud", "approuvee"),
    [
        ("humain, APPROVED a la tete", _noeud(102, {HUMAIN: [_revue()]}), True),
        (
            "App du coordinateur, ligne typee Bot",
            _noeud(102, {APP: [_revue(login=NU, type_auteur="Bot")]}),
            True,
        ),
        (
            "App du coordinateur, login deja suffixe",
            _noeud(102, {APP: [_revue(login=APP, type_auteur="Bot")]}),
            True,
        ),
        (
            "App, ligne NON typee",
            _noeud(102, {APP: [_revue(login=APP, type_auteur="")]}),
            False,
        ),
        (
            "App, homonyme UTILISATEUR du slug",
            _noeud(102, {APP: [_revue(login=NU, type_auteur="User")]}),
            False,
        ),
        ("oid de commit vide", _noeud(102, {HUMAIN: [_revue(oid="")]}), False),
        (
            "approbation sur une tete anterieure",
            _noeud(102, {HUMAIN: [_revue(oid=HEAD_MOVED)]}),
            False,
        ),
        (
            "APPROVED puis CHANGES_REQUESTED",
            _noeud(102, {HUMAIN: [
                _revue(),
                _revue(etat="CHANGES_REQUESTED", date="2026-11-27T11:00:00Z"),
            ]}),
            False,
        ),
        (
            "CHANGES_REQUESTED puis APPROVED",
            _noeud(102, {HUMAIN: [
                _revue(etat="CHANGES_REQUESTED"),
                _revue(date="2026-11-27T11:00:00Z"),
            ]}),
            True,
        ),
        (
            "APPROVED puis CONCERNS en corps",
            _noeud(102, {HUMAIN: [
                _revue(),
                _revue(etat="COMMENTED", corps="VERDICT: CONCERNS\na reprendre",
                       date="2026-11-27T11:00:00Z"),
            ]}),
            False,
        ),
        (
            "APPROVED puis COMMENTED muet (une phrase de levee)",
            _noeud(102, {HUMAIN: [
                _revue(),
                _revue(etat="COMMENTED", corps="Point 2 leve : traite par le commit abc.",
                       date="2026-11-27T11:00:00Z"),
            ]}),
            True,
        ),
        ("approbation DISMISSED", _noeud(102, {HUMAIN: [_revue(etat="DISMISSED")]}), False),
        (
            "APPROVED d'un autre auteur",
            _noeud(102, {HUMAIN: [_revue(login="clusterManager-Myia")]}),
            False,
        ),
        ("aucune voix du coordinateur", _noeud(102), False),
        ("sans tete lue", _noeud(102, {HUMAIN: [_revue()]}, tete=""), False),
        (
            "fenetre de reviews tronquee",
            _noeud(102, {HUMAIN: [_revue()]}, totaux={HUMAIN: 11}),
            False,
        ),
    ],
)
def test_seule_une_approbation_reelle_a_la_tete_exacte_priorise(cas, noeud, approuvee):
    approuvees, _tronquees = ORG._priorite_approuvees([noeud])
    assert (102 in approuvees) is approuvee, cas


def test_une_lecture_incomplete_est_nommee_jamais_lue_comme_une_absence():
    approuvees, tronquees = ORG._priorite_approuvees([
        _noeud(102, {HUMAIN: [_revue()]}, tete=""),
        _noeud(103, {HUMAIN: [_revue()]}, totaux={HUMAIN: 11}),
        _noeud(104, {HUMAIN: [_revue()]}),
        {"pas": "un noeud de PR"},
    ])
    assert approuvees == {104}
    assert tronquees == [102, 103]


def test_les_alias_du_faux_sont_ceux_de_la_requete():
    assert {login: alias for alias, login in ORG._priorite_aliases().items()} == ALIAS


def test_la_requete_lit_les_prs_ouvertes_filtrees_par_auteur():
    requete = ORG._priorite_query()
    assert "states: OPEN" in requete
    assert f"first: {ORG.PRIORITE_PAGE}" in requete
    assert "orderBy: {field: CREATED_AT, direction: ASC}" in requete
    assert "$after: String" in requete and "after: $after" in requete
    for login, alias in ALIAS.items():
        assert (
            f'{alias}: reviews(last: {ORG.PRIORITE_REVUES}, author: "{login}")'
            in requete
        ), login
    for champ in ("number", "headRefOid", "totalCount", "state", "body",
                  "submittedAt", "author { login __typename }", "commit { oid }",
                  "pageInfo { hasNextPage endCursor }"):
        assert champ in requete, champ
    assert "%" not in requete


def test_un_login_hors_grammaire_est_refuse_avant_toute_lecture(monkeypatch):
    """Un login entre dans la requete : hors grammaire, rien n'est envoye."""
    monkeypatch.setattr(ORG, "COORDINATOR_VOICES", frozenset({HUMAIN, 'x" OR 1'}))
    runner = PriorityRunner(serveur=ServeurPriorite({}))

    resultat = ORG.lire_priorite(runner, {"GH_TOKEN": "jeton"})

    assert resultat["lecture"] == ORG.PRIORITE_NON_MESUREE
    assert "grammaire" in resultat["motif"]
    assert not _lectures(runner)
    assert runner.budgets == []


# --- la lecture : une seule, paginee, bornee, toujours nommee ---------------------


def test_lecture_mesuree_trois_pages_sous_le_nom_de_curseur_de_la_requete():
    serveur = ServeurPriorite({
        None: _page(
            [_noeud(101, {HUMAIN: [_revue()]}), _noeud(102)], suite=True, curseur="c1"
        ),
        "c1": _page(
            [_noeud(103, {APP: [_revue(login=NU, type_auteur="Bot")]})],
            suite=True, curseur="c2",
        ),
        "c2": _page([_noeud(104, {HUMAIN: [_revue()]})]),
    })
    runner = PriorityRunner(serveur=serveur)

    resultat = ORG.lire_priorite(runner, {"GH_TOKEN": "jeton"})

    assert resultat == {
        "lecture": ORG.PRIORITE_LUE,
        "approuvees": {101, 103, 104},
        "tronquees": [],
        "pages": 3,
        "lues": 4,
    }
    # Une requete par page, ni plus ni moins : la boucle se termine.
    assert serveur.appels == [None, "c1", "c2"]
    requetes = [cmd for _, cmd in _lectures(runner)]
    # `gh api graphql -f query=<requete>` puis, pour une suite, `-f after=<curseur>`.
    assert [len(cmd) for cmd in requetes] == [5, 7, 7]
    # Le curseur passe sous le nom de la variable de la requete (`$after`).
    assert requetes[1][5:] == ["-f", "after=c1"]
    assert requetes[2][5:] == ["-f", "after=c2"]
    # La borne de la lecture est posee une fois, levee une fois.
    assert runner.budgets == [ORG.PRIORITE_BUDGET_S, None]
    # Chaque page est lue sous le jeton epingle de la passe.
    assert all(env == {"GH_TOKEN": "jeton"} for _, env in runner.calls)


def test_une_lecture_mesuree_sans_approuvee_est_une_mesure_pas_une_panne():
    runner = PriorityRunner(serveur=ServeurPriorite({None: _page([_noeud(101)])}))

    resultat = ORG.lire_priorite(runner, {"GH_TOKEN": "jeton"})

    assert resultat["lecture"] == ORG.PRIORITE_LUE
    assert resultat["approuvees"] == set()


def _serveur_sans_fin(curseurs: int = 30) -> ServeurPriorite:
    """Un serveur qui dit toujours « il y a une suite », curseur inedit a chaque page."""
    pages: dict[str | None, object] = {}
    precedent: str | None = None
    for index in range(1, curseurs + 1):
        pages[precedent] = _page([_noeud(100 + index)], suite=True, curseur=f"c{index}")
        precedent = f"c{index}"
    return ServeurPriorite(pages)


def _serveur_illisible_en_page_2() -> ServeurPriorite:
    """Deux pages, la seconde ILLISIBLE (rc non nul) -- la premiere est pourtant lue."""
    serveur = ServeurPriorite({
        None: _page([_noeud(101)], suite=True, curseur="c1"),
        "c1": _page([_noeud(102, {HUMAIN: [_revue()]})]),
    })
    serveur.rc["c1"] = 1
    return serveur


@pytest.mark.parametrize(
    ("panne", "serveur", "motif", "appels"),
    [
        (
            "rc-non-nul",
            _serveur_illisible_en_page_2(),
            "page 2 rc=1",
            2,
        ),
        (
            "stdout-illisible",
            ServeurPriorite({None: "{pas du json"}),
            "UnexpectedError : page priorite : stdout illisible",
            1,
        ),
        (
            "erreur-graphql",
            ServeurPriorite({None: json.dumps({"errors": [{"message": "rate limit"}]})}),
            "UnexpectedError : page priorite : reponse GraphQL en erreur ou illisible",
            1,
        ),
        (
            "payload-sans-pullrequests",
            ServeurPriorite({None: json.dumps({"data": {"repository": None}})}),
            "UnexpectedError : page priorite : pullRequests absent du payload",
            1,
        ),
        ("garde-de-pages", _serveur_sans_fin(), "garde de 20 pages atteinte", 20),
        (
            "page-sans-curseur",
            ServeurPriorite({None: _page([_noeud(101, {HUMAIN: [_revue()]})], suite=True)}),
            "page sans curseur",
            1,
        ),
        (
            "exception-du-runner",
            None,
            "AssertionError : commande non scriptee : gh api graphql",
            1,
        ),
    ],
)
def test_une_lecture_en_panne_est_nommee_et_sa_borne_toujours_levee(
    panne, serveur, motif, appels
):
    """Panne quelle qu'en soit sa forme : un etat NOMME, jamais un ensemble vide.

    Une panne lue comme « aucune PR approuvee » serait un ordre faux presente
    comme une mesure ; la borne, elle, doit toujours etre levee -- une borne qui
    fuit tronquerait l'evaluation des PRs a celle d'une lecture annexe.
    """
    runner = PriorityRunner(serveur=serveur)

    resultat = ORG.lire_priorite(runner, {"GH_TOKEN": "jeton"})

    assert resultat["lecture"] == ORG.PRIORITE_NON_MESUREE, panne
    assert resultat["motif"].startswith(motif), resultat["motif"]
    assert "\n" not in resultat["motif"], "le motif tient sur une ligne"
    # Jamais un ensemble vide qui se lirait « aucune approuvee ».
    assert "approuvees" not in resultat
    assert len(_lectures(runner)) == appels
    assert runner.budgets[0] == ORG.PRIORITE_BUDGET_S
    assert runner.budgets[-1] is None
    assert runner.budgets.count(None) == 1


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
