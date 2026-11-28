"""Tests des BORNES de duree de l'organe `merge_ready` (GO du coordinateur).

Deux bornes, deux garants :

- `CMD_TIMEOUT_S` : delai maximal d'UN sous-processus. Depasse, l'enfant
  est tue et le rc vaut 124 (`timeout(1)`) ;
- l'ECHEANCE DE PR : posee par la boucle de passe (`set_pr_budget`), portee
  par le runner -- chaque sous-processus de la PR recoit
  `min(CMD_TIMEOUT_S, reste)`, et l'echeance passee le sous-processus ne
  part plus.

Le contrat que ces tests verrouillent est celui-la : **un delai expire est
une MESURE IMPOSSIBLE, pas un defaut**. Il ne rougit rien -- ni la PR, ni
le bilan de la passe -- il ne provoque ni `run-error` ni exit 1, et la passe
CONTINUE (le passage suivant reessaie la PR).

Une troisieme surface est bornee par la meme echeance (review du 26/11) :
la construction de l'INDEX DE PILE, a cache froid. C'est le seul travail
couteux de l'evaluation qui se fait EN PROCESSUS -- il ne passe pas par le
runner, qui ne le bornait donc pas. La construction recoit le budget de la
PR qui la declenche, UNE fois par passe ; delai expire, la PR est saisie
(motif `stack-timeout`, porte `unmeasured`) et rien n'est fusionne. Trois
temoins le couvrent : a cache froid, la construction expire puis laisse
avancer la PR suivante ; elle ne retient jamais une passe plus longtemps
qu'UN budget ; et l'indicateur de cache du module du gate n'y court-circuite
pas la borne.

Mesure a l'origine des bornes (24/11) : une PR (#25063) a occupe 1 587 s
dans une passe dont le budget global est de 2 700 s -- la borne globale se
lit ENTRE deux PRs, elle n'interrompt donc jamais une PR en cours. Le
journal porte un verdict par PR, pas une duree par commande : il ne dit pas
quelle commande a pris ce temps. D'ou les bornes ici.

Aucun reseau : les lectures passent par le runner scripte de
`test_merge_ready.py` ; les trois tests du runner reel n'invoquent que
`sys.executable` sur une commande locale qui dort.
"""

import sys
import threading
import time

import pytest

import merge_ready as mr
from scripts.tests.test_merge_ready import ScriptedRunner, run_organ
import scripts.tests.test_merge_ready as organ


def _index_de_pile_vide() -> dict:
    """Index de pile vide : porte MESUREE, aucun appel git reel."""
    return {}


@pytest.fixture(autouse=True)
def _porte_stack_mesuree(monkeypatch):
    """Porte STACK injectee (comme dans `test_merge_ready.py`) : aucun git."""
    monkeypatch.setattr(mr.gate, "default_stack_index", _index_de_pile_vide)


@pytest.fixture(autouse=True)
def _construction_de_pile_vierge(monkeypatch):
    """Chaque test repart d'une construction VIERGE.

    L'etat de la construction (fil en cours, resultat) est un attribut du
    MODULE sous test -- celui que `run_organ` execute. Un test qui laisse
    une construction en cours ne doit pas la leguer au suivant. `raising=False`
    : sur un code sans construction bornee, le temoin doit echouer sur ce
    qu'il mesure, pas sur l'absence de l'attribut.
    """
    monkeypatch.setattr(
        organ.mr, "_PILE_CONSTRUCTION",
        {"evenement": None, "resultat": None, "echeance": None},
        raising=False,
    )


# --- runner reel : la borne par sous-processus -----------------------------


def test_le_runner_reel_tue_un_sous_processus_au_dela_du_delai(monkeypatch):
    """Au-dela de `CMD_TIMEOUT_S`, l'enfant est tue et le rc vaut 124.

    Falsification : sans la borne, la commande dort 30 s et le run
    rendrait rc=0 -- la mesure aurait l'air reussie.
    """
    monkeypatch.setattr(mr, "CMD_TIMEOUT_S", 0.3)
    runner = mr.SubprocessRunner()
    res = runner.run([sys.executable, "-c", "import time; time.sleep(30)"])
    assert res.returncode == mr.TIMEOUT_RC == 124
    assert res.stdout == ""


def test_le_runner_reel_ne_lance_rien_quand_l_echeance_de_pr_est_passee():
    """Echeance de PR passee : rien ne part, meme une commande instantanee.

    La commande ecrirait « lance » sur stdout : une sortie vide prouve que
    le sous-processus n'a pas ete lance (et non qu'il a echoue).
    """
    runner = mr.SubprocessRunner()
    runner.set_pr_budget(0.0)
    res = runner.run([sys.executable, "-c", "print('lance')"])
    assert res.returncode == mr.TIMEOUT_RC
    assert "lance" not in res.stdout


def test_l_echeance_de_pr_raccourcit_le_delai_par_sous_processus():
    """L'echeance de PR borne le sous-processus : 0,2 s, pas 300 s.

    Sans le raccordement (le sous-processus ignorant l'echeance), la
    commande dort 30 s et le test echoue -- c'est la falsification.
    """
    runner = mr.SubprocessRunner()
    runner.set_pr_budget(0.3)
    res = runner.run([sys.executable, "-c", "import time; time.sleep(30)"])
    assert res.returncode == mr.TIMEOUT_RC


def test_le_budget_pose_ne_survit_pas_a_son_terme():
    """`set_pr_budget(None)` leve l'echeance : le runner redevient nominal."""
    runner = mr.SubprocessRunner()
    runner.set_pr_budget(0.0)
    assert runner.run([sys.executable, "-c", "print('ok')"]).returncode == mr.TIMEOUT_RC
    runner.set_pr_budget(None)
    res = runner.run([sys.executable, "-c", "print('ok')"])
    assert res.returncode == 0
    assert "ok" in res.stdout


# --- le contrat : un delai ne derougit rien ---------------------------------


class RunnerDelaiSurUnePR(ScriptedRunner):
    """Le delai ne frappe que la PR 201 : la 202 reste mergeable.

    C'est ce qui permet de montrer que le delai n'ARRETE pas la passe.
    """

    def run(self, cmd, env=None):
        c = list(cmd)
        if c[:3] == ["gh", "pr", "view"] and len(c) > 3 and c[3] == "201":
            return mr.RunResult(mr.TIMEOUT_RC, "", "delai depasse")
        return super().run(cmd, env)


class RunnerDelaiSurMergeabilite(ScriptedRunner):
    """Le delai frappe la lecture d'etat de mergeabilite (REST ``pulls/N``).

    Le rechauffage (``--jq``), la lecture des reviews et la lecture
    paginee des fichiers sont exclus : ce sont d'autres surfaces.
    """

    def run(self, cmd, env=None):
        c = list(cmd)
        chemin = c[2].split("?", 1)[0] if len(c) > 2 else ""
        if (c[:2] == ["gh", "api"] and "/pulls/" in chemin
                and "--jq" not in c
                and not chemin.endswith("/reviews")
                and not chemin.endswith("/files")):
            return mr.RunResult(mr.TIMEOUT_RC, "", "delai depasse")
        return super().run(cmd, env)


class RunnerAvecEcheance(ScriptedRunner):
    """Runner qui MEMORISE les budgets de PR poses par la boucle de passe."""

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.budgets: list[float | None] = []

    def set_pr_budget(self, budget_s):
        self.budgets.append(budget_s)


def test_un_rc_124_ne_derive_rien(tmp_path):
    """LE contrat : un delai expire ne rougit NI la PR NI le bilan.

    PR 201 : lecture expiree (rc 124). PR 202 : PR ordinaire.
    - le bilan de la passe reste `rc=0` (aucune erreur, aucun rouge) ;
    - 201 est `skipped` avec un motif de delai -- pas `run-error` ;
    - 202 est evaluee ET fusionnee : le delai n'a pas arrete la passe.
    """
    runner = RunnerDelaiSurUnePR(prs=(201, 202))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    assert rc == 0, "un delai ne doit pas rougir le bilan de la passe"
    assert [row["pr"] for row in lines] == [201, 202]
    assert lines[0]["verdict"] == "skipped", lines[0]
    assert lines[0]["reason"].startswith("timeout:"), lines[0]["reason"]
    assert not any(row["verdict"] == "run-error" for row in lines)
    assert lines[1]["verdict"] == "merged", lines[1]


def test_un_delai_de_l_organe_b0_sait_la_pr_sans_la_rougir(tmp_path):
    """L'organe B.0 expire : motif `b0-timeout`, et surtout PAS de fusion.

    Falsification : un rc=124 lu comme un rc « hors contrat » produirait
    un `run-error` et un bilan rouge -- exactement ce que la borne
    interdit.
    """
    runner = ScriptedRunner(prs=(211,), nits_rc=mr.TIMEOUT_RC)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    assert rc == 0
    assert lines[-1]["verdict"] == "skipped", lines[-1]
    assert lines[-1]["reason"] == "b0-timeout", lines[-1]["reason"]
    merges = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert not merges, "une PR dont l'organe B.0 a expire ne doit pas etre fusionnee"


def test_un_delai_de_lecture_de_mergeabilite_sait_la_pr_sans_la_rougir(tmp_path):
    """L'etat de mergeabilite reste INCONNU : motif `mergeable-state:timeout`.

    « timeout » n'est ni « clean » ni un etat pending : la PR est saisie,
    pas parsee pour etre rejouee, et pas rougie.
    """
    runner = RunnerDelaiSurMergeabilite(prs=(221,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    assert rc == 0
    assert lines[-1]["verdict"] == "skipped", lines[-1]
    assert lines[-1]["reason"] == "mergeable-state:timeout", lines[-1]["reason"]
    merges = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert not merges, "un etat de mergeabilite inconnu ne se fusionne pas"


# --- la borne de PR est bien posee par la boucle de passe ------------------


def test_le_delai_par_pr_est_pose_et_leve_autour_de_chaque_pr(tmp_path):
    """La boucle pose l'echeance AVANT la lecture et la leve APRES l'evaluation.

    Le merge reste hors echeance : une echeance atteinte au milieu d'un
    merge laisserait l'etat de la fusion inconnu. Le motif le dit : le
    budget est leve (`None`) avant le merge.
    """
    runner = RunnerAvecEcheance(prs=(301, 302))
    rc, _lines, _journal = run_organ(tmp_path, runner, extra=("--apply",))

    assert rc == 0
    # La lecture GROUPEE des approbations (#28009) ouvre la passe sous sa
    # propre borne, levee avant la boucle : la premiere echeance de PR vient
    # apres cette trame.
    assert runner.budgets[:2] == [mr.PRIORITE_BUDGET_S, None]
    budgets = runner.budgets[2:]
    assert budgets[0] == mr.PR_DEADLINE_S == 600.0
    assert budgets[1] is None, "l'echeance doit etre levee apres l'evaluation"
    # Une echeance posee et levee par PR evaluee.
    poses = [b for b in budgets if b is not None]
    assert len(poses) == len([b for b in budgets if b is None])


def test_le_delai_par_pr_est_surchargeable_en_ligne_de_commande():
    """`--pr-deadline-s` existe, et une valeur negative est refusee."""
    args = mr._parse_args(["--pr-deadline-s", "42"])
    assert args.pr_deadline_s == 42.0
    assert mr._parse_args([]).pr_deadline_s == mr.PR_DEADLINE_S
    with pytest.raises(SystemExit):
        mr._parse_args(["--pr-deadline-s", "-1"])


# --- la construction de l'index de pile, a cache froid (review du 26/11) --------


class _PileAFinCommandee:
    """Une construction d'index pile dont la FIN est commandee par le test.

    Le temoin veut prouver un ORDRE -- la passe a-t-elle attendu la
    construction ? -- pas une duree : la construction ne rend qu'apres le
    signal ``liberer``. ``fin`` est l'instant ou elle a rendu.
    """

    def __init__(self) -> None:
        self.liberer = threading.Event()
        self.terminee = threading.Event()
        self.fin: float | None = None
        self.appels = 0

    def __call__(self) -> dict:
        self.appels += 1
        # Garde-fou : sans liberation, le temoin echoue en 10 s au lieu de
        # suspendre la session.
        self.liberer.wait(10)
        self.fin = time.monotonic()
        self.terminee.set()
        return {}


class _RunnerPortantLEcheance(ScriptedRunner):
    """Le runner scripte, qui porte AUSSI la vraie echeance de PR.

    La boucle de passe pose le budget par ``set_pr_budget`` ; l'etape 3 lit
    le reste par ``_remaining_s``. Les deux methodes sont celles du runner
    de production : elles ne touchent que deux attributs, le dispatch
    scripte est inchange.
    """

    set_pr_budget = mr.SubprocessRunner.set_pr_budget
    _remaining_s = mr.SubprocessRunner._remaining_s


class _RunnerQuiLibereLaPile(_RunnerPortantLEcheance):
    """Note l'instant de lecture de chaque vue ; la lecture de la vue de
    ``pr_de_liberation`` libere la construction de l'index pile."""

    def __init__(
        self, *, pile: _PileAFinCommandee, pr_de_liberation: int, **kwargs
    ) -> None:
        super().__init__(**kwargs)
        self.pile = pile
        self.pr_de_liberation = pr_de_liberation
        self.lectures: dict[int, float] = {}
        self.appels_pile_a_la_liberation = 0

    def run(self, cmd, env=None):
        c = list(cmd)
        if c[:3] == ["gh", "pr", "view"] and len(c) > 3:
            numero = int(c[3])
            self.lectures[numero] = time.monotonic()
            if numero == self.pr_de_liberation:
                self.appels_pile_a_la_liberation = self.pile.appels
                self.pile.liberer.set()
                # La vue n'est rendue qu'une fois la construction finie : le
                # temoin ne depend d'aucune course entre les deux fils.
                assert self.pile.terminee.wait(10), "la construction n'a pas rendu"
        return super().run(cmd, env)


def _espionner_l_attente(monkeypatch) -> list[float]:
    """Le delai que l'etape 3 s'autorise a attendre, pour chaque PR."""
    attentes: list[float] = []
    attendre = getattr(organ.mr, "_attendre_la_pile", None)

    def espion(evenement, reste_s):
        attentes.append(reste_s)
        if attendre is None:
            return evenement.is_set()
        return attendre(evenement, reste_s)

    monkeypatch.setattr(organ.mr, "_attendre_la_pile", espion, raising=False)
    return attentes


def test_pile_a_cache_froid_expire_puis_laisse_avancer_la_pr_suivante(
    tmp_path, monkeypatch,
):
    """CACHE FROID : la construction de l'index pile depasse son budget.

    Budget : 0,3 s (`--pr-deadline-s`) -- c'est celui que la construction
    recoit de la PR qui la declenche. Elle ne finit que lorsque la vue de la
    PR 204 est lue.
    - 201, la PR qui la declenche, attend ce budget puis est SAISIE
      (`stack-timeout`) : porte `unmeasured`, incident nomme, aucune fusion ;
    - le bilan reste rc=0 ;
    - la passe N'A PAS ATTENDU la construction : les vues de 202 et 203 sont
      lues, et leur verdict ecrit, pendant qu'elle tourne encore -- sans
      aucune attente, l'echeance de la construction etant passee ;
    - la construction n'est pas relancee pendant qu'elle tourne ;
    - une fois finie, son resultat sert la PR suivante : 204 est fusionnee,
      porte `measured`.

    Falsification (appel direct, sans budget -- tete 4bd21455d5a1) :
    l'evaluation de 201 reste DANS la construction jusqu'a sa garde (10 s),
    puis 201, 202 et 203 sont fusionnees avec une porte dite `measured`.
    """
    pile = _PileAFinCommandee()
    monkeypatch.setattr(organ.mr.gate, "default_stack_index", pile)
    attentes = _espionner_l_attente(monkeypatch)
    runner = _RunnerQuiLibereLaPile(
        pile=pile, pr_de_liberation=204, prs=(201, 202, 203, 204),
    )

    rc, lines, _ = run_organ(
        tmp_path, runner, extra=("--apply", "--pr-deadline-s", "0.3"),
    )

    assert rc == 0, "un delai de la construction ne doit pas rougir le bilan"
    assert [row["pr"] for row in lines] == [201, 202, 203, 204]
    for row in lines[:3]:
        assert row["verdict"] == "skipped", row
        assert row["reason"] == "stack-timeout", row["reason"]
        assert row["stack"] == "unmeasured"
        assert "delai depasse (budget de 0.3 s)" in row["stack_incidents"][0]
    assert pile.fin is not None, "la construction n'a jamais rendu"
    # La passe n'a pas attendu : 202 et 203 lues -- et saisies -- PENDANT la construction.
    assert runner.lectures[202] < pile.fin
    assert runner.lectures[203] < pile.fin
    assert len(attentes) == 3, attentes
    assert 0 < attentes[0] <= 0.35, attentes
    assert attentes[1] == 0 and attentes[2] == 0, attentes
    # Mono-vol : aucune seconde construction pendant que la premiere tournait.
    assert runner.appels_pile_a_la_liberation == 1
    # Une fois finie, l'index est mesure : la PR suivante est fusionnee.
    assert lines[3]["verdict"] == "merged", lines[3]
    assert lines[3]["stack"] == "measured", lines[3]
    merges = [c[3] for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert merges == ["204"], merges


def test_la_pile_ne_retient_jamais_la_passe_plus_qu_un_budget(
    tmp_path, monkeypatch,
):
    """UN budget par passe : l'echeance passee, plus aucune PR n'attend.

    Budget : 0,2 s. La construction ne rend pas pendant la passe. 201, la PR
    qui la declenche, attend AU PLUS ce budget puis est saisie
    (`stack-timeout`) ; 202 et 203 attendent ZERO -- l'echeance de la
    construction est passee ; rien n'est fusionne, la construction n'est pas
    relancee, le bilan reste rc=0.

    Falsification (tete 4bd21455d5a1) : chacune des trois PR reste dans
    l'appel direct jusqu'a la garde (10 s), puis est fusionnee.
    """
    pile = _PileAFinCommandee()
    monkeypatch.setattr(organ.mr.gate, "default_stack_index", pile)
    attentes = _espionner_l_attente(monkeypatch)
    runner = _RunnerPortantLEcheance(prs=(201, 202, 203))
    try:
        rc, lines, _ = run_organ(
            tmp_path, runner, extra=("--apply", "--pr-deadline-s", "0.2"),
        )
        en_cours_a_la_sortie = pile.fin is None
    finally:
        pile.liberer.set()

    assert rc == 0
    assert [row["pr"] for row in lines] == [201, 202, 203]
    for row in lines:
        assert row["verdict"] == "skipped", row
        assert row["reason"] == "stack-timeout", row["reason"]
        assert row["stack"] == "unmeasured"
        assert "delai depasse (budget de 0.2 s)" in row["stack_incidents"][0]
    assert len(attentes) == 3, attentes
    assert 0 < attentes[0] <= 0.21, attentes
    assert attentes[1] == 0 and attentes[2] == 0, attentes
    assert pile.appels == 1, "une construction en cours a ete relancee"
    assert en_cours_a_la_sortie, (
        "la construction a rendu pendant la passe : le temoin ne mesure plus rien"
    )
    merges = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert not merges, "une PR saisie sur delai ne doit pas etre fusionnee"


def test_un_indicateur_built_du_module_du_gate_ne_court_circuite_pas_la_borne(
    tmp_path, monkeypatch,
):
    """Le module du gate dit « index construit » -- par un AUTRE appelant.

    Dans un meme processus, un organe importe ou un test anterieur peut
    avoir laisse ``_STACK_INDEX_CACHE["built"]`` a Vrai. Cet indicateur ne
    prouve pas qu'UNE construction bornee a eu lieu ici : la premiere PR qui
    demande l'index passe quand meme par elle. Une lecture de l'indicateur en
    guise de raccourci avait remis l'appel direct, sans budget, sur la
    selection etendue des tests.
    """
    pile = _PileAFinCommandee()
    monkeypatch.setattr(organ.mr.gate, "default_stack_index", pile)
    monkeypatch.setattr(
        organ.mr.gate, "_STACK_INDEX_CACHE",
        {"built": True, "index": {"201": []}, "incidents": []},
    )
    attentes = _espionner_l_attente(monkeypatch)
    runner = _RunnerPortantLEcheance(prs=(201, 202))
    try:
        rc, lines, _ = run_organ(
            tmp_path, runner, extra=("--apply", "--pr-deadline-s", "0.2"),
        )
        en_cours_a_la_sortie = pile.fin is None
    finally:
        pile.liberer.set()

    assert rc == 0
    assert [row["pr"] for row in lines] == [201, 202]
    for row in lines:
        assert row["verdict"] == "skipped", row
        assert row["reason"] == "stack-timeout", row["reason"]
        assert row["stack"] == "unmeasured"
    assert len(attentes) == 2, attentes
    assert 0 < attentes[0] <= 0.21 and attentes[1] == 0, attentes
    assert pile.appels == 1, "une construction en cours a ete relancee"
    assert en_cours_a_la_sortie
    merges = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert not merges, "une PR saisie sur delai ne doit pas etre fusionnee"
