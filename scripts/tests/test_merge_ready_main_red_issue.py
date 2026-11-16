"""Tests de l'issue canonique du rouge de `main` (#26706).

La sentinelle `main-red` ne retient plus les merges "en silence" : elle
ouvre (ou REUTILISE) UNE issue vivante `[main-red] <check> — <test>`, que
la lane de reparation reclame (`[CLAIMED]`) et que la PR de reparation
nomme (`See #`). La FERMETURE appartient a la sentinelle : elle ferme l'issue
des que le verdict redevient vert, mesure sur `main`.

Ces tests sont hermetiques : aucun reseau, aucun `gh` reel. Tout passe par
un runner scripte qui repond aux appels de l'organe.

Le controle positif rejoue l'EPISODE DU 15/11 : la sentinelle posee au
commit `ffdfd724e3` (rouge) et levee au commit `2e4411d3bc` (vert) doivent
produire une issue ouverte puis fermee — sans jamais ouvrir deux issues.

Le cas de REOUVERTURE couvre la voie `known_number` : une issue fermee par
une PR de reparation portant `Closes #` (avant que `main` n'ait rejoue ses
tests) doit etre rouverte par la sentinelle, qui cite le SHA rouge, et il ne
doit pas en etre cree une seconde.
"""

import importlib.util
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
MERGE_READY_PATH = HERE.parent / "coordination" / "merge_ready.py"
_spec = importlib.util.spec_from_file_location(
    "merge_ready_main_red_under_test", MERGE_READY_PATH
)
mr = importlib.util.module_from_spec(_spec)
sys.modules["merge_ready_main_red_under_test"] = mr
_spec.loader.exec_module(mr)

CHECK = "Scripts Tests (CPU)"
#: Les deux commits de l'episode du 15/11 : la sentinelle y est posee, puis
#: levee. Ce sont les memes SHA que ceux cites par le coordinateur.
ROUGE_15_11 = "ffdfd724e3fb25ee8c188a11cc0ca7adbd7528bf"
VERT_15_11 = "2e4411d3bc0000000000000000000000000000ab"
TEST_15_11 = "tests/scripts/test_merge_ready.py::test_une_reprise_de_test"


def _check_run(conclusion: str, summary: str = "", started_at: str = "2026-11-15T07:00:00Z") -> str:
    """Une ligne de check-run JSON, au format lu par `_scripts_tests_check`."""
    return json.dumps(
        {
            "name": CHECK,
            "conclusion": conclusion,
            "status": "completed",
            "started_at": started_at,
            "id": 4242,
            "output": {"summary": summary},
            "details_url": "",
        }
    )


class FakeRunner:
    """Runner scripte : repond aux appels de la sentinelle et de l'issue.

    L'etat des issues est REEL au sens du test : `gh issue create` ouvre
    une issue, `gh issue close` la ferme, `gh issue reopen` la rouvre, et la
    recherche renvoie les issues ouvertes. Un episode replaye donc exactement
    ce que verrait la production.
    """

    def __init__(self, history, verdicts, *, search_rc: int = 0,
                 create_rc: int = 0, close_rc: int = 0,
                 reopen_rc: int = 0, view_rc: int = 0) -> None:
        self.history = list(history)
        self.verdicts = dict(verdicts)
        self.search_rc = search_rc
        self.create_rc = create_rc
        self.close_rc = close_rc
        self.reopen_rc = reopen_rc
        self.view_rc = view_rc
        self.issues: dict[int, dict] = {}
        self.ouvertes: list[int] = []
        self.calls: list[list[str]] = []
        self._prochain = 26710

    # -- Runner ------------------------------------------------------------
    def run(self, cmd, env=None):
        self.calls.append(list(cmd))
        if "search/issues" in cmd:
            return self._recherche()
        if len(cmd) > 2 and cmd[1] == "api" and "commits?sha=main" in cmd[2]:
            return mr.RunResult(0, "\n".join(self.history), "")
        if len(cmd) > 2 and cmd[1] == "api" and "/check-runs?" in cmd[2]:
            sha = cmd[2].split("/commits/")[1].split("/check-runs")[0]
            return mr.RunResult(0, self.verdicts.get(sha, ""), "")
        if len(cmd) > 2 and cmd[1] == "api" and "/actions/jobs/" in cmd[2]:
            return mr.RunResult(0, "[]", "")
        if cmd[1:2] == ["issue"] and cmd[2] == "create":
            return self._creation(cmd)
        if cmd[1:2] == ["issue"] and cmd[2] == "close":
            return self._fermeture(cmd)
        if cmd[1:2] == ["issue"] and cmd[2] == "reopen":
            return self._rouverture(cmd)
        if cmd[1:2] == ["issue"] and cmd[2] == "view":
            return self._lecture(cmd)
        if cmd[1:2] == ["issue"] and cmd[2] == "edit":
            return self._edition(cmd)
        return mr.RunResult(0, "", "")

    def sleep(self, seconds: float) -> None:  # noqa: D401 - contrat Runner
        return None

    # -- etat des issues ---------------------------------------------------
    def _recherche(self):
        if self.search_rc != 0:
            return mr.RunResult(self.search_rc, "", "rate limited")
        items = [
            {
                "number": number,
                "title": self.issues[number]["title"],
                "body": self.issues[number]["body"],
            }
            for number in self.ouvertes
        ]
        return mr.RunResult(0, json.dumps({"total_count": len(items), "items": items}), "")

    def _creation(self, cmd):
        if self.create_rc != 0:
            return mr.RunResult(self.create_rc, "", "refus de creation")
        number = self._prochain
        self._prochain += 1
        self.issues[number] = {
            "title": cmd[cmd.index("--title") + 1],
            "body": Path(cmd[cmd.index("--body-file") + 1]).read_text(encoding="utf-8"),
            "state": "OPEN",
        }
        self.ouvertes.append(number)
        return mr.RunResult(0, f"https://github.com/jsboige/CoursIA/issues/{number}\n", "")

    def _fermeture(self, cmd):
        if self.close_rc != 0:
            return mr.RunResult(self.close_rc, "", "refus de fermeture")
        number = int(cmd[3])
        if number in self.ouvertes:
            self.ouvertes.remove(number)
        if number in self.issues:
            self.issues[number]["state"] = "CLOSED"
        return mr.RunResult(0, "", "")

    def _rouverture(self, cmd):
        if self.reopen_rc != 0:
            return mr.RunResult(self.reopen_rc, "", "refus de rouverture")
        number = int(cmd[3])
        if number not in self.ouvertes:
            self.ouvertes.append(number)
        if number in self.issues:
            self.issues[number]["state"] = "OPEN"
        return mr.RunResult(0, "", "")

    def _lecture(self, cmd):
        if self.view_rc != 0:
            return mr.RunResult(self.view_rc, "", "refus de lecture")
        number = int(cmd[3])
        if number not in self.issues:
            return mr.RunResult(1, "", "issue introuvable")
        entry = self.issues[number]
        return mr.RunResult(
            0,
            json.dumps(
                {
                    "number": number,
                    "title": entry.get("title", ""),
                    "body": entry.get("body", ""),
                    "state": entry.get("state", "OPEN"),
                }
            ),
            "",
        )

    def _edition(self, cmd):
        number = int(cmd[3])
        # L'issue peut etre inconnue du fake (index de recherche en retard) :
        # elle existe cote GitHub, l'edition doit aboutir.
        entry = self.issues.setdefault(
            number, {"title": "", "body": "", "state": "OPEN"}
        )
        if "--title" in cmd:
            entry["title"] = cmd[cmd.index("--title") + 1]
        if "--body-file" in cmd:
            entry["body"] = Path(
                cmd[cmd.index("--body-file") + 1]
            ).read_text(encoding="utf-8")
        return mr.RunResult(0, "", "")

    # -- raccourcis de verification ---------------------------------------
    def creations(self) -> list[list[str]]:
        return [c for c in self.calls if c[2:3] == ["create"]]

    def fermetures(self) -> list[list[str]]:
        return [c for c in self.calls if c[2:3] == ["close"]]

    def rouvertures(self) -> list[list[str]]:
        return [c for c in self.calls if c[2:3] == ["reopen"]]


def _runner(*, rouge: str = ROUGE_15_11, vert: str | None = None,
            test: str = TEST_15_11) -> FakeRunner:
    """Runner portant l'episode : un commit rouge, et optionnellement un vert."""
    verdicts = {rouge: _check_run("failure", f"FAILED {test}")}
    history = [rouge]
    if vert:
        verdicts[vert] = _check_run("success", started_at="2026-11-15T09:00:00Z")
        history = [vert, rouge]
    return FakeRunner(history, verdicts)


def _hold(tmp_path: Path) -> Path:
    return tmp_path / "holds" / "hold.txt"


def _lignes_sentinelle(hold: Path) -> list[str]:
    if not hold.exists():
        return []
    return [
        ligne
        for ligne in hold.read_text(encoding="utf-8-sig").splitlines()
        if ligne.strip().startswith(f"{mr.MAIN_RED_HOLD_NUMBER} {mr.MAIN_RED_HOLD_PREFIX}")
    ]


def _titre_attendu(test: str) -> str:
    return f"[main-red] {CHECK} — {test}"


def test_le_rouge_de_main_ouvre_une_issue_canonique(tmp_path):
    """Le rouge ouvre UNE issue, et la retenue est posee dans le meme run."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)

    assert len(runner.ouvertes) == 1
    number = runner.ouvertes[0]
    assert runner.issues[number]["title"] == _titre_attendu(TEST_15_11)
    assert ROUGE_15_11 in runner.issues[number]["body"]
    assert TEST_15_11 in runner.issues[number]["body"]
    # La retenue est posee elle aussi : l'issue ne remplace pas la porte.
    assert _lignes_sentinelle(hold), "la retenue globale doit etre posee"


def test_une_seconde_execution_reutilise_l_issue_sans_en_ouvrir_deuxieme(tmp_path):
    """Un meme episode = UNE issue : le second run la REUTILISE."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    mr.refresh_main_red_hold(runner, {}, hold)

    assert len(runner.ouvertes) == 1, "le second run a ouvert une seconde issue"
    assert len(runner.creations()) == 1
    assert not runner.fermetures()


def test_un_test_qui_change_reutilise_la_meme_issue(tmp_path):
    """Un meme episode qui change de test en echec reste UNE issue."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    number = runner.ouvertes[0]

    runner.verdicts[ROUGE_15_11] = _check_run(
        "failure", "FAILED tests/autre/test_autre.py::test_autre"
    )
    mr.refresh_main_red_hold(runner, {}, hold)

    assert len(runner.ouvertes) == 1, "le changement de test a ouvert une seconde issue"
    assert runner.issues[number]["title"] == _titre_attendu(
        "tests/autre/test_autre.py::test_autre"
    )


def test_le_vert_ferme_l_issue_et_retire_la_retenue(tmp_path):
    """Au vert : l'issue est fermee et la retenue retiree."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    number = runner.ouvertes[0]

    runner.verdicts[ROUGE_15_11] = _check_run("success")
    runner.history = [ROUGE_15_11]
    mr.refresh_main_red_hold(runner, {}, hold)

    assert number not in runner.ouvertes, "l'issue n'a pas ete fermee"
    assert len(runner.fermetures()) == 1
    assert _lignes_sentinelle(hold) == [], "la retenue aurait du etre retiree"


def test_le_controle_positif_de_l_episode_du_15_novembre(tmp_path):
    """Controle positif : l'episode reel du 15/11, joue de bout en bout.

    La sentinelle est POSEE au commit `ffdfd724e3` (rouge) et LEVEE au
    commit `2e4411d3bc` (vert). Entre les deux : une issue ouverte, puis
    fermee. Aucune seconde issue, aucune retenue residuelle.
    """
    runner = _runner(rouge=ROUGE_15_11)
    hold = _hold(tmp_path)

    # Instant 1 : le commit rouge est la tete de `main`. La sentinelle se
    # pose et l'issue s'ouvre.
    mr.refresh_main_red_hold(runner, {}, hold)
    assert len(runner.ouvertes) == 1
    assert runner.issues[runner.ouvertes[0]]["title"] == _titre_attendu(TEST_15_11)
    assert _lignes_sentinelle(hold)

    # Instant 2 : le correctif est passe sur `main` (commit vert). L'issue
    # se ferme, la retenue tombe.
    runner.verdicts[VERT_15_11] = _check_run(
        "success", started_at="2026-11-15T09:00:00Z"
    )
    runner.history = [VERT_15_11, ROUGE_15_11]
    mr.refresh_main_red_hold(runner, {}, hold)

    assert runner.ouvertes == [], "l'issue du 15/11 aurait du etre fermee au vert"
    assert len(runner.creations()) == 1, "exactement UNE issue pour l'episode"
    assert _lignes_sentinelle(hold) == []


def test_une_recherche_illisible_n_ouvre_pas_d_issue_mais_pose_la_retenue(tmp_path):
    """Fail-closed : une recherche illisible n'ouvre RIEN (pas de doublon).

    Une retention en double est pire qu'une absence : deux lanes y
    reclameraient le meme rouge. La retenue, elle, reste posee — elle est
    ecrite AVANT l'issue.
    """
    runner = _runner()
    runner.search_rc = 1
    hold = _hold(tmp_path)

    mr.refresh_main_red_hold(runner, {}, hold)

    assert not runner.ouvertes, "une issue a ete ouverte malgre une recherche illisible"
    assert not runner.creations()
    assert _lignes_sentinelle(hold), "la retenue globale doit etre posee malgre l'echec"


def test_le_vert_sans_issue_au_repertoire_ne_echoue_pas(tmp_path):
    """Pas d'issue ouverte et un verdict vert : rien a faire, rien ne casse."""
    runner = FakeRunner([VERT_15_11], {VERT_15_11: _check_run("success")})
    hold = _hold(tmp_path)

    mr.refresh_main_red_hold(runner, {}, hold)

    assert not runner.creations()
    assert not runner.fermetures()
    assert _lignes_sentinelle(hold) == []


def test_le_creation_d_issue_echouee_ne_perd_pas_la_retenue(tmp_path):
    """Une creation refusee ne doit pas faire disparaitre la porte."""
    runner = _runner()
    runner.create_rc = 1
    hold = _hold(tmp_path)

    mr.refresh_main_red_hold(runner, {}, hold)

    assert not runner.ouvertes
    assert _lignes_sentinelle(hold), "la retenue globale doit rester posee"


def test_le_titre_de_l_issue_porte_le_prefixe_canonique():
    """Le prefixe est la CLE de recherche : il doit etre inchange."""
    assert mr.MAIN_RED_ISSUE_TITLE_PREFIX == "[main-red]"
    titre = mr.main_red_issue_title(CHECK, "tests/x.py::test_y")
    assert titre == "[main-red] Scripts Tests (CPU) — tests/x.py::test_y"
    assert titre.startswith(mr.MAIN_RED_ISSUE_TITLE_PREFIX)


def test_le_corps_de_l_issue_dit_comment_la_reparer():
    """Le corps doit dire QUOI faire : c'est lui que la lane lit."""
    corps = mr.main_red_issue_body(ROUGE_15_11, CHECK, TEST_15_11)
    assert "[CLAIMED]" in corps
    assert "See #N" in corps
    assert ROUGE_15_11 in corps
    assert TEST_15_11 in corps


def test_le_corps_de_l_issue_interdit_la_fermeture_par_la_pr():
    """La fermeture appartient a la sentinelle : le corps ne dit pas `Closes`.

    Une PR de reparation qui porte `Closes #N` ferme l'episode au merge du
    correctif -- avant que `main` ait rejoue `Scripts Tests (CPU)` (20 a
    30 min). Pendant ce temps aucune issue n'est ouverte, et la branche
    « aucune issue → voie normale » renvoie chaque lane reparer seule.
    """
    corps = mr.main_red_issue_body(ROUGE_15_11, CHECK, TEST_15_11)
    assert "Closes #N" not in corps
    # La formule `Closes` peut apparaitre, mais seulement comme interdiction.
    for ligne in corps.splitlines():
        if "Closes" in ligne:
            assert "**pas**" in ligne or "fermeture" in ligne.lower()


def test_le_corps_de_l_issue_porte_le_marqueur_html():
    """Le marqueur HTML est la preuve de l'origine machine de l'issue.

    Il survit a une renumerotation par un humain, et se relit par `grep` :
    c'est lui qui rend l'issue reconnaissable meme si le titre change.
    """
    corps = mr.main_red_issue_body(ROUGE_15_11, CHECK, TEST_15_11)
    assert mr.MAIN_RED_ISSUE_MARKER in corps
    assert corps.startswith(mr.MAIN_RED_ISSUE_MARKER)


def test_une_issue_renumerotee_est_reconnue_par_son_marqueur(tmp_path):
    """Le titre est l'index, le marqueur est la preuve : les deux comptent."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    number = runner.ouvertes[0]

    # Un humain renumerote l'issue : elle reste l'issue de l'episode.
    runner.issues[number]["title"] = "main rouge du 15/11 (renumerote a la main)"
    runner.verdicts[ROUGE_15_11] = _check_run(
        "failure", f"FAILED {TEST_15_11}"
    )
    mr.refresh_main_red_hold(runner, {}, hold)

    assert len(runner.ouvertes) == 1, "le marqueur n'a pas ete reconnu"
    assert not runner.creations() or len(runner.creations()) == 1


def test_la_retenue_porte_le_numero_de_l_issue(tmp_path):
    """La retenue porte `issue=N` : le run suivant vise CETTE issue."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)

    ligne = _lignes_sentinelle(hold)[0]
    assert f"issue={runner.ouvertes[0]}" in ligne


def test_un_index_de_recherche_en_retard_n_ouvre_pas_de_seconde_issue(tmp_path):
    """Deux runs rapproches ne doivent PAS ouvrir deux issues.

    L'index de recherche de GitHub peut avoir du retard : le second run
    ne voit pas encore l'issue fraichement creee. C'est la retenue (qui
    porte `issue=N`) qui lui permet de la retrouver sans chercher.
    """
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    creee = runner.ouvertes[0]
    assert len(runner.creations()) == 1

    # L'index ne voit plus rien (latence de recherche simulee).
    runner.ouvertes = []
    runner.issues = {}

    mr.refresh_main_red_hold(runner, {}, hold)

    assert len(runner.creations()) == 1, "une seconde issue a ete ouverte"
    assert not runner.ouvertes, "la recherche ne voit rien, il ne doit rien rester ouvert"


def test_le_vert_ferme_l_issue_meme_si_la_recherche_ne_la_voit_pas(tmp_path):
    """La fermeture vise le numero inscrit dans la retenue, pas la recherche."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    creee = runner.ouvertes[0]

    # La recherche ne voit plus l'issue ; la retenue, elle, porte son numero.
    runner.ouvertes = []
    runner.verdicts[ROUGE_15_11] = _check_run("success")
    mr.refresh_main_red_hold(runner, {}, hold)

    assert runner.fermetures(), "l'issue n'a pas ete fermee"
    assert creee in [int(cmd[3]) for cmd in runner.fermetures()]


def test_une_issue_fermee_pendant_un_rouge_persistent_est_reouverte(tmp_path):
    """Rouge persistant + issue fermee : la sentinelle la rouvre, sans doublon.

    Le cas mesure (revue ai-01 du 16/11) : une PR de reparation portant
    `Closes #N` ferme l'issue au MERGE du correctif, alors que `main` n'a pas
    encore rejoue `Scripts Tests (CPU)` (20 a 30 min). Pendant ce temps
    aucune issue n'est ouverte et la branche « aucune issue → voie normale »
    renvoie chaque lane reparer seule.

    La voie `known_number` (le numero inscrit dans la retenue) est donc
    relue : on lit l'etat, on rouvre si le rouge tient, et on ne cree
    AUCUNE seconde issue.
    """
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    creee = runner.ouvertes[0]
    assert len(runner.creations()) == 1

    # Une PR de reparation portant `Closes #` ferme l'issue au merge.
    runner.ouvertes.remove(creee)
    runner.issues[creee]["state"] = "CLOSED"

    # Le rouge tient toujours : le meme commit, le meme verdict.
    mr.refresh_main_red_hold(runner, {}, hold)

    assert runner.rouvertures(), "l'issue n'a pas ete rouverte"
    assert creee in [int(cmd[3]) for cmd in runner.rouvertures()]
    assert len(runner.creations()) == 1, "une seconde issue a ete ouverte"
    assert creee in runner.ouvertes, "l'issue doit rester ouverte"


def test_la_rouverture_cite_le_sha_rouge(tmp_path):
    """Le commentaire de rouverture porte le SHA rouge : la preuve d'episode."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)
    creee = runner.ouvertes[0]
    runner.ouvertes.remove(creee)
    runner.issues[creee]["state"] = "CLOSED"

    mr.refresh_main_red_hold(runner, {}, hold)

    cmd = next(c for c in runner.rouvertures())
    commentaire = cmd[cmd.index("--comment") + 1]
    assert ROUGE_15_11 in commentaire
    assert CHECK in commentaire


def test_une_issue_ouverte_n_est_pas_rouverte_deux_fois(tmp_path):
    """Rouge persistant + issue deja ouverte : aucune rouverture superflue."""
    runner = _runner()
    hold = _hold(tmp_path)
    mr.refresh_main_red_hold(runner, {}, hold)

    mr.refresh_main_red_hold(runner, {}, hold)

    assert not runner.rouvertures(), "l'issue etait deja ouverte"
    assert len(runner.creations()) == 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
