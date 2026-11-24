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

Mesure a l'origine des bornes (24/11) : une PR (#25063) a occupe 1 587 s
dans une passe dont le budget global est de 2 700 s -- la borne globale se
lit ENTRE deux PRs, elle n'interrompt donc jamais une PR en cours. D'ou les
deux bornes ici.

Aucun reseau : les lectures passent par le runner scripte de
`test_merge_ready.py` ; les trois tests du runner reel n'invoquent que
`sys.executable` sur une commande locale qui dort.
"""

import sys

import pytest

import merge_ready as mr
from scripts.tests.test_merge_ready import ScriptedRunner, run_organ


def _index_de_pile_vide() -> dict:
    """Index de pile vide : porte MESUREE, aucun appel git reel."""
    return {}


@pytest.fixture(autouse=True)
def _porte_stack_mesuree(monkeypatch):
    """Porte STACK injectee (comme dans `test_merge_ready.py`) : aucun git."""
    monkeypatch.setattr(mr.gate, "default_stack_index", _index_de_pile_vide)


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
    assert runner.budgets[0] == mr.PR_DEADLINE_S == 600.0
    assert runner.budgets[1] is None, "l'echeance doit etre levee apres l'evaluation"
    # Une echeance posee et levee par PR evaluee.
    poses = [b for b in runner.budgets if b is not None]
    assert len(poses) == len([b for b in runner.budgets if b is None])


def test_le_delai_par_pr_est_surchargeable_en_ligne_de_commande():
    """`--pr-deadline-s` existe, et une valeur negative est refusee."""
    args = mr._parse_args(["--pr-deadline-s", "42"])
    assert args.pr_deadline_s == 42.0
    assert mr._parse_args([]).pr_deadline_s == mr.PR_DEADLINE_S
    with pytest.raises(SystemExit):
        mr._parse_args(["--pr-deadline-s", "-1"])
