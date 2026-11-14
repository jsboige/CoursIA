"""Budget de concurrence de `lean_exec` — le seuil compare a la PARALLELISME
ACCORDEE, pas aux places reservees (#26480).

Fichier dedie : les tests de la capacite vivent ici, sans collision avec le
fichier de tests general (precedent : `test_lean_exec_run_cwd.py`).

Le defaut, mesure le 14/11 sur `ai-01` : l'organe tuait tout `lake build`
multi-modules. `lean_exec` accorde `granted_jobs=6`, la supervision comparait
le nombre de descendants a `budget=3` — et comptait le processus `lake` (le
scheduler) parmi les descendants : 6 compilations + 1 scheduler = 7 > 3. Le run
etait tue ALORS qu'il utilisait exactement la parallelisme qu'on lui avait
accordee, et l'echec etait presente comme un `timeout`.

Ces tests simulent un lake avec plus de descendants que le budget, sans
Windows, sans Lake et sans toolchain.
"""

from __future__ import annotations

import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))

import lean_exec as le  # noqa: E402


def _fake_lake(root_pid=1000, workers=3, schedulers=1):
    """(table pid->ppid, pid->nom) d'un faux lake : `workers` compilations
    `lean` et `schedulers` processus `lake`, tous enfants de la racine."""
    table, names = {}, {}
    pid = root_pid + 1
    for _ in range(workers):
        table[pid] = root_pid
        names[pid] = "lean"
        pid += 1
    for _ in range(schedulers):
        table[pid] = root_pid
        names[pid] = "lake"
        pid += 1
    return table, names


def test_le_budget_compte_les_compilations_pas_le_scheduler(monkeypatch):
    table, names = _fake_lake(workers=3, schedulers=2)
    monkeypatch.setattr(le, "_proc_name", lambda pid, _t: names.get(pid, ""))
    # 3 compilations ; les 2 processus `lake` ne sont PAS des compilations.
    assert le.count_lean_workers(1000, table) == 3


def test_un_run_a_la_parallelesme_accordee_n_est_pas_une_violation(monkeypatch):
    # CONTROLE NEGATIF : l'etat nominal d'aujourd'hui (la parallelisme
    # accordee, plus le scheduler) ne doit PAS etre un rouge. C'est
    # exactement l'etat que l'organe tuait a tort.
    granted, budget = 3, 3
    table, names = _fake_lake(workers=granted, schedulers=1)
    monkeypatch.setattr(le, "_proc_name", lambda pid, _t: names.get(pid, ""))
    own = le.count_lean_workers(1000, table)
    assert own == granted
    assert le.budget_violation_reason(own, granted, budget) is None


def test_une_vraie_violation_est_comptee_au_dela_du_seuil(monkeypatch):
    # TEMOIN : un lake avec PLUS de descendants que le budget declenche le
    # rouge, et la raison nomme la cause au lieu de dire `timeout`.
    granted, budget = 3, 3
    table, names = _fake_lake(workers=granted + 2, schedulers=1)
    monkeypatch.setattr(le, "_proc_name", lambda pid, _t: names.get(pid, ""))
    own = le.count_lean_workers(1000, table)
    reason = le.budget_violation_reason(own, granted, budget)
    assert reason is not None
    assert "5 compilations lean" in reason
    assert "3" in reason


def test_la_parallelesme_accordee_never_depasse_les_places_reservees():
    # L'incoherence qui tuait les runs : une parallelisme accordee (6)
    # superieure aux places reservees dans le cap machine (3).
    assert le.effective_granted(6, 3) == 3
    assert le.effective_granted(2, 3) == 2
    assert le.effective_granted(0, 3) == 0


def test_le_drapeau_kjobs_estinerte_mais_le_levier_reel_est_lean_num_threads():
    # Le drapeau que l'organe posait ne borne rien : dans Lake, `-K` est une
    # CLE DE CONFIGURATION (`-K key[=value]`), ni `-j` ni `--jobs` n'existent,
    # et aucune option de configuration `jobs` n'est definie. Le seuil
    # compare a la parallelisme accordee, qui elle passe par
    # `LEAN_NUM_THREADS` — le seul levier mesure qui borne la concurrence
    # reelle de Lake (cf. la mesure de #26480).
    assert le.bound_command(["lake", "build"], 5) == [
        "lake", "build", "-Kjobs=5"]
    assert "LEAN_NUM_THREADS" in le.__doc__
    assert "inerte" in le.bound_command.__doc__.lower()
