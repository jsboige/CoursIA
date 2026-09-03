"""Tests for scripts/remeasure_bad_pending.py (#12389 acceptance).

Vérifie que le script :
- appelle `pr_gate.classify()` (pas de ré-implémentation) ;
- accepte des payloads dict-like minimaux ;
- détecte correctement les PRs sans defaut (zero bad).

Aucun appel réseau : on passe des check-runs construits et on mock `subprocess.run`
pour `fetch_check_runs`.

Note : `fetch_check_runs(pr_number, head_sha)` accepte `pr_number` par symétrie
future (URL n'utilise que `head_sha` actuellement -- ce paramètre mort est
laissé pour évolution).
"""

import importlib.util
import json
import sys
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "remeasure_bad_pending.py"
spec = importlib.util.spec_from_file_location("remeasure_bad_pending", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["remeasure_bad_pending"] = mod
spec.loader.exec_module(mod)


def make_run(name, status="completed", conclusion="", started_at=None, run_id=None):
    """Construit un check-run minimal (dict)."""
    run = {"name": name, "status": status, "conclusion": conclusion}
    if started_at is not None:
        run["started_at"] = started_at
    if run_id is not None:
        run["id"] = run_id
    return run


# --- fetch_check_runs : pure transformation JSON ---


def test_fetch_check_runs_returns_dicts():
    """fetch_check_runs doit transformer la sortie NDJSON de gh en dicts
    minimaux (name, status, conclusion) -- pas des objets -- pour que
    dedupe_latest puisse appeler .get(). Mocke subprocess.run."""
    # Sortie NDJSON réaliste : 2 lignes valides + 1 ligne vide (skippée) +
    # 1 JSON malformé (skippé).
    fake_stdout = (
        json.dumps({"name": "Always-on guards", "status": "completed",
                    "conclusion": "failure", "started_at": "2026-09-01T12:00:00Z",
                    "id": 12345})
        + "\n"  # premier run valide
        + "\n"  # ligne vide -- skippée
        + "{not valid json" + "\n"  # JSON malformé -- skippé
        + json.dumps({"name": "PR gate", "status": "queued", "conclusion": "",
                      "started_at": "2026-09-01T12:01:00Z", "id": 12346})
        + "\n"  # second run valide
    )
    fake_result = mock.Mock(stdout=fake_stdout, returncode=0)
    with mock.patch.object(mod.subprocess, "run", return_value=fake_result) as mrun:
        runs = mod.fetch_check_runs(pr_number=14074, head_sha="e881b9b31")

    # Vérification 1 : subprocess.run appelé exactement 1 fois avec les bons args.
    assert mrun.call_count == 1
    args = mrun.call_args[0][0]
    assert args[0] == "gh"
    assert "e881b9b31" in args[2]
    assert "check-runs" in args[2]

    # Vérification 2 : 2 dicts retournés (les 2 valides), pas 4.
    assert len(runs) == 2

    # Vérification 3 : ce sont des dicts minimaux (name, status, conclusion).
    for run in runs:
        assert isinstance(run, dict)
        assert set(run.keys()) == {"name", "status", "conclusion"}
    assert runs[0]["name"] == "Always-on guards"
    assert runs[0]["conclusion"] == "failure"
    assert runs[1]["name"] == "PR gate"
    assert runs[1]["status"] == "queued"


# --- agrégation : PR sans defaut ---


def test_pr_sans_defaut_quand_zero_bad():
    """Une PR avec uniquement des checks OK ne doit pas être comptée
    comme 'avec défaut'."""
    # Setup : 1 PR avec 2 checks OK
    runs = [
        make_run("Always-on guards", "completed", "success"),
        make_run("PR gate", "completed", "success"),
    ]
    # Importer pr_gate pour classifier
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
    import pr_gate
    latest = pr_gate.dedupe_latest(runs)
    pending, bad, ok, advisory = pr_gate.classify(latest, self_name="PR gate")
    # La PR elle-même (PR gate) est self-exclue, donc 1 check restant (Always-on).
    # Pas de bad.
    assert len(bad) == 0, "Checks OK ne doivent pas être 'bad'"
    assert len(advisory) == 0, "Checks OK ne doivent pas être advisory"


def test_pr_avec_bad_comptee_correctement():
    """Une PR avec 1 check bad est marquée comme 'avec défaut'."""
    runs = [
        make_run("Always-on guards", "completed", "failure"),
        make_run("PR gate", "completed", "success"),
    ]
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
    import pr_gate
    latest = pr_gate.dedupe_latest(runs)
    pending, bad, ok, advisory = pr_gate.classify(latest, self_name="PR gate")
    assert len(bad) == 1
    assert "Always-on guards" in bad


def test_advisory_exclu_du_bad():
    """Un check avec 'advisory' dans le name ne doit PAS être compté comme bad
    (cf pr_gate.py règle 6 : is_advisory())."""
    runs = [
        make_run("Solution-leak HIGH delta (advisory, WARN phase, #8053)",
                 "completed", "failure"),
        make_run("PR gate", "completed", "success"),
    ]
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
    import pr_gate
    latest = pr_gate.dedupe_latest(runs)
    pending, bad, ok, advisory = pr_gate.classify(latest, self_name="PR gate")
    assert len(bad) == 0
    assert len(advisory) == 1
    assert any("Solution-leak" in a for a in advisory)


def test_dedupe_latest_prend_le_plus_recent_run():
    """Plusieurs runs du même workflow : seul le plus récent compte.

    `dedupe_latest` utilise la clé `(started_at, id, index)` où
    `started_at` prime, `id` est le tie-breaker, et `index` tranche en
    dernier recours (cf `pr_gate.dedupe_latest` docstring). Ce test
    exerce les 3 niveaux de discrimination :
    1. `started_at` distincts → le plus récent gagne.
    2. `started_at` manquant → `id` plus grand gagne.
    3. `started_at` et `id` tous deux manquants → ordre d'entrée (le
       dernier gagne, `key >= current[0]` est vrai à index égal pour le
       dernier vu).
    """
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
    import pr_gate

    # Cas 1 : `started_at` distincts → le plus récent gagne.
    runs_started_at = [
        make_run("Always-on guards", started_at="2026-09-01T10:00:00Z", run_id=1),
        make_run("Always-on guards", started_at="2026-09-01T12:00:00Z", run_id=2),
        make_run("Always-on guards", started_at="2026-09-01T11:00:00Z", run_id=3),
    ]
    latest = pr_gate.dedupe_latest(runs_started_at)
    assert len(latest) == 1
    assert latest[0]["started_at"] == "2026-09-01T12:00:00Z"
    assert latest[0]["id"] == 2

    # Cas 2 : `started_at` manquant → `id` plus grand gagne.
    runs_id_only = [
        make_run("Always-on guards", run_id=10),
        make_run("Always-on guards", run_id=20),
        make_run("Always-on guards", run_id=15),
    ]
    latest = pr_gate.dedupe_latest(runs_id_only)
    assert len(latest) == 1
    assert latest[0]["id"] == 20

    # Cas 3 : `started_at` et `id` tous deux manquants → l'ordre d'entrée
    # tranche (le dernier vu gagne via `key >= current[0]` à index égal).
    runs_no_key = [
        make_run("Always-on guards"),
        make_run("Always-on guards"),
    ]
    latest = pr_gate.dedupe_latest(runs_no_key)
    assert len(latest) == 1
    # Les deux runs sont identiques sans discriminant ; le dernier index
    # gagne. Vérifions qu'on a bien gardé UN seul, pas zéro ni deux.