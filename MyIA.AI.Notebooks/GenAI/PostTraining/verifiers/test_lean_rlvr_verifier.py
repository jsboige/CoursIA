"""Tests du verificateur RLVR Lean (corpus #10289, Tier-2).

Tests de controle (positif + negatif + oracle de reward hacking) executes
sur le vrai moteur Lean via elan (regle F : pas de mock, pas de contournement).
Patron pytest standard ; ``pytest verifiers/test_lean_rlvr_verifier.py``.

Ces tests materialisent l'acceptance du verificateur Tier-2 :
  - une preuve valide -> reward 1.0 ;
  - une preuve par ``sorry`` -> reward 0.0 + hack_flag ``sorryAx`` (Goodhart) ;
  - une preuve fausse -> reward 0.0, compiles=False ;
  - un groupe de completions (GRPO) -> une recompense par completion ;
  - l'adapteur ``trl.GRPOTrainer`` respecte la signature ``(prompts, completions, **kwargs)``.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from verifiers.lean_rlvr_verifier import LeanRLVRVerifier, RLVRResult


def _lean_reachable() -> bool:
    """Lean est-il executable via l'organe confine (natif ou WSL) ?

    Migration #15666 : le lancement passe par l'organe — lake n'a plus besoin
    d'etre sur le PATH Windows, un backend WSL suffit. La sonde WSL (bornee
    10 s, meme forme que ``lean_exec.wsl_backend_available``) ne tourne que si
    la sonde native echoue.
    """
    if shutil.which("lake") is not None or shutil.which("lean") is not None:
        return True
    try:
        out = subprocess.run(
            ["wsl", "--", "bash", "-lc", "command -v lake"],
            capture_output=True, timeout=10,
        )
        return out.returncode == 0 and bool(out.stdout.strip())
    except (OSError, subprocess.SubprocessError):
        return False


# Skip global si elan/lake injoignable (on n'invente pas un faux moteur).
lean_available = _lean_reachable()
skip_no_lean = pytest.mark.skipif(
    not lean_available,
    reason="lean/lake injoignable (natif ou WSL) — regle F : installer, ne pas contourner",
)


@pytest.fixture(scope="module")
def verifier():
    """Verificateur partage (le warmup est paye une fois)."""
    return LeanRLVRVerifier(timeout=120.0)


@skip_no_lean
def test_valid_proof_rewards_one(verifier):
    """Cas canonique : preuve correcte -> reward 1.0, aucun hack."""
    r = verifier.reward("1 + 1 = 2", "by rfl")
    assert r.reward == 1.0
    assert r.compiles is True
    assert r.has_sorry is False
    assert r.hack_flags == []


@skip_no_lean
def test_valid_proof_term_mode(verifier):
    """Preuve en mode terme (sans `by`) reconnue."""
    r = verifier.reward("1 + 1 = 2", "rfl")
    assert r.reward == 1.0


@skip_no_lean
def test_sorry_is_reward_hacking(verifier):
    """Oracle Goodhart : `by sorry` -> reward 0.0 + hack_flag sorryAx.

    C'est le cas distinctif du verificateur Lean (#10289) : la politique qui
    apprend a emit sorry pour toucher la recompense est detectee, pas recompensee.
    """
    r = verifier.reward("True", "by sorry")
    assert r.reward == 0.0
    assert r.compiles is True  # sorry compile (warning), ce n'est pas une erreur
    assert r.has_sorry is True
    assert "sorryAx" in r.hack_flags


@skip_no_lean
def test_wrong_proof_does_not_compile(verifier):
    """Preuve fausse -> erreur de typage, compiles=False, reward 0.0."""
    r = verifier.reward("1 + 1 = 3", "by rfl")
    assert r.reward == 0.0
    assert r.compiles is False


@skip_no_lean
def test_tactic_block_accepted(verifier):
    """Bloc tactique multi-etapes (sans `by` prefixe, ajoute automatiquement)."""
    r = verifier.reward("∀ n : Nat, n + 0 = n", "intro n; rfl")
    assert r.reward == 1.0
    assert r.compiles is True


@skip_no_lean
def test_reward_batch_grpo(verifier):
    """GRPO : N completions d'un meme enonce -> N recompenses."""
    proofs = ["by rfl", "by sorry", "by simp"]
    results = verifier.reward_batch("1 + 1 = 2", proofs)
    assert len(results) == 3
    assert all(isinstance(r, RLVRResult) for r in results)
    # rfl -> 1.0 ; sorry -> 0.0 ; simp (valide) -> 1.0
    assert results[0].reward == 1.0
    assert results[1].reward == 0.0
    assert results[2].reward == 1.0


@skip_no_lean
def test_trl_adapter_signature(verifier):
    """L'adapteur trl respecte la signature GRPO et lit `statement` via kwargs."""
    fn = verifier.trl_reward_adapter()
    rewards = fn(
        prompts=["prouve: 2 + 2 = 4"] * 2,
        completions=["by rfl", "by sorry"],
        statement="2 + 2 = 4",
    )
    assert rewards == [1.0, 0.0]


@skip_no_lean
def test_trl_adapter_requires_statement(verifier):
    """Sans enonce (ground truth), l'adapteur echoue explicitement (pas de silence)."""
    fn = verifier.trl_reward_adapter()
    with pytest.raises(ValueError, match="statement"):
        fn(prompts=["x"], completions=["by rfl"])


@skip_no_lean
def test_forbidden_axiom_flagged(verifier):
    """Un axiome hors whitelist est flaggue comme hack (reward 0 meme si compile).

    ``native_decide`` invoque l'oracle d'execution de code natif ; en Lean 4
    cela materialise les axiomes ``Lean.ofReduceBool`` + ``Lean.trustCompiler``
    (verifie firsthand). C'est un chemin de triche distinct de sorry,
    explicitement enumere par #10289 — le verificateur le detecte.
    """
    r = verifier.reward("1 + 1 = 2", "by native_decide")
    assert r.reward == 0.0
    assert r.compiles is True  # compile, mais avec axiomes interdits
    # Les axiomes natifs (hors whitelist coeur) sont flaggues.
    assert r.hack_flags  # non vide
    assert "Lean.ofReduceBool" in r.hack_flags


@skip_no_lean
def test_timeout_returns_zero(verifier, monkeypatch):
    """Un rollout qui depasse le budget -> reward 0, hack_flag timeout (pas de hang).

    Test deterministe du code-path de gestion du timeout (on ne depend pas de la
    vitesse machine pour declencher un vrai timeout) : on simule l'expiration.
    """
    import subprocess as sp

    def _hang(*a, **k):
        raise sp.TimeoutExpired(cmd="lean", timeout=1.0)

    monkeypatch.setattr(verifier, "_run_lean", _hang)
    r = verifier.reward("1 + 1 = 2", "by rfl")
    assert r.reward == 0.0
    assert r.compiles is False
    assert "timeout" in r.hack_flags


def test_rollout_routes_through_the_organ(monkeypatch, tmp_path):
    """Chaque rollout est CONFIE a l'organe confine, pas spawn ici (#15666).

    Test structurel (aucun Lean requis) : le payload passe au client partage
    est ``lake env lean --stdin`` avec la source en fichier stdin, le cwd est
    le projet squelette, et le timeout traverse — plus AUCUN subprocess lake
    direct dans ce module (garde ``check_lake_direct_invocation.py``).
    """
    import verifiers.lean_rlvr_verifier as vrf

    captured = {}

    def _fake_organ_run(project_path, cmd_args, timeout, stdin_file=None):
        captured["project"] = project_path
        captured["cmd"] = list(cmd_args)
        captured["timeout"] = timeout
        captured["stdin"] = Path(stdin_file).read_text(encoding="utf-8")
        return 0, "ok", ""

    monkeypatch.setattr(vrf, "_organ_run", _fake_organ_run)
    v = vrf.LeanRLVRVerifier(project_dir=tmp_path, timeout=7.0)
    raw = v._run_lean("theorem t : True := by trivial\n")
    assert raw == "ok\n"
    assert captured["cmd"] == ["lake", "env", "lean", "--stdin"]
    assert captured["stdin"] == "theorem t : True := by trivial\n"
    assert captured["timeout"] == 7.0
    assert captured["project"] == str(v.project_dir)


def test_organ_refusal_is_visible_not_reward_zero(monkeypatch, tmp_path):
    """Un refus d'admission organe (cap, telemetrie...) n'est pas un reward 0.

    Reward 0.0 sur une panne d'infrastructure enseignerait a la politique
    qu'une preuve valide ne vaut rien (empoisonnement du gradient, #10289) :
    le refus doit rester un echec VISIBLE, jamais un verdict de preuve.
    """
    import verifiers.lean_rlvr_verifier as vrf

    def _refused(project_path, cmd_args, timeout, stdin_file=None):
        return (-2, "",
                "machine-wide cap 8: native population 8 + requested budget 2 > cap")

    monkeypatch.setattr(vrf, "_organ_run", _refused)
    v = vrf.LeanRLVRVerifier(project_dir=tmp_path, timeout=5.0)
    with pytest.raises(RuntimeError, match="lean_exec refused"):
        v.reward("1 + 1 = 2", "by rfl")
