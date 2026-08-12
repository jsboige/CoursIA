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

import pytest

from verifiers.lean_rlvr_verifier import LeanRLVRVerifier, RLVRResult

# Skip global si elan/lake absent du runner (on n'invente pas un faux moteur).
elan_available = shutil.which("lake") is not None or shutil.which("lean") is not None
skip_no_lean = pytest.mark.skipif(
    not elan_available, reason="elan/lake absent — regle F : installer, ne pas contourner"
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
