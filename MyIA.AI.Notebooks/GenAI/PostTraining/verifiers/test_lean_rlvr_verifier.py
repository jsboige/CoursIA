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

from verifiers import lean_rlvr_verifier as verifier_module
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
    # Les axiomes natifs (hors whitelist coeur) sont flaggues. Le nom
    # materiel derive de la version Lean (drift mesure : v4.34 materialise
    # ``rlvr_task._native.native_decide.ax_1_1``) — l'oracle (reward 0 +
    # flags non vides) est la garantie, pas le nom exact.
    assert r.hack_flags  # non vide
    assert any(
        "native" in f.lower() or "ofReduceBool" in f or "trustCompiler" in f
        for f in r.hack_flags
    ), f"axiome natif attendu, pas {r.hack_flags}"


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


# -- contrat de la migration vers l'organe confine (#23054) ------------------
#
# Tests deterministes du contrat de delegation (stub du client partage) :
# les tests de controle ci-dessus restent a execution REELLE (elan/lake) —
# ici on verifie la FORME de la delegation, pas le moteur Lean.


def test_run_lean_delegates_to_organ(monkeypatch, tmp_path):
    """Chaque rollout passe par l'organe confine (stdin_file), pas un spawn direct."""
    from pathlib import Path

    calls = {}

    class _StubNbu:
        @staticmethod
        def _organ_run(project_path, cmd_args, timeout, stdin_file=None, organ=None):
            calls["args"] = (project_path, list(cmd_args), timeout, stdin_file, organ)
            # Contenu capture AU MOMENT de l'appel : _run_lean supprime le
            # fichier dans son finally avant que le test ne le relise.
            calls["stdin"] = (
                Path(stdin_file).read_text(encoding="utf-8")
                if stdin_file else None)
            return (0, "ok stdout", "")

    monkeypatch.setattr(
        "verifiers.lean_rlvr_verifier._get_lean_notebook_utils",
        lambda: _StubNbu)
    fake_organ = tmp_path / "lean_exec.py"
    fake_organ.write_text("# stub", encoding="utf-8")
    monkeypatch.setattr(
        "verifiers.lean_rlvr_verifier._find_lean_exec",
        lambda: fake_organ)

    verifier = LeanRLVRVerifier(project_dir=tmp_path / "project", timeout=30.0)  # warmup via stub
    out = verifier._run_lean("theorem x : True := by trivial")
    project_path, cmd_args, timeout, stdin_file, organ = calls["args"]
    assert cmd_args[1:] == ["env", "lean", "--stdin"]
    # NOM NU, jamais un chemin resolu : l'organe execute l'enfant via bash
    # (un chemin Windows y est une commande introuvable — mesure 2026-11-03).
    assert cmd_args[0] == "lake"
    assert calls["stdin"] == "theorem x : True := by trivial"
    assert isinstance(timeout, int) and timeout > 0
    assert organ == fake_organ
    assert project_path == str(verifier.project_dir)
    assert "ok stdout" in out


def test_organ_refusal_zero_reward(monkeypatch, tmp_path):
    """Refus de l'organe (admission/budget) -> reward 0.0 + organ_refused, pas un hang."""
    class _StubNbu:
        @staticmethod
        def _organ_run(project_path, cmd_args, timeout, stdin_file=None, organ=None):
            return (-2, "", "insufficient: cap machine epuise")

    monkeypatch.setattr(
        "verifiers.lean_rlvr_verifier._get_lean_notebook_utils",
        lambda: _StubNbu)

    verifier = LeanRLVRVerifier(project_dir=tmp_path / "project", timeout=30.0)  # warmup avalé
    r = verifier.reward("1 + 1 = 2", "by rfl")
    assert r.reward == 0.0
    assert r.compiles is False
    assert r.hack_flags == ["organ_refused"]
    assert "insufficient" in r.raw_output


def test_organ_timeout_maps_to_timeout_flag(monkeypatch, tmp_path):
    """Timeout remonte par l'organe (rc -1) -> meme verdict qu'un timeout direct."""
    class _StubNbu:
        @staticmethod
        def _organ_run(project_path, cmd_args, timeout, stdin_file=None, organ=None):
            return (-1, "", "TIMEOUT after 30s")

    monkeypatch.setattr(
        "verifiers.lean_rlvr_verifier._get_lean_notebook_utils",
        lambda: _StubNbu)

    verifier = LeanRLVRVerifier(project_dir=tmp_path / "project", timeout=30.0)  # warmup avalé
    r = verifier.reward("1 + 1 = 2", "by rfl")
    assert r.reward == 0.0
    assert r.compiles is False
    assert r.hack_flags == ["timeout"]
    assert r.raw_output.startswith("<timeout after")


def _fake_lean(tmp_path, monkeypatch, version="4.35.0"):
    """Installe un lean factice local, sans dépendance à elan ni au réseau.

    ``ELAN_HOME`` est pointé vers un répertoire vide : elan y(logne) ses
    toolchains, et le proxy elan du poste ne peut donc pas écraser le faux
    binaire (il échouerait au lieu de répondre).

    Windows : ``CreateProcess`` ne résout que ``.exe`` et cherche dans le
    PATH du **processus parent** — un script ne peut pas y être déclenché.
    On interpose donc la mesure elle-même ; la reconstruction du tag est
    couverte par les tests de l'organe (``scripts/lean/tests``), et la mesure
    complète est exercée par la CI Linux.
    """
    import os

    bindir = tmp_path / "bin"
    bindir.mkdir()
    if os.name == "nt":
        monkeypatch.setattr(
            "verifiers.lean_rlvr_verifier._installed_toolchain",
            lambda: f"leanprover/lean4:v{version}",
        )
    else:
        lean = bindir / "lean"
        lean.write_text(f'#!/bin/sh\necho "Lean (version {version}, fake)"\n', encoding="utf-8")
        lean.chmod(0o755)
        monkeypatch.setenv("PATH", str(bindir))
    monkeypatch.setenv("HOME", str(tmp_path / "home"))
    monkeypatch.setenv("ELAN_HOME", str(tmp_path / "elan"))
    (tmp_path / "elan" / "bin").mkdir(parents=True)
    (tmp_path / "home" / ".elan" / "bin").mkdir(parents=True)
    return os.fspath(bindir)


def _no_warmup(monkeypatch):
    monkeypatch.setattr(LeanRLVRVerifier, "_warmup", lambda self: None)


def _empty_inventory(monkeypatch):
    """Declaration vide : ni pin d'hote, ni pin de flotte (isole un palier)."""
    organ = verifier_module._get_lean_toolchain()
    monkeypatch.setattr(organ, "load_inventory", lambda *args, **kwargs: {})


def _host(monkeypatch, name):
    """Force le nom d'hote, cle de la declaration par environnement."""
    organ = verifier_module._get_lean_toolchain()
    monkeypatch.setattr(organ, "current_host", lambda: name)


def test_toolchain_environment_pin_is_exact_and_logged(monkeypatch, tmp_path, caplog):
    import logging

    _fake_lean(tmp_path, monkeypatch)
    _no_warmup(monkeypatch)
    monkeypatch.setenv("ELAN_TOOLCHAIN", "leanprover/lean4:v4.33.0")
    project = tmp_path / "project"
    project.mkdir()
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.32.1\n")

    with caplog.at_level(logging.INFO):
        verifier = LeanRLVRVerifier(project_dir=project)

    assert verifier.toolchain == "leanprover/lean4:v4.33.0"
    assert verifier.pin_source == "env"
    assert (project / "lean-toolchain").read_text() == "leanprover/lean4:v4.32.1\n"
    assert "toolchain=leanprover/lean4:v4.33.0 pin=env" in caplog.text

    monkeypatch.setattr("verifiers.lean_rlvr_verifier.Path.home", lambda: tmp_path)
    managed = LeanRLVRVerifier()
    assert (managed.project_dir / "lean-toolchain").read_text() == (
        "leanprover/lean4:v4.33.0\n"
    )


def test_toolchain_project_pin_precedes_resolved_default(monkeypatch, tmp_path):
    _fake_lean(tmp_path, monkeypatch)
    _no_warmup(monkeypatch)
    monkeypatch.delenv("ELAN_TOOLCHAIN", raising=False)
    project = tmp_path / "project"
    project.mkdir()
    pin = "leanprover/lean4:v4.33.1-custom"
    (project / "lean-toolchain").write_text(pin + "\n")

    verifier = LeanRLVRVerifier(project_dir=project)

    assert (verifier.toolchain, verifier.pin_source) == (pin, "projet")


def test_resolved_default_is_logged_but_not_written_to_managed_skeleton(
    monkeypatch, tmp_path, caplog
):
    import logging

    _fake_lean(tmp_path, monkeypatch, version="4.35.0")
    _no_warmup(monkeypatch)
    monkeypatch.delenv("ELAN_TOOLCHAIN", raising=False)
    monkeypatch.setattr("verifiers.lean_rlvr_verifier.Path.home", lambda: tmp_path)
    # Declaration absente : on isole le palier « defaut elan », non fige.
    _empty_inventory(monkeypatch)
    managed = tmp_path / ".cache" / "rlvr-lean"

    with caplog.at_level(logging.INFO):
        verifier = LeanRLVRVerifier()

    assert (verifier.toolchain, verifier.pin_source) == (
        "leanprover/lean4:v4.35.0", "default_resolu"
    )
    assert not (managed / "lean-toolchain").exists()
    assert "toolchain=leanprover/lean4:v4.35.0 pin=default_resolu" in caplog.text


def test_unmeasurable_default_warns_before_the_last_resort(monkeypatch, tmp_path, caplog):
    import logging

    _no_warmup(monkeypatch)
    monkeypatch.delenv("ELAN_TOOLCHAIN", raising=False)
    monkeypatch.setattr("verifiers.lean_rlvr_verifier._installed_toolchain", lambda: None)
    monkeypatch.setattr("verifiers.lean_rlvr_verifier.Path.home", lambda: tmp_path)
    _empty_inventory(monkeypatch)

    with caplog.at_level(logging.WARNING):
        verifier = LeanRLVRVerifier()

    # Le repli est un tag PRESENT dans le parc : l'ancien v4.27.0 (absent de
    # tout poste mesure) ne peut plus etre atteint.
    assert verifier.toolchain == "leanprover/lean4:v4.33.0"
    assert verifier.pin_source == "fallback_averti"
    assert "téléchargement elan peut être requis" in caplog.text


def test_declared_environment_pin_wins_over_the_resolved_default(
    monkeypatch, tmp_path, caplog
):
    """Le pin DECLARE par le poste prime sur son defaut elan mesure.

    C'est le correctif de la derive inter-postes : sans declaration, chaque
    poste epinglait son propre defaut elan (v4.11.0 sur ai-01 mesure le
    2026-11-10, v4.35.0 sur po-2027 mesure le 2026-11-04).
    """
    import logging

    _fake_lean(tmp_path, monkeypatch, version="4.11.0")
    _no_warmup(monkeypatch)
    monkeypatch.delenv("ELAN_TOOLCHAIN", raising=False)
    monkeypatch.setattr("verifiers.lean_rlvr_verifier.Path.home", lambda: tmp_path)
    _host(monkeypatch, "myia-ai-01")
    managed = tmp_path / ".cache" / "rlvr-lean"

    with caplog.at_level(logging.INFO):
        verifier = LeanRLVRVerifier()

    assert verifier.pin_source == "declaration"
    assert verifier.toolchain == "leanprover/lean4:v4.33.0"
    assert (managed / "lean-toolchain").read_text() == "leanprover/lean4:v4.33.0\n"
    assert "toolchain=leanprover/lean4:v4.33.0 pin=declaration" in caplog.text


def test_fleet_pin_applies_to_a_host_that_declares_nothing(monkeypatch, tmp_path):
    """Un poste sans declaration suit le pin de flotte : la derive cesse."""
    _fake_lean(tmp_path, monkeypatch, version="4.11.0")
    _no_warmup(monkeypatch)
    monkeypatch.delenv("ELAN_TOOLCHAIN", raising=False)
    monkeypatch.setattr("verifiers.lean_rlvr_verifier.Path.home", lambda: tmp_path)
    _host(monkeypatch, "poste-sans-declaration")

    verifier = LeanRLVRVerifier()

    assert verifier.pin_source == "declaration_flotte"
    assert verifier.toolchain == "leanprover/lean4:v4.33.0"
