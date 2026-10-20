#!/usr/bin/env python3
"""Anti-drift pins pour le banc volet B (#18430) : leandojo_v2_bench.py.

Le banc compare le prouveur LeanDojo-v2 au harnais maison sur le rung 52
(CALIBRATION_CONWAY_LAS_ROUND_TRIP). Sa validite repose sur des joints que
rien ne garde coherents entre eux : le modele LLM doit rester celui des
traces maison (sinon la comparaison porte sur le moteur, pas l'organe), le
budget doit rester aligne sur la passe 17 (1 800 s), l'enonce doit rester
celui du rung, et le contournement LEAN_PATH doit continuer a parser la
sortie integrale de ``lake env printenv`` (les deux bugs mesures de
pantograph 0.3.15). Ce test pince chaque joint sans reseau ni WSL : tout
drift leve ici avant de fausser une mesure.

Run: python -m pytest scripts/tests/test_leandojo_v2_bench.py
"""
import asyncio
import importlib.util
import subprocess
import sys
import time
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
BENCH = (
    REPO
    / "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover"
    / "integration/leandojo_v2_bench.py"
)


def _load_bench():
    spec = importlib.util.spec_from_file_location("leandojo_v2_bench", BENCH)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["leandojo_v2_bench"] = mod  # requis par les dataclasses
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def bench():
    return _load_bench()


def test_bench_file_exists():
    assert BENCH.is_file(), f"banc introuvable: {BENCH}"


def test_model_matches_house_traces(bench):
    # config.py PROVIDERS["openrouter"] : anthropic/claude-opus-4.7 par defaut,
    # non surcharge par les .env locaux (mesure du 2026-10-12). Si ce pin casse,
    # la comparaison porte sur un autre moteur que les traces maison.
    assert bench.HOUSE_MODEL == "anthropic/claude-opus-4.7"


def test_budget_matches_house_pass17(bench):
    assert bench.HOUSE_REASONING_BUDGET_S == 1800.0


def test_rung_statement_is_round_trip(bench):
    assert bench.RUNG_NAME == "CALIBRATION_CONWAY_LAS_ROUND_TRIP"
    # Identifiants qualifies : le REPL Pantograph ne charge pas le namespace
    # Conway (mesure du 2026-10-12, "Unknown identifier digitsToNat").
    assert bench.RUNG_STATEMENT == (
        "forall (n : Nat), Conway.digitsToNat (Conway.natToDigits n) = n"
    )


def test_protocol_gap_documents_toolchain_pin(bench):
    # L'ecart de protocole doit citer la toolchain EXACTE du wheel
    # (pantograph/lean-toolchain = v4.29.1, mesure du 2026-10-12), pas une
    # approximation : c'est ce qui rend le mini-lake reproductible.
    import inspect

    src = inspect.getsource(bench)
    assert "v4.29.1" in src
    assert "lean-toolchain" in src


def test_lake_lean_path_parses_full_printenv(bench, monkeypatch):
    # Bug mesure : `lake env printenv LEAN_PATH` rend VIDE sur lake 5.0.0 ;
    # seul `lake env printenv` integral porte LEAN_PATH. Le parseur doit
    # extraire la ligne exacte, pas la premiere ligne contenant "LEAN".
    fake = subprocess.CompletedProcess(
        args=[],
        returncode=0,
        stdout=(
            "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus\n"
            "LEAN_RECURSION_COUNT=1\n"
            "LEAN_PATH=/pkg/build/lib/lean:/proj/.lake/build/lib/lean:"
            "/toolchain/lib/lean\n"
            "LEAN_SRC_PATH=/pkg:/proj\n"
        ),
    )
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: fake)
    assert bench.lake_lean_path("/proj") == (
        "/pkg/build/lib/lean:/proj/.lake/build/lib/lean:/toolchain/lib/lean"
    )


def test_lake_lean_path_missing_raises(bench, monkeypatch):
    fake = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="PATH=/usr/bin\n"
    )
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: fake)
    with pytest.raises(bench.ConfigError):
        bench.lake_lean_path("/proj")


def test_openrouter_key_missing_raises(bench, monkeypatch):
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    with pytest.raises(bench.ConfigError):
        bench._openrouter_key()


def test_bench_result_shape(bench):
    r = bench.BenchResult(
        rung=bench.RUNG_NAME, mode="step_by_step",
        model=bench.HOUSE_MODEL, budget_s=1800.0, success=False,
    )
    d = r.__dataclass_fields__
    for key in (
        "llm_calls", "tactic_steps", "elapsed_s", "termination",
        "tactics_tried", "proof_mode_output",
    ):
        assert key in d, f"champ de mesure manquant: {key}"


def test_no_secrets_in_source():
    src = BENCH.read_text(encoding="utf-8")
    assert "sk-" not in src
    assert "OPENROUTER_API_KEY" in src  # lu de l'env, jamais en dur
    assert 'os.environ.get("OPENROUTER_API_KEY"' in src


# --- Deadline de bout en bout (mesure adjoint 2026-10-13, c.6143211874) ---
# bench_whole_proof n'appliquait jamais budget_s (budget 0.001 s rendait
# success=True en 0.1 s), et requests.post dans _post n'avait pas de timeout :
# le budget etait controle seulement avant un appel synchrone non borne.


def test_transport_timeout_none_without_deadline(bench):
    assert bench.transport_timeout_s(None) is None


def test_transport_timeout_bounded_by_remaining_and_cap(bench):
    # borne par le temps restant...
    assert bench.transport_timeout_s(0.05) == 0.05
    # ...et par le plafond transport, jamais au-dela
    assert bench.transport_timeout_s(1e9) == bench.REQUEST_TIMEOUT_CAP_S


def test_transport_timeout_negative_means_budget_exhausted(bench):
    # <= 0 : l'appel ne doit pas partir du tout (budget_hit dans _post)
    assert bench.transport_timeout_s(-1.0) <= 0


def test_post_passes_timeout_pin(bench):
    # Pin structurel : l'appel requests doit porter le timeout calcule --
    # sans lui, la deadline residuelle ne borne rien.
    import inspect

    src = inspect.getsource(bench)
    assert "timeout=timeout" in src


class _FakeStepServer:
    """Serveur factice : goal_start_async dort 0.05 s pour rendre la boucle
    step deterministement hors budget (budget_s=0.001)."""

    async def goal_start_async(self, _stmt):
        await asyncio.sleep(0.05)
        return "state0"

    async def goal_tactic_async(self, state, _tac):
        return state


def test_step_mode_budget_timeout(monkeypatch, bench):
    async def fake_start(*_a, **_k):
        return _FakeStepServer()

    monkeypatch.setattr(bench, "_start_server", fake_start)
    monkeypatch.setattr(
        bench, "_make_openrouter_generator",
        lambda **_k: type("G", (), {
            "calls": 0, "budget_hit": False,
            "generate": lambda self, _s: "rwcommute",
        })(),
    )
    result = asyncio.run(
        bench.bench_step_by_step("/proj", budget_s=0.001, max_calls=10, timeout_s=1)
    )
    # goal_start a deja consomme 0.05 s > budget 0.001 s : la boucle casse
    # en tete, avant tout appel LLM.
    assert result.success is False
    assert result.termination == "budget_s_timeout"
    assert result.llm_calls == 0


class _FakeWholeGen:
    calls = 1
    budget_hit = True

    def generate_whole_proof(self, _thm):
        return "induction n with k ih; simp"


def test_whole_proof_budget_hit_never_compiles(monkeypatch, bench):
    # budget_hit pendant la generation : pas de check_compile, pas de
    # reussite -- termination budget_s_timeout (le cas du dossier adjoint :
    # budget 0.001 s, generation 0.05 s, success=True attendu casse).
    compiled = []

    class _Srv:
        async def check_compile_async(self, _code):
            compiled.append(1)
            return []

    async def fake_start(*_a, **_k):
        return _Srv()

    monkeypatch.setattr(bench, "_start_server", fake_start)
    monkeypatch.setattr(
        bench, "_make_openrouter_generator", lambda **_k: _FakeWholeGen()
    )
    result = asyncio.run(
        bench.bench_whole_proof("/proj", budget_s=0.001, timeout_s=1)
    )
    assert result.success is False
    assert result.termination == "budget_s_timeout"
    assert compiled == []  # la verification ne part pas : rien a verifier


def test_whole_proof_elapsed_over_budget_fails(monkeypatch, bench):
    # budget_hit faux, mais la generation a dure plus que le budget : la
    # preuve est nee hors budget -> echec, pas de compilation.
    compiled = []

    class _Srv:
        async def check_compile_async(self, _code):
            compiled.append(1)
            return []

    async def fake_start(*_a, **_k):
        return _Srv()

    class _SlowGen:
        calls = 1
        budget_hit = False

        def generate_whole_proof(self, _thm):
            time.sleep(0.05)  # 50x le budget
            return "sorry"

    monkeypatch.setattr(bench, "_start_server", fake_start)
    monkeypatch.setattr(
        bench, "_make_openrouter_generator", lambda **_k: _SlowGen()
    )
    result = asyncio.run(
        bench.bench_whole_proof("/proj", budget_s=0.001, timeout_s=1)
    )
    assert result.success is False
    assert result.termination == "budget_s_timeout"
    assert compiled == []
    assert result.elapsed_s >= 0.05


# --- Le joint deadline de la VRAIE factory (mesure adjoint 2026-10-13) -----
#
# Recoupement adjoint sur 4920b146840 : la factory recevait ``deadline`` mais
# instanciait ``OpenRouterTacticGenerator()`` sans le transmettre -- depuis
# le VRAI generateur, ``self.deadline`` restait None, ``timeout`` None et
# ``budget_hit`` inatteignable (une requete partait meme budget epuise).
# Ces tests appellent la VRAIE factory, sans reseau ni wheel : les
# dependances lourdes (``lean_dojo_v2.*``, ``loguru``) sont injectees en
# doublons minimaux, seul ``requests.post`` est intercepte.


def _inject_factory_deps(monkeypatch):
    """Doublons minimaux des imports internes de la factory."""
    import types

    class _HFTacticGenerator:
        def __init__(self, model_name: str = "") -> None:
            self.model_name = model_name
            self.used_tactics = set()

    hf_runner = types.ModuleType(
        "lean_dojo_v2.external_api.python.external_models.hf_runner")
    hf_runner.HFTacticGenerator = _HFTacticGenerator
    parser = types.ModuleType(
        "lean_dojo_v2.external_api.python.external_models.external_parser")
    parser.pre_process_input = lambda _model, s: s
    # Fidele a la branche "claude" REELLE d'external_parser.py (mesure
    # 2026-10-20) : tronque toute sortie a une ligne. Le shim du banc doit
    # etre IMMUNISE contre ce comportement sur les preuves entieres.
    parser.post_process_output = (
        lambda _model, s: s.split("lean")[-1].split("```")[0].split("\n")[1]
    )
    loguru = types.ModuleType("loguru")

    class _Logger:
        @staticmethod
        def error(_msg):
            pass

        @staticmethod
        def info(_msg):
            pass

    loguru.logger = _Logger()
    for name, mod in {
        "lean_dojo_v2": types.ModuleType("lean_dojo_v2"),
        "lean_dojo_v2.external_api":
            types.ModuleType("lean_dojo_v2.external_api"),
        "lean_dojo_v2.external_api.python":
            types.ModuleType("lean_dojo_v2.external_api.python"),
        "lean_dojo_v2.external_api.python.external_models":
            types.ModuleType("lean_dojo_v2.external_api.python.external_models"),
        "lean_dojo_v2.external_api.python.external_models.hf_runner": hf_runner,
        "lean_dojo_v2.external_api.python.external_models.external_parser":
            parser,
        "loguru": loguru,
    }.items():
        monkeypatch.setitem(sys.modules, name, mod)


def test_factory_transmits_deadline_and_timeout(monkeypatch, bench):
    # La deadline passee a la factory doit atteindre le generateur : stockee
    # telle quelle, borne du transport = temps restant (plafonne a 120 s).
    _inject_factory_deps(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "cle-de-test")
    deadline = time.monotonic() + 50.0
    gen = bench._make_openrouter_generator(deadline=deadline)
    assert gen.deadline == deadline  # le joint defectueux laissait None ici

    class _Resp:
        @staticmethod
        def json():
            return {"choices": [{"message": {"content": "exact"}}]}

    posted = []
    monkeypatch.setattr(
        "requests.post", lambda *a, **k: posted.append(k) or _Resp())
    outs = gen._post("prompt", n=1, max_tokens=8)
    assert outs == ["exact"]
    assert len(posted) == 1
    timeout = posted[0]["timeout"]
    assert 0 < timeout <= bench.REQUEST_TIMEOUT_CAP_S
    assert timeout <= 50.0  # le temps restant, pas le seul plafond global


def test_factory_expired_deadline_sends_no_request(monkeypatch, bench):
    # Budget deja epuise a l'entree : la requete ne part pas du tout et la
    # coupure remonte via budget_hit -- atteignable DEPUIS la vraie factory.
    _inject_factory_deps(monkeypatch)
    deadline = time.monotonic() - 1.0
    gen = bench._make_openrouter_generator(deadline=deadline)
    assert gen.deadline == deadline

    posted = []
    monkeypatch.setattr("requests.post", lambda *a, **k: posted.append(k))
    assert gen._post("prompt", n=1, max_tokens=8) == []
    assert posted == []
    assert gen.budget_hit is True


def test_factory_without_deadline_keeps_none(monkeypatch, bench):
    # Sans deadline le transport reste non borne (None) -- comportement
    # documente, distinct du joint defectueux qui rendait TOUTE deadline None.
    _inject_factory_deps(monkeypatch)
    gen = bench._make_openrouter_generator()
    assert gen.deadline is None


# --- Defauts de transport mesures le 2026-10-20 (run 2026-10-12 degenere) ---
#
# Sonde HTTP 200 sur openrouter : "n": 4 rend 1 SEUL choix (l'API Anthropic
# n'a pas de sampling n). Le generateur v2 attend n echantillons par pas ;
# sans emulation, le dedoublonnage used_tactics epuise la recherche en 3
# appels (5,9 s contre 1 925 s maison). Second defaut : la branche claude
# de post_process_output tronque a UNE ligne -- fatal aux preuves entieres.


def test_extract_whole_proof_fenced_block(bench):
    # Sortie brute mesuree le 2026-10-20 (7 lignes fence comprise) : la
    # preuve doit resister ENTIERE, pas une ligne.
    raw = (
        "```lean\n"
        "  induction n using Conway.natToDigits.induct with\n"
        "  | case1 => rfl\n"
        "  | case2 n h ih =>\n"
        "    unfold Conway.natToDigits\n"
        "    simp [h, Conway.digitsToNat, ih]\n"
        "```"
    )
    assert bench._extract_whole_proof(raw) == (
        "induction n using Conway.natToDigits.induct with\n"
        "  | case1 => rfl\n"
        "  | case2 n h ih =>\n"
        "    unfold Conway.natToDigits\n"
        "    simp [h, Conway.digitsToNat, ih]"
    )


def test_extract_whole_proof_unterminated_and_raw(bench):
    # bloc non termine (pas de fermeture) et sortie nue : passes tels quels
    assert bench._extract_whole_proof("```lean\n  rfl") == "rfl"
    assert bench._extract_whole_proof("  induction n\n  rfl") == (
        "induction n\n  rfl"
    )


def test_extract_whole_proof_strips_think_block(bench):
    # Sortie MESUREE le 2026-10-20 (run corrige) : claude-opus-4.7 ouvre
    # d'un bloc <think>...</think> AVANT la fence. L'extrateur doit rendre
    # la preuve seule -- jamais le raisonnement au check_compile.
    measured = (
        "<think>\n"
        "I need to prove this theorem but I don't know the definitions.\n"
        "Likely `natToDigits` produces digits and `digitsToNat` reverses it.\n"
        "</think>\n\n"
        "```lean\n"
        "  induction n using Nat.strong_induction_on with\n"
        "  | _ n ih =>\n"
        "    unfold Conway.natToDigits Conway.digitsToNat\n"
        "    simp_all\n"
        "    split <;> simp_all <;> omega\n"
        "```"
    )
    assert bench._extract_whole_proof(measured) == (
        "induction n using Nat.strong_induction_on with\n"
        "  | _ n ih =>\n"
        "    unfold Conway.natToDigits Conway.digitsToNat\n"
        "    simp_all\n"
        "    split <;> simp_all <;> omega"
    )


def test_extract_whole_proof_think_without_fence(bench):
    # think retire meme sans fence derriere : reste rendu nu.
    assert bench._extract_whole_proof(
        "<think>\nreasoning\n</think>\n  rfl"
    ) == "rfl"


def test_post_emulates_n_with_successive_requests(monkeypatch, bench):
    # openrouter rend 1 choix par requete : _post doit repeter la requete
    # jusqu'a n choix collectes, chaque payload demandant n=1.
    _inject_factory_deps(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "cle-de-test")
    gen = bench._make_openrouter_generator(deadline=time.monotonic() + 60.0)

    payloads = []

    class _Resp:
        @staticmethod
        def json():
            return {"choices": [{"message": {"content": "exact rfl"}}]}

    def fake_post(_url, headers=None, json=None, timeout=None):
        payloads.append(json)
        return _Resp()

    import requests as _requests

    monkeypatch.setattr(_requests, "post", fake_post)
    outs = gen._post("prompt", n=4, max_tokens=256)
    assert outs == ["exact rfl"] * 4  # 4 choix collectes
    assert len(payloads) == 4  # ...par 4 requetes successives
    assert all(p["n"] == 1 for p in payloads)  # jamais "n": k dans le payload
    assert gen.calls == 4  # chaque sous-requete compte


def test_post_emulation_stops_when_budget_expires(monkeypatch, bench):
    # Budget epuise en pleine emulation : les sous-requetes suivantes ne
    # partent pas, budget_hit monte, les choix deja collectes sont rendus.
    _inject_factory_deps(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "cle-de-test")
    # deadline courte : la 1re sous-requete (60 ms) la consomme presque toute
    gen = bench._make_openrouter_generator(
        deadline=time.monotonic() + 0.03
    )

    class _Resp:
        @staticmethod
        def json():
            return {"choices": [{"message": {"content": "simp"}}]}

    def fake_post(_url, headers=None, json=None, timeout=None):
        time.sleep(0.06)
        return _Resp()

    import requests as _requests

    monkeypatch.setattr(_requests, "post", fake_post)
    outs = gen._post("prompt", n=4, max_tokens=256)
    assert gen.budget_hit is True
    assert len(outs) < 4  # emulation coupee avant n choix


def test_post_error_midway_returns_collected(monkeypatch, bench):
    # Erreur API en pleine emulation : on rend ce qui est deja collecte,
    # sans hammer le serveur -- et budget_hit reste faux (erreur != budget).
    _inject_factory_deps(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "cle-de-test")
    gen = bench._make_openrouter_generator(deadline=time.monotonic() + 60.0)

    state = {"n": 0}

    class _OkResp:
        @staticmethod
        def json():
            return {"choices": [{"message": {"content": "rfl"}}]}

    class _ErrResp:
        @staticmethod
        def json():
            return {"error": {"message": "rate limited"}}

    def fake_post(_url, headers=None, json=None, timeout=None):
        state["n"] += 1
        return _OkResp() if state["n"] == 1 else _ErrResp()

    import requests as _requests

    monkeypatch.setattr(_requests, "post", fake_post)
    outs = gen._post("prompt", n=4, max_tokens=256)
    assert outs == ["rfl"]
    assert state["n"] == 2  # erreur arrete l'emulation
    assert gen.budget_hit is False


def test_generate_whole_proof_returns_full_proof(monkeypatch, bench):
    # Pin fonctionnel du second defaut : generate_whole_proof rend la preuve
    # COMPLETE extraite du bloc, jamais la premiere ligne (le run 2026-10-12
    # avait "induction n using Nat.strong_induction_on with" -- une ligne).
    _inject_factory_deps(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "cle-de-test")
    gen = bench._make_openrouter_generator(deadline=time.monotonic() + 60.0)

    class _Resp:
        @staticmethod
        def json():
            return {
                "choices": [
                    {
                        "message": {
                            "content": (
                                "```lean\n"
                                "  induction n using Conway.natToDigits.induct with\n"
                                "  | case1 => rfl\n"
                                "```"
                            )
                        }
                    }
                ]
            }

    import requests as _requests

    monkeypatch.setattr(_requests, "post", lambda *a, **k: _Resp())
    proof = gen.generate_whole_proof("theorem t : True := by")
    assert proof.count("\n") == 1  # deux lignes : pas de troncature une-ligne
    assert "case1 => rfl" in proof
