"""Contrats du coeur et du transport REST de l'automate (pli 0 v2, #26511).

Meme discipline que test_structured_outputs_core.py (GenAI/Texte, #25018) :
les exceptions du coeur (`AutomataInputError` -> status invalid,
`AutomataRunError` -> status error) et la serialisation JSON des resultats
d'operations (automata-lib renomme les etats en int apres complement/union)
sont verifiees ici, puis le vrai transport TCP local (uvicorn + httpx) exerce
le service FastAPI `POST /automata/run` sur le meme contrat.

Valeurs de reference mesurees firsthand sur ce siege (automata-lib) :
  - DFA pair de 'a' (celui du carnet, cellule 2.3) : 'aa' accepte,
    trace ['q_even', 'q_odd', 'q_even'] ; 'ab' rejete ; '' accepte.
  - read_input_stepwise rend l'etat initial compris (un etat de plus que de
    symboles consommes).
"""

from __future__ import annotations

import socket
import sys
import threading
import time
from pathlib import Path

import httpx
import pytest
import uvicorn

sys.path.insert(0, str(Path(__file__).resolve().parent))

from automata_core import (
    AutomataInputError,
    build_dfa,
    run,
)
from automata_service import create_app


# Le DFA pair de 'a' du carnet (section 2.3), en forme JSON du contrat.
EVEN_A = {
    "states": ["q_even", "q_odd"],
    "input_symbols": ["a", "b"],
    "transitions": {
        "q_even": {"a": "q_odd", "b": "q_even"},
        "q_odd": {"a": "q_even", "b": "q_odd"},
    },
    "initial_state": "q_even",
    "final_states": ["q_even"],
}

# DFA reconnaissant les mots se terminant par 'b' (meme alphabet).
ENDS_B = {
    "states": ["p0", "p1"],
    "input_symbols": ["a", "b"],
    "transitions": {
        "p0": {"a": "p0", "b": "p1"},
        "p1": {"a": "p0", "b": "p1"},
    },
    "initial_state": "p0",
    "final_states": ["p1"],
}


# ---------------------------------------------------------------------------
# Coeur : construction et validation
# ---------------------------------------------------------------------------


def test_payload_must_be_dict() -> None:
    with pytest.raises(AutomataInputError):
        run("pas un objet")


def test_automaton_must_be_dict() -> None:
    with pytest.raises(AutomataInputError):
        run({"automaton": "q_even"})


def test_automaton_missing_fields() -> None:
    spec = dict(EVEN_A)
    del spec["final_states"]
    with pytest.raises(AutomataInputError):
        run({"automaton": spec})


def test_automaton_invalid_transition() -> None:
    # Transition vers un etat absent : la validation structurelle
    # d'automata-lib doit etre relayee en AutomataInputError.
    spec = {
        "states": ["q_even", "q_odd"],
        "input_symbols": ["a", "b"],
        "transitions": {
            "q_even": {"a": "q_odd", "b": "q_ghost"},
            "q_odd": {"a": "q_even", "b": "q_odd"},
        },
        "initial_state": "q_even",
        "final_states": ["q_even"],
    }
    with pytest.raises(AutomataInputError):
        run({"automaton": spec})


def test_unknown_op() -> None:
    with pytest.raises(AutomataInputError):
        run({"automaton": EVEN_A, "op": "minify"})


# ---------------------------------------------------------------------------
# Coeur : op=accepts (verdict + trace)
# ---------------------------------------------------------------------------


def test_accepts_nominal_measured() -> None:
    result = run({"automaton": EVEN_A, "word": "aa"})
    assert result["accepted"] is True
    # Mesure firsthand : l'etat initial est compris dans la trace.
    assert result["trace"] == ["q_even", "q_odd", "q_even"]


def test_accepts_rejected_word() -> None:
    result = run({"automaton": EVEN_A, "word": "ab"})
    assert result["accepted"] is False
    assert result["trace"] == ["q_even", "q_odd", "q_odd"]


def test_accepts_empty_word() -> None:
    result = run({"automaton": EVEN_A, "word": ""})
    assert result["accepted"] is True  # q_even est final
    assert result["trace"] == ["q_even"]


def test_word_must_be_string() -> None:
    with pytest.raises(AutomataInputError):
        run({"automaton": EVEN_A, "word": 12})


def test_word_outside_alphabet() -> None:
    with pytest.raises(AutomataInputError):
        run({"automaton": EVEN_A, "word": "abc"})


# ---------------------------------------------------------------------------
# Coeur : operations (complement / union / intersection)
# ---------------------------------------------------------------------------


def test_complement_flips_verdict() -> None:
    spec = run({"automaton": EVEN_A, "op": "complement"})["automaton"]
    complement = build_dfa(spec)
    assert complement.accepts_input("ab") is True  # impair de 'a'
    assert complement.accepts_input("aa") is False


def test_union_nominal() -> None:
    spec = run({"automaton": EVEN_A, "op": "union", "other": ENDS_B})["automaton"]
    union = build_dfa(spec)
    assert union.accepts_input("aa") is True  # pair de 'a'
    assert union.accepts_input("ab") is True  # finit par 'b'
    assert union.accepts_input("a") is False  # aucun des deux


def test_intersection_nominal() -> None:
    spec = run({"automaton": EVEN_A, "op": "intersection", "other": ENDS_B})["automaton"]
    inter = build_dfa(spec)
    assert inter.accepts_input("aab") is True  # pair de 'a' ET finit par 'b'
    assert inter.accepts_input("aa") is False  # ne finit pas par 'b'
    assert inter.accepts_input("ab") is False  # impair de 'a'


def test_serialize_roundtrip_after_state_rename() -> None:
    # automata-lib renomme les etats en int apres une operation : la
    # serialisation doit rester relisible par build_dfa (cles str en JSON).
    spec = run({"automaton": EVEN_A, "op": "complement"})["automaton"]
    assert isinstance(spec["states"][0], str)
    again = run({"automaton": spec, "op": "complement"})["automaton"]
    back = build_dfa(again)
    assert back.accepts_input("aa") is True  # double complement = langage initial


def test_binary_op_alphabet_mismatch() -> None:
    other = {
        "states": ["p0", "p1"],
        "input_symbols": ["0", "1"],
        "transitions": {
            "p0": {"0": "p0", "1": "p1"},
            "p1": {"0": "p0", "1": "p1"},
        },
        "initial_state": "p0",
        "final_states": ["p1"],
    }
    with pytest.raises(AutomataInputError):
        run({"automaton": EVEN_A, "op": "union", "other": other})


def test_binary_op_missing_other() -> None:
    with pytest.raises(AutomataInputError):
        run({"automaton": EVEN_A, "op": "union"})


# ---------------------------------------------------------------------------
# Transport : vrai serveur TCP local (uvicorn + httpx)
# ---------------------------------------------------------------------------


def _start_local_server() -> tuple[uvicorn.Server, threading.Thread, int]:
    """Démarre le service sur un port libre (même harnais que le jumeau Texte)."""
    app = create_app()
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]
    server = uvicorn.Server(
        uvicorn.Config(app, host="127.0.0.1", port=port, log_level="critical")
    )
    thread = threading.Thread(target=server.run, daemon=True)
    thread.start()
    deadline = time.monotonic() + 5
    while not server.started and thread.is_alive() and time.monotonic() < deadline:
        time.sleep(0.01)
    assert server.started, "le serveur local n'a pas démarré"
    return server, thread, port


def _stop_local_server(server: uvicorn.Server, thread: threading.Thread) -> None:
    server.should_exit = True
    thread.join(timeout=5)
    assert not thread.is_alive(), "le serveur local ne s'est pas arrêté"


def test_loopback_http_ok_accepts() -> None:
    """Exerce le vrai transport TCP local sur le chemin nominal."""
    server, thread, port = _start_local_server()
    try:
        response = httpx.post(
            f"http://127.0.0.1:{port}/automata/run",
            json={"automaton": EVEN_A, "word": "aa"},
            timeout=2,
        )
    finally:
        _stop_local_server(server, thread)

    assert response.status_code == 200
    body = response.json()
    assert body["status"] == "ok"
    assert body["data"]["accepted"] is True
    assert body["data"]["trace"] == ["q_even", "q_odd", "q_even"]


def test_loopback_http_invalid_paths() -> None:
    """Les trois familles d'entree invalide -> 422 status invalid."""
    server, thread, port = _start_local_server()
    base = f"http://127.0.0.1:{port}/automata/run"
    try:
        missing_field = httpx.post(
            base, json={"automaton": {"states": ["q_even"]}}, timeout=2
        )
        bad_op = httpx.post(
            base, json={"automaton": EVEN_A, "op": "minify", "word": "aa"}, timeout=2
        )
        bad_word = httpx.post(
            base, json={"automaton": EVEN_A, "word": "abc"}, timeout=2
        )
        extra_field = httpx.post(
            base, json={"automaton": EVEN_A, "word": "aa", "detail": True}, timeout=2
        )
    finally:
        _stop_local_server(server, thread)

    for response in (missing_field, bad_op, bad_word, extra_field):
        assert response.status_code == 422
        assert response.json()["status"] == "invalid"
