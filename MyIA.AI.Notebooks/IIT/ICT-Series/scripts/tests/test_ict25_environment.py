"""Test du bloc d'environnement fige porte par les artefacts ICT-25 (#5105).

Ce que ce test prouve
---------------------
  1. `environment_block` rend les six sections attendues : horodatage,
     version de Python, versions des paquets, etat CUDA, etat git,
     empreintes du pilote.
  2. Le pilote est reellement empreinte : les SHA-256 correspondent au
     contenu des fichiers sur disque.
  3. Le bloc est stable : deux appels rendent le meme environnement.
  4. `protocol_block` garde son contrat a trois champs : le bloc
     d'environnement est un **frere** du protocole, pas un de ses champs.

Le test n'a **aucune dependance lourde** (ni torch, ni transformers) :
il tourne partout, y compris en CI sans GPU.

Issue : #5105.
"""
import hashlib
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
sys.path.insert(0, str(SCRIPTS))

from ict25_records import (  # noqa: E402
    ENV_PACKAGES,
    ENV_PILOT_FILES,
    environment_block,
    protocol_block,
)


def test_environment_block_carries_the_six_sections():
    env = environment_block()
    assert set(env) == {"captured_at_utc", "python", "packages", "cuda",
                        "git", "pilot"}
    assert env["python"]
    assert env["captured_at_utc"].endswith("Z")
    assert set(env["packages"]) == set(ENV_PACKAGES)
    for name in ("torch", "transformers", "peft", "bitsandbytes"):
        assert name in ENV_PACKAGES
        assert isinstance(env["packages"][name], str)


def test_environment_block_fingerprints_the_pilot():
    env = environment_block()
    assert set(env["pilot"]) == set(ENV_PILOT_FILES)
    for name, fp in env["pilot"].items():
        assert fp.startswith("sha256:"), name
        assert len(fp) == len("sha256:") + 64, name
        attendu = "sha256:" + hashlib.sha256(
            (SCRIPTS / name).read_bytes()).hexdigest()
        assert fp == attendu, name


def test_environment_block_is_stable():
    a = environment_block()
    b = environment_block()
    assert a["packages"] == b["packages"]
    assert a["pilot"] == b["pilot"]
    assert a["git"]["sha"] == b["git"]["sha"]


def test_environment_block_survives_an_unreadable_probe():
    """Un pilote absent ne leve pas : il est note `absent`."""
    env = environment_block(pilot_files=("fichier_absent_ict25.py",))
    assert env["pilot"]["fichier_absent_ict25.py"] == "absent"


def test_protocol_block_keeps_its_three_fields():
    proto = protocol_block(max_completion_length=1024, seeds=(0, 1, 42), steps=120)
    assert set(proto) == {"max_completion_length", "seeds", "steps"}


def test_the_runner_writes_the_env_block_next_to_the_protocol():
    source = (SCRIPTS / "ict25a_scaleup_grpo.py").read_text(encoding="utf-8")
    assert "environment_block()" in source
    assert '"env": env' in source
    assert '"protocol": protocol_block' in source


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"OK   : {name}")
            except AssertionError as exc:
                failures += 1
                print(f"ECHEC: {name} -> {exc}")
    print()
    if failures:
        print(f"{failures} TEST(S) EN ECHEC")
        raise SystemExit(1)
    print("TOUS LES TESTS PASSENT")
