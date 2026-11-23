"""Test du protocole porte par les artefacts ICT-25 (#21998).

Ce que ce test prouve
---------------------
  1. `protocol_block` rend les trois champs sans lesquels le regime d'un run
     n'est pas re-derivable : le budget de completion, les seeds resolus et
     le nombre de steps.
  2. Il refuse les valeurs qui rendraient l'artefact trompeur plutot que
     muet : un cap nul ou negatif, un nombre de steps nul, une liste de
     seeds vide.
  3. `ict25_arms.py` **transmet** le cap a `GRPOConfig` au lieu de le figer,
     et il l'ecrit dans les metriques de chaque seed.
  4. L'artefact agrege porte le bloc de protocole, et il ne declare plus
     `steps` / `seeds` a la main en plus du bloc (deux sources pour la meme
     valeur divergeraient au premier changement).

Le defaut corrige, mesure sur les artefacts existants : deux bras produits
sous des budgets differents (`cap 80` et `cap 1024`) sont indistinguables
depuis l'artefact, puisque le cap n'y figurait pas. Une comparaison entre ces
deux bras se lisait donc comme une comparaison a protocole egal.

Le test n'a **aucune dependance lourde** (ni torch, ni transformers) : il
tourne partout, y compris en CI sans GPU. Il est executable par pytest et
directement (`python test_ict25_protocol.py`).

Issue : #21998.
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
sys.path.insert(0, str(SCRIPTS))

from ict25_records import (  # noqa: E402
    DEFAULT_MAX_COMPLETION_LENGTH,
    protocol_block,
)

ARMS_SOURCE = (SCRIPTS / "ict25_arms.py").read_text(encoding="utf-8")


def test_protocol_block_carries_the_three_fields():
    """1. Cap, seeds et steps sortent ensemble."""
    got = protocol_block(max_completion_length=1024, seeds=(0, 1, 42), steps=120)
    assert got == {
        "max_completion_length": 1024,
        "seeds": [0, 1, 42],
        "steps": 120,
    }


def test_protocol_block_seeds_are_materialised():
    """1bis. Un iterable a usage unique ne laisse pas un generateur dans l'artefact."""
    got = protocol_block(max_completion_length=80, seeds=iter([7, 42]), steps=40)
    assert got["seeds"] == [7, 42]
    assert isinstance(got["seeds"], list)


def test_protocol_block_refuses_a_cap_that_would_hide_the_regime():
    """2. Un cap nul ou negatif rendrait la comparaison muette : il est refuse."""
    for bad in (0, -1):
        try:
            protocol_block(max_completion_length=bad, seeds=[0], steps=10)
        except ValueError:
            pass
        else:
            raise AssertionError(f"cap {bad} accepte alors qu'il n'a pas de sens")
    for bad in (None, 1024.0, True, "1024"):
        try:
            protocol_block(max_completion_length=bad, seeds=[0], steps=10)
        except TypeError:
            pass
        else:
            raise AssertionError(f"cap {bad!r} accepte alors qu'il n'est pas un entier")


def test_protocol_block_refuses_an_empty_or_invalid_seed_set():
    """2bis. Un run sans seed n'est pas re-derivable."""
    try:
        protocol_block(max_completion_length=1024, seeds=[], steps=10)
    except ValueError:
        pass
    else:
        raise AssertionError("une liste de seeds vide a ete acceptee")
    try:
        protocol_block(max_completion_length=1024, seeds=[0, "42"], steps=10)
    except TypeError:
        pass
    else:
        raise AssertionError("un seed non entier a ete accepte")


def test_arms_threads_the_cap_into_grpoconfig():
    """3. Le cap n'est plus fige : la CLI le fait descendre jusqu'a GRPOConfig."""
    assert "max_completion_length=max_completion_length," in ARMS_SOURCE, (
        "GRPOConfig ne recoit pas le cap : le run et l'artefact peuvent diverger"
    )
    assert "max_completion_length=1024," not in ARMS_SOURCE, (
        "le cap reste fige a 1024 dans le code : --max-completion-length serait mort"
    )
    assert "--max-completion-length" in ARMS_SOURCE, "la CLI n'expose pas le cap"
    assert "max_completion_length=args.max_completion_length" in ARMS_SOURCE, (
        "run_seed ne recoit pas le cap demande par la CLI"
    )
    assert '"max_completion_length": max_completion_length' in ARMS_SOURCE, (
        "les metriques du seed ne portent pas le cap effectivement utilise"
    )


def test_artifact_uses_the_protocol_block_once():
    """4. Le bloc de protocole est la source unique de steps/seeds."""
    assert "**protocol_block(" in ARMS_SOURCE, "l'artefact ne porte pas le bloc de protocole"
    assert '"steps": args.steps,' not in ARMS_SOURCE, (
        "steps est declare a la main en plus du bloc : deux sources pour la meme valeur"
    )
    assert '"seeds": seeds,' not in ARMS_SOURCE, (
        "seeds est declare a la main en plus du bloc : deux sources pour la meme valeur"
    )


def test_default_cap_is_the_documented_one():
    """Le defaut de la CLI et celui du module sont la meme constante."""
    assert DEFAULT_MAX_COMPLETION_LENGTH == 1024
    assert "default=DEFAULT_MAX_COMPLETION_LENGTH" in ARMS_SOURCE


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
