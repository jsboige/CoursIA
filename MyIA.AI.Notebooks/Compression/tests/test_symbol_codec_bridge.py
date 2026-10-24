"""Fixtures : le codec natif du carnet 02 confronte au module Lean.

L'item 6 de #22377 demande deux symboles distincts de poids egal, des
permutations d'entree et une table ou les longueurs ne sont pas toutes
egales. L'item 7 demande les controles negatifs : etiquettes dupliquees,
symbole absent, code non prefixe, flux tronque.

Regle de lecture : les longueurs et les mots de code viennent **du carnet**
(`symbol_codec_bridge`), le fixture Lean est **lu dans le fichier Lean**
(`lean_demo_lengths`). Aucun parametre du codec n'est recopie dans ce fichier.
"""

from __future__ import annotations

import copy
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import symbol_codec_bridge as bridge  # noqa: E402

# Poids du carnet (cellule 14, exemple jouet) : quatre octets, longueurs 1-2-3-3.
TOY = {ord("a"): 8, ord("b"): 4, ord("c"): 2, ord("d"): 2}


@pytest.fixture(scope="module")
def toy_lengths() -> dict[int, int]:
    return bridge.canonical_lengths(TOY)


@pytest.fixture(scope="module")
def toy_code(toy_lengths: dict[int, int]) -> dict[int, str]:
    return bridge.canonical_code(toy_lengths)


def test_the_codec_functions_come_from_the_notebook(toy_lengths):
    """Les fonctions sont extraites du carnet, pas redefinies ici."""
    assert toy_lengths and set(toy_lengths) == set(TOY)
    assert bridge.huffman.__module__ != __name__


def test_two_distinct_symbols_of_equal_weight_get_distinct_words():
    """Item 6 : deux symboles distincts de poids egal restent discernables."""
    weights = {0: 5, 1: 5, 2: 5, 3: 5}
    lengths = bridge.canonical_lengths(weights)
    code = bridge.canonical_code(lengths)
    assert len(set(code.values())) == len(weights)
    assert bridge.is_injective(code)
    # Poids egaux => memes longueurs, mais les mots restent distincts et dans
    # l'ordre (longueur, symbole) — le contrat de `canonPairs`.
    assert len(set(lengths.values())) == 1
    assert bridge.symbol_order(lengths) == [0, 1, 2, 3]


def test_permuting_the_input_leaves_the_canonical_form_invariant():
    """Item 6 : la forme canonique ne depend pas de l'ordre d'entree."""
    reference = bridge.canonical_code(bridge.canonical_lengths(TOY))
    keys = list(TOY)
    for permutation in ([3, 2, 1, 0], [2, 0, 3, 1]):
        shuffled = {keys[i]: TOY[keys[i]] for i in permutation}
        lengths = bridge.canonical_lengths(shuffled)
        assert bridge.canonical_code(lengths) == reference


def test_non_constant_lengths_match_the_lean_demo(toy_lengths):
    """Item 6 : la table 1-2-3-3 est celle du module Lean, lue a la source."""
    ordered = [toy_lengths[s] for s in bridge.symbol_order(toy_lengths)]
    assert ordered == bridge.lean_demo_lengths()
    assert len(set(ordered)) > 1


def test_round_trip_over_the_lean_demo_symbols(toy_code, toy_lengths):
    """Le codec natif fait l'aller-retour exact sur la table du module Lean."""
    message = bytes(symbol for symbol in bridge.symbol_order(toy_lengths))
    bits = bridge.encoder(message, toy_code)
    L = max(toy_lengths.values())
    symbols, lengths = bridge.table_decodage(toy_code, L)
    assert bridge.decoder(bits, symbols, lengths, L) == message
    assert bridge.is_prefix_free(toy_code)


def test_absent_symbol_is_an_explicit_failure(toy_code):
    """Item 7 : un symbole absent echoue, il ne produit pas un mot par defaut."""
    absent = max(TOY) + 1
    with pytest.raises(KeyError):
        bridge.encoder(bytes([absent]), toy_code)


def test_duplicate_words_break_injectivity_but_pass_the_prefix_check(toy_code):
    """Item 7 : deux symboles sur le meme mot — et ce que le prefixe ne voit pas.

    Des mots *identiques* ne sont pas des prefixes stricts l'un de l'autre :
    un controle de prefixe seul laisse donc passer la duplication. C'est
    l'injectivite qui la detecte — deux garanties distinctes, et c'est le
    point du controle negatif.
    """
    degenerate = copy.deepcopy(toy_code)
    first, second = bridge.symbol_order({s: len(w) for s, w in toy_code.items()})[:2]
    degenerate[second] = degenerate[first]
    assert not bridge.is_injective(degenerate)
    assert bridge.is_prefix_free(degenerate)


def test_non_prefix_code_is_detected(toy_code):
    """Item 7 : un mot prefixe d'un autre est rejete par la propriete."""
    broken = {0: "0", 1: "01", 2: "10"}
    assert not bridge.is_prefix_free(broken)
    # Et le code du carnet, lui, est prefixe.
    assert bridge.is_prefix_free(toy_code)


def test_truncated_stream_does_not_return_the_original(toy_code, toy_lengths):
    """Item 7 : un flux tronque au milieu d'un mot n'est pas le message.

    Le decodage est aveugle a la coupure (aucune integrite) : il rend des
    octets qui ne sont pas ceux d'origine. C'est exactement ce que le
    controle negatif du module Lean enonce — un code prefixe n'est pas un
    mecanisme d'integrite.
    """
    message = bytes(symbol for symbol in bridge.symbol_order(toy_lengths))
    bits = bridge.encoder(message, toy_code)
    L = max(toy_lengths.values())
    symbols, lengths = bridge.table_decodage(toy_code, L)
    truncated = bits[:-1]
    assert bridge.decoder(truncated, symbols, lengths, L) != message


def test_singleton_is_one_bit_in_the_notebook():
    """La convention Python du singleton, mesuree : un bit, pas le mot vide.

    Le carnet code un alphabet a un symbole sur un bit (`{symbole: 1}`,
    `{symbole: "0"}`). Le module Lean mesure l'autre convention possible :
    la feuille-racine, mot vide, cout nul (`costL_singleton_empty_word`).
    Ce test fige la difference au lieu de la confondre.
    """
    lengths, code = bridge.huffman({5: 7})
    assert lengths == {5: 1}
    assert code == {5: "0"}
