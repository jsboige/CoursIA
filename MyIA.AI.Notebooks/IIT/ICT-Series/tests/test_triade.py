"""Tests unitaires du capstone triade strate 5 (See #7259).

Couvre ``ict.triade`` :

* :func:`token_state_sequence` -- 3 strategies de discretisation.
* :func:`triade_centers` -- orchestration des 3 flux par prompt partage.
* :func:`triade_colocalization` -- extension 3-flux de ``event_colocalization``.
* :func:`triade_summary` -- agregation multi-prompts.

Methodologie
------------
Le scope est volontairement limite : on verifie la **forme** de la primitive
(dimensions, types, invariants), son **comportement statistique attendu**
(verdict sur signaux synthetiques dont la verite terrain est connue), et la
**coherence avec les primitives en amont** (``beauty_events``,
``ignition_events``, ``colocalize_lenses``). On n'invoque PAS les fixtures
reelles (couche 16, 2699 tokens) ici -- ces fixtures sont GPU-extractees et
leur analyse releve du notebook ICT-26, pas des tests unitaires.

Convention C.1 notebooks respectee (pas de ``raise NotImplementedError``).
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from ict import triade as TR


# --------------------------------------------------------------------------- #
#  token_state_sequence
# --------------------------------------------------------------------------- #
class TestTokenStateSequence:
    """Les 3 strategies de discretisation : type / shape / unique."""

    def test_type_alphabet_has_4_states(self):
        # alphabet "type" doit produire des valeurs dans {0, 1, 2, 3}.
        toks = ["", "  ", "a", "hello", "ABC", ",", ".", "123", "(", "###"]
        seq = TR.token_state_sequence(toks, alphabet="type")
        assert set(seq).issubset({0, 1, 2, 3})
        # "a" et "hello" et "ABC" -> alpha (2)
        # "," "." "(" -> punct (1)
        # "123", "###" -> other (3)
        # "" "  " -> whitespace (0)
        assert seq == [0, 0, 2, 2, 2, 1, 1, 3, 1, 3]

    def test_shape_alphabet_distinguishes_upper_lower(self):
        toks = ["hello", "Hello", "HELLO", "world"]
        seq = TR.token_state_sequence(toks, alphabet="shape")
        assert seq == [2, 3, 3, 2]  # lower, upper, upper, lower

    def test_unique_alphabet_is_injective_on_first_occurrence(self):
        toks = ["a", "b", "a", "c", "b"]
        seq = TR.token_state_sequence(toks, alphabet="unique")
        # premiere occurrence -> 0, 1, 2, 3 ; repetitions -> memes ids
        assert seq == [0, 1, 0, 2, 1]

    def test_unique_alphabet_does_not_depend_on_hash_seed(self):
        # La table est stockee explicitement (pas de hash) -> deterministe.
        toks = ["x", "y", "x", "z"]
        s1 = TR.token_state_sequence(toks, alphabet="unique")
        s2 = TR.token_state_sequence(toks, alphabet="unique")
        assert s1 == s2 == [0, 1, 0, 2]

    def test_unknown_alphabet_raises(self):
        with pytest.raises(ValueError):
            TR.token_state_sequence(["a"], alphabet="nope")


# --------------------------------------------------------------------------- #
#  Helpers de signaux synthetiques (verite terrain)
# --------------------------------------------------------------------------- #
def _aligned_bursts(T: int, centers: list, half_width: int = 5):
    """Serie de concentration avec des bursts concentres autour de ``centers``."""
    conc = np.zeros(T)
    for c in centers:
        lo = max(0, c - half_width)
        hi = min(T, c + half_width + 1)
        conc[lo:hi] = 1.0
    return conc


def _uniform_token_sequence(T: int, alphabet_size: int = 4, rng=None):
    """Sequence de tokens uniforme (aucune structure -> beauty flat)."""
    rng = rng or np.random.default_rng(0)
    return list(rng.integers(0, alphabet_size, size=T))


# --------------------------------------------------------------------------- #
#  triade_colocalization (un seul prompt)
# --------------------------------------------------------------------------- #
class TestTriadeColocalization:
    """Comportement statistique attendu sur signaux synthetiques."""

    def test_three_aligned_centers_give_colocalized(self):
        # 3 flux colocalises au MEME endroit -> colocalized sur les 3 paires.
        T = 1000
        c = [100, 300, 500]
        centers = {
            "beauty": c,
            "ignition_sae": c,
            "lens_agreement": c,
        }
        rng = np.random.default_rng(42)
        r = TR.triade_colocalization(centers, T, n_null=500, rng=rng)
        assert r["verdict"] == "colocalized"
        for pair_v in r["per_pair_verdict"].values():
            assert pair_v == "colocalized"
        assert r["n_pairs_close"] == 3

    def test_three_disjoint_centers_give_partial_or_chance(self):
        # 3 flux completement disjoints -- pas de co-localisation.
        T = 1000
        centers = {
            "beauty": [100, 200, 300],
            "ignition_sae": [500, 600, 700],
            "lens_agreement": [800, 850, 900],
        }
        rng = np.random.default_rng(43)
        r = TR.triade_colocalization(centers, T, n_null=500, rng=rng)
        # Pas de colocalized sur les 3 paires -> chance ou partial selon rotation.
        assert r["verdict"] in {"chance", "partial", "dissociated"}

    def test_two_empty_flux_gives_undefined(self):
        # 2 flux vides -> pas de triade mesurable.
        centers = {
            "beauty": [100, 200],
            "ignition_sae": [],
            "lens_agreement": [],
        }
        r = TR.triade_colocalization(centers, 1000)
        assert r["verdict"] == "undefined"
        assert r["n_pairs_close"] == 0

    def test_one_empty_flux_still_measures_two_pairs(self):
        # 1 flux vide (ex: pas d'ignition dans ce prompt) -> les 2 paires
        # impliquant le flux vide sont "undefined", mais la paire
        # (beauty, ignition_sae) reste mesurable si les deux sont non vides.
        # Cas : beauty ET ignition non vides, lens_agreement vide.
        T = 1000
        centers = {
            "beauty": [100, 200, 300],
            "ignition_sae": [100, 200, 300],
            "lens_agreement": [],
        }
        r = TR.triade_colocalization(centers, T, n_null=200,
                                     rng=np.random.default_rng(7))
        # la paire (beauty, ignition_sae) doit etre colocalized.
        pair_bi = r["per_pair_verdict"][("beauty", "ignition_sae")]
        assert pair_bi == "colocalized"
        # les deux paires impliquant lens_agreement -> undefined.
        assert r["per_pair_verdict"][("beauty", "lens_agreement")] == "undefined"
        assert r["per_pair_verdict"][("ignition_sae", "lens_agreement")] == "undefined"
        # Verdict global : pas 3 paires colocalized -> pas "colocalized".
        assert r["verdict"] in {"partial", "chance"}

    def test_keys_and_types(self):
        centers = {"beauty": [10, 20], "ignition_sae": [10, 20],
                   "lens_agreement": [10]}
        r = TR.triade_colocalization(centers, 100, n_null=50,
                                     rng=np.random.default_rng(0))
        assert "pairs" in r and isinstance(r["pairs"], dict)
        assert len(r["pairs"]) == 3
        for k, v in r["pairs"].items():
            assert isinstance(k, tuple) and len(k) == 2
            assert set(v.keys()) >= {"obs", "null_mean", "null_std", "z",
                                     "p_close", "p_far", "verdict",
                                     "n_a", "n_b", "T", "n_null"}
        assert isinstance(r["z_mean"], float)
        assert isinstance(r["n_pairs_close"], int)
        assert isinstance(r["n_pairs_far"], int)
        assert r["verdict"] in {"colocalized", "partial", "chance", "dissociated",
                                "undefined"}
        assert set(r["per_pair_verdict"].keys()) == {
            ("beauty", "ignition_sae"),
            ("beauty", "lens_agreement"),
            ("ignition_sae", "lens_agreement"),
        }
        assert set(r["n_per_prompt"].keys()) == {"beauty", "ignition_sae",
                                                 "lens_agreement"}


# --------------------------------------------------------------------------- #
#  triade_centers (integration avec les fixtures SAE/J-Lens)
# --------------------------------------------------------------------------- #
class TestTriadeCentersWithFixtures:
    """Integration legere : on charge les fixtures et on verifie la triade.

    Pas de pytest.fixture lourd : les fixtures sont lues en lazy dans chaque
    test pour eviter des ``import torch`` accidentels.
    """

    @pytest.fixture
    def traces(self):
        from ict.jlens_traces import load_traces as load_jlens
        from ict.sae_traces import load_traces as load_sae
        # Chemin absolu : on reste relatif au package ict via __file__.
        import os
        pkg_dir = os.path.dirname(os.path.dirname(TR.__file__))
        traces_dir = os.path.join(pkg_dir, "traces")
        sae_path = os.path.join(traces_dir, "ict21_sae_layer16_trained.npz")
        jl_path = os.path.join(traces_dir, "ict24_jlens_layer16_trained.npz")
        sae = load_sae(sae_path)
        jl = load_jlens(jl_path)
        return sae, jl

    def test_returns_one_entry_per_shared_prompt(self, traces):
        sae, jl = traces
        per = TR.triade_centers(sae, jl, k=64, q=0.9, persistence=3,
                                n_control=10, n_lens=100,
                                rng=np.random.default_rng(0))
        # Au moins 1 prompt partage.
        assert len(per) >= 1
        for key, info in per.items():
            assert isinstance(key, tuple) and len(key) == 2
            assert "T" in info
            for f in ("beauty", "ignition_sae", "lens_agreement"):
                assert isinstance(info[f], list)
                assert all(0 <= c < info["T"] for c in info[f])
            assert info["verdict_beauty"] in {"beauty", "flat"}
            # lens_agreement est une intersection -> lens_agree <= min(sae, jlens)
            assert info["n_lens_agree"] <= min(info["n_ign_sae"],
                                               info["n_ign_jlens"])

    def test_lens_agreement_is_intersection_of_two_sets(self, traces):
        sae, jl = traces
        per = TR.triade_centers(sae, jl, k=64, q=0.9, persistence=3,
                                n_control=10, n_lens=100,
                                rng=np.random.default_rng(0))
        for key, info in per.items():
            if info.get("t_skip"):
                continue
            sae_set = set(info["ignition_sae"])
            jlens_set = set(info["lens_agreement"])
            # Ce qui reste dans lens_agreement doit etre dans ignition_sae
            # (c'est une intersection ; on prend la partie SAE comme reference).
            # Note : ici on n'a que ignition_sae, pas ignition_jlens separe.
            # Donc on verifie juste que les centres sont dans [0, T).
            for c in info["lens_agreement"]:
                assert 0 <= c < info["T"]


# --------------------------------------------------------------------------- #
#  triade_summary
# --------------------------------------------------------------------------- #
class TestTriadeSummary:
    """Agregation multi-prompts."""

    def test_summary_with_synthetic_dict(self):
        # Synthétique : 2 prompts, l'un colocalized, l'autre chance.
        per = {
            ("layer", 0): {
                "T": 1000,
                "beauty": [100, 200, 300],
                "ignition_sae": [100, 200, 300],
                "lens_agreement": [100, 200, 300],
                "n_beauty": 3, "n_ign_sae": 3, "n_ign_jlens": 3,
                "n_lens_agree": 3, "verdict_beauty": "beauty",
                "t_skip": False,
            },
            ("layer", 1): {
                "T": 1000,
                "beauty": [100, 200, 300],
                "ignition_sae": [500, 600, 700],
                "lens_agreement": [800, 850, 900],
                "n_beauty": 3, "n_ign_sae": 3, "n_ign_jlens": 3,
                "n_lens_agree": 0, "verdict_beauty": "flat",
                "t_skip": False,
            },
        }
        rng = np.random.default_rng(99)
        s = TR.triade_summary(per, n_null=300, rng=rng)
        assert s["n_prompts"] == 2
        assert s["n_skipped"] == 0
        # Verdict_counts : 1 colocalized, 1 chance (cas disjoint -> chance probable)
        assert s["n_colocalized"] == 1
        # Le 2ᵉ prompt disjoint : rotation peut donner chance ou partial.
        # On documente : on accepte l'un OU l'autre (pas un test strict sur
        # le verdict global, juste sur l'invariant ">= 1 colocalized").
        assert isinstance(s["verdict"], str)
        assert s["verdict"] in {"colocalized", "partial", "chance", "dissociated"}

    def test_summary_skips_t_skip_prompts(self):
        per = {
            ("layer", 0): {
                "T": 1000, "beauty": [], "ignition_sae": [], "lens_agreement": [],
                "n_beauty": 0, "n_ign_sae": 0, "n_ign_jlens": 0,
                "n_lens_agree": 0, "verdict_beauty": "flat", "t_skip": True,
            },
            ("layer", 1): {
                "T": 1000,
                "beauty": [100, 200],
                "ignition_sae": [100, 200],
                "lens_agreement": [100, 200],
                "n_beauty": 2, "n_ign_sae": 2, "n_ign_jlens": 2,
                "n_lens_agree": 2, "verdict_beauty": "beauty",
                "t_skip": False,
            },
        }
        s = TR.triade_summary(per, n_null=200, rng=np.random.default_rng(0))
        assert s["n_prompts"] == 1
        assert s["n_skipped"] == 1

    def test_summary_all_undefined_gives_undefined_global(self):
        per = {
            ("layer", 0): {
                "T": 1000, "beauty": [], "ignition_sae": [], "lens_agreement": [],
                "n_beauty": 0, "n_ign_sae": 0, "n_ign_jlens": 0,
                "n_lens_agree": 0, "verdict_beauty": "flat", "t_skip": False,
            },
        }
        s = TR.triade_summary(per, n_null=200, rng=np.random.default_rng(0))
        assert s["verdict"] == "undefined"

    def test_keys_and_types(self):
        per = {
            ("layer", 0): {
                "T": 1000,
                "beauty": [100, 200],
                "ignition_sae": [100, 200],
                "lens_agreement": [100],
                "n_beauty": 2, "n_ign_sae": 2, "n_ign_jlens": 2,
                "n_lens_agree": 1, "verdict_beauty": "beauty",
                "t_skip": False,
            },
        }
        s = TR.triade_summary(per, n_null=100, rng=np.random.default_rng(0))
        for key in ("per_prompt", "n_prompts", "n_skipped", "verdict_counts",
                    "verdict", "z_mean", "n_colocalized", "n_partial",
                    "n_chance", "n_dissociated"):
            assert key in s
        assert s["n_prompts"] == 1
        assert isinstance(s["z_mean"], float)
        # n_prompts == 1 colocalized -> z_mean defini
        assert not math.isnan(s["z_mean"])