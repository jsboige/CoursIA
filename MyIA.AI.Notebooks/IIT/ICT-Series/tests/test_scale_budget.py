"""Tests du plan d'echelle GPU-free du protocole Geometry of Truth v2 (#16760 G1).

Le module teste est numpy-only : aucune carte, aucun torch. Ces tests
verrouillent le contrat que l'arbitrage ai-01 13:48Z + amendement 13:53Z
exige de G1 : batterie deterministe, quatre rungs (R1-R3 Qwen3.5 SAE-couverts
+ R4 Swift Qwen3.8 non couvert, contraste generation a taille egale),
arithmetique explicite, et la reponse a la sonde >= 70B (aucune SAE publiee
au-dessus du plafond de la collection -- un fait de registre, pas une
estimation).
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.scale_budget import (
    BATTERY,
    BATTERY_LABELS,
    LADDER,
    MAX_SAE_BACKBONE,
    NOMINAL_PARAMS_E9,
    format_plan,
    plan_rung,
    sae_lookup,
    weights_gib,
)

SWIFT_MODEL = "ukisai/Swift-1.5-Qwen3.8-27b-W4A16-AWQ"


class TestBattery:
    def test_24_enonces_12_vrai_12_faux(self):
        assert len(BATTERY) == 24
        assert sum(BATTERY_LABELS) == 12
        assert len(BATTERY_LABELS) == 24

    def test_deterministe_litteral(self):
        # Litteral pur : deux imports (ou deux executions) rendent le meme
        # objet -- precondition du budget mesure, la batterie est la seule
        # entree temps.
        assert BATTERY[0] == "The city of Paris is in France."
        assert BATTERY[-1] == "The city of Nairobi is in Morocco."
        assert BATTERY[0] in BATTERY
        assert "The city of Tokyo is in Poland." in BATTERY  # exemple du papier

    def test_format_cities_du_papier(self):
        # Format exact du dataset cities (Marks & Tegmark 2023) : la
        # batterie doit etre consommable par le protocole sans adaptation.
        for text in BATTERY:
            assert text.startswith("The city of ") and text.endswith(".")


class TestLadder:
    def test_quatre_rungs_croissants_puis_contraste(self):
        # R1-R3 : echelle croissante intra-Qwen3.5 ; R4 : meme taille nominale,
        # generation Qwen3.8 -- c'est le contraste generation, pas un palier.
        assert [e["model"] for e in LADDER[:3]] == list(NOMINAL_PARAMS_E9)
        assert LADDER[3]["model"] == SWIFT_MODEL
        nominals = [e["nominal_params_e9"] for e in LADDER]
        assert nominals == [2.0, 9.0, 27.0, 27.0]

    def test_r1_r3_sae_couvert_l0_50(self):
        # Les trois rungs d'echelle sont couverts par la collection Qwen-Scope
        # (extension verifiee sur #17842 c.5840438191) : W32K / W64K / W80K.
        by_model = {e["model"]: e for e in LADDER[:3]}
        assert by_model["Qwen/Qwen3.5-2B-Base"]["sae_repo"] == \
            "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50"
        assert by_model["Qwen/Qwen3.5-9B-Base"]["sae_repo"] == \
            "Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50"
        assert by_model["Qwen/Qwen3.5-27B"]["sae_repo"] == \
            "Qwen/SAE-Res-Qwen3.5-27B-W80K-L0_50"
        assert [by_model[m]["d_sae"] for m in by_model] == [32768, 65536, 81920]
        assert all(e["k"] == 50 for e in LADDER[:3])

    def test_r4_swift_non_couvert(self):
        # Amendement 13:53Z : R4 est un fine-tune hors collection Qwen-Scope --
        # aucune SAE publiee. Le harness doit le savoir SANS le mesurer.
        swift = LADDER[3]
        assert swift["rung"] == "R4"
        assert swift["sae_repo"] is None
        assert swift["d_sae"] is None and swift["k"] is None
        assert swift["n_layers"] is None  # lu au chargement depuis la config
        assert sae_lookup(SWIFT_MODEL) is None

    def test_generations_une_variable_puis_contraste(self):
        # R1-R3 : une seule variable d'echelle (tous Qwen3.5) ; R4 isole la
        # generation (Qwen3.8) a taille egale -- le pont distillation 1.5B
        # reste intra-Qwen2.5, hors LADDER.
        gens = [e["generation"] for e in LADDER]
        assert gens == ["Qwen3.5", "Qwen3.5", "Qwen3.5", "Qwen3.8"]


class TestArithmetique:
    def test_weights_gib_bf16(self):
        # 1e9 parametres a 16 bits = 2e9 octets = 1.863 Gio.
        assert abs(weights_gib(1_000_000_000, 16) - 2e9 / 1024**3) < 1e-9

    def test_weights_gib_nf4_quart(self):
        assert abs(weights_gib(1_000_000_000, 4.25) / weights_gib(1_000_000_000, 16) - 4.25 / 16) < 1e-9

    def test_plafond_sae_de_la_collection(self):
        # Reponse a la sonde (b) : rien de publie au-dessus du 35B-A3B.
        assert MAX_SAE_BACKBONE["model"] == "Qwen/Qwen3.5-35B-A3B-Base"
        assert MAX_SAE_BACKBONE["nominal_params_e9"] == 35.0

    def test_sonde_70b_sae_impossible(self):
        # Un echelon >= 70B n'a aucune SAE publiee : sae_lookup rend None.
        assert sae_lookup("Qwen/Qwen3.5-72B") is None
        plan = plan_rung("Qwen/Qwen3.5-72B", 24.0)
        assert plan["sae"]["available"] is False
        assert plan["sae"]["repo"] is None
        # nf4 ~ 35.6 Gio : irrealisable sur UNE carte de 24, bi-carte sur deux.
        assert plan["nf4"]["placement"] == "irrealisable sur ce parc"
        bi = plan_rung("Qwen/Qwen3.5-72B", 24.0, two_cards=True)
        assert bi["nf4"]["placement"] == "bi-carte"

    def test_plan_27b_sur_carte_24(self):
        plan = plan_rung("Qwen/Qwen3.5-27B", 24.0)
        assert plan["sae"]["available"] is True
        # nf4 ~ 13.4 Gio : carte unique ; bf16 ~ 50.3 Gio : debordement CPU
        # (c'est le mode bf16-offload du harness, metrique integre).
        assert plan["nf4"]["placement"] == "carte unique"
        assert plan["bf16"]["placement"] == "debordement CPU (device_map=auto)"
        assert plan["measured"] is False  # l'arithmetique ne se prend pas pour une mesure

    def test_plan_swift_non_couvert_carte_unique(self):
        # R4 AWQ : ~16 Go de poids annonces par ai-01 -- l'arithmetique nf4
        # (13.4 Gio pour 27e9) le confirme carte unique sur GPU 2, SAE NON.
        plan = plan_rung(SWIFT_MODEL, 24.0)
        assert plan["sae"]["available"] is False
        assert plan["nf4"]["placement"] == "carte unique"
        assert plan["nominal_params_e9"] == 27.0

    def test_plan_chemin_local_exige_nominal_explicite(self):
        # Les poids Swift sont sur le disque d'ai-01 : le chemin local n'a
        # pas de suffixe exploitable, le nominal doit venir du rung.
        plan = plan_rung("D:/models/Swift-1.5-Qwen3.8-27b", 24.0,
                         nominal_params_e9=27.0)
        assert plan["n_params_nominal"] == 27_000_000_000
        assert plan["nf4"]["weights_gib"] == 13.36

    def test_format_plan_mentionne_le_plafond_et_la_mesure(self):
        text = format_plan([plan_rung("Qwen/Qwen3.5-27B", 24.0)])
        assert "35B-A3B" in text
        assert "mesures par" in text
        assert "27B" in text


class TestSuffixe:
    def test_suffixe_nominal(self):
        # 30B-A3B -> 30.0 ; 1.7B -> 1.7 ; suffixe absent -> 0.0.
        from ict.scale_budget import _suffix_e9
        assert _suffix_e9("Qwen/Qwen3-30B-A3B-Base") == 30.0
        assert _suffix_e9("Qwen/Qwen3-1.7B-Base") == 1.7
        assert _suffix_e9("Qwen/Qwen3.5-27B") == 27.0
        assert _suffix_e9("Qwen/sans-suffixe") == 0.0

    def test_suffixe_insensible_a_la_casse(self):
        # Les checkpoints quantifies tiers melangent "27b" minuscule
        # (Swift W4A16) et "27B" majuscule (Qwen) : meme lecture.
        from ict.scale_budget import _suffix_e9
        assert _suffix_e9(SWIFT_MODEL) == 27.0
        assert _suffix_e9(SWIFT_MODEL) == _suffix_e9("Qwen/Qwen3.5-27B")
