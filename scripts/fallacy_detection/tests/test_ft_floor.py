#!/usr/bin/env python3
"""Tests hermetiques du FT LoRA (#20359, brique 3).

Aucun test ne charge le modele, torch ou peft : l'inference et l'entrainement sont des
dependances d'execution. Ce qui est teste ici est la partie qui doit tenir sans elles --
la cible d'entrainement, le decoupage en lots, le reset par pli, la reutilisation des
organes des briques 1-2 et la consignation du protocole au rapport.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import ft_floor as ftf  # noqa: E402
import zeroshot_floor as zsf  # noqa: E402

LABELS = ["Abus de langage", "Influence", "Insuffisance", "Tricherie"]


class TestCibleEntrainement:
    def test_la_cible_est_la_lettre_de_letiquette_dans_lordre_transmis(self):
        # Ordre trie : Abus(A), Influence(B), Insuffisance(C), Tricherie(D).
        assert ftf.target_letter("Abus de langage", sorted(LABELS)) == "A"
        assert ftf.target_letter("Tricherie", sorted(LABELS)) == "D"

    def test_la_cible_et_largmax_sont_inverses_lun_de_lautre(self):
        # La prediction prend la lettre dominante puis la mappe a l'etiquette ; la
        # cible d'entrainement prend l'etiquette puis la mappe a la lettre : le
        # modele apprend exactement ce que la mesure lit (round-trip).
        ordered = sorted(LABELS)
        letter = ftf.target_letter("Influence", ordered)
        assert ordered[ord(letter) - ord("A")] == "Influence"

    def test_une_etiquette_hors_liste_echoue_nominalement(self):
        with pytest.raises(ValueError):
            ftf.target_letter("Famille inconnue", sorted(LABELS))


class TestLots:
    def test_le_decoupage_est_deterministe_par_graine(self):
        a = ftf.letter_batches(10, 3, 42)
        b = ftf.letter_batches(10, 3, 42)
        assert a == b

    def test_deux_epochs_ne_partagent_pas_la_permutation(self):
        # La permutation est derivee de (graine, epoch) : chaque epoch reçoit
        # son ordre propre, reproductible -- verifie, pas seulement documente.
        flat = lambda e: [i for b in ftf.letter_batches(20, 4, 42, epoch=e) for i in b]
        assert flat(0) != flat(1) and flat(1) != flat(2)
        assert flat(1) == [i for b in ftf.letter_batches(20, 4, 42, epoch=1) for i in b]

    def test_les_lots_couvrent_chaque_index_une_fois(self):
        flat = [i for batch in ftf.letter_batches(10, 3, 42) for i in batch]
        assert sorted(flat) == list(range(10))

    def test_aucun_lot_ne_depasse_la_taille_demandee(self):
        assert all(len(b) <= 3 for b in ftf.letter_batches(10, 3, 42))


class TestReutilisationDesOrganes:
    def test_les_organes_de_la_brique_2_sont_importes_pas_reecrits(self):
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert "from zeroshot_floor import" in source or \
            "from .zeroshot_floor import" in source
        # Aucune reecriture locale des organes reutilises.
        assert "def build_prompt" not in source
        assert "def score_item" not in source
        assert "def letter_token_ids" not in source
        assert "def agreement_rate" not in source
        assert ftf.build_prompt is zsf.build_prompt

    def test_les_organes_de_la_brique_1_sont_importes(self):
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert "grouped_folds" in source and "evaluate" in source


class TestResetParPli:
    def test_fold_scope_decharge_ladapter_en_sortie(self):
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert ".unload()" in source

    def test_le_protocole_est_fixe_sans_early_stopping(self):
        # Les epochs sont une constante de protocole, pas une borne tunee :
        # la boucle epuise EPOCHS, aucune metrique du pli test ne l'arrete.
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert "for epoch in range(EPOCHS):" in source
        assert ftf.EPOCHS == 3 and ftf.LORA_RANK == 16 and ftf.LORA_ALPHA == 32

    def test_la_loss_porte_le_token_lettre_cible(self):
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert "token_ids[target_letter(label, ordered_labels)]" in source
        assert "cross_entropy" in source


class TestConsignation:
    def test_le_rapport_consigne_la_revision_et_le_protocole(self):
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert '"model_revision": revision_resolved' in source
        assert '"model_revision_pinned": revision' in source
        assert '"lora": {' in source
        assert '"reset_per_fold"' in source
        assert '"loss_curve_per_fold"' in source

    def test_le_prompt_dentrainement_est_le_meme_organne_que_linference(self):
        # train_letter_token render via build_prompt : le modele apprend sur le
        # prompt exact que la mesure lit ensuite (pas de prompt dedie au FT).
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert "build_prompt(text, ordered_labels)" in source

    def test_labsence_de_peft_est_une_erreur_nominale(self):
        source = Path(ftf.__file__).read_text(encoding="utf-8")
        assert "Fine-tuning indisponible" in source
        assert "raise SystemExit" in source
