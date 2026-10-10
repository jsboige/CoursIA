#!/usr/bin/env python3
"""Tests hermetiques du plancher zero-shot (#20244, protocole v2).

Aucun test ne charge le modele : l'inference est une dependance d'execution, pas du
depot. Ce qui est teste ici est la partie qui doit tenir sans elle -- la construction
du prompt, la rotation d'options, la lecture argmax, la compatibilite avec l'organe
d'evaluation et le taux d'accord entre bras.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import baseline_branch_detection as bbd  # noqa: E402
import zeroshot_floor as zsf  # noqa: E402

LABELS = ["Abus de langage", "Influence", "Insuffisance", "Tricherie"]


class TestPromptFerme:
    def test_le_prompt_porte_chaque_famille_verbatim_une_par_ligne(self):
        prompt = zsf.build_prompt("dialogue", sorted(LABELS))
        for label in LABELS:
            assert f". {label}" in prompt
        # Ordre transmis trie : lettres consecutives depuis A.
        assert "A. Abus de langage" in prompt
        assert "D. Tricherie" in prompt
        assert "E." not in prompt

    def test_lordre_transmis_fait_la_correspondance_lettre_etiquette(self):
        rotated = ["Tricherie", "Abus de langage", "Influence", "Insuffisance"]
        prompt = zsf.build_prompt("dialogue", rotated)
        assert "A. Tricherie" in prompt
        assert "B. Abus de langage" in prompt
        assert "D. Insuffisance" in prompt

    def test_le_prompt_porte_le_texte_integral(self):
        texte = "Tu me dis que le mariage compte ; je te dis que je compte."
        assert texte in zsf.build_prompt(texte, sorted(LABELS))


class TestRotation:
    def test_la_rotation_est_deterministe_par_graine(self):
        base = sorted(LABELS)
        assert zsf.rotate_order(base, "42:0") == zsf.rotate_order(base, "42:0")

    def test_deux_index_differents_peuvent_tourner_differemment(self):
        base = sorted(LABELS)
        orders = {tuple(zsf.rotate_order(base, f"42:{i}")) for i in range(8)}
        # Sur 4 etiquettes, 8 tirages : au moins deux ordres distincts attendus.
        # (Probabilite d'un seul ordre : 4!/4**8 ~ 6e-4 -- un echec ici serait un bug.)
        assert len(orders) > 1

    def test_la_rotation_ne_perd_ni_ne_duplique_letiquette(self):
        rotated = zsf.rotate_order(sorted(LABELS), "42:7")
        assert sorted(rotated) == sorted(LABELS)


class TestLectureArgmax:
    def test_argmax_sur_les_scores_de_lettres(self):
        scores = {"A": 1.0, "B": 3.0, "C": 2.0, "D": -1.0}
        ordered = sorted(LABELS)
        letter = max(sorted(scores), key=lambda l: scores[l])
        assert ordered[ord(letter) - ord("A")] == "Influence"
        # La mecanique du predicat : la lettre dominante designe l'etiquette de
        # l'ordre passe -- ici B = 2e etiquette triee.
        assert letter == "B"

    def test_les_jetons_lettres_multi_tokens_sont_refuses(self):
        class FakeTokenizer:
            def encode(self, text, add_special_tokens=False):
                return [1, 2]  # toute lettre se fragmente : refus attendu
        with pytest.raises(SystemExit, match="fragmentee"):
            zsf.letter_token_ids(FakeTokenizer(), sorted(LABELS))


class TestCompatibiliteOrganes:
    def test_le_predicat_mocke_passe_par_evaluate(self, tmp_path):
        rows = []
        for i, label in enumerate(LABELS):
            for j in range(4):
                rows.append({
                    "text": f"texte {label} {j} du scenario {i}",
                    "family": label,
                    "node_key": f"{label}-{j}",
                    "scenario_path": f"scenario-{i}",
                })
        corpus = tmp_path / "corpus.jsonl"
        corpus.write_text(
            "\n".join(json.dumps(r, ensure_ascii=False) for r in rows) + "\n",
            encoding="utf-8",
        )
        items = bbd.load_corpus(corpus, "branch")
        folds = bbd.grouped_folds(items, 2)

        def predict(_train, test_items, _fold):
            out = []
            for k, item in enumerate(test_items):
                out.append(item["label"] if k % 3 != 2 else "Mauvaise famille")
            return out

        result = bbd.evaluate(predict, items, folds)
        assert 0.0 < result["macro_f1_mean"] < 1.0
        assert len(result["folds"]) == 2


class TestJournalEtAccord:
    def test_le_taux_daccord_se_lit_depuis_le_journal(self, tmp_path):
        log = tmp_path / "predictions_zero_shot.jsonl"
        entries = [{"agree": True}, {"agree": True}, {"agree": False}, {"agree": True}]
        log.write_text(
            "\n".join(json.dumps(e, ensure_ascii=False) for e in entries) + "\n",
            encoding="utf-8",
        )
        assert zsf.agreement_rate(log) == pytest.approx(0.75)

    def test_journal_vide_rend_aucun_taux(self, tmp_path):
        log = tmp_path / "vide.jsonl"
        log.write_text("", encoding="utf-8")
        assert zsf.agreement_rate(log) is None


class TestDeterminisme:
    def test_la_mesure_ne_genere_pas_et_desactive_le_thinking(self):
        source = Path(zsf.__file__).read_text(encoding="utf-8")
        assert "enable_thinking=False" in source
        assert "do_sample" not in source  # aucune generation echantillonnee : passe avant seule
