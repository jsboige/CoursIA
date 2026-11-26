# -*- coding: utf-8 -*-
"""Tests de la sonde de calibration #15294 (probe_calib_pass1).

Ces tests verrouillent les cinq ecarts de fidelite releves par la revue
[NanoClaw] sur la PR #24055 -- ils sont ecrits pour que la regle publiee
soit EXECUTABLE, pas seulement ecrite :

  1. `pass1_avec_repli` doit reproduire la LECTURE PERMISSIVE HISTORIQUE
     (queue apres le dernier 'Answer:', sinon toute la reponse). Une
     troisieme regle (dernier nombre de toute la reponse) existe et est
     publiee sous SON nom -- lui attribuer le nom du repli etait l'ecart.
  2. `marqueur_answer` (le marqueur 'Answer:' est present) et
     `nombre_apres_answer` (un nombre suit ce marqueur) sont DEUX
     marqueurs distincts : les confondre rendait le compteur trompeur.
  3. Un nombre a plusieurs groupes de milliers ('1,000,000') doit rester
     UN token : decoupe en ('1,000','000'), il se lisait 0.0.
  4. Les repetitions doivent produire plusieurs runs dans le meme artefact.
  5. La bande [20 %, 70 %] est INCLUSIVE.

Suite hermetique : aucun serveur, aucun GPU, aucun reseau.
"""

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

_MOD_PATH = Path(__file__).resolve().parents[1] / "probe_calib_pass1.py"
_spec = importlib.util.spec_from_file_location("probe_calib_pass1", _MOD_PATH)
probe = importlib.util.module_from_spec(_spec)
sys.modules["probe_calib_pass1"] = probe
_spec.loader.exec_module(probe)

GOLD = {"Answer": "12"}


def _item(gold: str = "12") -> dict:
    return {"ID": "chal-test", "Body": "Body", "Question": "Question",
            "Answer": gold}


class TestLecturesDistinctes(unittest.TestCase):
    """Reserve 1 : trois lectures nommees, trois regles distinctes."""

    def test_reponse_conforme_acceptee_par_les_lectures(self):
        sc = probe.svamp_reward(_item(), "blabla\nAnswer: 12")
        self.assertEqual(sc["ok"], 1)
        self.assertEqual(sc["ok_avec_repli"], 1)
        self.assertEqual(sc["ok_dernier_nombre"], 1)

    def test_sans_marqueur_le_repli_historique_accepte_la_reponse(self):
        # Ni la stricte ni... la stricte refuse ; le repli historique
        # (pas de marqueur -> toute la reponse) accepte.
        sc = probe.svamp_reward(_item(), "la reponse est 12")
        self.assertEqual(sc["ok"], 0)
        self.assertEqual(sc["ok_avec_repli"], 1)
        self.assertFalse(sc["marqueur_answer"])

    def test_marqueur_sans_nombre_le_repli_historique_refuse(self):
        # Le cas mesure par la revue : le marqueur est present mais aucun
        # chiffre ne suit. La regle historique donne zero ; seule la
        # troisieme regle (dernier nombre de TOUTE la reponse) accepte.
        sc = probe.svamp_reward(_item(), "je calcule 12.\nAnswer:")
        self.assertEqual(sc["ok"], 0)
        self.assertEqual(sc["ok_avec_repli"], 0)
        self.assertEqual(sc["ok_dernier_nombre"], 1)
        self.assertTrue(sc["marqueur_answer"])
        self.assertFalse(sc["nombre_apres_answer"])

    def test_nombre_avant_le_marqueur_ne_compte_pas_en_strict(self):
        sc = probe.svamp_reward(_item(), "un essai 99\nAnswer: 12")
        self.assertEqual(sc["ok"], 1)
        self.assertEqual(sc["pred"], "12.0")

    def test_deux_marqueurs_le_dernier_gagne(self):
        sc = probe.svamp_reward(_item(), "Answer: 99\npuis\nAnswer: 12")
        self.assertEqual(sc["ok"], 1)
        self.assertEqual(sc["pred"], "12.0")

    def test_le_repli_historique_egalise_la_regle_dorigine(self):
        """Le repli doit etre BIT-A-BIT la regle du probe d'origine.

        La regle historique est reimplementee ici a partir du commit
        d'origine (9dfb86cdd240) : le test echoue si le nom 'avec_repli'
        designe un jour autre chose que cette regle.
        """
        def regle_historique(reply: str) -> bool:
            tail = reply.rsplit("Answer:", 1)[-1] if "Answer:" in reply else reply
            nums = probe._NUM.findall(tail)
            if not nums:
                return False
            pred = probe._to_float(nums[-1])
            return pred is not None and abs(pred - float("12")) < 1e-4

        replies = [
            "Answer: 12",
            "la reponse est 12",
            "je calcule 12.\nAnswer:",
            "un essai 99\nAnswer: 12",
            "Answer: 99\npuis\nAnswer: 12",
            "Answer: 1,000,000",
            "aucun nombre ici",
            "",
            "Answer: -3",
            "la reponse est 12.0\nAnswer: 12",
        ]
        for reply in replies:
            with self.subTest(reply=reply):
                sc = probe.svamp_reward(_item(), reply)
                self.assertEqual(
                    bool(sc["ok_avec_repli"]), regle_historique(reply))


class TestNombres(unittest.TestCase):
    """Reserve 3 : les groupes de milliers ne doivent pas se decouper."""

    def test_plusieurs_groupes_de_milliers_restent_un_token(self):
        self.assertEqual(probe._NUM.findall("vaut 1,000,000 ici"),
                         ["1,000,000"])

    def test_un_seul_groupe_de_milliers(self):
        self.assertEqual(probe._NUM.findall("vaut 1,000 ici"), ["1,000"])

    def test_virgule_decimale_non_decoupee(self):
        self.assertEqual(probe._NUM.findall("vaut 1,5 ici"), ["1,5"])

    def test_lecture_des_groupes_de_milliers(self):
        self.assertEqual(probe._to_float("1,000,000"), 1000000.0)
        self.assertEqual(probe._to_float("1,000"), 1000.0)
        self.assertEqual(probe._to_float("1,5"), 1.5)
        self.assertEqual(probe._to_float("1.5"), 1.5)

    def test_gold_en_groupes_de_milliers_accepte(self):
        sc = probe.svamp_reward(_item("1,000,000"), "Answer: 1,000,000")
        self.assertEqual(sc["ok"], 1)
        self.assertEqual(sc["ok_avec_repli"], 1)

    def test_nombre_negatif(self):
        sc = probe.svamp_reward(_item("-3"), "Answer: -3")
        self.assertEqual(sc["ok"], 1)


class TestCompteurs(unittest.TestCase):
    """Reserve 2 : deux compteurs distincts, somme = l'ancien compteur."""

    def _run(self, replies):
        def _fake_chat(base, model, messages, max_tokens=300, timeout=180):
            reply, finish = replies.pop(0)
            return reply, finish

        with patch.object(probe, "chat", _fake_chat):
            return probe.run_svamp("http://x", "m", [_item()] * len(replies))

    def test_deux_compteurs_sont_distincts_et_completent(self):
        r = self._run([
            ("Answer: 12", "stop"),        # conforme
            ("la reponse est 12", "stop"),  # pas de marqueur, nombre juste
            ("je calcule 12.\nAnswer:", "stop"),  # marqueur sans nombre
            ("rien du tout", "stop"),       # ni marqueur ni nombre
        ])
        # pas de marqueur : 2 items (dont celui qui a un nombre)
        self.assertEqual(r["items_sans_marqueur_answer"], 2)
        # marqueur sans nombre : 1 item
        self.assertEqual(r["items_sans_nombre_apres_answer"], 1)
        # l'ancien compteur conflait les deux : 3
        self.assertEqual(r["items_sans_marqueur_answer"]
                         + r["items_sans_nombre_apres_answer"], 3)

    def test_les_lectures_sont_comptees_separement(self):
        r = self._run([
            ("Answer: 12", "stop"),
            ("la reponse est 12", "stop"),
            ("je calcule 12.\nAnswer:", "stop"),
        ])
        self.assertEqual(r["pass1"], round(1 / 3, 4))
        self.assertEqual(r["pass1_avec_repli"], round(2 / 3, 4))
        self.assertEqual(r["pass1_dernier_nombre"], 1.0)


class TestBande(unittest.TestCase):
    """Les bornes sont inclusives."""

    def test_bornes_inclusives(self):
        self.assertTrue(probe.verdict(0.70).startswith("DANS_LA_BANDE"))
        self.assertTrue(probe.verdict(0.20).startswith("DANS_LA_BANDE"))

    def test_hors_bande(self):
        self.assertTrue(probe.verdict(0.7001).startswith("SUR_LA_BANDE"))
        self.assertTrue(probe.verdict(0.1999).startswith("SOUS_LA_BANDE"))


class TestRepetitions(unittest.TestCase):
    """Reserve 4 : les repetitions doivent etre JOINTES a l'artefact."""

    def test_reps_produisent_plusieurs_runs_dans_le_meme_artefact(self):
        items = [_item()]
        with patch.object(probe, "wait_ready", lambda *a, **k: True), \
             patch.object(probe, "run_svamp", lambda *a, **k: {
                 "corpus": "svamp", "model": "m", "n": 1, "pass1": 0.5,
                 "pass1_avec_repli": 0.5, "pass1_dernier_nombre": 0.5,
                 "items_sans_marqueur_answer": 0,
                 "items_sans_nombre_apres_answer": 0,
                 "items_tronques": 0, "errors": 0, "wall_s": 0.1,
                 "items": []}), \
             patch.object(sys, "argv", ["probe", "--svamp-file",
                                        str(_corpus_file(items)),
                                        "--reps", "2", "--items", "1",
                                        "--out", str(_tmp_out())]):
            rc = probe.main()
        self.assertEqual(rc, 0)
        import json
        art = json.loads(_tmp_out().read_text(encoding="utf-8"))
        self.assertEqual(len(art["runs"]), 4)   # 2 modeles x 2 repetitions
        self.assertEqual([r["run_id"] for r in art["runs"]],
                         ["mini#1", "mini#2", "qwen#1", "qwen#2"])
        # l'artefact porte la definition des lectures : une colonne ne se
        # resume pas dans le nom de sa cle.
        self.assertIn("pass1_avec_repli", art["lectures"])
        self.assertIn("HISTORIQUE", art["lectures"]["pass1_avec_repli"])


_OUT = None


def _tmp_out():
    global _OUT
    if _OUT is None:
        import tempfile
        _OUT = Path(tempfile.mkdtemp()) / "art.json"
    return _OUT


def _corpus_file(items):
    import json
    import tempfile
    p = Path(tempfile.mkdtemp()) / "corpus.json"
    p.write_text(json.dumps(items), encoding="utf-8")
    return p


if __name__ == "__main__":
    unittest.main()
