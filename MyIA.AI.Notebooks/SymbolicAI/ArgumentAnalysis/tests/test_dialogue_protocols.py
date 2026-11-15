# -*- coding: utf-8 -*-
"""Tests de structure de dialogue_protocols.py — purs (qualification issuecomment-5770146198)."""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import dialogue_protocols as d


class TestComptes(unittest.TestCase):
    def test_registre_walton_krabbe(self):
        self.assertEqual(d.protocol_counts()["walton_krabbe_types"], 6)

    def test_neuf_actes(self):
        self.assertEqual(d.protocol_counts()["speech_acts"], 9)

    def test_deux_protocoles_implantes(self):
        self.assertEqual(d.protocol_counts()["protocols"], ["inquiry", "persuasion"])

    def test_transitions_comptees(self):
        c = d.protocol_counts()
        self.assertEqual(c["inquiry_transitions"], 25)
        self.assertEqual(c["persuasion_transitions"], 26)


class TestMachineEtats(unittest.TestCase):
    def setUp(self):
        self.S = d.SpeechAct
        self.mv = lambda sp, a: d.DialogueMove(sp, a)
        self.inq = d.InquiryProtocol()
        self.per = d.PersuasionProtocol()

    def test_inquiry_trace_valide_terminee(self):
        trace = [self.mv("A", self.S.QUESTION), self.mv("B", self.S.CLAIM),
                 self.mv("A", self.S.SUPPORT), self.mv("B", self.S.UNDERSTAND),
                 self.mv("A", self.S.UNDERSTAND)]
        r = self.inq.validate_trace(trace)
        self.assertTrue(r["valid"] and r["terminated"])

    def test_persuasion_terminee_par_concede(self):
        trace = [self.mv("A", self.S.CLAIM), self.mv("B", self.S.CHALLENGE),
                 self.mv("A", self.S.ARGUE), self.mv("B", self.S.CONCEDE)]
        r = self.per.validate_trace(trace)
        self.assertTrue(r["valid"] and r["terminated"])
        self.assertEqual(r["reason"], "_term_concede")

    def test_transition_invalide_detectee(self):
        # En inquiry, CONCEDE ne repond pas a REFUTE
        self.assertFalse(self.inq.is_valid_move(self.S.REFUTE, self.S.CONCEDE))

    def test_boucle_detectee(self):
        # La MEME paire d'actes repetee 3 fois : (QUESTION, CLAIM) x 3
        s = self.S
        trace = [self.mv("A", s.QUESTION), self.mv("B", s.CLAIM),
                 self.mv("A", s.QUESTION), self.mv("B", s.CLAIM),
                 self.mv("A", s.QUESTION), self.mv("B", s.CLAIM)]
        self.assertTrue(self.inq.is_terminal_state(trace))

    def test_boucle_periode_3_non_detectee(self):
        # Limite documentee (divergence 3) : ABC ABC n'est pas vu.
        s = self.S
        trace = [self.mv("A", s.QUESTION), self.mv("B", s.CLAIM),
                 self.mv("A", s.SUPPORT), self.mv("B", s.QUESTION),
                 self.mv("A", s.CLAIM), self.mv("B", s.ARGUE)]
        self.assertFalse(self.inq.is_terminal_state(trace))

    def test_double_retract_termine_persuasion(self):
        s = self.S
        trace = [self.mv("A", s.CHALLENGE), self.mv("B", s.RETRACT),
                 self.mv("A", s.QUESTION), self.mv("B", s.RETRACT),
                 self.mv("A", s.RETRACT)]
        self.assertTrue(self.per.is_terminal_state(trace))

    def test_double_retract_inatteignable_par_transitions(self):
        # Divergence 5 (docstring) : seul CHALLENGE mene a RETRACT, et
        # RETRACT ne mene pas a RETRACT — deux RETRACT consecutifs sont un
        # etat que la table interdit : _term_double_retract est inatteignable
        # par tout dialogue legal.
        s = self.S
        menent = [a for a in s if s.RETRACT in self.per.allowed_transitions.get(a, [])]
        self.assertEqual(menent, [s.CHALLENGE])
        self.assertNotIn(s.RETRACT, self.per.allowed_transitions[s.RETRACT])
        trace = [self.mv("A", s.CHALLENGE), self.mv("B", s.RETRACT),
                 self.mv("A", s.RETRACT)]
        r = self.per.validate_trace(trace)
        self.assertFalse(r["valid"])
        self.assertEqual(r["first_invalid"], 2)
        # la condition reste vive sur la trace interdite (code mort, pas code absent)
        self.assertTrue(self.per.is_terminal_state(trace))


class TestFixturePartagee(unittest.TestCase):
    """Garde aller-retour sur la fixture partagee (design du carnet de reference sas).

    data/dialogue_protocols_examples.json : 9 transitions + 7 terminaisons,
    exemples synthetiques domaine public. Le moteur doit rendre exactement
    les verdicts consignes.
    """

    def setUp(self):
        import json
        from pathlib import Path
        chemin = Path(__file__).resolve().parent.parent / "data" / "dialogue_protocols_examples.json"
        self.examples = json.loads(chemin.read_text(encoding="utf-8"))
        self.protos = {"inquiry": d.InquiryProtocol(), "persuasion": d.PersuasionProtocol()}

    def test_neuf_transitions(self):
        for ex in self.examples["transitions"]:
            proto = self.protos[ex["dialogue"]]
            got = proto.is_valid_move(d.SpeechAct[ex["from"]], d.SpeechAct[ex["to"]])
            self.assertEqual(got, ex["allowed"], ex)

    def test_sept_terminaisons(self):
        def historique(acts):
            return [d.DialogueMove(speaker=f"loc{i % 2}", act=d.SpeechAct[a], content="-")
                    for i, a in enumerate(acts)]
        for ex in self.examples["terminations"]:
            proto = self.protos[ex["dialogue"]]
            got = proto.is_terminal_state(historique(ex["acts"]))
            self.assertEqual(got, ex["terminal"], ex)


if __name__ == "__main__":
    unittest.main(verbosity=2)
