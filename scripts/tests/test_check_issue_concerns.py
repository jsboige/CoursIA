#!/usr/bin/env python3
"""Tests unitaires de `scripts/ci/check_issue_concerns.py` (#20183).

L'organe recense les Concerns du mainteneur restes sans reponse dans les fils
d'issues. Toute la logique de decision est pure (elle prend une liste de
`Comment` et rend un `IssueReport`) : c'est elle que ces tests exercent, hors
reseau. Seules `list_issue_numbers` et `fetch_comments` parlent a GitHub.

Les cas sont calques sur les fils de controle mesures le 2026-10-10 :

  - #19898 — deux Concerns user (08/10 10:11Z, 21:00Z), deux gestes de lane
    (`[CLAIMED]`, `[VERIFICATION]`) intercalaires, reponse ai-01 du 09/10 22:37Z.
    A l'etat du 08/10 : NON REPONDUS + `gesture-after`. A l'etat courant :
    REPONDUS.
  - #17889 — « Concern pris en compte — oui, les transcripts portent plus… »
    est un ACK de lane : il ne compte PAS comme Concern neuf, mais il REPOND
    (2410 caracteres de fond).
  - #16757 — « **Concern pris (ai-01).** » : decore de markdown, il doit etre
    reconnu comme ACK et non comme Concern.
  - #18601 — la reponse ne dit jamais « Concern » ; elle cite l'horodatage du
    Concern (« question du 15:30Z »). Exiger le mot fabriquerait un faux « sans
    reponse ».

Couvre aussi le plancher fail-closed : un acquittement nu ne repond pas, et un
fil qui ne porte que des gestes laisse le Concern NON REPONDU.

Le module est charge par chemin (`importlib`) : `scripts/ci/` n'est pas un
paquet importable, et deux organes peuvent partager un nom de module.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

_HERE = Path(__file__).resolve()
_SPEC = importlib.util.spec_from_file_location(
    "check_issue_concerns", _HERE.parent.parent / "ci" / "check_issue_concerns.py"
)
assert _SPEC and _SPEC.loader
mod = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = mod
_SPEC.loader.exec_module(mod)

Comment = mod.Comment


def c(cid: int, created_at: str, body: str, author: str = "jsboige") -> Comment:
    return Comment(id=cid, author=author, created_at=created_at, body=body)


CLAIM = "[CLAIMED] lane myia-po-2024:CoursIA-2 -- pli 1 (cartography verification, c.125)"
VERIF = "[VERIFICATION] pli 1 — verification firsthand par git grep sur main (c.125)"
CONCERN_1 = (
    "Concern: Puisque ca n'a pas ete cite, ca meriterait quand meme d'inclure "
    "l'annonce officielle qui vient avec ce depot."
)
CONCERN_2 = (
    "Concern: Il me semble qu'il y a des resultats tout a fait interessant en "
    "complexite algorithmique qui n'ont pas ete releves ici."
)
REPLY_19898 = (
    "**Reponse ai-01 a tes deux Concerns (08/10, 10:11Z et 21:00Z).** Elle "
    "arrive avec plus d'une journee de retard, et c'est un manquement."
)


class ClassifyTests(unittest.TestCase):
    def test_user_concern(self):
        self.assertEqual(mod.classify(c(1, "2026-10-08T10:11:27Z", CONCERN_1)), "concern")

    def test_lane_ack_is_not_a_concern(self):
        body = "Concern pris en compte — oui, les transcripts portent plus que la premiere vague."
        self.assertEqual(mod.classify(c(2, "2026-09-26T15:51:15Z", body)), "ack")

    def test_markdown_decorated_ack_is_not_a_concern(self):
        # #16757 : « **Concern pris (ai-01).** » — la decoration de tete est
        # neutralisee avant le match.
        self.assertEqual(mod.classify(c(3, "2026-09-18T22:21:56Z", "**Concern pris (ai-01).** Oui.")), "ack")

    def test_ack_from_a_non_user_login_is_not_a_concern(self):
        # Le compte ai-01 est distinct de jsboige : hors de la classe concern.
        got = mod.classify(c(4, "2026-09-18T22:21:56Z", "**Concern pris (ai-01).**", author="myia-ai-01"))
        self.assertNotEqual(got, "concern")

    def test_lane_gestures(self):
        self.assertEqual(mod.classify(c(5, "2026-10-08T11:56:59Z", CLAIM)), "gesture")
        self.assertEqual(mod.classify(c(6, "2026-10-08T11:57:25Z", VERIF)), "gesture")
        self.assertEqual(
            mod.classify(c(7, "2026-10-09T23:06:46Z", "[LIVRAISON] Pli 1 — lecture du depot")),
            "gesture",
        )

    def test_plain_comment_is_other(self):
        self.assertEqual(mod.classify(c(8, "2026-10-07T16:36:24Z", "Elements de mesure sur la livraison en double.")), "other")


class CitesTests(unittest.TestCase):
    def test_word_concern(self):
        self.assertTrue(mod.cites(c(1, "2026-10-08T10:11:27Z", CONCERN_1), c(9, "2026-10-09T22:37:10Z", REPLY_19898)))

    def test_timestamp_citation_without_the_word(self):
        # #18601 : la reponse cite « question du 15:30Z », jamais le mot.
        concern = c(10, "2026-10-07T15:30:59Z", "Concern: Livraison en double et 2 nits de ma part.")
        reply = c(11, "2026-10-07T16:36:24Z", "Elements de mesure sur la livraison en double (question du 15:30Z), pour que l'arbitrage soit court.")
        self.assertTrue(mod.cites(concern, reply))

    def test_quote_citation(self):
        concern = c(12, "2026-10-01T10:00:00Z", "Concern: le kernel drift sur trois notebooks de la serie GenAI Image.")
        reply = c(13, "2026-10-02T10:00:00Z", "Sur le point remonte : le kernel drift sur trois notebooks de la serie GenAI Image est corrige.")
        self.assertTrue(mod.cites(concern, reply))

    def test_unrelated_reply_does_not_cite(self):
        concern = c(14, "2026-10-01T10:00:00Z", CONCERN_2)
        reply = c(15, "2026-10-02T10:00:00Z", "J'ai pousse la branche et lance les tests.")
        self.assertFalse(mod.cites(concern, reply))

    def test_hhmm_token(self):
        # Forme non interpolante (garde #17276) : assertEqual ferait sortir la valeur.
        self.assertTrue(
            mod.hhmm_token("2026-10-07T15:30:59Z") == "15:30Z",
            "hhmm_token doit extraire HH:MM depuis l'ISO",
        )


class ResponseCandidateTests(unittest.TestCase):
    def test_bare_ack_is_not_a_response(self):
        self.assertFalse(mod.is_response_candidate("ack", c(16, "2026-10-01T10:00:00Z", "Concern pris.")))

    def test_substantive_ack_is_a_response(self):
        body = "Concern pris en compte — " + ("voici la carte de ce qui se distille. " * 8)
        self.assertTrue(mod.is_response_candidate("ack", c(17, "2026-10-01T10:00:00Z", body)))

    def test_gesture_is_not_a_response(self):
        self.assertFalse(mod.is_response_candidate("gesture", c(18, "2026-10-01T10:00:00Z", CLAIM)))

    def test_ordinary_comment_is_a_response_candidate(self):
        self.assertTrue(mod.is_response_candidate("other", c(19, "2026-10-01T10:00:00Z", "Voici l'arbitrage.")))


class AnalyseTests(unittest.TestCase):
    def test_founding_shape_19898_open_state(self):
        """Etat du 08/10 : deux Concerns, deux gestes, aucune reponse."""
        comments = [
            c(6057598699, "2026-10-08T10:11:27Z", CONCERN_1),
            c(6059329048, "2026-10-08T11:56:59Z", CLAIM),
            c(6059336062, "2026-10-08T11:57:25Z", VERIF),
            c(6068963568, "2026-10-08T21:00:39Z", CONCERN_2),
        ]
        report = mod.analyse_comments(19898, comments)
        self.assertEqual(len(report.concerns), 2)
        self.assertEqual([f.status for f in report.concerns], ["NON REPONDU", "NON REPONDU"])
        self.assertTrue(report.gesture_after)
        self.assertEqual(len(report.unresolved), 2)

    def test_founding_shape_19898_answered_state(self):
        """Etat courant : la reponse ai-01 du 09/10 22:37Z cite les deux."""
        comments = [
            c(6057598699, "2026-10-08T10:11:27Z", CONCERN_1),
            c(6059329048, "2026-10-08T11:56:59Z", CLAIM),
            c(6059336062, "2026-10-08T11:57:25Z", VERIF),
            c(6068963568, "2026-10-08T21:00:39Z", CONCERN_2),
            c(6090422607, "2026-10-09T22:37:10Z", REPLY_19898, author="myia-ai-01"),
            c(6090780198, "2026-10-09T23:06:46Z", "[LIVRAISON] Pli 1 — lecture du depot"),
        ]
        report = mod.analyse_comments(19898, comments)
        self.assertEqual([f.status for f in report.concerns], ["REPONDU", "REPONDU"])
        self.assertEqual([f.proof for f in report.concerns], [6090422607, 6090422607])
        self.assertEqual(report.unresolved, [])
        # Le geste reste visible comme drapeau aggravant.
        self.assertTrue(report.gesture_after)

    def test_fp_ack_17889_counts_one_concern_and_is_answered(self):
        comments = [
            c(5845689098, "2026-09-26T11:00:41Z", "## Mission livree : transcriptions + plan de distillation"),
            c(
                5846009215,
                "2026-09-26T11:47:30Z",
                "Concern: Merci pour ce premier jet, mais il me semble qu'il y a un peu plus a distiller des transcripts.",
            ),
            c(
                5847630219,
                "2026-09-26T15:51:15Z",
                "Concern pris en compte — oui, les transcripts portent plus que la premiere vague. "
                "Voici la carte de ce qui se distille et ou. " * 20,
            ),
        ]
        report = mod.analyse_comments(17889, comments)
        self.assertEqual(len(report.concerns), 1, "l'ACK de lane ne doit pas compter comme un Concern neuf")
        self.assertEqual(report.concerns[0].status, "REPONDU")

    def test_fp_response_18601_answered_without_the_word(self):
        comments = [
            c(6041148439, "2026-10-07T15:30:59Z", "Concern: Livraison en double et 2 nits de ma part."),
            c(
                6042352101,
                "2026-10-07T16:36:24Z",
                "Elements de mesure sur la livraison en double (question du 15:30Z), pour que l'arbitrage soit court.",
            ),
        ]
        report = mod.analyse_comments(18601, comments)
        self.assertEqual(len(report.concerns), 1)
        self.assertEqual(report.concerns[0].status, "REPONDU")

    def test_bare_ack_leaves_the_concern_open(self):
        """Fail-closed : un acquittement nu ne referme rien."""
        comments = [
            c(1, "2026-10-01T10:00:00Z", CONCERN_1),
            c(2, "2026-10-01T11:00:00Z", "Concern pris."),
        ]
        report = mod.analyse_comments(42, comments)
        self.assertEqual(report.concerns[0].status, "NON REPONDU")

    def test_unrelated_later_comment_is_manual_review(self):
        comments = [
            c(1, "2026-10-01T10:00:00Z", CONCERN_1),
            c(2, "2026-10-01T11:00:00Z", "Pousse la branche, les tests passent."),
        ]
        report = mod.analyse_comments(43, comments)
        self.assertEqual(report.concerns[0].status, "MANUAL_REVIEW")
        self.assertEqual(len(report.unresolved), 1, "fail-closed : MANUAL_REVIEW reste dans la liste")

    def test_no_concern_no_report(self):
        comments = [c(1, "2026-10-01T10:00:00Z", CLAIM), c(2, "2026-10-01T11:00:00Z", "ok")]
        self.assertEqual(mod.analyse_comments(44, comments).concerns, [])

    def test_excerpt_is_bounded(self):
        report = mod.analyse_comments(45, [c(1, "2026-10-01T10:00:00Z", CONCERN_1 * 20)])
        self.assertLessEqual(len(report.concerns[0].excerpt), 200)


class RenderTests(unittest.TestCase):
    def test_clean_thread(self):
        text = mod.render_text([], "2026-09-25", "open", 581)
        self.assertIn("Aucun", text)
        self.assertIn("581", text)

    def test_gesture_after_issue_is_listed_first(self):
        plain = mod.analyse_comments(10, [c(1, "2026-10-05T10:00:00Z", CONCERN_1)])
        flagged = mod.analyse_comments(
            11, [c(2, "2026-10-01T10:00:00Z", CONCERN_2), c(3, "2026-10-02T10:00:00Z", CLAIM)]
        )
        text = mod.render_text([plain, flagged], "2026-09-25", "open", 2)
        self.assertLess(text.index("#11"), text.index("#10"))
        self.assertIn("gesture-after", text)


if __name__ == "__main__":
    unittest.main()
