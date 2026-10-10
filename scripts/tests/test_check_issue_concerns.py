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

    def test_ack_routes_the_same_under_every_lane_login(self):
        # #20186 : un accuse de reception de lane se juge par sa FORME, pas par le
        # compte qui le porte. Hors de jsboige il tombait dans « other », le seul
        # seau sans plancher de substance.
        for login in ("jsboige", "myia-ai-01", "myia-po-2026", "clusterManager-Myia"):
            self.assertEqual(
                mod.classify(c(20, "2026-09-18T22:21:56Z", "Concern pris en compte.", author=login)),
                "ack",
                f"l'ACK doit se router pareil sous {login}",
            )

    def test_non_lane_login_is_not_presumed_a_lane(self):
        # Le routage ne s'elargit pas a tout le monde : un compte hors flotte garde
        # le seau « other » — et c'est « proves » qui l'empeche de refermer.
        self.assertEqual(
            mod.classify(c(21, "2026-09-18T22:21:56Z", "Concern pris en compte.", author="un-contributeur")),
            "other",
        )

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

    def test_hhmm_token_yields_empty_on_a_foreign_format(self):
        # #20186 : une milliseconde, un offset ou un null ne doivent pas tuer le run
        # sur les 580 issues pour une donnee non essentielle.
        # Forme non interpolante (garde #17276, meme classe que le test ci-dessus) :
        # assertEqual ferait sortir la valeur dans les logs CI.
        for bad in ("2026-10-07T15:30:59.000Z", "2026-10-07T15:30:59+00:00", "", None):
            self.assertTrue(
                mod.hhmm_token(bad) == "",
                "hhmm_token doit rendre une chaine vide sur un format non-Z",
            )


class CiteStrengthTests(unittest.TestCase):
    """#20186 : les trois formes de citation ne se valent pas."""

    def test_timestamp_is_strong(self):
        concern = c(30, "2026-10-07T15:30:59Z", "Concern: Livraison en double et 2 nits de ma part.")
        reply = c(31, "2026-10-07T16:36:24Z", "Elements de mesure (question du 15:30Z), pour que l'arbitrage soit court.")
        self.assertEqual(mod.cite_strength(concern, reply), mod.CITE_STRONG)

    def test_quoted_text_is_strong(self):
        concern = c(32, "2026-10-01T10:00:00Z", "Concern: le kernel drift sur trois notebooks de la serie GenAI Image.")
        reply = c(33, "2026-10-02T10:00:00Z", "Sur le point remonte : le kernel drift sur trois notebooks de la serie GenAI Image est corrige.")
        self.assertEqual(mod.cite_strength(concern, reply), mod.CITE_STRONG)

    def test_the_word_alone_is_weak(self):
        concern = c(34, "2026-10-01T10:00:00Z", CONCERN_2)
        reply = c(35, "2026-10-02T10:00:00Z", "Merci, je note ce Concern pour la prochaine passe.")
        self.assertEqual(mod.cite_strength(concern, reply), mod.CITE_WEAK)

    def test_no_form_at_all_is_none(self):
        concern = c(36, "2026-10-01T10:00:00Z", CONCERN_2)
        reply = c(37, "2026-10-02T10:00:00Z", "J'ai pousse la branche et lance les tests.")
        self.assertEqual(mod.cite_strength(concern, reply), mod.CITE_NONE)

    def test_a_foreign_date_does_not_forge_a_strong_citation(self):
        # Un jeton vide ne doit pas matcher toute reponse : `"" in text` est vrai.
        concern = c(40, "pas-une-date", CONCERN_2)
        reply = c(41, "2026-10-02T10:00:00Z", "J'ai pousse la branche et lance les tests.")
        self.assertEqual(mod.cite_strength(concern, reply), mod.CITE_NONE)

    def test_cites_remains_the_weak_predicate(self):
        concern = c(38, "2026-10-01T10:00:00Z", CONCERN_2)
        reply = c(39, "2026-10-02T10:00:00Z", "Merci, je note ce Concern pour la prochaine passe.")
        self.assertTrue(mod.cites(concern, reply))


class ProvesTests(unittest.TestCase):
    """#20186 : ce qui REFERME un Concern."""

    def test_strong_citation_closes_whatever_the_kind(self):
        concern = c(50, "2026-10-07T15:30:59Z", "Concern: Livraison en double.")
        reply = c(51, "2026-10-07T16:36:24Z", "Voir la question du 15:30Z, c'est traite.")
        for kind in ("other", "ack"):
            self.assertTrue(mod.proves(concern, reply, kind))

    def test_the_word_alone_closes_only_a_substantive_ack(self):
        concern = c(52, "2026-10-01T10:00:00Z", CONCERN_2)
        reply = c(53, "2026-10-02T10:00:00Z", "Je note ce Concern pour la prochaine passe.")
        self.assertTrue(mod.proves(concern, reply, "ack"))
        self.assertFalse(mod.proves(concern, reply, "other"))

    def test_nothing_closes_on_no_citation(self):
        concern = c(54, "2026-10-01T10:00:00Z", CONCERN_2)
        reply = c(55, "2026-10-02T10:00:00Z", "J'ai pousse la branche.")
        for kind in ("other", "ack"):
            self.assertFalse(mod.proves(concern, reply, kind))


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

    def test_bare_lane_ack_under_another_login_does_not_close(self):
        """#20186 : le seau « other » n'est pas un passe-droit."""
        comments = [
            c(1, "2026-10-01T10:00:00Z", CONCERN_1),
            c(2, "2026-10-01T11:00:00Z", "Concern pris en compte (myia-ai-01).", author="myia-ai-01"),
        ]
        report = mod.analyse_comments(70, comments)
        self.assertNotEqual(report.concerns[0].status, "REPONDU")
        self.assertEqual(len(report.unresolved), 1, "fail-closed : le Concern reste liste")

    def test_word_only_long_comment_stays_manual_review(self):
        """Le mot seul ne referme pas, meme long, hors acquittement de lane."""
        comments = [
            c(1, "2026-10-01T10:00:00Z", CONCERN_1),
            c(
                2,
                "2026-10-01T11:00:00Z",
                "Point de situation : le Concern evoque la semaine derniere reste dans ma pile, "
                "je n'ai pas encore eu le temps de regarder le depot annonce. " * 3,
            ),
        ]
        report = mod.analyse_comments(71, comments)
        self.assertEqual(report.concerns[0].status, "MANUAL_REVIEW")
        self.assertEqual(len(report.unresolved), 1)

    def test_substantive_lane_ack_under_another_login_still_closes(self):
        """La doctrine de #17889 survit au changement de login."""
        comments = [
            c(1, "2026-10-01T10:00:00Z", CONCERN_1),
            c(
                2,
                "2026-10-01T11:00:00Z",
                "Concern pris en compte — voici la carte de ce qui se distille. " * 6,
                author="myia-ai-01",
            ),
        ]
        report = mod.analyse_comments(72, comments)
        self.assertEqual(report.concerns[0].status, "REPONDU")
        self.assertEqual(report.concerns[0].proof, 2)

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
