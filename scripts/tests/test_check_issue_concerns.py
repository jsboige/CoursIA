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

Classe ``user-remark`` (#20185, classe 2) : sous le login partage, l'auteur ne
separe pas un post de lane d'une remarque du mainteneur — c'est la FORME du corps
qui tranche (six signatures mesurees, ``lane_signature``). Une reponse non signee
sans reponse reste ouverte ; un post de lane signe n'est jamais un candidat ; une
citation forte (horodatage) referme ; le mot « Concern » ne referme pas une
remarque ; un geste de lane apres la remarque leve ``gesture-after``.

Le module est charge par chemin (`importlib`) : `scripts/ci/` n'est pas un
paquet importable, et deux organes peuvent partager un nom de module.
"""

from __future__ import annotations

import importlib.util
import json
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
#: #2159 — le Concern du 2026-10-18T22:26Z et la reponse de lane du
#: 2026-10-19T03:56Z qui le cite (faux NON REPONDU mesure avant le correctif).
CONCERN_2159 = (
    "Concern: Alors qu'on continue empiler des modules dans le cadre de cet "
    "Epic, est-ce qu'il ne serait pas temps de faire une pause pour voir ou "
    "en est la toute derniere version de Mathlib sur le sujet ?"
)
REPLY_2159 = (
    "[INFO] Reponse au Concern du 2026-10-18T22:26Z — releve mesure "
    "Mathlib-vs-lac + projets externes — Grain: DEEP/research-code — lane "
    "myia-po-2025:CoursIA\n\nAucun fichier edite, aucun module ajoute."
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

    def test_gesture_without_the_concern_is_never_a_candidate(self):
        """Le comportement historique est conserve quand le Concern n'est pas fourni."""
        self.assertFalse(
            mod.is_response_candidate("gesture", c(18, "2026-10-01T10:00:00Z", CLAIM))
        )

    def test_gesture_that_cites_the_concern_strongly_is_a_response(self):
        """#2159 : un geste de lane qui cite l'horodatage du Concern y repond."""
        concern = c(30, "2026-10-18T22:26:03Z", CONCERN_2159)
        reply = c(31, "2026-10-19T03:56:43Z", REPLY_2159)
        self.assertEqual(mod.classify(reply), "gesture")
        self.assertTrue(mod.cites_concern(concern, reply))
        self.assertTrue(mod.is_response_candidate("gesture", reply, concern))

    def test_lane_signature_contract_requires_utc_minute(self):
        """Le format observé des lanes inclut heure et minute UTC (#2159)."""
        concern = c(30, "2026-10-18T22:26:03Z", CONCERN_2159)
        dated_reply = c(
            31,
            "2026-10-19T03:56:43Z",
            "[INFO] Reponse au Concern du 2026-10-18T22:26Z — releve mesure.",
        )
        date_only_reply = c(
            32,
            "2026-10-19T03:56:43Z",
            "[INFO] Reponse au Concern du 2026-10-18 — releve mesure.",
        )

        self.assertTrue(mod.cites_concern(concern, dated_reply))
        self.assertFalse(mod.cites_concern(concern, date_only_reply))

    def test_gesture_that_does_not_cite_the_concern_stays_excluded(self):
        concern = c(32, "2026-10-18T22:26:03Z", CONCERN_2159)
        reply = c(33, "2026-10-19T03:56:43Z", "[INFO] Releve mesure — aucun fichier edite.")
        self.assertEqual(mod.classify(reply), "gesture")
        self.assertFalse(mod.cites_concern(concern, reply))
        self.assertFalse(mod.is_response_candidate("gesture", reply, concern))

    def test_incidental_short_window_is_not_a_citation(self):
        """Une fenetre courte partagee par coincidence ne referme rien.

        Mesure sur 624 issues : la fenetre de 40 caracteres attrapait des
        fragments sans lien (« 46`, `37642385421`, `37642397358` » — une suite
        de numeros de PR). Le geste n'est candidat que par horodatage ou par
        extrait long.
        """
        concern = c(
            34,
            "2026-10-20T16:08:51Z",
            "Diagnostic — la derive portee par une classe « scheduled-orphan », "
            "mesuree sur 4 snapshots. Les ids 37642385421 et 37642397358 "
            "portent la derive.",
        )
        reply = c(
            35,
            "2026-10-22T16:57:47Z",
            "[INFO] candidate-delivered — deja livre par PR #21634. "
            "Voir 46`, `37642385421`, `37642397358`, `3764.",
        )
        self.assertFalse(mod.cites_concern(concern, reply))
        self.assertFalse(mod.is_response_candidate("gesture", reply, concern))

    def test_long_quote_is_a_citation(self):
        """Un extrait long du texte du Concern reste une citation."""
        body = (
            "Diagnostic — la derive portee par une classe « scheduled-orphan », "
            "mesuree sur 4 snapshots. Les ids 37642385421 et 37642397358 "
            "portent la derive."
        )
        concern = c(36, "2026-10-20T16:08:51Z", body)
        reply = c(
            37,
            "2026-10-22T16:57:47Z",
            "[INFO] Reponse au diagnostic : « " + body + " » — traite par PR #21634.",
        )
        self.assertTrue(mod.cites_concern(concern, reply))
        self.assertTrue(mod.is_response_candidate("gesture", reply, concern))

    def test_long_quote_keeps_gesture_candidate_without_minute_signature(self):
        """#24672 : l'extrait fort garde la voie ouverte sans HH:MMZ."""
        body = (
            "Le diagnostic mesure une derive persistante dans les quatre snapshots "
            "et montre que les identifiants de suivi ne suffisent pas a expliquer "
            "le changement observe dans les resultats."
        )
        concern = c(38, "2026-10-18T22:26:03Z", body)
        signature = "[INFO] Reponse au Concern du 2026-10-18 — "

        # L'absence de minutes ne neutralise pas une citation assez longue.
        quoted_80 = c(39, "2026-10-19T03:56:43Z", signature + body[20:100])
        self.assertNotIn("22:26Z", quoted_80.body)
        self.assertTrue(mod.cites_concern(concern, quoted_80))
        self.assertTrue(mod.is_response_candidate("gesture", quoted_80, concern))

        # La date seule n'est pas une citation forte, et 40–79 caractères
        # restent sous le seuil mesuré.
        for length in (40, 79):
            with self.subTest(length=length):
                short_quote = c(
                    40 + length,
                    "2026-10-19T03:56:43Z",
                    signature + body[:length],
                )
                self.assertFalse(mod.cites_concern(concern, short_quote))
                self.assertFalse(
                    mod.is_response_candidate("gesture", short_quote, concern)
                )

    def test_quote_strength_keeps_the_80_character_boundary(self):
        concern = c(38, "2026-10-01T10:00:00Z", "x" * 80)
        short_quote = c(39, "2026-10-02T10:00:00Z", "[INFO] " + "x" * 79)
        boundary_quote = c(40, "2026-10-02T10:00:00Z", "[INFO] " + "x" * 80)

        self.assertFalse(mod.cites_concern(concern, short_quote))
        self.assertTrue(mod.cites_concern(concern, boundary_quote))

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

    def test_the_2159_shape_is_answered(self):
        """#2159 : le geste de lane qui cite le Concern le referme."""
        comments = [
            c(6255920966, "2026-10-18T22:26:03Z", CONCERN_2159),
            c(6259310809, "2026-10-19T03:56:43Z", REPLY_2159),
        ]
        report = mod.analyse_comments(2159, comments)
        self.assertEqual(len(report.concerns), 1)
        self.assertEqual(report.concerns[0].status, "REPONDU")
        self.assertEqual(report.concerns[0].proof, 6259310809)
        # Le geste qui referme n'aggrave pas : le drapeau vise les gestes
        # poses apres le Concern et qui n'y repondent pas.
        self.assertFalse(report.concerns[0].gesture_after)
        self.assertFalse(report.gesture_after)

    def test_the_2159_shape_control_without_citation(self):
        """Controle : sans citation, le meme geste ne referme rien."""
        comments = [
            c(6255920966, "2026-10-18T22:26:03Z", CONCERN_2159),
            c(
                6259310809,
                "2026-10-19T03:56:43Z",
                "[INFO] Releve mesure — aucun fichier edite.",
            ),
        ]
        report = mod.analyse_comments(2159, comments)
        self.assertEqual(report.concerns[0].status, "NON REPONDU")
        self.assertTrue(report.concerns[0].gesture_after)

    def test_unrelated_later_comment_is_manual_review(self):
        comments = [
            c(1, "2026-10-01T10:00:00Z", CONCERN_1),
            c(2, "2026-10-01T11:00:00Z", "Pousse la branche, les tests passent."),
        ]
        # Classe 1 seule : le second commentaire est lui-meme un candidat de la
        # classe 2 (post non signe du compte partage) — hors scope de ce test.
        report = mod.analyse_comments(43, comments, classes=("user-concern",))
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
        report = mod.analyse_comments(71, comments, classes=("user-concern",))
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


class LaneSignatureTests(unittest.TestCase):
    """Classe 2 : les signatures mesurees qui ecartent un post de lane."""

    def test_hors_flotte_closure_preflight_needs_manual_review(self):
        body = (
            "Hors flotte — clôture sur preuve, périmètre P1 de #25670.\n\n"
            "[CLOSURE PREFLIGHT]\nschema: 1\nlane: astra:CoursIA\n"
            "issue: 23793\nverdict: CLOSE\n"
        )
        report = mod.analyse_comments(
            23793, [c(1, "2026-11-10T19:15:33Z", body)],
            classes=("user-remark",),
        )
        self.assertEqual(len(report.remarks), 1)
        self.assertEqual(report.remarks[0].status, "MANUAL_REVIEW")

    def test_human_copying_header_keeps_the_remark(self):
        body = (
            "Hors flotte — clôture sur preuve.\n\n"
            "[CLOSURE PREFLIGHT]\nschema: 1\nlane: astra:CoursIA\n"
            "Je cite le dossier : il faut rouvrir car le test échoue."
        )
        report = mod.analyse_comments(
            1, [c(1, "2026-11-10T19:15:33Z", body)],
            classes=("user-remark",),
        )
        self.assertEqual(len(report.remarks), 1)
        self.assertEqual(report.remarks[0].status, "MANUAL_REVIEW")

    def test_closure_preflight_mention_is_not_a_lane_signature(self):
        text = "Pourquoi ce dossier [CLOSURE PREFLIGHT] est-il clos ?"
        self.assertEqual(mod.lane_signature(text), "")
        report = mod.analyse_comments(
            1, [c(1, "2026-11-10T19:15:33Z", text)],
            classes=("user-remark",),
        )
        self.assertEqual(len(report.remarks), 1)
        self.assertEqual(report.remarks[0].status, "NON REPONDU")

    def test_lane_near_seat(self):
        self.assertEqual(
            mod.lane_signature("[CLAIMED] lane myia-po-2024:CoursIA-2 — reprise du pli"),
            "lane-near-seat",
        )

    def test_seat_token_even_backticked(self):
        # Un jeton de siege encage reste une signature : c'est la lane qui
        # l'ecrit, l'encagement ne change pas l'auteur.
        self.assertEqual(
            mod.lane_signature("Rapport de `myia-po-2024:CoursIA-2`, pousse ce matin."),
            "seat-token",
        )

    def test_grain_tag(self):
        self.assertEqual(
            mod.lane_signature("Grain: LIGHT/guard — passe de garde"), "grain-tag"
        )

    def test_cycle_watermark(self):
        self.assertEqual(
            mod.lane_signature("Point de situation (c.278)."), "cycle-watermark"
        )

    def test_cycle_watermark_bounded_does_not_eat_a_comment_id(self):
        # #21621 : un id de commentaire n'est pas un numero de cycle. Le motif
        # borne a quatre chiffres prend c.2199 (controle positif) et laisse
        # c.6280946388 a la classe user-remark (controle negatif) — sinon une
        # remarque du mainteneur qui cite un id est ecartee en silence.
        self.assertEqual(
            mod.lane_signature("Point de situation (c.2199)."), "cycle-watermark"
        )
        self.assertEqual(
            mod.lane_signature("Voir la remarque c.6280946388 sur ce point."), ""
        )

    def test_head_tag_after_decoration(self):
        self.assertEqual(
            mod.lane_signature("**[LIVRAISON] Pli 1 — lecture du depot**"), "head-tag"
        )

    def test_maintainer_voice_is_unsigned(self):
        self.assertEqual(
            mod.lane_signature(
                "Reponse ecrite qui tranche : option 1 — garder l'indice tel quel. "
                "La valeur 8 n'est pas un spoiler : c'est un parametre de l'experience."
            ),
            "",
        )


class RemarkActTests(unittest.TestCase):
    """L'intention declaree est enregistree, pas filtrante."""

    def test_question(self):
        self.assertEqual(mod.remark_act("Est-ce qu'on garde l'indice ?"), mod.ACT_QUESTION)

    def test_directive(self):
        self.assertEqual(
            mod.remark_act("Decision : on reste sur l'option 1."), mod.ACT_DIRECTIVE
        )

    def test_statement(self):
        self.assertEqual(
            mod.remark_act("Le rendu est propre sur cette serie."), mod.ACT_STATEMENT
        )


class RemarkAnalysisTests(unittest.TestCase):
    """Classe 2 : la machinerie de reponse s'applique telle quelle aux remarques."""

    REMARK = (
        "Reponse ecrite qui tranche : option 1 — garder l'indice tel quel. "
        "La valeur 8 n'est pas un spoiler : c'est un parametre de l'experience."
    )

    def test_maintainer_remark_without_answer_is_open(self):
        report = mod.analyse_comments(
            21092,
            [c(6233713025, "2026-10-17T12:09:20Z", self.REMARK)],
            classes=("user-remark",),
        )
        self.assertEqual(len(report.remarks), 1)
        finding = report.remarks[0]
        self.assertEqual(finding.status, "NON REPONDU")
        self.assertEqual(finding.act, mod.ACT_DIRECTIVE)
        self.assertEqual(finding.slug, "user-remark")

    def test_lane_signed_comment_is_never_a_remark(self):
        # Aucun de ces corps n'est un geste (le seau les garderait sinon hors
        # classe par le genre) : c'est bien ``lane_signature`` qui les ecarte.
        for body in (
            "Point de situation (c.278), cote myia-po-2024:CoursIA-2 : le pli avance.",
            "Point de situation (c.278) : rien de neuf sur cette serie.",
            "Grain: LIGHT/guard -- passe de garde sur les liens.",
        ):
            report = mod.analyse_comments(
                7, [c(2, "2026-10-18T01:25:00Z", body)], classes=("user-remark",)
            )
            self.assertEqual(report.remarks, [], f"corps signe retenu : {body[:60]}")

    def test_head_tag_is_routed_to_manual_review_not_excluded(self):
        # #21621 : « [NanoClaw] a raison… » est une vraie remarque du
        # mainteneur ; le tag entre crochets, sans autre signature de lane, est
        # ambigu — il est route vers MANUAL_REVIEW au lieu d'etre ecarte.
        report = mod.analyse_comments(
            11,
            [c(20, "2026-10-18T09:00:00Z", "[NanoClaw] a raison de pousser ce point.")],
            classes=("user-remark",),
        )
        self.assertEqual(len(report.remarks), 1)
        self.assertEqual(report.remarks[0].status, "MANUAL_REVIEW")
        self.assertEqual(report.excluded, {})

    def test_excluded_comments_are_counted_by_signature(self):
        # #21621 : l'ecart cesse d'etre silencieux — il est compte et publie,
        # en texte comme en JSON, pour que le total ne passe pas pour exhaustif.
        report = mod.analyse_comments(
            12,
            [
                c(30, "2026-10-18T09:00:00Z", "Point de situation (c.278)."),
                c(31, "2026-10-18T10:00:00Z", self.REMARK),
            ],
            classes=("user-remark",),
        )
        self.assertEqual(report.excluded, {"cycle-watermark": 1})
        self.assertEqual(len(report.remarks), 1)
        self.assertEqual(
            report.as_dict()["excluded_by_signature"], {"cycle-watermark": 1}
        )

    def test_remark_closed_by_a_strong_citation(self):
        report = mod.analyse_comments(
            8,
            [
                c(10, "2026-10-17T12:09:20Z", self.REMARK),
                c(
                    11,
                    "2026-10-17T13:00:00Z",
                    "Sur ta reponse du 12:09Z : option 1 retenue, je la mets en oeuvre.",
                ),
            ],
            classes=("user-remark",),
        )
        self.assertEqual(report.remarks[0].status, "REPONDU")
        self.assertEqual(report.remarks[0].proof, 11)

    def test_remark_with_unrelated_later_comment_is_manual_review(self):
        report = mod.analyse_comments(
            9,
            [
                c(10, "2026-10-17T12:09:20Z", self.REMARK),
                c(11, "2026-10-17T13:00:00Z", "J'ai pousse la branche, les tests passent."),
            ],
            classes=("user-remark",),
        )
        statuses = [r.status for r in report.remarks]
        # Le second commentaire est lui-meme un candidat (meme forme, compte
        # partage) : le plancher sur-signale au lieu de filtrer — assume (#20185).
        self.assertEqual(statuses, ["MANUAL_REVIEW", "NON REPONDU"])

    def test_the_word_concern_does_not_close_a_remark(self):
        report = mod.analyse_comments(
            10,
            [
                c(10, "2026-10-17T12:09:20Z", self.REMARK),
                c(11, "2026-10-17T13:00:00Z", "Ce Concern est note pour la prochaine passe."),
            ],
            classes=("user-remark",),
        )
        self.assertNotEqual(report.remarks[0].status, "REPONDU")

    def test_a_foreign_login_is_not_a_maintainer_remark(self):
        report = mod.analyse_comments(
            5,
            [c(1, "2026-10-17T12:09:20Z", self.REMARK, author="un-contributeur")],
            classes=("user-remark",),
        )
        self.assertEqual(report.remarks, [])

    def test_lane_gesture_after_a_remark_is_the_aggravating_flag(self):
        report = mod.analyse_comments(
            6,
            [
                c(1, "2026-10-17T12:09:20Z", self.REMARK),
                c(2, "2026-10-18T01:25:00Z", CLAIM),
            ],
            classes=("user-remark",),
        )
        self.assertEqual(report.remarks[0].status, "NON REPONDU")
        self.assertTrue(report.remarks[0].gesture_after)
        self.assertTrue(report.gesture_after)

    def test_class_scoping_keeps_the_classes_independent(self):
        comments = [
            c(1, "2026-10-01T10:00:00Z", CONCERN_1),
            c(2, "2026-10-01T11:00:00Z", "Le rendu est propre."),
        ]
        only_concerns = mod.analyse_comments(3, comments, classes=("user-concern",))
        only_remarks = mod.analyse_comments(3, comments, classes=("user-remark",))
        self.assertEqual(len(only_concerns.concerns), 1)
        self.assertEqual(only_concerns.remarks, [])
        self.assertEqual(only_remarks.concerns, [])
        self.assertEqual(len(only_remarks.remarks), 1)
        self.assertEqual(only_remarks.remarks[0].status, "NON REPONDU")


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

    def test_remark_renders_with_its_act(self):
        report = mod.analyse_comments(
            12,
            [c(1, "2026-10-17T12:09:20Z", "Decision : on garde l'option 1.")],
            classes=("user-remark",),
        )
        text = mod.render_text([report], "2026-09-25", "open", 1)
        self.assertIn("[directive]", text)
        self.assertIn("remarque(s)", text)

    def test_exclusions_are_published_in_the_text_output(self):
        # #21621 : le nombre d'ecartes par signature figure dans la sortie.
        report = mod.analyse_comments(
            13,
            [
                c(40, "2026-10-18T09:00:00Z", "Point de situation (c.278)."),
                c(41, "2026-10-18T10:00:00Z", "Le rendu est propre."),
            ],
            classes=("user-remark",),
        )
        text = mod.render_text([report], "2026-09-25", "open", 1)
        self.assertIn("1 commentaire(s) ecarte(s) par signature de lane", text)
        self.assertIn("cycle-watermark 1", text)


class Utf8OutputTests(unittest.TestCase):
    def test_emoji_excerpt_survives_a_cp1252_stdout(self):
        # Mesure 2026-10-30 : un emoji dans un extrait de commentaire crashait
        # le print sur un stdout redirige en page de codes ANSI (cp1252,
        # UnicodeEncodeError apres lecture de 686 issues) -- exactement le
        # canal de la ligne [CONCERNS] de la restitution coordinateur (#20183).
        import io as _io

        emoji_concern = "Concern: le rendu casse \U0001f680 partout"
        original = sys.stdout
        original_fetch = mod.fetch_comments
        raw = _io.BytesIO()
        sys.stdout = _io.TextIOWrapper(raw, encoding="cp1252")
        try:
            mod.fetch_comments = lambda number: [
                c(60, "2026-10-19T09:00:00Z", emoji_concern)
            ]
            rc = mod.main(["--issues", "15"])
            sys.stdout.flush()
            payload = raw.getvalue()
        finally:
            sys.stdout = original
            mod.fetch_comments = original_fetch
        self.assertEqual(rc, 0)
        out = payload.decode("utf-8")
        self.assertIn("non resolu", out)
        self.assertIn("\U0001f680", out)


RESERVE_HERMES = (
    "[Hermes] COMMENT_WITH_CONCERNS : le claim « multi-seed » n'est tenu que "
    "sur 2 graines — le body annonce 4 graines distinctes."
)
LIFT_WITH_TIMESTAMP = (
    "[OVERRIDE] lane myia-ai-01 : je leve la reserve d'Hermes du 14:05Z — "
    "les 4 graines sont livrees au commit 83ac846."
)


class ReserveMarkerTests(unittest.TestCase):
    """Classe reviewer-reserve : position d'emission, grammaire restreinte."""

    def test_verdict_prefix_posed_is_detected(self):
        self.assertEqual(
            mod.reserve_marker(RESERVE_HERMES), "COMMENT_WITH_CONCERNS"
        )

    def test_severity_glyph_posed_is_detected(self):
        self.assertEqual(mod.reserve_marker("🟡 le gap 2 n'est pas couvert"), "🟡")

    def test_decoration_before_marker_still_poses(self):
        # Le gras de tete est neutralise, comme ``classify`` : l'emission
        # degradee reste une emission.
        self.assertIsNotNone(mod.reserve_marker("**CHANGES_REQUESTED** — scope"))

    def test_marker_cited_mid_body_is_not_posed(self):
        # #13030 : la mention du verdict (une reponse qui le reprend) n'est
        # pas une reserve neuve.
        body = "Reponse : ta reserve COMMENT_WITH_CONCERNS est traitee au commit."
        self.assertIsNone(mod.reserve_marker(body))

    def test_bare_concerns_word_is_not_a_reserve(self):
        # Vocabulaire de la campagne elle-meme (« la liste [CONCERNS] postee
        # par le coordinateur ») : la sous-chaine nue est exclue du cote issues.
        self.assertIsNone(
            mod.reserve_marker("La liste [CONCERNS] postee par le coordinateur.")
        )

    def test_prose_marker_is_not_a_reserve_on_issues(self):
        # « avant merge » etc. sont des marqueurs PR-contextuels (B.0) ; sur
        # les issues, la prose de lane en est saturee — exclus de cette classe.
        self.assertIsNone(
            mod.reserve_marker("Il reste un point a regler avant merge.")
        )


class ReserveAnalysisTests(unittest.TestCase):
    """Classe reviewer-reserve : statut tri-eti et drapeau gesture-after."""

    def test_reserve_without_answer_is_open(self):
        report = mod.analyse_comments(
            9,
            [c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES)],
            classes=("reviewer-reserve",),
        )
        self.assertEqual(len(report.reserves), 1)
        finding = report.reserves[0]
        self.assertEqual(finding.status, "NON REPONDU")
        self.assertEqual(finding.marker, "COMMENT_WITH_CONCERNS")
        self.assertEqual(finding.slug, "reviewer-reserve")
        self.assertFalse(finding.gesture_after)

    def test_reserve_detectable_regardless_of_author(self):
        # La classe cible la reserve POSEE, pas un auteur : un bot reviewer
        # (clusterManager-Myia) ou un siege de lane portent la meme forme.
        for author in ("clusterManager-Myia", "myia-po-2025"):
            report = mod.analyse_comments(
                9,
                [c(52, "2026-11-05T14:05:12Z", RESERVE_HERMES, author=author)],
                classes=("reviewer-reserve",),
            )
            self.assertEqual(len(report.reserves), 1, f"auteur : {author}")

    def test_lift_citing_timestamp_refermes(self):
        # Convention mesuree des levees : « [OVERRIDE] ... reserve ... du
        # 14:05Z » porte l'horodatage — citation forte, la reserve est REPONDU.
        report = mod.analyse_comments(
            9,
            [
                c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES),
                c(53, "2026-11-06T09:00:00Z", LIFT_WITH_TIMESTAMP),
            ],
            classes=("reviewer-reserve",),
        )
        self.assertEqual(len(report.reserves), 1)
        self.assertEqual(report.reserves[0].status, "REPONDU")
        self.assertEqual(report.reserves[0].proof, 53)

    def test_plain_reply_without_citation_is_manual_review(self):
        # Fail-closed : une reponse qui ne cite ni l'heure ni le texte laisse
        # la reserve en MANUAL_REVIEW, pas en REPONDU.
        report = mod.analyse_comments(
            9,
            [
                c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES),
                c(54, "2026-11-06T09:00:00Z", "Vu, on regarde la question."),
            ],
            classes=("reviewer-reserve",),
        )
        self.assertEqual(report.reserves[0].status, "MANUAL_REVIEW")

    def test_claim_after_reserve_raises_gesture_after(self):
        # Le geste de lane qui ne referme pas aggrave : drapeau pose, la
        # reserve reste ouverte.
        report = mod.analyse_comments(
            9,
            [
                c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES),
                c(55, "2026-11-05T15:00:00Z", CLAIM),
            ],
            classes=("reviewer-reserve",),
        )
        self.assertEqual(len(report.reserves), 1)
        self.assertTrue(report.reserves[0].gesture_after)
        self.assertTrue(report.gesture_after)
        self.assertIn(report.reserves[0], report.unresolved)

    def test_classes_scoping_leaves_reserves_out(self):
        # Les tests scoping : sans la classe demandee, aucune reserve rendue.
        report = mod.analyse_comments(
            9,
            [c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES)],
            classes=("user-concern",),
        )
        self.assertEqual(report.reserves, [])
        self.assertEqual(report.unresolved, [])

    def test_report_dict_carries_reserves(self):
        report = mod.analyse_comments(
            9,
            [c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES)],
            classes=("reviewer-reserve",),
        )
        payload = report.as_dict()
        self.assertIn("reserves", payload)
        self.assertEqual(payload["reserves"][0]["marker"], "COMMENT_WITH_CONCERNS")
        self.assertEqual(payload["reserves"][0]["status"], "NON REPONDU")

    def test_render_counts_reserves_and_labels_marker(self):
        report = mod.analyse_comments(
            9,
            [c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES)],
            classes=("reviewer-reserve",),
        )
        text = mod.render_text([report], "2026-09-25", "open", 1)
        self.assertIn("1 reserve(s) de relecteur", text)
        self.assertIn("[reserve COMMENT_WITH_CONCERNS]", text)


def test_cli_reserve_only_is_visible_and_fail_on_open(monkeypatch, capsys):
    """Une issue sans Concern ni remark ne doit pas perdre sa réserve."""
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES)
    ])
    rc = mod.main(["--issues", "9", "--classes", "reviewer-reserve",
                   "--json", "--fail-on-open"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert payload["unresolved"] == 1
    assert payload["reserves_total"] == 1
    assert payload["reserves_unresolved"] == 1
    assert payload["issues"][0]["reserves"][0]["comment_id"] == 51


def test_cli_reserve_only_text_reports_the_open_reserve(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES)
    ])
    rc = mod.main(["--issues", "9", "--classes", "reviewer-reserve",
                   "--fail-on-open"])
    text = capsys.readouterr().out
    assert rc == 1
    assert "1 reserve(s) de relecteur" in text
    assert "COMMENT_WITH_CONCERNS" in text


def test_cli_resolved_reserve_is_counted_but_not_open(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(51, "2026-11-05T14:05:12Z", RESERVE_HERMES),
        c(53, "2026-11-06T09:00:00Z", LIFT_WITH_TIMESTAMP),
    ])
    rc = mod.main(["--issues", "9", "--classes", "reviewer-reserve",
                   "--json", "--fail-on-open"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["unresolved"] == 0
    assert payload["reserves_total"] == 1
    assert payload["reserves_unresolved"] == 0


EXTERNAL_REPORT = (
    "Bonjour, je suis etudiant en L3 et le notebook 3.02 ne s'execute pas "
    "en entier : la cellule 12 leve une erreur d'import sur seaborn. J'ai "
    "suivi l'installation pas a pas. Merci pour ce cours formidable."
)
EXTERNAL_AUTHOR = "etudiant-l3-2026"


class ExternalAnalysisTests(unittest.TestCase):
    """Classe external-unanswered (#20185) : auteur hors flotte, tri-eti."""

    def test_external_comment_without_answer_is_open(self):
        report = mod.analyse_comments(
            21,
            [c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
               author=EXTERNAL_AUTHOR)],
            classes=("external-unanswered",),
        )
        self.assertEqual(len(report.externals), 1)
        finding = report.externals[0]
        self.assertEqual(finding.status, "NON REPONDU")
        self.assertEqual(finding.author, EXTERNAL_AUTHOR)
        self.assertEqual(finding.slug, "external-unanswered")
        self.assertFalse(finding.gesture_after)

    def test_fleet_and_bot_authors_are_not_external(self):
        # La classe cible l'AUTEUR hors flotte : logins de flotte (compte
        # partage, sieges myia-*, sieges reels mesures, bot reviewer) et bots
        # d'integration ne comptent jamais.
        for author in ("jsboige", "myia-po-2025", "clusterManager-Myia",
                       "jsboigeEpita", "jsboigeEPF",
                       "dependabot[bot]", "github-actions[bot]"):
            report = mod.analyse_comments(
                21,
                [c(71, "2026-11-10T10:12:00Z", EXTERNAL_REPORT, author=author)],
                classes=("external-unanswered",),
            )
            self.assertEqual(report.externals, [], f"auteur : {author}")

    def test_seat_lane_posts_are_not_external(self):
        # Controle positif mesure (#22267, c6811299399) : un [CLAIMED] pose
        # par le siege reel jsboigeEpita est un post de lane, pas un constat
        # externe — sans l'extension LANE_LOGIN, la classe inondait de posts
        # de flotte.
        report = mod.analyse_comments(
            22267,
            [
                c(6811299399, "2026-11-12T01:05:36Z",
                  "[CLAIMED] lane myia-po-2023:CoursIA -- audit de contenu "
                  "des 21 paires en derive avant toute attestation.",
                  author="jsboigeEpita"),
            ],
            classes=("external-unanswered",),
        )
        self.assertEqual(report.externals, [])

    def test_shared_seat_concern_is_user_concern(self):
        # Controle mesure (#23983, cIC_kwDOH2Odns8AAAABhtf6Mw) : le siege
        # jsboigeEPF sert AUSSI de plume au mainteneur — un « Concern: » poste
        # sous ce login doit tomber dans le filet user-concern (il lui
        # echappait avant l'extension LANE_LOGIN).
        report = mod.analyse_comments(
            23983,
            [c(78, "2026-11-01T11:22:56Z",
               "Concern: OK pour des carnets specifiques quand le veto sera "
               "leve, mais sinon je pensais comme on l'a dit.",
               author="jsboigeEPF")],
            classes=("user-concern",),
        )
        self.assertEqual(len(report.concerns), 1)
        self.assertEqual(report.concerns[0].status, "NON REPONDU")

    def test_reply_citing_timestamp_refermes(self):
        # Convention de la campagne (#20185) : la lane repond « en citant le
        # commentaire oublie » — l'horodatage est la forme forte.
        report = mod.analyse_comments(
            21,
            [
                c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
                   author=EXTERNAL_AUTHOR),
                c(72, "2026-11-11T09:00:00Z",
                  "Reponse au signalement du 10:12Z : seaborn est passe en "
                  "dependance optionnelle, le fix arrive au prochain merge."),
            ],
            classes=("external-unanswered",),
        )
        self.assertEqual(len(report.externals), 1)
        self.assertEqual(report.externals[0].status, "REPONDU")
        self.assertEqual(report.externals[0].proof, 72)

    def test_reply_quoting_excerpt_refermes(self):
        long_excerpt = (
            "la cellule 12 leve une erreur d'import sur seaborn. J'ai suivi "
            "l'installation pas a pas."
        )
        report = mod.analyse_comments(
            21,
            [
                c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
                   author=EXTERNAL_AUTHOR),
                c(73, "2026-11-11T09:00:00Z",
                  f"Merci pour le rapport : « {long_excerpt} » — la cause "
                  "est identifiee, la correction est en revue."),
            ],
            classes=("external-unanswered",),
        )
        self.assertEqual(report.externals[0].status, "REPONDU")
        self.assertEqual(report.externals[0].proof, 73)

    def test_plain_fleet_reply_without_citation_is_manual_review(self):
        # Fail-closed : une reponse de flotte qui ne cite ni l'heure ni le
        # texte laisse le constat en MANUAL_REVIEW, pas en REPONDU.
        report = mod.analyse_comments(
            21,
            [
                c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
                   author=EXTERNAL_AUTHOR),
                c(74, "2026-11-11T09:00:00Z",
                   "Merci du signalement, on regarde la cellule concernee."),
            ],
            classes=("external-unanswered",),
        )
        self.assertEqual(report.externals[0].status, "MANUAL_REVIEW")

    def test_second_external_comment_is_not_a_response(self):
        # Seule la flotte trier un commentaire externe : un second externe
        # (« +1 ») ne fait meme pas passer le constat en MANUAL_REVIEW.
        report = mod.analyse_comments(
            21,
            [
                c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
                   author=EXTERNAL_AUTHOR),
                c(75, "2026-11-10T11:00:00Z", "Meme probleme pour moi, +1.",
                   author="autre-etudiant"),
            ],
            classes=("external-unanswered",),
        )
        self.assertEqual(report.externals[0].status, "NON REPONDU")

    def test_bot_after_external_is_not_a_candidate(self):
        # Un bot d'integration qui passe apres le signalement (label, stale)
        # n'est ni une reponse ni un geste : le constat reste NON REPONDU.
        report = mod.analyse_comments(
            21,
            [
                c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
                   author=EXTERNAL_AUTHOR),
                c(76, "2026-11-10T12:00:00Z", "This issue is stale.",
                   author="stale[bot]"),
            ],
            classes=("external-unanswered",),
        )
        self.assertEqual(report.externals[0].status, "NON REPONDU")

    def test_claim_after_external_raises_gesture_after(self):
        # La lane travaille (claim) sans trier le contributeur : drapeau
        # aggravant, le constat reste ouvert.
        report = mod.analyse_comments(
            21,
            [
                c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
                   author=EXTERNAL_AUTHOR),
                c(77, "2026-11-10T14:00:00Z", CLAIM),
            ],
            classes=("external-unanswered",),
        )
        self.assertEqual(len(report.externals), 1)
        self.assertTrue(report.externals[0].gesture_after)
        self.assertTrue(report.gesture_after)
        self.assertIn(report.externals[0], report.unresolved)

    def test_classes_scoping_leaves_externals_out(self):
        report = mod.analyse_comments(
            21,
            [c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
               author=EXTERNAL_AUTHOR)],
            classes=("user-concern",),
        )
        self.assertEqual(report.externals, [])
        self.assertEqual(report.unresolved, [])

    def test_report_dict_carries_externals(self):
        report = mod.analyse_comments(
            21,
            [c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
               author=EXTERNAL_AUTHOR)],
            classes=("external-unanswered",),
        )
        payload = report.as_dict()
        self.assertIn("externals", payload)
        self.assertEqual(payload["externals"][0]["author"], EXTERNAL_AUTHOR)
        self.assertEqual(payload["externals"][0]["status"], "NON REPONDU")

    def test_render_counts_externals_and_labels_author(self):
        report = mod.analyse_comments(
            21,
            [c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT,
               author=EXTERNAL_AUTHOR)],
            classes=("external-unanswered",),
        )
        text = mod.render_text([report], "2026-09-25", "open", 1)
        self.assertIn("1 externe(s)", text)
        self.assertIn(f"[ext {EXTERNAL_AUTHOR}]", text)


def test_cli_external_only_is_visible_and_fail_on_open(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT, author=EXTERNAL_AUTHOR)
    ])
    rc = mod.main(["--issues", "21", "--classes", "external-unanswered",
                   "--json", "--fail-on-open"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert payload["unresolved"] == 1
    assert payload["externals_total"] == 1
    assert payload["externals_unresolved"] == 1
    assert payload["issues"][0]["externals"][0]["comment_id"] == 70
    assert payload["issues"][0]["externals"][0]["author"] == EXTERNAL_AUTHOR


def test_cli_external_only_text_reports_the_open_constat(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT, author=EXTERNAL_AUTHOR)
    ])
    rc = mod.main(["--issues", "21", "--classes", "external-unanswered",
                   "--fail-on-open"])
    text = capsys.readouterr().out
    assert rc == 1
    assert "1 externe(s)" in text
    assert EXTERNAL_AUTHOR in text


def test_cli_resolved_external_is_counted_but_not_open(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(70, "2026-11-10T10:12:00Z", EXTERNAL_REPORT, author=EXTERNAL_AUTHOR),
        c(72, "2026-11-11T09:00:00Z",
          "Reponse au signalement du 10:12Z : seaborn est passe en "
          "dependance optionnelle, le fix arrive au prochain merge."),
    ])
    rc = mod.main(["--issues", "21", "--classes", "external-unanswered",
                   "--json", "--fail-on-open"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["unresolved"] == 0
    assert payload["externals_total"] == 1
    assert payload["externals_unresolved"] == 0


# --------------------------------------------------------------------------- #
# Classe ``ask-unanswered`` (#20185, 5e classe) — formes mesurees le
# 2026-11-14 sur le corpus (70 issues les plus recentes portant « [ASK » en
# corps) : 7 tags POSES en emission, 63 citations de prose. Reels : #24357
# NON REPONDU, #23384 NON REPONDU (claim partageant du vocabulaire = pas une
# reponse), #25510/#18911 REPONDU (citation forte), #18285/#20386/#20697
# MANUAL_REVIEW.
# --------------------------------------------------------------------------- #

ASK_BARE = "[ASK] Route au mainteneur — décision de modèle de données (point 3 de #24246)"

ASK_ADDRESSEE = (
    "[ASK c.138 ai-01:CoursIA-2] Arbitrage mainteneur requis — les 5 décisions "
    "de contenu ne sont pas actionnables sans tranche"
)

ASK_QUOTE_SEED = (
    "le regime des push sur main doit trancher entre assessment seul et "
    "edition unilaterale par la lane, avec preuve et sans force push"
)


class AskTagTests(unittest.TestCase):
    def test_bare_ask_posed_is_detected(self):
        self.assertEqual(mod.ask_tag(ASK_BARE), "ASK")

    def test_addressee_inside_bracket_is_kept(self):
        # Forme mesuree #18285 : le destinataire vit DANS le crochet.
        self.assertEqual(mod.ask_tag(ASK_ADDRESSEE), "ASK c.138 ai-01:CoursIA-2")

    def test_double_bracket_group_with_decoration(self):
        # Forme mesuree #18911 : « **[ASK][VIBE-SUPPLY] Lane Vibe… ».
        self.assertEqual(
            mod.ask_tag(f"**[ASK][VIBE-SUPPLY] Lane Vibe po-2025 — queue vide"),
            "ASK",
        )

    def test_decoration_and_head_group_before_tag(self):
        self.assertEqual(mod.ask_tag("**[DISPATCH] [ASK] choisir un grain**"), "ASK")

    def test_prose_citation_is_not_posed(self):
        # 63 des 70 issues du corpus citent « [ASK » en PROSE (regles,
        # vocabulaire de campagne) sans jamais poser de question — mesure.
        body = "Le mainteneur demande un tag [ASK USER] dans le registre des questions."
        self.assertIsNone(mod.ask_tag(body))

    def test_mid_body_ask_is_not_posed(self):
        body = "Recapitulatif du cycle : la lane a pose un `[ASK]` hier, et la reponse est venue."
        self.assertIsNone(mod.ask_tag(body))

    def test_ask_user_tag_is_returned_for_caller_to_exclude(self):
        # L'exclusion (registre user) se decide dans analyse_comments pour
        # nourrir le compte publie — ask_tag rend le tag tel quel.
        self.assertEqual(mod.ask_tag("[ASK USER] fermer ou garder le registre ?"), "ASK USER")


class AskAnalysisTests(unittest.TestCase):
    def test_ask_without_answer_is_open(self):
        # Forme mesuree #24357 : dernier commentaire du fil, aucun candidat.
        report = mod.analyse_comments(
            31, [c(80, "2026-11-13T14:15:14Z", ASK_BARE)],
            classes=("ask-unanswered",),
        )
        self.assertEqual(len(report.asks), 1)
        self.assertEqual(report.asks[0].status, "NON REPONDU")
        self.assertFalse(report.asks[0].gesture_after)
        self.assertIn(report.asks[0], report.unresolved)

    def test_reply_citing_timestamp_refermes(self):
        # Forme mesuree #25510 : un geste de lane ([DELIVERED]) qui porte
        # l'horodatage de l'ASK referme (exception #2159 du candidat geste).
        report = mod.analyse_comments(
            31,
            [
                c(80, "2026-11-12T18:30:01Z", ASK_BARE),
                c(81, "2026-11-13T09:00:00Z",
                  "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #26250 -- "
                  "reponse au [ASK] du 18:30Z : assessment livre."),
            ],
            classes=("ask-unanswered",),
        )
        self.assertEqual(report.asks[0].status, "REPONDU")
        self.assertEqual(report.asks[0].proof, 81)
        self.assertNotIn(report.asks[0], report.unresolved)

    def test_reply_quoting_excerpt_refermes(self):
        ask_body = f"[ASK] {ASK_QUOTE_SEED} — arbitrage demande."
        reply_body = (
            "Reponse du coordinateur : je tranche pour l'assessment seul — "
            f"« {ASK_QUOTE_SEED} » releve du cas mesure, pas de la regle."
        )
        report = mod.analyse_comments(
            31,
            [
                c(80, "2026-11-12T18:30:01Z", ask_body),
                c(81, "2026-11-13T09:00:00Z", reply_body),
            ],
            classes=("ask-unanswered",),
        )
        self.assertEqual(report.asks[0].status, "REPONDU")
        self.assertEqual(report.asks[0].proof, 81)

    def test_claim_sharing_vocabulary_is_not_an_answer(self):
        # Forme mesuree #23384 : un [CLAIMED] qui reprend les chemins de l'ASK
        # (vocabulaire partage, quote courte) ne repond pas a la question —
        # la citation FORTE seule referme.
        report = mod.analyse_comments(
            31,
            [
                c(80, "2026-11-03T23:20:48Z",
                  "[ASK] Arbitrage convention `metadata.papermill.input_path` "
                  "demande a ai-01 -- souleve par la review Hermes de #23320."),
                c(81, "2026-11-03T23:46:24Z",
                  "[CLAIMED] lane myia-po-2028:CoursIA -- paths: "
                  "MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/08-KernelMemory-Hybrid-Search.ipynb"),
            ],
            classes=("ask-unanswered",),
        )
        self.assertEqual(report.asks[0].status, "NON REPONDU")
        self.assertTrue(report.asks[0].gesture_after)

    def test_plain_fleet_reply_without_citation_is_manual_review(self):
        # Plancher fail-closed : une reponse existe mais ne prouve rien —
        # ni tratee ni ignoree (#20186).
        report = mod.analyse_comments(
            31,
            [
                c(80, "2026-11-13T14:15:14Z", ASK_BARE),
                c(81, "2026-11-14T08:00:00Z",
                  "Vu sur le dashboard, la decision est en cours."),
            ],
            classes=("ask-unanswered",),
        )
        self.assertEqual(report.asks[0].status, "MANUAL_REVIEW")

    def test_ask_user_is_excluded_to_the_user_registry(self):
        # [ASK USER] vit dans le registre des questions user
        # (user-blocker-signaling.md) — l'ecart est publie, jamais muet.
        report = mod.analyse_comments(
            31,
            [c(80, "2026-11-13T14:15:14Z", "[ASK USER] fermer ou garder le registre ?")],
            classes=("ask-unanswered",),
        )
        self.assertEqual(report.asks, [])
        self.assertEqual(report.excluded.get("ask-user-registry"), 1)

    def test_bot_ask_is_ignored(self):
        report = mod.analyse_comments(
            31,
            [c(80, "2026-11-13T14:15:14Z", ASK_BARE, author="github-actions[bot]")],
            classes=("ask-unanswered",),
        )
        self.assertEqual(report.asks, [])

    def test_non_lane_ask_is_published_as_excluded(self):
        # Un [ASK] sous un login externe releve de external-unanswered :
        # ecart publie pour que le total ne passe pas pour exhaustif.
        report = mod.analyse_comments(
            31,
            [c(80, "2026-11-13T14:15:14Z", ASK_BARE, author="unEtudiant42")],
            classes=("ask-unanswered",),
        )
        self.assertEqual(report.asks, [])
        self.assertEqual(report.excluded.get("ask-non-lane"), 1)

    def test_classes_scoping_leaves_asks_out(self):
        report = mod.analyse_comments(
            31, [c(80, "2026-11-13T14:15:14Z", ASK_BARE)],
            classes=("user-concern",),
        )
        self.assertEqual(report.asks, [])
        self.assertEqual(report.unresolved, [])

    def test_report_dict_carries_asks_with_tag(self):
        report = mod.analyse_comments(
            31, [c(80, "2026-11-13T14:15:14Z", ASK_ADDRESSEE)],
            classes=("ask-unanswered",),
        )
        payload = report.as_dict()
        self.assertIn("asks", payload)
        self.assertEqual(payload["asks"][0]["tag"], "ASK c.138 ai-01:CoursIA-2")
        self.assertEqual(payload["asks"][0]["status"], "NON REPONDU")

    def test_render_counts_asks_and_labels_tag(self):
        report = mod.analyse_comments(
            31, [c(80, "2026-11-13T14:15:14Z", ASK_BARE)],
            classes=("ask-unanswered",),
        )
        text = mod.render_text([report], "2026-09-25", "open", 1)
        self.assertIn("1 ask(s)", text)
        self.assertIn("[ASK]", text)


def test_cli_ask_only_is_visible_and_fail_on_open(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(80, "2026-11-13T14:15:14Z", ASK_BARE)
    ])
    rc = mod.main(["--issues", "31", "--classes", "ask-unanswered",
                   "--json", "--fail-on-open"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert payload["unresolved"] == 1
    assert payload["asks_total"] == 1
    assert payload["asks_unresolved"] == 1
    assert payload["issues"][0]["asks"][0]["comment_id"] == 80
    assert payload["issues"][0]["asks"][0]["tag"] == "ASK"


def test_cli_ask_only_text_reports_the_open_ask(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(80, "2026-11-13T14:15:14Z", ASK_BARE)
    ])
    rc = mod.main(["--issues", "31", "--classes", "ask-unanswered",
                   "--fail-on-open"])
    text = capsys.readouterr().out
    assert rc == 1
    assert "1 ask(s)" in text
    assert "NON REPONDU" in text


def test_cli_resolved_ask_is_counted_but_not_open(monkeypatch, capsys):
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(80, "2026-11-12T18:30:01Z", ASK_BARE),
        c(81, "2026-11-13T09:00:00Z",
          "[DELIVERED] lane myia-ai-01:CoursIA-2 -- reponse au [ASK] du "
          "18:30Z : assessment livre, pas d'edition unilaterale."),
    ])
    rc = mod.main(["--issues", "31", "--classes", "ask-unanswered",
                   "--json", "--fail-on-open"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["unresolved"] == 0
    assert payload["asks_total"] == 1
    assert payload["asks_unresolved"] == 0


CONCERN_BARE = "**Concern** : la preuve mesuree manque (log CI absent du body)."
#: Reponse de lane fortement citante : signature de lane + horodatage
#: ``10:00Z`` du commentaire porteur (la forme mesuree #18601).
LANE_REPLY_10Z = (
    "[INFO] lane myia-po-2025:CoursIA-2 -- reponse au 10:00Z : preuve "
    "livree dans la PR #123, log CI cite dans le body."
)


class ClosedOverRemarkTests(unittest.TestCase):
    """Classe 6 ``closed-over-remark`` (#20185) : la VUE contextuelle.

    L'evenement n'est pas un commentaire mais une FERMETURE d'issue posee
    au-dessus d'une detection des classes 1-5. Trois statuts : sans reponse
    (verbatim, non resolu), repondu AVANT la fermeture (pas d'evenement),
    repondu APRES la fermeture (``REPONDU APRES CLOTURE`` : rendu avec preuve,
    non resolu = faux — l'arbitrage rouvrir/justifier appartient a la phase 2).
    """

    def test_closure_over_unanswered_concern(self):
        # Forme fondee : Concern jamais repondu, issue fermee dessous —
        # l'evenement SUPPLEE la detection (un seul non resolu, cadre fermeture).
        report = mod.analyse_comments(
            30,
            [
                c(1, "2026-10-01T10:00:00Z", CONCERN_BARE),
                c(2, "2026-10-02T09:00:00Z",
                  "[CLAIMED] lane myia-po-2025:CoursIA-2"),
            ],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-10-05T00:00:00Z",
        )
        self.assertEqual(len(report.concerns), 1)
        self.assertEqual(len(report.closures), 1)
        closure = report.closures[0]
        self.assertEqual(closure.comment_id, 1)
        self.assertEqual(closure.status, "NON REPONDU")
        self.assertEqual(closure.source, "user-concern")
        self.assertEqual(closure.closed_at, "2026-10-05T00:00:00Z")
        # La detection source n'est pas comptee deux fois : l'unresolved est
        # l'evenement de fermeture, pas le Concern nu.
        self.assertEqual(
            [(x.slug, x.comment_id) for x in report.unresolved],
            [("closed-over-remark", 1)],
        )

    def test_answered_before_closure_is_not_an_event(self):
        # Reponse forte AVANT la fermeture : la fermeture est legitime, aucun
        # evenement a arbitrer.
        report = mod.analyse_comments(
            30,
            [
                c(1, "2026-10-01T10:00:00Z", CONCERN_BARE),
                c(2, "2026-10-03T08:00:00Z", LANE_REPLY_10Z),
            ],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-10-05T00:00:00Z",
        )
        self.assertEqual(report.concerns[0].status, "REPONDU")
        self.assertEqual(report.closures, [])
        self.assertEqual(report.unresolved, [])

    def test_answered_after_closure_is_reported_not_unresolved(self):
        # Reponse forte APRES la fermeture : l'evenement existe et porte sa
        # preuve, mais il n'est PAS non resolu — rouvrir ou justifier par
        # ecrit appartient a la phase 2 de la campagne.
        report = mod.analyse_comments(
            30,
            [
                c(1, "2026-10-01T10:00:00Z", CONCERN_BARE),
                c(2, "2026-10-06T08:00:00Z", LANE_REPLY_10Z),
            ],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-10-05T00:00:00Z",
        )
        self.assertEqual(report.concerns[0].status, "REPONDU")
        self.assertEqual(len(report.closures), 1)
        closure = report.closures[0]
        self.assertEqual(closure.status, "REPONDU APRES CLOTURE")
        self.assertEqual(closure.proof, 2)
        self.assertNotIn(closure, report.unresolved)

    def test_open_issue_never_builds_closures(self):
        report = mod.analyse_comments(
            30,
            [c(1, "2026-10-01T10:00:00Z", CONCERN_BARE)],
            classes=("closed-over-remark",),
            state="open",
        )
        self.assertEqual(len(report.concerns), 1)
        self.assertEqual(report.closures, [])
        self.assertEqual(
            [(x.slug, x.comment_id) for x in report.unresolved],
            [("user-concern", 1)],
        )

    def test_requesting_the_view_forces_the_five_detections(self):
        # Demander SEULE la classe 6 detecte les classes 1-5 : l'evenement de
        # fermeture vit au-dessus d'un commentaire porte par sa classe source.
        report = mod.analyse_comments(
            30,
            [c(1, "2026-10-01T10:00:00Z", CONCERN_BARE)],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-10-05T00:00:00Z",
        )
        self.assertEqual(len(report.concerns), 1)
        self.assertEqual(report.closures[0].source, "user-concern")

    def test_manual_review_carries_to_the_closure(self):
        # Une detection MANUAL_REVIEW (reponse sans preuve) reste un evenement
        # ouvert sous la fermeture — le plancher fail-closed traverse la vue.
        report = mod.analyse_comments(
            30,
            [
                c(1, "2026-10-01T10:00:00Z", CONCERN_BARE),
                c(2, "2026-10-02T08:00:00Z",
                  "Vu sur le dashboard, la decision est en cours."),
            ],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-10-05T00:00:00Z",
        )
        closure = report.closures[0]
        self.assertEqual(closure.status, "MANUAL_REVIEW")
        self.assertIn(closure, report.unresolved)

    def test_closure_over_ask(self):
        report = mod.analyse_comments(
            31,
            [c(80, "2026-11-13T14:15:14Z", ASK_BARE)],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-11-14T00:00:00Z",
        )
        self.assertEqual(report.closures[0].source, "ask-unanswered")
        self.assertEqual(report.closures[0].status, "NON REPONDU")

    def test_missing_closed_at_fails_closed(self):
        # Issue fermee sans ``closed_at`` exploitable : tout non-repondu reste
        # un evenement, aucun ``APRES CLOTURE`` n'est fabrique (l'instant
        # manque, on ne l'invente pas) — le REPONDU reste saute.
        report = mod.analyse_comments(
            31,
            [
                c(1, "2026-10-01T10:00:00Z", CONCERN_BARE),
                c(2, "2026-10-03T08:00:00Z", LANE_REPLY_10Z),
                c(3, "2026-11-13T14:15:14Z", ASK_BARE),
            ],
            classes=("closed-over-remark",),
            state="closed",
            closed_at=None,
        )
        by_id = {f.comment_id: f for f in report.closures}
        self.assertNotIn(1, by_id)  # REPONDU : fermeture legitime, saute
        self.assertEqual(by_id[3].status, "NON REPONDU")
        self.assertEqual(by_id[3].source, "ask-unanswered")

    def test_render_labels_closures(self):
        report = mod.analyse_comments(
            30,
            [c(1, "2026-10-01T10:00:00Z", CONCERN_BARE)],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-10-05T00:00:00Z",
        )
        text = mod.render_text([report], "2026-10-01", "closed", 1)
        self.assertIn("1 cloture(s)-dessus", text)
        self.assertIn("[fermee 2026-10-05T00:00:00Z sur user-concern]", text)

    def test_as_dict_carries_closures(self):
        report = mod.analyse_comments(
            30,
            [c(1, "2026-10-01T10:00:00Z", CONCERN_BARE)],
            classes=("closed-over-remark",),
            state="closed",
            closed_at="2026-10-05T00:00:00Z",
        )
        payload = report.as_dict()
        self.assertEqual(len(payload["closures"]), 1)
        self.assertEqual(payload["closures"][0]["source"], "user-concern")
        self.assertEqual(
            payload["closures"][0]["status"], "NON REPONDU"
        )


def test_cli_closure_view_wires_issue_state(monkeypatch, capsys):
    # Le CLI demande l'etat de l'issue quand la classe 6 est requise : une
    # seule requete supplementaire par issue, et le compte JSON porte la vue.
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [
        c(1, "2026-10-01T10:00:00Z", CONCERN_BARE),
        c(2, "2026-10-02T09:00:00Z", "[CLAIMED] lane myia-po-2025:CoursIA-2"),
    ])
    monkeypatch.setattr(mod, "fetch_issue_state", lambda number: {
        "state": "closed", "closed_at": "2026-10-05T00:00:00Z",
    })
    rc = mod.main(["--issues", "30", "--classes", "closed-over-remark",
                   "--json", "--fail-on-open"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 1  # l'evenement de fermeture est non resolu
    assert payload["closures_total"] == 1
    assert payload["closures_unresolved"] == 1
    assert payload["issues"][0]["closures"][0]["source"] == "user-concern"


def test_cli_open_issue_skips_state_noise(monkeypatch, capsys):
    # Hors classe 6, ``fetch_issue_state`` n'est JAMAIS appele : la vue
    # contextuelle ne coute rien aux passes existantes.
    calls = []

    def _spy(number):
        calls.append(number)
        return {"state": "open", "closed_at": None}

    monkeypatch.setattr(mod, "fetch_issue_state", _spy)
    monkeypatch.setattr(mod, "fetch_comments", lambda number: [])
    mod.main(["--issues", "30", "--classes", "ask-unanswered", "--json"])
    capsys.readouterr()
    assert calls == []


if __name__ == "__main__":
    unittest.main()
