"""Tests use vs mention de CONCERN_MARKERS (#11636), 2e reformulation de la
classe fermee pour CONDITIONAL_LIFT (#11246).

Un rapport de correction qui NOMME le verdict qu'il corrige n'emets pas de
reserve. Cas fondateur #11628 (mesure : le SEUL item bloquant du gate au
moment du merge) :

    Fix review ai-01 (CHANGES_REQUESTED) — commit 06956bd0a.

Le nom du verdict est entre PARENTHESES, pas entre guillemets — `_strip_quoted`
ne le voyait pas et aucun CITERS ne matche « review ai-01 («. L'incitation
etait inversee : le rapport le PLUS precis etait classe BOT-CONCERN pendant
qu'un « done » passait — le gate penalisait exactement le comportement que
B.0 cherche a obtenir.

La classe est rare et mesurée (1/60 PRs mergees, #11636) : le correctif est
etroit — verbe/locution de reference + nom de verdict FORMEL entre
parentheses, deux conditions cumulatives. Une emission parenthesee sans
verbe de reference reste vivante (controle positif).

Aucun appel reseau : classify/has_live_marker sont purs.
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

# Corps EXACT du commentaire 2026-08-18T12:17:52Z de #11628 (auteur po-2026,
# poste via gh CLI donc sans CRLF). C'etait le seul item bloquant du gate.
FIXTURE_11628_BODY = (
    "Fix review ai-01 (CHANGES_REQUESTED) — commit 06956bd0a.\n"
    "\n"
    "Re-alignement de la couche interpretation sur les sorties du run "
    "committe : md[9,28,30,34,36,40,44]. Au-dela de la liste du review, "
    "md[9] (reference prospective 'Sharpe 0.683, +50,12 %') corrige aussi — "
    "G.1.\n"
    "\n"
    "Recit retourne honnetement : le modele ATTEINT sa barre (val_sharpe "
    "1.218 > 0.7, checkpoint charge = episode 200, le dernier), +184,62 % "
    "total / +41,98 % annualise OOS, MaxDD -26,55 %, win rate 53,46 %, 2806 "
    "trades, actions Hold 4076 / Buy 3558 / Sell 942 / Close 2704 (net-long "
    "avec rotation active). md[30] re-ecrit : le best-checkpoint n'a pas eu "
    "a trancher CE run (pic = fin) mais aurait preserve le +0,655 de l'ep 60 "
    "sans la recuperation de l'ep 200.\n"
    "\n"
    "Splice chirurgical JSON : seules les 7 cellules markdown changent "
    "(verifie par id nbformat), 0 cellule code, outputs intacts, sources "
    "byte-identiques a main. Diff markdown-only -> pas de re-exec (gel "
    "disque)."
)

MENTION = "Fix review ai-01 (CHANGES_REQUESTED) — commit 06956bd0a."
USAGE = ("[Hermes] — CHANGES_REQUESTED : la cellule 19 casse C.2, "
         "a corriger avant merge.")


def test_mention_et_usage_cote_a_cote():
    """Acceptance 1+2 : les DEUX formes dans le MEME test — la mention
    (rapport de correction) ne reserve pas, l'usage (vraie reserve) reserve.
    Verifier une seule forme par test laisserait un fix tuer l'autre."""
    assert mod.classify("myia-po-2026", MENTION) is None
    assert mod.classify("hermes-bot", USAGE) == "BOT-CONCERN"


def test_has_live_marker_faux_sur_mention_vrai_sur_usage():
    """Acceptance de #11636 : has_live_marker rend False sur la mention ET
    True sur l'usage, dans la meme invocation — sinon on remplace un faux
    positif par un faux negatif, qui lui ne se signale pas."""
    assert mod.has_live_marker(
        mod._strip_mentioned_verdicts(MENTION), mod.CONCERN_MARKERS) is False
    assert mod.has_live_marker(
        mod._strip_mentioned_verdicts(USAGE), mod.CONCERN_MARKERS) is True


def test_fixture_reelle_11628_nest_plus_un_nit():
    """Corps complet du commentaire fondateur : rapport de correction, pas
    une reserve. AVANT le fix, c'etait l'unique item bloquant du gate."""
    assert mod.classify("myia-po-2026", FIXTURE_11628_BODY) is None


def test_emission_parenthesee_sans_verbe_reste_vivante():
    """Controle du cumul : un verdict entre parentheses SANS verbe de
    reference devant est une EMISSION (« (CHANGES_REQUESTED) sur la ligne
    19 »), pas une mention — la parenthese seule n'exempte rien."""
    bare = "(CHANGES_REQUESTED) sur la ligne 19, a corriger avant merge."
    assert mod.classify("hermes-bot", bare) == "BOT-CONCERN"


def test_agent_intercale_entre_verbe_et_parenthese():
    """Le cas reel porte un nom d'agent entre le verbe et la parenthese
    (« Fix review ai-01 (…) ») : la fenetre de 40 chars l'accepte, meme
    mecanique que l'attribution de `_is_cited`."""
    spaced = "Fix review hermes, relue au passage (CHANGES_REQUESTED) — commit abc."
    assert mod.classify("myia-po-2026", spaced) is None


def test_locutions_de_reference_couvertes():
    """La famille decrite par #11636, au-dela du cas fondateur : suite a / en
    reponse a / corrige."""
    for body in (
        "Suite a la review ai-01 (CHANGES_REQUESTED) du 12:38, les 7 cellules "
        "sont re-alignees — commit 06956bd0a.",
        "En reponse a ton verdict (NEEDS_CHANGES) : le split est fait.",
        "Corrige la reponse de po-2023 (COMMENT_WITH_CONCERNS) — commit def456.",
    ):
        assert mod.classify("myia-po-2026", body) is None, body


def test_verdict_nu_hors_parenthese_reste_vivant():
    """Non-regression : le meme verbe de reference suivi d'un verdict NU
    (hors parentheses) reste une emission potentielle — la voie ne touche
    QUE la forme parenthesee."""
    naked = "Fix review ai-01 CHANGES_REQUESTED — commit 06956bd0a."
    assert mod.classify("hermes-bot", naked) == "BOT-CONCERN"


def test_retro_11628_le_gate_passe():
    """Le livrable en retro : PR de po-2026 portant le rapport de correction
    reeel, mergee ensuite — plus aucun signal bloquant."""
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [{"author": {"login": "myia-po-2026"},
                      "createdAt": "2026-08-18T12:17:52Z",
                      "body": FIXTURE_11628_BODY}],
        "reviews": [],
        "commits": [{"committedDate": "2026-08-18T12:30:00Z"}],
    }
    merged = datetime(2026, 8, 18, 13, 30, tzinfo=timezone.utc)
    assert mod.analyse(data, [], merged)["blocked"] is False
