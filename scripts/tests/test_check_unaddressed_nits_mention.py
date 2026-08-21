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


# ---------------------------------------------------------------------------
# #11809 — Position C : verdict DEVANT le marqueur de levee. Le motif
# `_MENTION_VERDICT_LIFTED` exige : un nom de verdict, un verbe de levee,
# puis une REFERENCE POINTABLE (commit SHA / PR # / issue #) entre
# parentheses. Une emission reelle (verdict avec description a suivre) ne
# matche pas — la voie discrimine par la presence de la reference.
# ---------------------------------------------------------------------------


def test_11809_verdict_devant_avec_commit_sha_devient_mention():
    """Forme du ticket : `CHANGES_REQUESTED adresse (commit <sha>)`.
    Verdict devant, levee par adresse + pointeur vers le commit qui leve."""
    body = "Suite a la review : CHANGES_REQUESTED adresse (commit 3dcd00029)."
    assert mod.classify("myia-po-2024", body) is None, body


def test_11809_verdict_devant_avec_pr_number_devient_mention():
    """Forme alternative : `SUSPECT_REGRESSION leve (PR #11806)`.
    PR #N est un identifiant pointable comme commit SHA."""
    body = "Le SUSPECT_REGRESSION leve (PR #11806) — verifie a la main."
    assert mod.classify("myia-po-2024", body) is None, body


def test_11809_verdict_devant_avec_issue_number_devient_mention():
    """Forme `(... leve (#N))` — le #N peut etre une issue, pas forcement PR.
    Le discriminateur est le `#` + digits en parens."""
    body = "Le CHANGES_REQUESTED traite (#11809), voie prise."
    assert mod.classify("myia-po-2024", body) is None, body


def test_11809_formes_accentuees_couvertes():
    """Cluster ecrit massivement sans accents (#11639) MAIS certains agents
    accentuent. Le pattern tolere les deux formes — `traite` et `traité`,
    `repondu` et `répondu`, `adresse` et `adressé`."""
    for body in (
        "CHANGES_REQUESTED traité (commit abc1234).",
        "CHANGES_REQUESTES adressé (PR #11758).",
        "COMMENT_WITH_CONCERNS répondu (commit def5678).",
        "SUSPECT_REGRESSION levée (PR #11744).",
    ):
        assert mod.classify("myia-po-2024", body) is None, body


def test_11809_emission_avec_description_reste_vivante():
    """Non-regression fondamentale : une emission reelle avec description a
    suivre ne doit PAS etre neutralisee. Le ticket insiste — « le remede
    evident `VERDICT <mot-de-levee>` rendrait le garde aveugle ». La
    contrainte ajoutee est la presence d'une REFERENCE POINTABLE."""
    body = (
        "CHANGES_REQUESTED : la sequence exec est UNORDERED, "
        "a corriger avant merge — voir le diff pour le detail."
    )
    # L'emission nue « CHANGES_REQUESTED: » reste comptée comme telle.
    # Hermes-bot (auteur) sans lift, verdict au state=CHANGES_REQUESTED :
    # le gate a deja un signal bloquant via le state, pas le body.
    # classify sur body seul doit rendre BOT-CONCERN (le verdict reste emis
    # dans la prose).
    assert mod.classify("hermes-bot", body) == "BOT-CONCERN", body


def test_11809_verdict_devant_sans_reference_reste_vivant():
    """Forme `CHANGES_REQUESTED adresse le bug` — le verbe de levee est la,
    mais PAS de reference pointable entre parentheses. La mention n'est pas
    etablie — le verdict reste emis. C'est exactement le discriminant que
    le ticket demande : « une levee designe *ce qui* leve ; une emission
    n'a rien a designer »."""
    body = "Le CHANGES_REQUESTED adresse le bug constrnct — pas de fix livre."
    assert mod.classify("hermes-bot", body) == "BOT-CONCERN", body


def test_11809_commit_sha_sans_verdict_ne_matche_pas():
    """Le pattern exige un verdict AVANT le verbe de levee — un SHA seul
    n'est pas un signal de mention. Non-regression : pas de FP sur les
    refs techniques pures."""
    body = "Le fix est dans (commit abc1234) — pas un verdict, juste un SHA."
    # classify doit rendre None (pas de CONCERN_MARKER dans cette prose).
    assert mod.classify("hermes-bot", body) is None, body


# ---------------------------------------------------------------------------
# #11984 — Position D : nominal `revue`/`review` + reference pointable.
# Instance fondatrice : #11911, commentaire 2026-08-20T14:50:21Z (corps
# EXACT ci-dessous) — un rapport de re-review classe BOT-CONCERN comme
# s'il emettait la reserve qu'il rapporte. Cinquieme reformulation de la
# classe use-vs-mention. Le discriminant n'est PAS le nominal seul : le
# contre-exemple de l'issue (« Cette review CHANGES_REQUESTED reste
# bloquante ») porte le nominal ET emet une reserve vivante.
# ---------------------------------------------------------------------------

FIXTURE_11911_BODY = (
    "Re-review request — la réparation demandée est livrée sur `221349b441` "
    "(tête actuelle, post-revue).\n"
    "\n"
    "La revue CHANGES_REQUESTED (07:32Z, SHA `5aa6e035`) pointait 2 défauts : "
    "(1) 0 output `image/png` committé, (2) stdout régressé (supprimé). "
    "Vérifié firsthand sur la tête actuelle :\n"
    "\n"
    "**1. Frames image/png présentes** : 8 outputs `image/png` committés dans "
    "les cells 10/15/20. Re-exéc authentique avec ComfyUI-Video joignable "
    "(`localhost:8189`, HTTP 401 = service UP, `run_generation=True`).\n"
    "\n"
    "CI CLEAN (0 fail). La revue visait l'ancien SHA `5aa6e035` — la tête "
    "`221349b441` adresse les 2 points bloquants."
)


def test_11984_fixture_reelle_11911_nest_plus_un_nit():
    """Le corps EXACT du commentaire bloqueur de #11911 : le verdict
    rapporte est neutralise, le commentaire n'est plus BOT-CONCERN."""
    assert mod.classify("jsboige", FIXTURE_11911_BODY) is None


def test_11984_revue_en_gras_avec_ref_pointable_devient_mention():
    """« La **revue** CHANGES_REQUESTED (07:32Z, SHA `...`) » — le gras
    markdown autour du nominal est couvert (frontiere etendue a `*`)."""
    body = "La **revue** CHANGES_REQUESTED (07:32Z, SHA `5aa6e035`) pointait 2 défauts."
    assert mod.classify("hermes-bot", body) is None, body


def test_11984_anglais_the_review_couvert():
    body = "the review CHANGES_REQUESTED (07:32Z, SHA 5aa6e035) flagged two defects."
    assert mod.classify("hermes-bot", body) is None, body


def test_11984_reference_pr_issue_couvertes():
    body = "la revue CHANGES_REQUESTED (cf #11911) est adressée par le commit."
    assert mod.classify("hermes-bot", body) is None, body


def test_11984_contre_exemple_issue_reste_vivant():
    """LE contre-exemple de l'issue, a ne PAS neutraliser : le nominal est
    devant le verdict mais il EMET une reserve vivante — aucune reference
    pointable n'etablit le rapport d'evenement passe."""
    body = "Cette review CHANGES_REQUESTED reste bloquante."
    assert mod.classify("hermes-bot", body) == "BOT-CONCERN", body


def test_11984_revue_sans_reference_pointable_reste_vivant():
    """Nominal + verdict mais la suite ne porte pas de reference pointable :
    la mention n'est pas etablie, le verdict reste emis."""
    body = "la revue CHANGES_REQUESTED du matin était sévère."
    assert mod.classify("hermes-bot", body) == "BOT-CONCERN", body


def test_11984_parenthese_non_pointable_reste_vivant():
    """Une parenthese qui ne porte NI SHA, NI numero, NI horodatage ne
    designe rien : « (de ai-01) » n'etablit pas le rapport passe."""
    body = "La review CHANGES_REQUESTED (de ai-01) reste bloquante."
    assert mod.classify("hermes-bot", body) == "BOT-CONCERN", body


def test_11984_emission_marker_deux_points_reste_vivante():
    """« Review CHANGES_REQUESTED: ... » — la forme MARKER: nue reste une
    emission (le garde `verdict(?![:.])` du nominal + l'absence de paren
    pointable la preservent)."""
    body = (
        "Review CHANGES_REQUESTED: la séquence exec est UNORDERED, "
        "à corriger avant merge."
    )
    assert mod.classify("hermes-bot", body) == "BOT-CONCERN", body


def test_11984_forme_11628_non_regie_par_le_nouveau_motif():
    """Non-regression : « Fix review ai-01 (CHANGES_REQUESTED) — commit ... »
    reste gere par le motif d'ORIGINE #11636 (verbe de reference + verdict
    entre parentheses), pas par la position D. Le strip applique au body
    doit neutraliser le verdict via _MENTION_VERDICT, et le nouveau motif
    ne doit PAS matcher seul sur cette forme."""
    body = "Fix review ai-01 (CHANGES_REQUESTED) — commit 06956bd0a."
    # Le nouveau motif seul ne matche pas (verdict entre parentheses, pas
    # de parenthese-pointable APRES le verdict).
    m = mod._MENTION_VERDICT_REVIEW.search(body)
    assert m is None, body
    # Le strip global neutralise toujours (via #11636).
    assert "CHANGES_REQUESTED" not in mod._strip_mentioned_verdicts(body)
