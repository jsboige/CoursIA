"""Tests for #16799 — levée tierce qui NOMME sa cible comptée comme réserve.

B.0 exige qu'une levée NOMME la remarque qu'elle traite (« une réponse écrite
sur la PR qui nomme la remarque »). Une levée tierce s'ouvre donc naturellement
sur « ## Levée tierce de la réserve X », puis cite le verdict qu'elle lève
avec auteur, heure et texte exact (« X a posé `VERDICT: CONCERNS` le <date> »).
L'organe lisait le fait de NOMMER comme une ÉMISSION : le geste qui débloquait
la PR créait un nit à son propre nom.

Défaut fondateur : la review réelle de myia-ai-01 sur #16710 (2026-09-19T02:08Z,
embarquée ici VERBATIM dans sa partie chargeante). Elle porte QUATRE familles
de narration d'une résolution — attribution, citation quotée, référence
démonstrative, timing de levée — et l'organe les comptait toutes comme réserves
debout. Mesure : classify = BOT-CONCERN avant, None après.

La voie retenue est l'ancrage en OUVERTURE (#16700, `_OPENING_LIFT_RE`) étendu
du qualificatif « tierce », pas des entrées CITERS par famille : l'ancrage
neutralise les quatre familles d'un coup, chaque CITERS n'en couvrirait qu'une.

Deux exigences d'acceptance portent sur ce fichier :

  - la review réelle de #16710 devient NEUTRALISÉE (classify None) ;
  - le CONTROLE POSITIF — l'émission réelle NanoClaw du 2026-09-18T16:17:57Z
    sur la même PR, préfixe de corps `VERDICT: CONCERNS (...)` — DOIT continuer
    à bloquer. C'est le témoin qui distingue « le corps narre » de « l'ancrage
    neutralise tout ».

Ce que la voie cesse d'attraper (acceptance 5, hérité #16700) : un corps
ouvrant sur « Levée tierce de la réserve X » qui émettrait une réserve NEUVE
en corps sort du recensement — résidu du corps mixte levée+réserve, mesuré
0/1718 corps (200 dernières PRs mergées, delta classify = 0), pinné par
`test_16799_residu_corps_mixte_documente`.

Aucun appel réseau : `classify` est pure, on lui passe le corps.
"""
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)


# Partie chargeante de la review réelle de myia-ai-01 sur #16710
# (2026-09-19T02:08:08Z), verbatim — du heading d'ouverture jusqu'à la
# re-mesure. Porte les QUATRE familles de narration : l'attribution
# (« a posé `VERDICT: CONCERNS` le 2026-09-18T16:17:57Z »), la citation
# quotée (« 19:40 « CONCERNS close — sweep ... » »), la référence
# démonstrative (« la CONCERNS ci-dessus (levée à l'instant) ») et le
# timing de levée (« levée ci-dessus, par un tiers, avant merge »).
REAL_16710_LIFT = """\
## Levée tierce de la réserve NanoClaw — et le seul geste qui reste

`clusterManager-Myia` a posé `VERDICT: CONCERNS` le 2026-09-18T16:17:57Z au head `43930d17` : *7 résidus de modèles obsolètes dans la metadata de coût de 2 notebooks*. Tu as répondu trois fois (19:40 « CONCERNS close — sweep `885316e2bd` », 20:50, 22:39 « re-review SVP »), et **tes trois réponses sont justes**.

**Re-mesure firsthand, head `ed3e019621`, sur les 11 fichiers de la PR** :

**0 occurrence, sur les 11 fichiers.** Le périmètre de cette mesure est celui des noms de modèles obsolètes — c'est exactement ce que la réserve nommait. Levée.

`check_unaddressed_nits.py` rend **exit 1** sur 4 nits : la CONCERNS ci-dessus (levée à l'instant) et 3 `PREFLIGHT_HOLD`/`BLOCKED` de l'adjoint. 3. Réserve NanoClaw : **levée ci-dessus**, par un tiers, avant merge, avec sa mesure.
"""

# Corps réel de la review NanoClaw du 2026-09-18T16:17:57Z sur #16710,
# verbatim dans sa partie verdict — ÉMISSION canonique en préfixe de corps.
# C'est le TÉMOIN de l'acceptance 2 : il doit rester compté.
REAL_16710_EMISSION = (
    "VERDICT: CONCERNS (code exécutable propre et vérifié ; 7 résidus de modèles "
    "obsolètes dans la metadata de coût de 2 notebooks — prose devenue fausse pour "
    "l'étudiant)\n\n**[NanoClaw]** — structural review #16710 (CoursIA), head `43930d17`."
)


# ---------------------------------------------------------------------------
# Le défaut fondateur : la levée réelle ne compte plus comme réserve
# ---------------------------------------------------------------------------

def test_16799_levee_reelle_16710_neutralisee():
    """classify : BOT-CONCERN -> None. La levée tierce qui nomme sa cible
    n'est plus une réserve debout."""
    assert mod.classify("myia-ai-01", REAL_16710_LIFT) is None


def test_16799_levee_reelle_porte_bien_les_marqueurs():
    """Contre-épreuve : le corps contient bien le marqueur nu et vivant SANS
    le fix (fenêtre d'attribution « a pose » hors CITERS, guillemets,
    démonstratif). Sans cette assertion, le test précédent passerait aussi
    sur un corps sans marqueur — il mesurerait l'absence, pas la levée."""
    assert "VERDICT: CONCERNS" in REAL_16710_LIFT
    assert "CONCERNS ci-dessus" in REAL_16710_LIFT
    # le marqueur nu est vivant hors mécanisme d'ouverture : preuve directe
    # que c'est _opens_on_lift qui neutralise, pas une citation fenêtrée
    sans_ouverture = REAL_16710_LIFT.split("\n", 1)[1].lstrip()
    assert mod.has_live_marker(sans_ouverture, mod.CONCERN_MARKERS) is True


# ---------------------------------------------------------------------------
# CONTRÔLE POSITIF (exigé par l'acceptance 2) — l'émission réelle bloque
# ---------------------------------------------------------------------------

def test_16799_controle_emission_nanoclaw_reste_comptee():
    """L'émission canonique (préfixe de corps `VERDICT: CONCERNS (...)`) de la
    même PR, même auteur bot, même jour — DOIT rester BOT-CONCERN."""
    assert mod.classify("clusterManager-Myia", REAL_16710_EMISSION) == "BOT-CONCERN"


def test_16799_controle_emission_apres_ouverture_neutre():
    """Cas dur : un corps qui OUVRE sur une phrase neutre puis ÉMET le verdict
    en préfixe de son premier bloc de verdict. L'ancrage d'ouverture ne doit
    neutraliser QUE les ouvertures de levée, jamais une émission réelle."""
    body = ("Contexte : re-review demandée après sweep.\n\n"
            "VERDICT: CONCERNS (2 résidus demeurent au head)")
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


# ---------------------------------------------------------------------------
# L'ouverture étendue : formes couvertes et non couvertes
# ---------------------------------------------------------------------------

def test_16799_formes_douverture_tierce_couvertes():
    """La famille directe du registre B.0 tierce."""
    for body in (
        "## Levée tierce de la réserve NanoClaw — détails ci-dessous",
        "**Levée tierce de la réserve Hermes** au head `abc1234`",
        "Levée tierce de la réserve de clusterManager-Myia, re-mesurée",
        "Levée tierce de réserve NanoClaw (forme sans article)",
    ):
        assert mod._opens_on_lift(body) is True, body
        assert mod.classify("myia-ai-01", body + "\n\n`VERDICT: CONCERNS` était la cible.") is None


def test_16799_formes_hors_registre_non_couvertes():
    """Le qualificatif est borné à « tierce » : les autres qualificatifs
    (« officielle », « totale ») et les rapports (« Levée des alertes »)
    restent hors ancrage — whack-a-mole minimal, une seule forme mesurée."""
    for body in (
        "## Levée officielle de la réserve",
        "Levée totale de la réserve",
        "## Levée des alertes CI : tout est vert",
    ):
        assert mod._opens_on_lift(body) is False, body


def test_16799_formes_16700_heritees_intactes():
    """Les formes fondatrices #16700 fonctionnent toujours (non-régression
    de l'alternance étendue)."""
    for body in (
        "## Levée de la réserve NanoClaw — détail",
        "Réserve levée par re-mesure au head `abc`",
        "Je lève la réserve posée à 16:17Z",
    ):
        assert mod._opens_on_lift(body) is True, body


# ---------------------------------------------------------------------------
# Résidu hérité #16700, mesuré 0/1718 — documenté et pinné
# ---------------------------------------------------------------------------

def test_16799_residu_corps_mixte_documente():
    """Acceptance 5 : ce que la voie cesse d'attraper. Un corps qui ouvre sur
    « Levée tierce de la réserve X » puis ÉMET une réserve NEUVE en corps
    sort du recensement. Résidu hérité du trade-off #16700 (corps mixte
    levée+réserve), mesuré 0 occurrence sur 1718 corps des 200 dernières PRs
    mergées. Le test PINNE le comportement pour que tout changement de ce
    résidu soit un geste délibéré, pas un effet de bord."""
    body = ("## Levée tierce de la réserve NanoClaw\n\n"
            "La réserve d'hier est levée.\n\n"
            "VERDICT: CONCERNS (un NOUVEAU problème trouvé au sweep)")
    assert mod.classify("myia-ai-01", body) is None  # résidu assumé
