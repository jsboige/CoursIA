"""#18149 -- un alias de persona en prefixe d'un lift identifie comme emis
par la lane du PR ne leve rien. Le cas fondateur (PR #18072, 2026-09-27)
est un commentaire `jsboige` prefixe `[NanoClaw]` et signe `lane
myia-po-2024:CoursIA` ; avant la garde, l'organe rendait `rc=0` sur cette
auto-reponse de l'auteur.

La voie persona de l'alias #13609 reste valide pour le dialogue
`clusterManager-Myia` <-> self-bot `jsboige` ; la porte se ferme des
qu'un prefixe de lane ou une signature de bas de corps est observable
dans le meme lift et correspond a la lane carrier de la PR.
"""
from __future__ import annotations

import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location(
    "check_unaddressed_nits",
    ROOT / "scripts" / "check_unaddressed_nits.py",
)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)


def at(hour: int) -> str:
    return f"2026-09-27T{hour:02d}:00:00Z"


MERGED = datetime(2026, 9, 27, 20, 0, tzinfo=timezone.utc)


def run(comments, body="", commits=None, threads=None, reviews=None,
        pr_author="jsboige", **extra):
    data = {
        "number": 18072,
        "title": "t",
        "author": {"login": pr_author},
        "body": body,
        "comments": comments,
        "reviews": reviews if reviews is not None else [],
        "commits": commits if commits is not None else [{"committedDate": at(19)}],
    }
    data.update(extra)
    return mod.analyse(data, threads or [], MERGED)


# Reserve `clusterManager-Myia` du test deduit de #18072 : review NanoClaw
# `COMMENTED` portant `CONCERNS`.
NIT_NANOCLAW = {
    "author": {"login": "clusterManager-Myia"},
    "state": "COMMENTED", "submittedAt": at(10),
    "body": ("[NanoClaw] - CONCERNS\n"
             "F1 finding sur cellule 3. F2 finding sur cellules 5-6."),
}

# Body de PR portant tag `Grain:` de la lane `myia-po-2024:CoursIA`.
PR_BODY = (
    "## Synthese\n\nMesure premiere.\n\n"
    "Grain: MED/notebook-python -- lane myia-po-2024:CoursIA "
    "-- prev: LIGHT/guard #18021\n"
)


def test_18149_cas_fondateur_18072_bloque():
    """#18149 cas fondateur : lift `jsboige` prefixe `[NanoClaw]` et
    signe `lane myia-po-2024:CoursIA` (la lane de la PR) ne leve PAS la
    reserve `clusterManager-Myia` -- l'organe rend `blocked=True`. Avant
    la garde, le prefixe `[NanoClaw]` etait lu comme marqueur persona et
    le lift etait credite (`rc=0`)."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("[NanoClaw] Reponse a la review du scan 17:57Z : les deux "
                 "points F1 et F2 sont leves, commits abc123 et def456. "
                 "-- lane myia-po-2024:CoursIA"),
    }
    res = run([lift], reviews=[NIT_NANOCLAW], body=PR_BODY)
    assert res["blocked"] is True, (
        "Lift `jsboige` prefixe `[NanoClaw]` ET signe par la lane de la PR "
        "ne doit PAS lever la reserve persona — c'est l'auto-reponse "
        "de l'auteur (#18149, instance fondatrice #18072)."
    )


def test_18149_cas_fondateur_18072_prefix_lane_header_bloque():
    """Forme (a) -- la lane est en tete de paragraphe `[machine:workspace]`
    plutot qu'en pied `-- lane ...`. Meme conclusion."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("[myia-po-2024:CoursIA] [NanoClaw] Reponse a la review "
                 "du scan 17:57Z : les deux points F1 et F2 sont leves, "
                 "commits abc123 et def456."),
    }
    res = run([lift], reviews=[NIT_NANOCLAW], body=PR_BODY)
    assert res["blocked"] is True


def test_18149_controle_negatif_persona_sans_signature_leve_toujours():
    """Le canal legitime Hermes self-bot `<->` clusterManager-Myia doit
    rester OUVERT : un commentaire `jsboige` prefixe `[NanoClaw]` mais
    SANS signature de lane (= Hermes self-bot parle a la persona) leve
    la reserve, comme avant #18149."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("[NanoClaw] Reprise du dialogue : les deux points F1 et "
                 "F2 sont leves, commits abc123 et def456."),
    }
    res = run([lift], reviews=[NIT_NANOCLAW], body=PR_BODY)
    assert res["blocked"] is False, (
        "Le canal legitime Hermes self-bot reste ouvert (#13609 / "
        "#18149 voie de droite) : sans signature de lane, l'alias "
        "persona doit toujours lever."
    )


def test_18149_controle_negatif_autre_lane_signe_bloque_aussi():
    """Une lane tierce qui prefixe `[NanoClaw]` ET signe une autre lane
    NE leve PAS non plus la reserve persona : le cross-lane lift filter
    de la voie 2 (`_CROSS_LANE_LIFT_RE`) precede l'alias #13609 et refuse
    deja un lift signe par une lane tierce sur une reserve persona --
    c'est le regime #14850 (lift lane tierce ne leve pas user voix nue ;
    par symetrie, il ne leve pas non plus persona ici). Test documente
    l'ordre d'application : cross-lane check d'abord, alias #13609
    ensuite, garde #18149 en queue -- #18149 n'agit que si les deux
    premieres passes ont deja laisse passer.
    """
    pr_body_tierce = (
        "## Synthese\n\nMesure premiere.\n\n"
        "Grain: MED/notebook-python -- lane myia-po-2024:CoursIA "
        "-- prev: LIGHT/guard #18021\n"
    )
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("[NanoClaw] Reprise du dialogue par une autre lane : "
                 "F1 et F2 leves. -- lane myia-po-2025:CoursIA-2"),
    }
    res = run([lift], reviews=[NIT_NANOCLAW], body=pr_body_tierce)
    # Comportement actuel (regime #14850 + cross-lane check) : bloque.
    # #18149 ne change rien ici.
    assert res["blocked"] is True


def test_18149_pr_sans_tag_grain_pas_de_garde():
    """Un PR sans `Grain:` lisible ne beneficie pas de la garde #18149
    (l'organe ignore la signature de lane). Ce n'est pas un
    retablissement de la voie nue : l'alias persona reste ouvert par
    defaut, comme avant. Mesure couverte par `is_out_of_fleet` /
    `variation_tag_required.py` (cf exemption #17713, hors perimetre
    #18149)."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("[NanoClaw] Reprise : les deux points F1 et F2 sont "
                 "leves, commit abc123. -- lane myia-po-2024:CoursIA"),
    }
    res = run([lift], reviews=[NIT_NANOCLAW], body="SYNTHESE sans tag Grain.")
    assert res["blocked"] is False


def test_18149_garde_unitaire_voxel_marker_lane():
    """Voxel : la fonction `_lift_signed_by_pr_lane` est exportee par le
    module et reconnaissable directement (controle structurel)."""
    # Cas du fondateur.
    lift_body = ("[NanoClaw] Reponse. -- lane myia-po-2024:CoursIA")
    pr_body = ("Grain: MED/notebook-python -- lane myia-po-2024:CoursIA")
    assert mod._lift_signed_by_pr_lane(lift_body, pr_body) is True
    # Cas voie (a)
    lift_a = "[myia-po-2024:CoursIA] corps"
    assert mod._lift_signed_by_pr_lane(lift_a, pr_body) is True
    # Cas lane tierce
    lift_other = "[NanoClaw] Reprise. -- lane myia-po-2025:CoursIA-2"
    assert mod._lift_signed_by_pr_lane(lift_other, pr_body) is False
    # Pas de lane dans le lift
    assert mod._lift_signed_by_pr_lane(
        "[NanoClaw] Reprise sans signature.", pr_body) is False
    # PR sans tag `Grain:`
    assert mod._lift_signed_by_pr_lane(
        lift_body, "SYNTHESE sans tag Grain.") is False
