"""#18937 -- la levee SIGNEE d'une reserve `[ADJOINT]` par l'adjoint lui-meme
doit lever sa reserve ; la levee non signee passait deja (organe inverse,
mesure sur la PR #18849 : commentaire 5954471018 `[ADJOINT] CONCERNS` du
02/10 14:17Z, leve par `[myia-po-2025:CoursIA-2] Je leve ma reserve ...` du
03/10 00:39Z -- 27 tests passes -- reste bloquee a B.0).

Deux pistes de l'issue, testees par les positifs/negatifs specifies :
- piste 1 : apparier role <-> role (`[ADJOINT]` <-> `[ADJOINT]`) ;
- piste 2 : alias role -> lane d'attache (ADJOINT -> myia-po-2025:CoursIA-2,
  coordinator-discipline R6) -- une levee signee de la lane de l'adjoint
  leve sa reserve role.

Negatifs : une lane tierce qui « leve » une reserve `[ADJOINT]` reste
bloquee ; une levee `[ADJOINT]` sur une reserve user voix nue reste
bloquee.
"""
from __future__ import annotations

import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location(
    "check_unaddressed_nits",
    ROOT / "scripts" / "check_unaddressed_nits.py",
)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)


def at(day: int, hour: int) -> str:
    return f"2026-10-0{day}T{hour:02d}:00:00Z"


MERGED = datetime(2026, 10, 3, 12, 0, tzinfo=timezone.utc)

# La PR reelle #18849 porte un tag Grain (la garde #18149 lit la lane du
# body) ; on reproduit ce contexte.
PR_BODY = (
    "Grain: MED/notebook-python -- lane myia-po-2024:CoursIA-3 -- "
    "prev: LIGHT/docs #18853"
)


def run(comments, body=PR_BODY, commits=None, threads=None, reviews=None,
        pr_author="jsboige", **extra):
    data = {
        "number": 18849,
        "title": "t",
        "author": {"login": pr_author},
        "body": body,
        "comments": comments,
        "reviews": reviews if reviews is not None else [],
        "commits": commits if commits is not None else [{"committedDate": at(2, 14)}],
    }
    data.update(extra)
    return mod.analyse(data, threads or [], MERGED)


# Reserve adjoint deduite du cas fondateur : commentaire `jsboige`
# (login partage) porteant le prefixe de role ADJOINT.
NIT_ADJOINT = {
    "author": {"login": "jsboige"}, "createdAt": at(2, 14),
    "body": ("[ADJOINT] CONCERNS\n"
             "Verdict corroborr a la tete mais deux reserves : "
             "cadrage S-Lens et fixture skippee."),
}

# Reserve user voix nue (sans prefixe) -- pour le negatif 2.
NIT_USER_NU = {
    "author": {"login": "jsboige"}, "createdAt": at(2, 14),
    "body": ("CONCERN: la garde X ne couvre pas le cas Y, "
             "a reconcilier avant merge."),
}


def test_positif_1_levee_role_leve_reserve_role():
    """Piste 1 : une levee `[ADJOINT] Je leve ma reserve ...` leve la
    reserve `[ADJOINT] CONCERNS` (avant #18937 : voie 3 exclut tout lift
    a prefixe de role -> bloque)."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(3, 0),
        "body": ("[ADJOINT] Je leve ma reserve du commentaire precedent : "
                 "les deux points sont corrobores a la tete fdee6125f2, "
                 "27 tests passes."),
    }
    res = run([NIT_ADJOINT, lift])
    assert res["blocked"] is False


def test_positif_2_levee_lane_attache_leve_reserve_role():
    """Piste 2 : la levee signee de la lane d'attache du role
    (`[myia-po-2025:CoursIA-2]`, alias R6) leve la reserve `[ADJOINT]`
    -- la forme exacte du cas fondateur #18849 (avant : voie 2 ->
    lift_has_lane sans nit_has_lane -> return False)."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(3, 0),
        "body": ("[myia-po-2025:CoursIA-2] Je leve ma reserve du commentaire "
                 "5954471018 : verification independante a la tete "
                 "fdee6125f2, 27 tests passes."),
    }
    res = run([NIT_ADJOINT, lift])
    assert res["blocked"] is False


def test_negatif_1_lane_tierce_ne_leve_pas():
    """Une lane tierce (`myia-po-2024:CoursIA-3`) qui « leve » une reserve
    `[ADJOINT]` reste bloquee : l'alias est nominatif, pas un joker."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(3, 0),
        "body": ("[myia-po-2024:CoursIA-3] Je leve la reserve ADJOINT : "
                 "verification croisee de mon cote."),
    }
    res = run([NIT_ADJOINT, lift])
    assert res["blocked"] is True


def test_negatif_2_role_ne_leve_pas_reserve_user_nue():
    """Une levee `[ADJOINT]` ne leve pas une reserve user voix nue :
    le scope emetteur de #14850 est preserve (la reserve nue n'appartient
    pas au role)."""
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(3, 2),
        "body": ("[ADJOINT] Je leve ma reserve : le cas Y est couvert "
                 "au commit suivant."),
    }
    res = run([NIT_USER_NU, lift])
    assert res["blocked"] is True


def test_18937_unitaire_bracket_token():
    """Voxel : `_bracket_token` normalise role et lane d'attache."""
    import re as _re
    role = _re.search(r"(?m)^\[ADJOINT\]", "[ADJOINT] corps")
    assert mod._bracket_token(role) == "ADJOINT"
    lane = _re.search(
        r"(?m)^\[myia-po-2025:CoursIA-2\]", "[myia-po-2025:CoursIA-2] corps")
    assert mod._bracket_token(lane) == "MYIA-PO-2025:COURSIA-2"
    lane_suite = _re.search(
        r"(?m)^\[myia-po-2025:CoursIA-2 suite\]",
        "[myia-po-2025:CoursIA-2 suite] corps")
    assert mod._bracket_token(lane_suite) == "MYIA-PO-2025:COURSIA-2"
