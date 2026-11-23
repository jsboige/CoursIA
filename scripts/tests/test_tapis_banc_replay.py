"""Le BANC DE REPLAY du tapis : les cas FIGES, rejoues hors reseau.

Ce que le banc mesure :

- la **derive des organes de decision** : chaque cas fige porte le code
  observe lors du rejeu REEL du 18/11 (qualification de 72 candidats sur le
  pool de la lane). Le banc rejoue les memes cas -- memes corps, memes fils,
  memes citations, memes PRs, meme instant de reference -- et doit rendre les
  memes codes. Un ecart signale que les neuf regles ont bouge ;
- la **mesure des refus** : la repartition des codes sur le corpus fige, et la
  couverture : chaque code d'ecart doit etre represente par au moins un cas.

Ce que le banc ne touche pas : le **branchement de production**. Il appelle
les organes (`tapis_rapide.etats`, `tapis_fil_complet.confirmer`) avec une
lecture figee et un lecteur de fil fige ; aucun module de production n'est
modifie par ce banc.

Aucun test ne touche le reseau : les cas sont lus dans
`scripts/tests/fixtures/tapis_replay_cases.json`.
"""
from __future__ import annotations

import json
import sys
from datetime import datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk  # noqa: E402
from coordination import tapis_fenetre, tapis_fil_complet  # noqa: E402
from coordination import tapis_rapide  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

FIXTURE = Path(__file__).parent / "fixtures" / "tapis_replay_cases.json"

#: Les neuf ecarts de regle : chacun doit etre represente par un cas fige.
CODES_ECART = ("HORSFLOTTE", "LABEL", "GEL", "LIVREE", "MERGEE", "COUVERTE",
               "RELACHEE", "PLAFOND", "RECLAMEE")


def _fixture() -> dict:
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def _lecture(fix: dict) -> gh_bulk.Lecture:
    """La lecture figee : les cas, leur contexte, leurs citations, leurs PRs."""
    issues = []
    for ctx in fix["contexte"]:
        body = f"Part of #{ctx['parent']}\n" if ctx.get("parent") else ""
        issues.append({"number": ctx["number"], "title": ctx["title"], "body": body,
                       "created_at": ctx["created_at"], "labels": ctx["labels"],
                       "comments": [], "comments_total": 0})
    citations: dict[int, list[dict]] = {}
    prs: list[dict] = []
    for cas in fix["cas"]:
        fil = cas["fil_complet"]
        issues.append({"number": cas["number"], "title": cas["title"],
                       "body": cas["body"], "created_at": cas["created_at"],
                       "labels": cas["labels"], "comments": fil[-12:],
                       "comments_total": len(fil)})
        if cas["citations"]:
            citations[cas["number"]] = list(cas["citations"])
        prs.extend(cas["prs"])
    return gh_bulk.Lecture(issues=issues, prs=prs, citations=citations,
                           lu_a=fix["maintenant"], secondes=0.0, appels=0)


def _rejouer(fix: dict, monkeypatch) -> dict[int, str]:
    """Rejoue les cas figes et rend le code de decision de chaque cas."""
    lec = _lecture(fix)
    maintenant = datetime.fromisoformat(fix["maintenant"].replace("Z", "+00:00"))
    etats = tapis_rapide.etats(lec, fix["lane"], maintenant, fix["jours"])
    cas_numeros = {c["number"] for c in fix["cas"]}
    codes = {e.numero: (e.ecart or "SERVI") for e in etats if e.numero in cas_numeros}

    # Le lecteur de fil COMPLET est fige : la production n'est pas touchee.
    fils = {c["number"]: c["fil_complet"] for c in fix["cas"]}
    monkeypatch.setattr(tapis_fenetre, "fil_complet",
                        lambda numero, repo=None: list(fils.get(numero) or []))
    retenus = [e for e in etats if e.ecart is None]
    confirmes, rejetes, _, _ = tapis_fil_complet.confirmer(
        retenus, lec, fix["lane"], maintenant, fix["jours"])
    for e in confirmes:
        if e.numero in cas_numeros:
            codes[e.numero] = "SERVI"
    for r in rejetes:
        if r["numero"] in cas_numeros:
            codes[r["numero"]] = r["code"]
    return codes


def test_le_banc_rejoue_les_memes_codes(monkeypatch):
    """Chaque cas fige rend le code observe lors du rejeu reel du 18/11."""
    fix = _fixture()
    codes = _rejouer(fix, monkeypatch)
    ecarts = []
    for cas in fix["cas"]:
        attendu = cas["attendu"]["code"]
        obtenu = codes.get(cas["number"])
        if obtenu != attendu:
            ecarts.append(f"#{cas['number']} : attendu {attendu}, obtenu {obtenu}")
    assert not ecarts, "derive des organes de decision : " + " ; ".join(ecarts)


def test_le_banc_couvre_les_neuf_ecarts(monkeypatch):
    """Les neuf ecarts de regle ont chacun un cas fige, et le cas servi aussi."""
    fix = _fixture()
    codes = _rejouer(fix, monkeypatch)
    vus = set(codes.values())
    for code in CODES_ECART:
        assert code in vus, f"aucun cas fige pour l'ecart {code}"
    assert "SERVI" in vus, "aucun cas fige servi"


def test_le_banc_mesure_la_repartition_des_refus(monkeypatch):
    """La mesure des refus : combien de cas par code, sur le corpus fige."""
    fix = _fixture()
    codes = _rejouer(fix, monkeypatch)
    repartition: dict[str, int] = {}
    for code in codes.values():
        repartition[code] = repartition.get(code, 0) + 1
    refuses = sum(v for k, v in repartition.items() if k != "SERVI")
    assert len(codes) == len(fix["cas"])
    assert refuses >= len(CODES_ECART), "le corpus fige doit porter chaque ecart"
    print(f"banc de replay : {len(codes)} cas -- {repartition}")


def test_le_banc_ne_lit_pas_le_reseau(monkeypatch):
    """Le banc rejoue HORS reseau : toute lecture reelle du fil le fait echouer.

    C'est la garantie qui rend le banc utilisable en CI : si l'injection du
    fil fige ne tenait pas, l'organe de production lirait GitHub -- ici, la
    lecture est une erreur explicite.
    """
    from coordination import gh_snapshot

    def _interdit(*a, **k):
        raise AssertionError("le banc ne doit pas lire le reseau")

    monkeypatch.setattr(gh_snapshot, "fetch_issue_comments", _interdit)
    fix = _fixture()
    codes = _rejouer(fix, monkeypatch)
    assert len(codes) == len(fix["cas"])
