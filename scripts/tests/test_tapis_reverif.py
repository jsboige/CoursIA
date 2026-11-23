"""Re-decision des grains servis au fil tronque (#27179) -- tests.

Temoin fondateur : #26534, servie par le tapis 2,1 j apres son [RELEASED],
invisible de la fenetre de 12 commentaires. La passe relit le fil complet des
grains servis tronques et rejoue `_decider` ; un ecart apparu ejecte le grain
et son remplacant entre. Les candidats de chaque test occupent chacun leur
niveau de visite (0, 1, 2...) : l'ordre servi est alors deterministe par
construction, insensible au decalage de tete par graine.
"""
from __future__ import annotations

import json
import subprocess
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

from coordination import gh_bulk
from coordination import tapis_rapide as tr
from coordination import tapis_reverif as trv

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 18, 12, 0, tzinfo=UTC)
LANE = "myia-po-2024:CoursIA-2"
AUTRE = "myia-po-2023:CoursIA-2"


def _h(heures: float) -> str:
    return tr._iso(NOW - timedelta(hours=heures))


def issue(n: int, titre: str = "", body: str = "", labels=(), comments=(),
          cree: str = "2026-10-01T00:00:00Z", total: int | None = None) -> dict:
    return {"number": n, "title": titre or f"Grain {n}", "body": body, "labels": list(labels),
            "created_at": cree, "comments": list(comments),
            "comments_total": len(comments) if total is None else total}


def com(heures: float, body: str) -> dict:
    return {"created_at": _h(heures), "author": "jsboige", "body": body}


def _visite(heures: float) -> dict:
    """Un marqueur de visite d'une autre lane : ni ecart, ni claim ouvert."""
    return com(heures, f"[DELIVERED] lane {AUTRE} -- PR #9 -- paths: serie/{heures}.ipynb")


def lecture(issues, prs=(), citations=None) -> gh_bulk.Lecture:
    return gh_bulk.Lecture(issues=list(issues), prs=list(prs), citations=citations or {})


def _file_et_tous(lec, grains=1, graine="g"):
    tous = tr.etats(lec, LANE, NOW)
    return tous, tr.ordonner(tous, LANE, NOW, grains, graine)


def _temoin_26534():
    """Le temoin : un [RELEASED] de 2,1 j noye sous 12 commentaires de bruit."""
    rendu = com(50, f"[RELEASED] lane {AUTRE} -- EPIC rendez-vous, aucun "
                    "sous-grain servable.")
    fenetre = [com(12 - i, f"bruit recent {i}") for i in range(12)]
    anciens = [com(60 + i, f"tranche ancienne {i}") for i in range(4)]
    it = issue(26534, comments=fenetre, cree="2026-01-01T00:00:00Z",
               total=len(anciens) + 1 + len(fenetre))
    complets = anciens[:2] + [rendu] + anciens[2:] + fenetre
    return it, complets


# --- la passe ----------------------------------------------------------------

def test_temoin_26534_le_grain_rendu_est_ejecte_et_remplace():
    """#26534 : le [RELEASED] de 2,1 j est plus vieux que la fenetre de 12 ;
    re-decide sur fil complet, le grain sort et son remplacant entre."""
    it, complets = _temoin_26534()
    remplacant = issue(11, comments=[_visite(150)], cree="2026-02-01T00:00:00Z")
    lec = lecture([it, remplacant])
    tous, file = _file_et_tous(lec)
    assert [e.numero for e in file] == [26534]
    note = next(n for e in file for n in e.notes if n.startswith("fil partiel"))
    assert "17" in note  # 12 lus sur 17
    file2, stats = trv.passer(tous, file, 1, LANE, NOW, 45, "g", lec,
                              lire=lambda n: complets if n == 26534 else [])
    assert [e.numero for e in file2] == [11]  # ejecte, remplacant entre
    assert stats["appels"] == 1 and stats["jetes"][0]["code"] == "RELACHEE"
    assert stats["echecs"] == [] and stats["borne"] is False
    ejecte = next(e for e in tous if e.numero == 26534)
    assert "rendue par" in ejecte.motif
    r = tr.rapport(lec, tous, file2, LANE, NOW, "g")
    # #22983 : RELACHEE est un ecart de recul -- le grain recule, il n'est pas jete
    assert r["en_recul"]["RELACHEE"][0]["numero"] == 26534
    assert "RELACHEE" not in r["ecartees"]
    r["reverif_fils"] = stats  # le main porte la passe dans le rapport
    sortie = tr.texte(r, "test")
    assert "re-decides sur fil complet" in sortie and "RELACHEE #26534" in sortie


def test_fil_tronque_sans_marqueur_cache_le_grain_reste():
    """Le fil complet ne change pas le verdict : le grain reste servi, la note
    dit la relecture."""
    fenetre = [com(10 - i, f"bruit {i}") for i in range(12)]
    it = issue(21, comments=fenetre, cree="2026-02-01T00:00:00Z", total=20)
    remplacant = issue(22, comments=[_visite(150)], cree="2026-03-01T00:00:00Z")
    lec = lecture([it, remplacant])
    tous, file = _file_et_tous(lec)
    assert [e.numero for e in file] == [21]
    complets = fenetre + [com(40, f"tranche ancienne {i}") for i in range(8)]
    file2, stats = trv.passer(tous, file, 1, LANE, NOW, 45, "g", lec,
                              lire=lambda n: complets if n == 21 else [])
    assert [e.numero for e in file2] == [21]
    assert stats["jetes"] == [] and stats["appels"] == 1
    assert any("fil complet relu (20 commentaires)" in n for n in file2[0].notes)
    assert not any(n.startswith("fil partiel") for n in file2[0].notes)


def test_fils_non_tronques_aucun_appel():
    def _explose(n):
        raise AssertionError(f"le fil #{n} n'est pas tronque : rien a relire")
    lec = lecture([issue(31, cree="2026-01-01T00:00:00Z"),
                   issue(32, comments=[_visite(150)], cree="2026-02-01T00:00:00Z")])
    tous, file = _file_et_tous(lec)
    assert [e.numero for e in file] == [31]
    file2, stats = trv.passer(tous, file, 1, LANE, NOW, 45, "g", lec, lire=_explose)
    assert [e.numero for e in file2] == [31]
    assert stats["appels"] == 0 and stats["jetes"] == [] and stats["borne"] is False


def test_fil_illisible_le_grain_reste_en_fail_open():
    fenetre = [com(10 - i, f"bruit {i}") for i in range(12)]
    it = issue(41, comments=fenetre, cree="2026-03-01T00:00:00Z", total=15)
    remplacant = issue(42, comments=[_visite(150)], cree="2026-04-01T00:00:00Z")
    lec = lecture([it, remplacant])

    def _panne(n):
        raise RuntimeError("gh api : HTTP 502")
    tous, file = _file_et_tous(lec)
    assert [e.numero for e in file] == [41]
    file2, stats = trv.passer(tous, file, 1, LANE, NOW, 45, "g", lec, lire=_panne)
    assert [e.numero for e in file2] == [41]
    assert stats["echecs"] == [41] and stats["appels"] == 1 and stats["jetes"] == []
    assert any(n.startswith("fil partiel") for n in file2[0].notes)  # honnete : fenetre


def test_deux_rendus_hors_fenetre_les_remplacants_entrent():
    """Deux grains tronques ejectes d'un coup : les remplacants entrent, eux
    memes non tronques, et la file reste a la taille demandee."""
    fenetre = [com(12 - i, f"bruit {i}") for i in range(12)]
    rendus = {51: com(50, f"[RELEASED] lane {AUTRE} -- barriere mesuree."),
              52: com(60, f"[RELEASED] lane {AUTRE} -- siege trop petit.")}
    cible1 = issue(51, comments=fenetre, cree="2026-01-01T00:00:00Z", total=17)
    # une visite dans la fenetre : cibles aux niveaux 0-1, remplacants 2-3,
    # ordre servi deterministe a chaque etape
    cible2 = issue(52, comments=fenetre[:11] + [_visite(150)],
                   cree="2026-01-02T00:00:00Z", total=17)
    remplacants = [issue(53, comments=[_visite(160), _visite(110)],
                         cree="2026-05-01T00:00:00Z"),
                   issue(54, comments=[_visite(160), _visite(110), _visite(60)],
                         cree="2026-05-02T00:00:00Z")]
    lec = lecture([cible1, cible2, *remplacants])
    tous, file = _file_et_tous(lec, grains=2)
    assert [e.numero for e in file] == [51, 52]
    appels = []

    def lire(n):
        appels.append(n)
        return fenetre + [rendus[n]] if n in rendus else []
    file2, stats = trv.passer(tous, file, 2, LANE, NOW, 45, "g", lec, lire=lire)
    assert [e.numero for e in file2] == [53, 54]  # remplacants, fils non tronques
    assert appels == [51, 52] and stats["appels"] == 2
    assert [j["code"] for j in stats["jetes"]] == ["RELACHEE", "RELACHEE"]


def test_borne_d_appels_arrete_en_disant():
    """La borne d'appels s'arrete AVANT le deuxieme fil : le grain non relu
    reste servi sur sa fenetre, et la sortie le dit."""
    fenetre = [com(12 - i, f"bruit {i}") for i in range(12)]
    cible1 = issue(61, comments=fenetre, cree="2026-01-01T00:00:00Z", total=17)
    cible2 = issue(62, comments=fenetre[:11] + [_visite(150)],
                   cree="2026-01-02T00:00:00Z", total=17)
    lec = lecture([cible1, cible2])
    tous, file = _file_et_tous(lec, grains=2)
    assert [e.numero for e in file] == [61, 62]
    file2, stats = trv.passer(tous, file, 2, LANE, NOW, 45, "g", lec,
                              lire=lambda n: list(fenetre), appels_max=1)
    assert [e.numero for e in file2] == [61, 62]  # rien rejete : bruit seulement
    assert stats["appels"] == 1 and stats["borne"] is True
    assert any(n.startswith("fil partiel") for n in file2[1].notes)  # non relu


# --- le main -----------------------------------------------------------------

def test_cli_json_en_ligne_porte_la_reverif(monkeypatch, capsysbinary):
    """En ligne (ni --lecture ni cache), la passe tourne au moment du service,
    ejecte le temoin de la tete et se lit dans --json ; RELACHEE etant un ecart
    de recul (#22983), le temoin reste servi, derriere son remplacant."""
    it, complets = _temoin_26534()
    lec = lecture([it, issue(11, comments=[_visite(150)], cree="2026-02-01T00:00:00Z")])
    monkeypatch.setattr(tr.gh_bulk, "lire_tout", lambda *a, **k: lec)
    monkeypatch.setattr(tr.tapis_origami, "mesurer", lambda *a, **k: (
        {}, {"active": False, "measured": False, "parked": [], "reason": "test"}))
    code = tr.main(["--lane", LANE, "--cache-s", "0", "--json", "--voie", "lourd"],
                   run=lambda argv, timeout: "", maintenant=NOW,
                   lire_fils=lambda n: complets if n == 26534 else [])
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0
    servis = [g["numero"] for g in sortie["grains"]]
    assert servis.index(11) < servis.index(26534)  # le remplacant passe devant
    assert sortie["reverif_fils"]["jetes"][0]["code"] == "RELACHEE"
    assert sortie["en_recul"]["RELACHEE"][0]["numero"] == 26534


def test_rejeu_hors_ligne_ne_relit_rien(tmp_path, capsysbinary):
    """Un rejeu --lecture est hors ligne par contrat : la passe ne tourne pas,
    le temoin est servi avec sa note « fil partiel »."""
    it, _ = _temoin_26534()
    (tmp_path / "issues.json").write_text(
        json.dumps([it, issue(11, comments=[_visite(150)], cree="2026-02-01T00:00:00Z")]),
        encoding="utf-8")
    (tmp_path / "prs_ouvertes.json").write_text("[]", encoding="utf-8")
    (tmp_path / "meta.json").write_text(json.dumps({"fetched_at": tr._iso(NOW)}),
                                        encoding="utf-8")

    def _explose(n):
        raise AssertionError("un rejeu ne relit aucun fil")
    code = tr.main(["--lane", LANE, "--lecture", str(tmp_path), "--json"],
                   run=lambda argv, timeout: "", lire_fils=_explose)
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0 and "reverif_fils" not in sortie
    assert 26534 in [g["numero"] for g in sortie["grains"]]


def test_cache_de_secours_ne_declenche_pas_la_passe(tmp_path, monkeypatch, capsysbinary):
    """La lecture de secours est servie depuis le cache : la passe reste
    eteinte (la fenetre y est assumee, #26926), aucun appel REST ne part."""
    import dataclasses
    import time as _time
    it, _ = _temoin_26534()
    lec = lecture([it, issue(7)])
    lec.lu_a = tr._iso(NOW - timedelta(hours=2))
    monkeypatch.setattr(tr.gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    monkeypatch.setattr(tr.tapis_origami, "mesurer", lambda *a, **k: (
        {}, {"active": False, "measured": False, "parked": [], "reason": "test"}))
    brut = {**dataclasses.asdict(lec), "_epoch": _time.time() - 3 * 3600}
    (tmp_path / "lecture-45j.json").write_text(json.dumps(brut), encoding="utf-8")
    monkeypatch.setattr(tr.gh_bulk, "lire_tout", lambda *a, **k: (_ for _ in ()).throw(
        gh_bulk.LectureIncomplete("issues", 1, "HTTP 502")))

    def _panne(argv, timeout):
        raise subprocess.CalledProcessError(1, argv, output="", stderr="HTTP 401")
    code = tr.main(["--lane", LANE, "--voie", "lourd"], run=_panne, maintenant=NOW,
                   lire_fils=lambda n: (_ for _ in ()).throw(AssertionError(
                       "la lecture de secours ne declenche pas la passe")))
    sortie = capsysbinary.readouterr().out.decode("utf-8")
    assert code == 0 and "#7 Grain 7" in sortie
    assert "re-decides sur fil complet" not in sortie
