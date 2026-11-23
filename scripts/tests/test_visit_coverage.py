"""Tests de `coordination/visit_coverage.py` : la couverture des visites (#27590).

Chaque role a son code d'ecart et son cas voisin ; l'avancee a ses deux preuves
(marqueur DELIVERED, commit cite) et leur voisin hors fenetre ; l'invariant du
16/11 a ses cas limites (marathon, claim propre) ; les codes de sortie de `main`
sont exerces sur un dossier rejoue. La propriete du tapis simule le service
reel : a chaque pas, la tete de `tapis_equilibre.ordre` a le niveau minimal du
pool, donc aucune issue n'atteint deux visites tant qu'une autre est a zero.
Aucun test ne touche le reseau.
"""
import importlib.util
import json
import re
import subprocess
from datetime import timedelta
from pathlib import Path

import pytest
from coordination import tapis_equilibre as te
from coordination import tapis_rapide as tr
from coordination import visit_coverage as vc

# Les fabriques de test_tapis_rapide.py, chargees par chemin : sous
# `--import-mode importlib`, `tests.` designe le premier paquet `tests` collecte.
_SPEC = importlib.util.spec_from_file_location(
    "_fabriques_tapis_rapide", Path(__file__).with_name("test_tapis_rapide.py"))
_fab = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_fab)
AUTRE, LANE, NOW = _fab.AUTRE, _fab.LANE, _fab.NOW
com, commit, etat, issue, lecture = _fab.com, _fab.commit, _fab.etat, _fab.issue, _fab.lecture

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")


def _etat(numero: int = 1, ecart: str | None = None, motif: str = "",
          titre: str = "Grain", visites: int = 0, visites_total: int = 0,
          cree: str = "2026-10-01T00:00:00Z", labels=(),
          mon_claim: bool = False) -> tr.Etat:
    """Un Etat construit a la main : le role et l'invariant sont purs."""
    return tr.Etat(numero=numero, titre=titre, labels=list(labels), cree_le=cree,
                   parent=None, famille=numero, conteneur=False, consolidation=False,
                   visites=visites, visites_total=visites_total, ecart=ecart,
                   motif=motif, mon_claim=mon_claim)


# --- le role, pour chaque code d'ecart --------------------------------------

@pytest.mark.parametrize(("code", "motif", "attendu"), [
    ("HORSFLOTTE", "Hors flotte — Marathon II", "hors-flotte"),
    ("LABEL", "label candidate-delivered : urne de cloture (coordinateur, adjoint)", "urne"),
    ("GEL", "ligne [FROZEN] dans le body (degel : retirer la ligne)", "mainteneur"),
    ("LIVREE", "dernier commentaire [INFO] candidate-delivered", "urne"),
    ("MERGEE", "livraison probable, commit abc1234", "urne"),
    ("COUVERTE", "PR ouverte #900 la cite", "revue"),
    ("RELACHEE", "rendue par myia-po-2027:CoursIA il y a 1.0 j (< 3 j)", "attente"),
    ("PLAFOND", "plafond EPIC (#22500) : visite de X il y a 3.0 j (< 7 j)", "attente"),
    ("ORIGAMI", "pli 3 non deplie", "attente"),
    ("RECLAMEE", "claim de myia-po-2027:CoursIA du 2026-11-20T10:00Z", "worker"),
])
def test_role_par_code_d_ecart(code, motif, attendu):
    assert vc.role(_etat(ecart=code, motif=motif)) == attendu


def test_role_servable_label_inconnu_et_marathon():
    assert vc.role(_etat()) == "worker"
    # un LABEL qui ne nomme pas candidate-delivered n'est pas l'urne
    e = _etat(ecart="LABEL", motif="label mystere")
    assert vc.role(e) == "autre" and e.motif == "label mystere"
    # tout marathon est au harnais, ecart de livraison compris (mesure du 20/11)
    assert vc.role(_etat(numero=26070, titre="[EPIC] Marathon de parite II")) == "harnais"
    assert vc.role(_etat(numero=26070, titre="Marathon", ecart="LIVREE",
                         motif="[INFO] candidate-delivered")) == "harnais"


def test_pr_de_revue_lit_le_numero_du_motif():
    assert vc.pr_de_revue(_etat(ecart="COUVERTE",
                                motif="votre PR #900 la cite : portez-la au merge")) == 900
    assert vc.pr_de_revue(_etat(ecart="COUVERTE", motif="PR ouverte #901 la cite")) == 901
    assert vc.pr_de_revue(_etat()) is None


# --- l'avancee dans la fenetre ----------------------------------------------

def test_avancee_par_delivered_dans_la_fenetre():
    lec = lecture([issue(1, comments=[com(5 * 24, f"[DELIVERED] lane {AUTRE} -- PR #900")])])
    e = etat(lec, 1)
    assert vc.avancee(e, lec, NOW) == f"[DELIVERED] de {AUTRE} le 2026-11-08"
    # le voisin hors fenetre (8 j) n'avance pas
    lec = lecture([issue(2, comments=[com(8 * 24, f"[DELIVERED] lane {AUTRE} -- PR #900")])])
    assert vc.avancee(etat(lec, 2), lec, NOW) is None


def test_avancee_par_commit_cite_dans_la_fenetre():
    lec = lecture([issue(1), issue(2)],
                  citations={1: [commit("abc1234def567", 24 * 3)],
                             2: [commit("def5678abc123", 24 * 9)]})
    assert vc.avancee(etat(lec, 1), lec, NOW) == "commit abc1234 du 2026-11-10"
    assert vc.avancee(etat(lec, 2), lec, NOW) is None  # hors fenetre


def test_une_visite_sans_preuve_n_avance_pas():
    lec = lecture([
        issue(1, comments=[com(5, f"[CLAIMED] lane {AUTRE} -- je prends")]),
        issue(2, comments=[com(5, f"[INFO] lane {AUTRE} — candidate-delivered")]),
    ])
    assert vc.avancee(etat(lec, 1), lec, NOW) is None
    assert vc.avancee(etat(lec, 2), lec, NOW) is None  # [INFO] n'est pas retenu


# --- l'invariant du 16/11 ----------------------------------------------------

def test_invariant_viole_et_respecte():
    r = vc.invariant([_etat(1, visites=0), _etat(2, visites=2)], NOW)
    assert r["viole"] and r["a_zero"] == [1] and r["a_deux"] == [2]
    assert vc.invariant([_etat(1, visites=1), _etat(2, visites=1)], NOW)["viole"] is False
    assert vc.invariant([_etat(1, visites=0)], NOW)["viole"] is False


def test_invariant_ignore_marathon_et_claim_propre():
    # un marathon a deux visites ne viole rien quand un servable est a zero
    etats_ = [_etat(1, visites=0), _etat(26070, titre="Marathon", visites=2)]
    assert vc.invariant(etats_, NOW)["viole"] is False
    # un claim propre sort du pool : ce n'est pas « une autre issue »
    etats_ = [_etat(1, visites=0), _etat(2, visites=2, mon_claim=True)]
    assert vc.invariant(etats_, NOW)["viole"] is False
    # une issue non reclamee a deux visites viole toujours
    etats_ = [_etat(1, visites=0), _etat(2, visites=2)]
    assert vc.invariant(etats_, NOW)["viole"] is True


def test_invariant_trie_par_anciennete_de_creation():
    etats_ = [_etat(n, visites=0, cree=(NOW - timedelta(days=n)).strftime("%Y-%m-%dT%H:%M:%SZ"))
              for n in (3, 1, 2)]
    assert vc.invariant(etats_, NOW)["a_zero"] == [3, 2, 1]


# --- le bilan par role -------------------------------------------------------

def test_bilan_par_role_compte_et_borne():
    etats_ = [_etat(numero=n, ecart="LIVREE", motif="dernier commentaire [INFO] candidate-delivered",
                    cree=(NOW - timedelta(days=10 + n)).strftime("%Y-%m-%dT%H:%M:%SZ"))
              for n in range(1, 26)]  # 25 livrees, toutes de plus de 7 j
    r = vc.bilan(etats_, lecture([]), NOW)
    urne = r["roles"]["urne"]
    assert urne["issues"] == 25 and urne["sans_visite"] == 25
    # le JSON rend la liste COMPLETE : la borne est une borne d'affichage
    assert len(urne["numeros_sans_visite"]) == 25
    assert urne["numeros_sans_visite"][0] == 25  # la plus ancienne d'abord
    assert r["urgences"]["nombre"] == 25
    assert r["jamais_visitees_nombre"] == 25


def test_le_json_rend_les_25_numeros_et_le_texte_annonce_les_5_manquants():
    """#27725 : la borne `LIMITE_LISTE` vaut pour l'affichage, pas pour la
    donnee. Le JSON rend les 25 numeros ; le texte en montre 20 et DIT qu'il
    en cache 5 -- une troncature invisible est un mensonge de l'organe."""
    etats_ = [_etat(numero=n, ecart="LIVREE", motif="dernier commentaire [INFO] candidate-delivered",
                    cree=(NOW - timedelta(days=10 + n)).strftime("%Y-%m-%dT%H:%M:%SZ"))
              for n in range(1, 26)]
    r = vc.bilan(etats_, lecture([]), NOW)
    assert len(r["roles"]["urne"]["numeros_sans_visite"]) == 25
    assert len(r["jamais_visitees"]) == 25
    assert len(r["urgences"]["numeros"]) == 25

    texte = vc._texte(r, "test")
    ligne = next(x for x in texte.splitlines() if x.strip().startswith("urne"))
    assert "et 5 autres" in ligne
    # les 20 affiches sont la tete de la liste complete, dans le meme ordre
    affiches = [int(x) for x in re.findall(r"#(\d+)", ligne.split("a 0 :")[1].split(";")[0])]
    assert len(affiches) == vc.LIMITE_LISTE
    assert affiches == r["roles"]["urne"]["numeros_sans_visite"][:vc.LIMITE_LISTE]


def test_le_texte_dit_le_nombre_cache_pour_chaque_liste_bornee():
    """Une liste de 21 numeros : 20 affiches, 1 cache, et le texte le dit."""
    assert vc._liste_texte([]) == "aucune"
    assert vc._liste_texte([1, 2]) == "#1, #2"
    assert vc._liste_texte(list(range(1, 22))) .endswith("... et 1 autre")
    assert vc._liste_texte(list(range(1, 26))).endswith("... et 5 autres")


def test_bilan_compte_les_visitees_non_avancees():
    lec = lecture([issue(1, comments=[com(5, f"[CLAIMED] lane {AUTRE} -- je prends")])])
    r = vc.bilan([etat(lec, 1)], lec, NOW)
    assert (r["roles"]["worker"]["visitees_non_avancees"],
            r["roles"]["worker"]["sans_visite"]) == (1, 0)
    # un commit cite dans la fenetre la fait avancer (sans fermer l'issue)
    vue = {**commit("abc1234def", 10), "ferme": False}
    lec = lecture([issue(1, comments=[com(5, f"[CLAIMED] lane {AUTRE} -- je prends")])],
                  citations={1: [vue]})
    assert vc.bilan([etat(lec, 1)], lec, NOW)["roles"]["worker"]["visitees_non_avancees"] == 0


def test_bilan_porte_la_pr_de_revue():
    prs = [{"number": 900, "title": "Fix(x,#1): y",
            "body": "Grain: x -- lane myia-po-2023:CoursIA"}]
    lec = lecture([issue(1)], prs=prs)
    r = vc.bilan([etat(lec, 1)], lec, NOW)
    assert r["roles"]["revue"]["issues"] == 1
    assert r["revue_prs"] == [{"numero": 1, "pr": 900}]


def test_bilan_exclut_tout_marathon_des_agregats():
    """Tous les marathons sont harnais, ecart ou non : la mesure du 20/11
    (443 issues hors marathons, 87 a 0 visite dont 59 d'urne et 12 de revue)
    sort les 16 marathons des roles du pool."""
    etats_ = [_etat(1),
              _etat(26070, titre="Marathon", ecart="LIVREE",
                    motif="[INFO] candidate-delivered"),
              _etat(26510, titre="Parite Rust")]
    r = vc.bilan(etats_, lecture([]), NOW)
    assert r["issues"] == 3 and r["hors_marathon"] == 1
    assert r["sans_visite"] == 1
    assert r["roles"]["harnais"]["issues"] == 2
    assert r["roles"]["urne"]["issues"] == 0


def test_ligne_dashboard_bornee():
    etats_ = [_etat(numero=n) for n in range(1, 121)] + [_etat(200, visites=2)]
    r = vc.bilan(etats_, lecture([]), NOW)
    code = 1 if (r["invariant"]["viole"] or r["urgences"]["nombre"]) else 0
    ligne = vc.ligne_dashboard(r, code)
    assert len(ligne) <= 200
    assert ligne.startswith("Couverture #27590") and "rc 1" in ligne
    assert "invariant VIOLE" in ligne


# --- les codes de sortie de main --------------------------------------------

def _dossier(tmp_path: Path, issues: list[dict], prs=None) -> Path:
    (tmp_path / "issues.json").write_text(json.dumps(issues), encoding="utf-8")
    (tmp_path / "prs_ouvertes.json").write_text(json.dumps(prs or []), encoding="utf-8")
    (tmp_path / "meta.json").write_text(
        json.dumps({"fetched_at": NOW.strftime("%Y-%m-%dT%H:%M:%SZ")}), encoding="utf-8")
    return tmp_path


def _sans_reseau(argv, timeout):
    return ""


def _panne(argv, timeout):
    raise subprocess.CalledProcessError(1, argv, output="", stderr="HTTP 401")


def test_main_rc0_tout_est_couvert(tmp_path, capsysbinary):
    issues = [issue(1),  # servable, a zero visite : seul du pool
              issue(2, labels=["candidate-delivered"],
                    comments=[com(2, f"[CLAIMED] lane {AUTRE} -- urne")]),
              issue(26071, titre="Marathon II -- jumeau")]  # harnais, hors agregats
    dossier = _dossier(tmp_path, issues)
    code = vc.main(["--lecture", str(dossier), "--json"], run=_sans_reseau)
    r = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0
    assert r["hors_marathon"] == 2 and r["sans_visite"] == 1
    assert r["roles"]["harnais"]["issues"] == 1
    assert r["urgences"]["nombre"] == 0 and r["invariant"]["viole"] is False


def test_main_rc1_invariant_viole(tmp_path, capsysbinary):
    # la consolidation echappe a LIVREE/MERGEE : deux claims y sont deux visites
    deux = [com(120, f"[CLAIMED] lane {AUTRE} -- a"), com(90, f"[CLAIMED] lane {AUTRE} -- b")]
    issues = [issue(1), issue(2, labels=["consolidation"], comments=deux)]
    dossier = _dossier(tmp_path, issues)
    code = vc.main(["--lecture", str(dossier), "--json"], run=_sans_reseau)
    r = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 1
    assert r["invariant"]["viole"] and r["invariant"]["a_zero"] == [1]
    assert r["invariant"]["a_deux"] == [2]


def test_main_rc1_urgence_urne_sans_visite(tmp_path, capsysbinary):
    issues = [issue(1, labels=["candidate-delivered"], cree="2026-09-01T00:00:00Z")]
    dossier = _dossier(tmp_path, issues)
    code = vc.main(["--lecture", str(dossier)], run=_sans_reseau)
    out = capsysbinary.readouterr().out.decode("utf-8")
    assert code == 1
    assert "Urgences" in out and "#1" in out


def test_main_rc2_lecture_incomplete_sans_secours(capsysbinary):
    code = vc.main(["--cache-s", "0"], run=_panne, maintenant=NOW)
    capture = capsysbinary.readouterr()
    assert code == 2
    assert capture.out == b""  # jamais un faux 0
    assert "jamais un faux 0" in capture.err.decode("utf-8")


def test_main_dashboard_line_bornee(tmp_path, capsysbinary):
    dossier = _dossier(tmp_path, [issue(1)])
    code = vc.main(["--lecture", str(dossier), "--dashboard-line"], run=_sans_reseau)
    ligne = capsysbinary.readouterr().out.decode("utf-8").strip()
    assert code == 0 and len(ligne) <= 200 and ligne.endswith("rc 0")


# --- la propriete du tapis (le test le plus important) ----------------------

def _pool(nb: int = 30) -> list[tr.Etat]:
    """Trente servables : visites initiales 0, 1, 2 et ages varies."""
    return [_etat(numero=100 + k,
                  cree=(NOW - timedelta(days=6 + 13 * k)).strftime("%Y-%m-%dT%H:%M:%SZ"),
                  visites=(0, 1, 2)[k % 3], visites_total=(0, 1, 2)[k % 3])
            for k in range(nb)]


def _servir(etats_: list[tr.Etat], graine: str, pas: int = 120) -> None:
    """Le service reel : servir la tete de l'ordre, incrementer ses visites."""
    conso = te.familles_consolidation(etats_)
    for i in range(pas):
        servi = te.ordre(etats_, etats_, graine, NOW)[0]
        zero = [e for e in etats_ if e.visites == 0]
        if zero:
            # aucune issue ne passe a deux visites tant qu'une autre est a zero
            assert servi.visites == 0, (
                f"pas {i} : #{servi.numero} servie a {servi.visites} visite(s) "
                f"pendant que #{zero[0].numero} est a 0")
        niveaux = [te.niveau(e, conso, NOW) for e in etats_]
        assert te.niveau(servi, conso, NOW) <= min(niveaux) + 1e-9, f"pas {i}"
        servi.visites += 1
        servi.visites_total += 1


def test_propriete_du_tapis_une_visite_chacun_avant_deux():
    _servir(_pool(), f"{LANE}|2026-11-20|3")


def test_propriete_du_tapis_autre_graine_et_deuxieme_lane():
    _servir(_pool(), f"{AUTRE}|2026-11-20|1")
    _servir(_pool(), "myia-po-2025:CoursIA-2|2026-11-20|5")


# --- l'atteignabilite : le claim de la lane n'est pas une violation ---------

def test_un_claim_visite_de_la_lane_n_est_pas_une_violation_d_equite():
    """Un claim que la lane tient en tete n'est pas une issue republiee.

    `atteignable` mesure l'equite sur le meme pool que `invariant` : le pool
    exclut les claims de la lane. La boucle de controle doit les exclure
    aussi, sinon l'organe rend rc 1 sur le fonctionnement normal du tirage
    (le coordinateur tient des claims) et masque les vraies violations.

    Sans cette exclusion, le test echoue : le claim passe en tete de tour
    (c'est ce que fait `ordonner`), il est donc servi alors que les deux
    jamais-visitees attendent -- et l'organe le compte comme une violation.
    """
    etats_ = [_etat(numero=1, visites=2, visites_total=2, mon_claim=True),
              _etat(numero=2, visites=0),
              _etat(numero=3, visites=0)]
    r = vc.atteignable(etats_, LANE, NOW)
    assert r["equite"] == []
    assert r["jamais_visitees"] == 2

# --- le parcage Origami : le role suit le tirage -----------------------------

def test_le_parcage_origami_passe_le_role_de_worker_a_attente(monkeypatch):
    """Un EPIC Origami parqué n'est pas un travail de worker : son depliage est
    reserve au coordinateur. Sans le parcage, l'organe le comptait « worker »
    alors que le tirage ne le sert jamais (mesure du 21/11 : cinq sur
    vingt et un)."""
    etats_ = [_etat(numero=18205, titre="EPIC origami : geometrie differentielle")]
    monkeypatch.setattr(
        vc.tapis_origami, "mesurer",
        lambda lecture, **kw: ({18205: "pli non deplie"},
                               {"measured": True, "parked": [18205],
                                "reason": "mesure faite"}))
    vc.parer_origami(etats_, None)
    assert etats_[0].ecart == "ORIGAMI"
    assert vc.role(etats_[0]) == "attente"


def test_une_mesure_origami_en_panne_ne_parque_rien(monkeypatch):
    """fail-OPEN, comme le tirage : une mesure absente ne fait pas disparaitre
    une issue du pool, elle se dit."""
    etats_ = [_etat(numero=18205, titre="EPIC origami : geometrie differentielle")]
    monkeypatch.setattr(
        vc.tapis_origami, "mesurer",
        lambda lecture, **kw: ({}, {"measured": False, "parked": [],
                                    "reason": "rejeu hors ligne"}))
    etat = vc.parer_origami(etats_, None)
    assert etats_[0].ecart is None
    assert vc.role(etats_[0]) == "worker"
    assert etat["measured"] is False
