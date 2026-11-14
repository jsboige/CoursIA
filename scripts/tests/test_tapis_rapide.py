"""Tests de `coordination/tapis_rapide.py`, la voie legere du tirage (#22983).

Chaque ecart est teste avec son cas voisin qui n'ecarte pas ; puis la variete,
la priorite legere, la graine, la CLI et la structure (plafonds de lignes).
Aucun test ne touche le reseau : les lectures sont construites en memoire.
"""
import ast
import json
import subprocess
import sys
from collections import Counter
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk
from coordination import tapis_rapide as tr

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 13, 12, 0, tzinfo=UTC)
LANE = "myia-po-2024:CoursIA-2"
AUTRE = "myia-po-2027:CoursIA"
COORD = Path(__file__).resolve().parents[1] / "coordination"


def _h(heures: float) -> str:
    return tr._iso(NOW - timedelta(hours=heures))


def issue(n: int, titre: str = "", body: str = "", labels=(), comments=(),
          cree: str = "2026-10-01T00:00:00Z", total: int | None = None) -> dict:
    return {"number": n, "title": titre or f"Grain {n}", "body": body, "labels": list(labels),
            "created_at": cree, "comments": list(comments),
            "comments_total": len(comments) if total is None else total}


def com(heures: float, body: str) -> dict:
    return {"created_at": _h(heures), "author": "jsboige", "body": body}


def lecture(issues, prs=(), citations=None) -> gh_bulk.Lecture:
    return gh_bulk.Lecture(issues=list(issues), prs=list(prs), citations=citations or {})


def etat(lec: gh_bulk.Lecture, n: int, lane: str = LANE) -> tr.Etat:
    return next(e for e in tr.etats(lec, lane, NOW) if e.numero == n)


def commit(sha: str, heures: float) -> dict:
    return {"sha": sha, "date": _h(heures), "sujet": "Fix: x"}


# --- ecarts -----------------------------------------------------------------

def test_label_candidate_delivered():
    lec = lecture([issue(1, labels=["candidate-delivered"]), issue(2, labels=["bug"])])
    assert etat(lec, 1).ecart == "LABEL" and etat(lec, 2).ecart is None


def test_gel_par_le_body_et_non_par_une_mention():
    lec = lecture([issue(1, body="[FROZEN] attente du user\n\nContexte"),
                   issue(2, body="Contexte : on parle ici du marqueur [FROZEN] en passant.")])
    assert etat(lec, 1).ecart == "GEL" and etat(lec, 2).ecart is None


def test_gel_du_fil_et_degel_par_une_lane_habilitee():
    gel = com(30, "[FROZEN] gel de la campagne -- lane myia-po-2023:CoursIA")
    degel_ok = com(5, "[UNFROZEN] lane myia-ai-01:CoursIA -- reprise")
    degel_ko = com(5, "[UNFROZEN] lane myia-po-2023:CoursIA -- reprise")
    lec = lecture([issue(1, comments=[gel]), issue(2, comments=[gel, degel_ok]),
                   issue(3, comments=[gel, degel_ko])])
    assert etat(lec, 1).ecart == "GEL"
    assert etat(lec, 2).ecart is None
    assert etat(lec, 3).ecart == "GEL"


def test_parapluie_gele_en_dur_et_ses_enfants():
    lec = lecture([issue(11601, titre="[EPIC] gele"), issue(2, body="Part of #11601"),
                   issue(3)])
    assert etat(lec, 11601).ecart == "GEL" and etat(lec, 2).ecart == "GEL"
    assert etat(lec, 3).ecart is None


def test_livree_par_le_dernier_commentaire_seulement():
    info = com(10, "Grain: x\n[INFO] candidate-delivered -- lane myia-po-2028:CoursIA")
    lec = lecture([issue(1, comments=[info]),
                   issue(2, comments=[info, com(2, "Une remarque sans marqueur.")])])
    assert etat(lec, 1).ecart == "LIVREE" and etat(lec, 2).ecart is None


def test_delivered_sans_paths_contre_avec_paths_sur_consolidation():
    sans = com(10, f"[DELIVERED] lane {AUTRE} -- PR #900")
    avec = com(10, f"[DELIVERED] lane {AUTRE} -- PR #901 -- paths: a/b.ipynb")
    lec = lecture([issue(1, comments=[sans]),
                   issue(2, labels=["consolidation"], comments=[avec]),
                   issue(3, labels=["consolidation"], comments=[sans]),
                   issue(4, comments=[sans, com(2, f"[NOT-DELIVERED] lane {LANE} -- manque B")])])
    assert etat(lec, 1).ecart == "LIVREE"
    assert etat(lec, 2).ecart is None and etat(lec, 3).ecart is None
    assert etat(lec, 4).ecart is None


def test_commit_citant_contre_closure_review_keep():
    keep = com(1, "[CLOSURE REVIEW] verdict: KEEP \u2014 #2 (critere 3 non livre)")
    citations = {1: [commit("abc1234def", 5)], 2: [commit("abc1234def", 5)],
                 3: [commit("abc1234def", 24 * 50)], 4: [commit("abc1234def", 5)]}
    lec = lecture([issue(1), issue(2, comments=[keep]), issue(3),
                   issue(4, titre="[EPIC] conteneur")], citations=citations)
    e1 = etat(lec, 1)
    assert e1.ecart == "MERGEE" and e1.motif == "livraison probable, commit abc1234"
    assert etat(lec, 2).ecart is None  # rouverte par la revue
    assert etat(lec, 3).ecart is None  # hors de la fenetre de 45 jours
    assert etat(lec, 4).ecart is None  # un conteneur ne s'ecarte pas par un commit


def test_mergee_epargne_la_consolidation_et_les_simples_citations():
    vue = {**commit("abc1234def", 5), "ferme": False}
    citations = {1: [commit("abc1234def", 5)], 2: [vue], 3: [vue, commit("def5678abc", 3)]}
    lec = lecture([issue(1, labels=["consolidation"]), issue(2), issue(3)], citations=citations)
    assert etat(lec, 1).ecart is None  # une tranche de consolidation ne la livre pas
    e2 = etat(lec, 2)
    assert e2.ecart is None and e2.derniere_visite == _h(5)  # citee : une visite, pas une livraison
    assert etat(lec, 3).motif == "livraison probable, commit def5678"


def test_pr_ouverte_cite_un_grain_contre_un_conteneur():
    prs = [{"number": 900, "title": "Fix(x,#1): y", "body": "Grain: x -- lane myia-po-2023:CoursIA"},
           {"number": 901, "title": "Docs", "body": f"Grain: x -- lane {LANE}\n\nSee #3"},
           {"number": 902, "title": "Add", "body": "Part of #2 ; voir #1234"}]
    lec = lecture([issue(1), issue(2, labels=["EPIC"]), issue(3), issue(123)], prs=prs)
    assert etat(lec, 1).ecart == "COUVERTE" and "#900" in etat(lec, 1).motif
    assert etat(lec, 2).ecart is None
    assert etat(lec, 3).ecart == "COUVERTE" and "votre PR #901" in etat(lec, 3).motif
    assert etat(lec, 123).ecart is None  # #1234 ne couvre pas #123


def test_claims_vivant_perime_mien_et_borne():
    """Depuis PLAFOND, un [CLAIMED] d'une autre lane sur un CONTENEUR est
    une visite recente : il ecarte via PLAFOND (borne ou pas), avant RECLAMEE.
    La note « claim borne » ne survit que pour un [OVERRIDE] paths: (une
    remise de main n'est pas une visite au sens du plafond)."""
    lec = lecture([
        issue(1, comments=[com(2, f"[CLAIMED] lane {AUTRE} -- je prends")]),
        issue(2, comments=[com(60, f"[CLAIMED] lane {AUTRE} -- je prends")]),
        issue(3, comments=[com(3, f"[CLAIMED] lane {LANE} -- je prends")]),
        issue(4, labels=["EPIC"], comments=[com(2, f"[CLAIMED] lane {AUTRE} -- paths: a/b/**")]),
        issue(5, labels=["EPIC"], comments=[com(2, f"[CLAIMED] lane {AUTRE} -- tout l'EPIC")]),
        issue(7, labels=["EPIC"], comments=[com(2, f"[OVERRIDE] lane {AUTRE} -- paths: a/b/**")]),
        issue(6, comments=[com(4, f"[CLAIMED] lane {AUTRE}"), com(1, f"[RELEASED] lane {AUTRE}")]),
    ])
    assert etat(lec, 1).ecart == "RECLAMEE" and AUTRE in etat(lec, 1).motif
    assert etat(lec, 2).ecart is None
    mien = etat(lec, 3)
    assert mien.ecart is None and mien.mon_claim and mien.notes[0] == "votre claim"
    assert etat(lec, 4).ecart == "PLAFOND"  # un claim borne reste une visite
    assert etat(lec, 5).ecart == "PLAFOND"
    borne = etat(lec, 7)
    assert borne.ecart is None and borne.notes == [f"claim borne de {AUTRE} : a/b/**"]
    # Le claim est ferme, mais le [RELEASED] d'il y a 1 h tient l'issue a l'ecart.
    assert etat(lec, 6).ecart == "RELACHEE"


def test_relachee_trois_jours_puis_resservie():
    """Mesure po-2023 du 13/11 : #17183, #13106, #7291 resservies a chaque lane
    alors que leur dernier marqueur etait un [RELEASED] motive d'une autre lane."""
    rendue = f"[RELEASED] lane {AUTRE} -- barriere reelle, mesuree"
    lec = lecture([
        issue(1, comments=[com(24, rendue)]),
        issue(2, comments=[com(24 * 4, rendue)]),
        issue(3, comments=[com(24, rendue), com(2, f"[CLAIMED] lane {AUTRE} -- je reprends")]),
        issue(4, comments=[com(24, f"[RELEASED] lane {LANE} -- siege trop petit")]),
        issue(5, comments=[com(24, rendue), com(2, f"[NOT-DELIVERED] lane {LANE} -- reste B")]),
        issue(6, labels=["EPIC"], comments=[com(24, rendue)]),
    ])
    e1 = etat(lec, 1)
    assert e1.ecart == "RELACHEE" and AUTRE in e1.motif
    assert etat(lec, 2).ecart is None          # au-dela de RELACHE_J jours
    assert etat(lec, 3).ecart == "RECLAMEE"    # le dernier marqueur n'est plus le [RELEASED]
    assert etat(lec, 4).ecart == "RELACHEE"    # ma propre lane l'a rendue : pas de retour
    assert etat(lec, 5).ecart is None          # un [NOT-DELIVERED] la rouvre
    assert etat(lec, 6).ecart == "RELACHEE"    # un conteneur rendu aussi


def test_livree_info_avec_lane_avant_le_mot():
    """Forme de #20603 (13/11) : le mot vient apres `lane X --` sur la ligne du tag."""
    lec = lecture([
        issue(1, comments=[com(3, f"[INFO] lane {AUTRE} — candidate-delivered (cloture G.9)")]),
        issue(2, comments=[com(3, f"[INFO] lane {AUTRE} — pas candidate-delivered : reste B")]),
        issue(3, comments=[com(3, f"[INFO] lane {AUTRE} -- etat\n\ncandidate-delivered plus tard")]),
    ])
    assert etat(lec, 1).ecart == "LIVREE"
    assert etat(lec, 2).ecart is None  # nie juste avant le mot
    assert etat(lec, 3).ecart is None  # le mot n'est pas sur la ligne du tag


def test_plafond_epic_visite_par_une_autre_lane():
    """Le tapis ne sert pas un EPIC que le gate L898 refuserait (#22500) :
    visite d'une AUTRE lane de moins de 7 jours -- ici perimee pour RECLAMEE
    (plus de 48 h), seule PLAFOND peut l'ecarter."""
    visite = com(72, f"[CLAIMED] lane {AUTRE} -- tranche")
    livre = com(24 * 5, f"[DELIVERED] lane {AUTRE} -- PR #900")
    vieux = com(24 * 8, f"[CLAIMED] lane {AUTRE} -- ancienne visite")
    lec = lecture([issue(10, labels=["EPIC"], comments=[visite]),
                   issue(11, labels=["EPIC"], comments=[livre]),
                   issue(12, labels=["EPIC"], comments=[vieux])])
    e10 = etat(lec, 10)
    assert e10.ecart == "PLAFOND"
    assert e10.motif == f"plafond EPIC (#22500) : visite de {AUTRE} il y a 3.0 j (< 7 j)"
    assert etat(lec, 11).ecart == "PLAFOND"  # un [DELIVERED] est une visite
    assert etat(lec, 11).motif == f"plafond EPIC (#22500) : visite de {AUTRE} il y a 5.0 j (< 7 j)"
    assert etat(lec, 12).ecart is None  # la visite a plus de PLAFOND_EPIC_J jours


def test_plafond_epic_filles_et_exemptions():
    """Une fille creee visite son parent ; sa propre lane, la consolidation
    et les non-conteneurs n'arment rien (#25443 pour la lane)."""
    mienne = com(72, f"[CLAIMED] lane {LANE} -- ma visite d'avant")
    lec = lecture([
        issue(20, labels=["EPIC"]),                       # parent d'une fille neuve
        issue(21, body="Part of #20", cree=_h(24 * 2)),   # fille creee il y a 2 j
        issue(22, labels=["EPIC"], comments=[mienne]),    # visite de MA lane
        issue(23, labels=["EPIC", "consolidation"],
              comments=[com(72, f"[CLAIMED] lane {AUTRE} -- retour")]),
        issue(24, comments=[com(72, f"[CLAIMED] lane {AUTRE}")]),  # pas un conteneur
    ])
    e20 = etat(lec, 20)
    assert e20.ecart == "PLAFOND"
    assert e20.motif == "plafond EPIC (#22500) : sous-issue #21 creee il y a 2.0 j (< 7 j)"
    assert etat(lec, 22).ecart is None   # mes visites n'arment pas (#25443)
    assert etat(lec, 23).ecart is None   # consolidation exempte
    assert etat(lec, 24).ecart is None   # PLAFOND ne vise que les conteneurs


def test_mon_claim_remonte_en_tete():
    issues = [issue(n, cree=f"2026-0{1 + n % 9}-01T00:00:00Z") for n in range(1, 30)]
    issues.append(issue(99, cree="2026-11-01T00:00:00Z",
                        comments=[com(3, f"[CLAIMED] lane {LANE} -- reprise")]))
    file = tr.ordonner(tr.etats(lecture(issues), LANE, NOW), LANE, NOW, 8)
    assert file[0].numero == 99 and len(file) == 8


def test_marqueur_en_deuxieme_ligne_apres_grain():
    body = f"Grain: DEEP/notebook-python -- lane {AUTRE}\n[CLAIMED] lane {AUTRE} -- tranche 2"
    decor = f"Grain: x\n> **[CLAIMED]** lane {AUTRE} -- cite en bloc"
    code = f"Exemple :\n```\n[CLAIMED] lane {AUTRE}\n```"
    lec = lecture([issue(1, comments=[com(2, body)]), issue(2, comments=[com(2, decor)]),
                   issue(3, comments=[com(2, code)])])
    assert etat(lec, 1).ecart == "RECLAMEE" and etat(lec, 2).ecart == "RECLAMEE"
    assert etat(lec, 3).ecart is None  # un marqueur dans du code ne se pose pas


def test_l_ordre_des_ecarts_le_premier_gagne():
    lec = lecture([issue(1, labels=["candidate-delivered"], body="[FROZEN] x")],
                  citations={1: [commit("f" * 12, 2)]})
    assert etat(lec, 1).ecart == "LABEL"


def test_parent_famille_conteneur_et_derniere_visite():
    lec = lecture([issue(10, titre="Racine"), issue(11, body="Part of #10"),
                   issue(12, titre="[EPIC #11] Phase 2 : tranche"),
                   issue(13, titre="Fix(ci,#12): titre de tranche",
                         comments=[com(30, f"[DELIVERED] lane {AUTRE} -- paths: x")]),
                   issue(14, titre="[EPIC] sans parent")],
                  citations={13: [commit("a" * 12, 10)]})
    e12, e13 = etat(lec, 12), etat(lec, 13)
    assert (e12.parent, e12.famille, e12.conteneur) == (11, 10, True)
    assert (e13.parent, e13.famille) == (12, 10)
    assert etat(lec, 10).conteneur and etat(lec, 14).conteneur
    assert not etat(lec, 13).conteneur
    assert e13.derniere_visite == _h(10)  # le commit est plus recent que le marqueur
    assert etat(lec, 14).derniere_visite is None


# --- ordre ------------------------------------------------------------------

def _familles(nb: int, par_famille: int = 2, consolidation: int | None = None) -> list[dict]:
    issues = []
    for f in range(nb):
        racine = 1000 + 10 * f
        labels = ["consolidation"] if f == consolidation else []
        issues.append(issue(racine, labels=labels, cree="2026-11-01T00:00:00Z"))
        issues += [issue(racine + k, body=f"Part of #{racine}") for k in range(1, par_famille)]
    return issues


def test_variete_trente_familles_huit_grains():
    file = tr.ordonner(tr.etats(lecture(_familles(30)), LANE, NOW), LANE, NOW, 8)
    assert len(file) == 8 and len({e.famille for e in file}) == 8


def test_une_seule_famille_dans_l_ordre_de_visite():
    lec = lecture([
        issue(1, titre="[EPIC] Racine", cree="2026-01-01T00:00:00Z"),
        issue(2, body="Part of #1", cree="2026-01-01T00:00:00Z"),
        issue(3, body="Part of #1", cree="2026-03-01T00:00:00Z"),
        issue(4, body="Part of #1", comments=[com(100, f"[CLAIMED] lane {AUTRE} -- paths: a")]),
        issue(5, body="Part of #1", comments=[com(300, f"[CLAIMED] lane {AUTRE} -- paths: b")]),
    ])
    file = tr.ordonner(tr.etats(lec, LANE, NOW), LANE, NOW, 8)
    # jamais visitees (la plus ancienne, le grain avant son conteneur), puis la moins recente
    assert [e.numero for e in file] == [2, 1, 3, 5, 4]


def test_quota_de_conteneurs_puis_complement():
    epics = [issue(100 + k, titre=f"[EPIC] racine {k}") for k in range(10)]
    grains = [issue(200 + k) for k in range(10)]
    file = tr.ordonner(tr.etats(lecture(epics + grains), LANE, NOW), LANE, NOW, 8)
    assert len(file) == 8 and sum(e.conteneur for e in file) == 2  # quota 8 x 0,25
    peu = tr.ordonner(tr.etats(lecture(epics + grains[:3]), LANE, NOW), LANE, NOW, 8)
    assert len(peu) == 8 and sum(not e.conteneur for e in peu) == 3  # les Epics completent


def test_priorite_legere_sur_deux_mille_graines():
    etats_ = tr.etats(lecture(_familles(30, consolidation=7)), LANE, NOW)
    vus: Counter = Counter()
    for k in range(2000):
        vus.update({e.famille for e in tr.ordonner(etats_, LANE, NOW, 8, graine=f"g{k}")})
    conso = vus.pop(1070)
    assert conso > max(vus.values())
    assert len(vus) == 29 and min(vus.values()) >= 1


def test_vieil_epic_et_cumul_des_poids():
    lec = lecture([issue(1, titre="[EPIC] ancien", labels=["consolidation"],
                         cree="2026-06-01T00:00:00Z"),
                   issue(2, titre="[EPIC] recent", cree="2026-11-01T00:00:00Z")])
    poids = tr.poids_familles(tr.etats(lec, LANE, NOW), NOW)
    assert poids[1][0] == pytest.approx(tr.PRIO_CONSOLIDATION * tr.PRIO_VIEIL_EPIC)
    assert poids[1][1] == ["consolidation", "vieil EPIC #1"]
    assert poids[2] == (1.0, [])


def test_graine_par_lane_et_par_tranche_de_quatre_heures():
    etats_ = tr.etats(lecture(_familles(30)), LANE, NOW)

    def liste(lane: str, quand: datetime) -> list[int]:
        return [e.numero for e in tr.ordonner(etats_, lane, quand, 8)]

    debut = NOW.replace(hour=12, minute=0)
    assert liste(LANE, debut) != liste(AUTRE, debut)
    assert liste(LANE, debut) == liste(LANE, debut.replace(hour=15, minute=59))


# --- CLI --------------------------------------------------------------------

def test_cli_lecture_en_panne_code_3_et_repli(capsys):
    def run(argv, timeout):
        raise subprocess.CalledProcessError(1, argv, output="", stderr="HTTP 401")

    assert tr.main(["--lane", LANE, "--cache-s", "0"], run=run, maintenant=NOW) == 3
    err = capsys.readouterr().err
    assert "Lecture incomplete (issues" in err
    assert f"python scripts/pick_idle_grain.py --belt --lane {LANE}" in err


def _dossier(tmp_path: Path, issues: list[dict], prs: list[dict]) -> Path:
    (tmp_path / "issues.json").write_text(json.dumps(issues), encoding="utf-8")
    (tmp_path / "prs_ouvertes.json").write_text(json.dumps(prs), encoding="utf-8")
    (tmp_path / "meta.json").write_text(json.dumps({"fetched_at": tr._iso(NOW)}),
                                        encoding="utf-8")
    return tmp_path


def test_cli_json_sur_un_dossier(tmp_path, capsysbinary):
    prs = [{"number": 900, "title": "Ma PR", "body": f"Grain: x -- lane {LANE}\nSee #1",
            "created_at": _h(30)}]
    dossier = _dossier(tmp_path, _familles(3) + [issue(1)], prs)
    code = tr.main(["--lane", LANE, "--lecture", str(dossier), "--json"],
                   run=lambda argv, timeout: "")
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0 and len(sortie["grains"]) == 6
    assert sortie["vos_prs"] == [{"numero": 900, "titre": "Ma PR", "age_j": 1.2}]
    assert sortie["ecartees"]["COUVERTE"] == [{"numero": 1, "motif":
                                               "votre PR #900 la cite : portez-la au merge"}]
    assert sortie["lecture"]["issues"] == 7 and sortie["maintenant"] == tr._iso(NOW)
    assert set(sortie) >= {"grains", "vos_prs", "ecartees", "lecture"}


def test_cli_pool_vide_dit_en_clair(tmp_path, capsysbinary):
    dossier = _dossier(tmp_path, [issue(1, labels=["candidate-delivered"])], [])
    assert tr.main(["--lane", LANE, "--lecture", str(dossier)],
                   run=lambda argv, timeout: "") == 0
    sortie = capsysbinary.readouterr().out.decode("utf-8")
    assert "Pool vide" in sortie and "LABEL 1" in sortie
    assert "portez d'abord au merge celles de plus de 24 h" in sortie


def test_rapport_et_texte_portent_la_note_de_fetch():
    """Un fetch d'origin/main echoue se voit dans le rapport JSON et la sortie
    texte (ligne lecture) ; sans note, la ligne n'en parle pas."""
    lec = lecture([issue(1)])
    lec.fetch_note = "fetch origin/main impossible (x), pointe locale gardee"
    r = tr.rapport(lec, tr.etats(lec, LANE, NOW), [], LANE, NOW, "g")
    assert r["lecture"]["fetch_note"] == lec.fetch_note
    assert "; fetch origin/main impossible" in tr.texte(r, "test")
    lec.fetch_note = None
    r = tr.rapport(lec, tr.etats(lec, LANE, NOW), [], LANE, NOW, "g")
    assert r["lecture"]["fetch_note"] is None
    assert "fetch" not in tr.texte(r, "test")


# --- structure --------------------------------------------------------------

def _nom(noeud: ast.AST) -> str:
    return getattr(noeud, "id", "") or getattr(noeud, "attr", "")


def _violations(source: str) -> list[str]:
    """Ce qui lancerait un processus ; `run_defaut` passe en valeur injectee est permis."""
    vus = []
    for noeud in ast.walk(ast.parse(source)):
        if isinstance(noeud, ast.Import):
            vus += [a.name for a in noeud.names if a.name.split(".")[0] == "subprocess"]
        if isinstance(noeud, ast.ImportFrom) and (noeud.module or "").startswith("subprocess"):
            vus.append(noeud.module)
        if isinstance(noeud, ast.Name | ast.Attribute) and _nom(noeud) in {
                "subprocess", "Popen", "system", "popen"}:
            vus.append(_nom(noeud))
        if isinstance(noeud, ast.Call) and _nom(noeud.func) in {
                "run", "run_defaut", "lire_issues_ouvertes", "lire_prs_ouvertes",
                "lire_citations_mergees"}:
            vus.append(_nom(noeud.func) + "()")
        if isinstance(noeud, ast.Constant) and isinstance(noeud.value, str) \
                and noeud.value.strip() == "gh":
            vus.append("'gh'")
    return vus


def test_tapis_rapide_ne_lance_aucun_processus():
    for nom in ("tapis_rapide.py", "tapis_marqueurs.py", "gh_cache.py"):
        assert _violations((COORD / nom).read_text(encoding="utf-8")) == [], nom
    temoin = "import subprocess\nfrom x import y as gh_bulk\ngh_bulk.run_defaut(['gh'], 9)\n"
    assert set(_violations(temoin)) == {"subprocess", "run_defaut()", "'gh'"}


# Plafonds releves une fois a la livraison (ecart MERGEE corrige, quota de conteneurs) ;
# un depassement se paie en extrayant un module, pas en relevant le plafond.
# tapis_marqueurs.py est la premiere extraction (lecture des marqueurs, 14/11) ;
# gh_cache.py la seconde (cache et verrou de la lecture, #22630, 14/11).
@pytest.mark.parametrize(("nom", "plafond"), [("gh_bulk.py", 260), ("tapis_rapide.py", 520),
                                              ("tapis_marqueurs.py", 130),
                                              ("gh_cache.py", 130)])
def test_plafonds_de_lignes(nom, plafond):
    texte = (COORD / nom).read_text(encoding="utf-8")
    assert len(texte.splitlines()) <= plafond
    for noeud in ast.walk(ast.parse(texte)):
        if isinstance(noeud, ast.FunctionDef | ast.AsyncFunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
