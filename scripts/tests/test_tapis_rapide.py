"""Tests de `coordination/tapis_rapide.py`, la voie legere du tirage (#22983).

Chaque ecart est teste avec son cas voisin qui n'ecarte pas ; puis la variete,
la priorite legere, la graine, la CLI et la structure (plafonds de lignes).
Aucun test ne touche le reseau : les lectures sont construites en memoire.
"""
import ast
import json
import subprocess
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk
from coordination import tapis_rapide as tr
from coordination import tapis_hors_flotte as thf

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


def test_label_pause_exclut_le_grain_quelle_que_soit_la_casse():
    """I5 (#28114) : la pause est une DONNEE (un label), pas une memoire.

    Le nom GitHub est libre : `Pause` et `pause` sont le meme label. Un grain
    qui ne porte pas le label reste servable -- la regle ne vise que lui.
    """
    lec = lecture([issue(1, labels=["pause"]), issue(2, labels=["Pause"]),
                   issue(3, labels=["bug"])])
    assert etat(lec, 1).ecart == "LABEL" and etat(lec, 2).ecart == "LABEL"
    assert "pause" in etat(lec, 1).motif
    assert etat(lec, 3).ecart is None


def test_le_role_d_un_grain_en_pause_est_attente():
    """La pause est une ATTENTE ; l'urne de cloture reste l'urne."""
    from coordination import visit_coverage
    lec = lecture([issue(1, labels=["pause"]), issue(2, labels=["candidate-delivered"])])
    assert visit_coverage.role(etat(lec, 1)) == "attente"
    assert visit_coverage.role(etat(lec, 2)) == "urne"


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
    # Raccord du classement (c3274) : une citation Git est un PASSAGE, pas
    # une visite -- elle ne rajeunit plus le dernier grain. L'ecart reste
    # nul : une citation n'a toujours ete ni une livraison ni une exclusion.
    assert e2.ecart is None
    assert e2.derniere_visite is None
    assert e2.etat_grain == "passage_seul"
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
    assert borne.ecart is None and borne.notes == [f"claim borne de {AUTRE}"]
    assert borne.occupes == [(AUTRE, "a/b/**")]  # le chemin entier, jamais tronque
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


def test_pause_explicite_ecarte_sans_delai():
    """#27726 : un [RELEASED] qui porte `attend: #N` ecarte le grain SANS
    delai. Au-dela des 3 jours de RELACHEE, la condition tient encore : la
    cible citee (#27553) est ouverte."""
    pause = com(24 * 5, f"[RELEASED] lane {AUTRE} -- en attente du GO\nattend: #27553")
    lec = lecture([issue(1, comments=[pause]), issue(27553),
                   issue(2, comments=[com(24 * 5,
                                          f"[RELEASED] lane {AUTRE} -- attente\nattend: Q-c.2344a")])])
    e1 = etat(lec, 1)
    assert e1.ecart == "PAUSE"
    assert "attend #27553" in e1.motif      # le motif nomme la condition
    assert etat(lec, 2).ecart == "PAUSE"    # une question user : meme code


def test_pause_levee_et_reprise_par_un_marqueur_posterieur():
    """La condition se leve quand la cible citee est fermee ; un marqueur
    posterieur rend le grain de nouveau servable."""
    pause = com(24 * 5, f"[RELEASED] lane {AUTRE} -- attente\nattend: #27553")
    # la cible (#27553) n'est plus dans la lecture : elle est fermee -> levee
    assert etat(lecture([issue(1, comments=[pause])]), 1).ecart is None
    # la cible est ouverte -> la pause tient
    lec = lecture([issue(1, comments=[pause]), issue(27553)])
    assert etat(lec, 1).ecart == "PAUSE"
    # un marqueur posterieur : l'issue redevient servable
    lec = lecture([issue(1, comments=[pause, com(2, f"[CLAIMED] lane {AUTRE} -- je reprends")]),
                   issue(27553)])
    assert etat(lec, 1).ecart == "RECLAMEE"


def test_pause_une_pr_ciblee_et_le_role_d_attente():
    """La cible peut etre une PR ouverte ; le role du code PAUSE est
    l'attente (visit_coverage), pas un role de service."""
    from coordination import visit_coverage as vc
    pause = com(24 * 5, f"[RELEASED] lane {AUTRE} -- attente du merge\nattend: #27900")
    prs = [{"number": 27900, "title": "Fix(x,#1): y", "body": f"Grain: x -- lane {AUTRE}"}]
    lec = lecture([issue(1, comments=[pause])], prs=prs)
    assert etat(lec, 1).ecart == "PAUSE"     # la PR citee est encore ouverte
    assert etat(lecture([issue(1, comments=[pause])]), 1).ecart is None  # fermee -> levee
    e = tr.Etat(numero=1, titre="Grain", labels=[], cree_le="2026-10-01T00:00:00Z",
                 parent=None, famille=1, conteneur=False, consolidation=False,
                 ecart="PAUSE", motif="pause de x il y a 5.0 j : attend #27900")
    assert vc.role(e) == "attente"


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


# --- hors flotte (#17713, #26893) -------------------------------------------

def test_hors_flotte_les_quatre_formes_declarees():
    for corps in (
        "Hors flotte — Marathon II. Part of #26078 ; See #26070.",
        "**Hors flotte** — Marathon II.",
        "- Hors flotte — Epic #26070, parent #26081.",
        "**Travail hors flotte déjà en cours par root dans la session Marathon II.**",
        "**État du 16 novembre 2026 — livré hors flotte sous #26070 / #26078.**",
        "Contexte.\n\nSuivi Marathon II hors flotte #17713. Livraison groupée.",
    ):
        assert thf.hors_flotte_declaration(corps), corps[:40]


def test_hors_flotte_prose_citation_et_code_ne_declarent_pas():
    for corps in (
        "Deux PRs ont fermé la même issue : #26598, une session hors flotte ouverte le 14/11.",
        "1. **`--claim` saute la jambe.** Le chemin parle d'une session hors flotte.",
        "> Hors flotte — Marathon II. Part of #26078.",
        # faux positifs mesures (#10643, #25509) : une puce ou un bloc qui
        # decrit une livraison cloud cite la regle, l'EPIC reste de flotte.
        "> - **Parcours visiteur POSIX (clone vierge)** : #25469 — session "
        "hors flotte #17713, clone vierge rejoue.",
        "- **Une PR par README.** Une livraison hors flotte #17713 couvre "
        "la vague batch20.",
        "Exemple :\n```\nHors flotte — Marathon II.\n```",
        "",
    ):
        assert thf.hors_flotte_declaration(corps) is None, corps[:40]


def test_ecart_hors_flotte_domine_le_label():
    lec = lecture([issue(1, labels=["candidate-delivered"],
                         body="Hors flotte — Marathon II."),
                   issue(2, body="Texte ordinaire de flotte.")])
    e1, e2 = etat(lec, 1), etat(lec, 2)
    assert e1.ecart == "HORSFLOTTE" and "#17713" in e1.motif
    assert e2.ecart is None


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
    # Raccord du classement (c3274) : la derniere visite est le dernier
    # GRAIN -- ici le marqueur de livraison. Le commit, plus recent, n'est
    # qu'un passage : il ne rajeunit pas le grain.
    assert e13.derniere_visite == _h(30)
    assert e13.etat_grain == "grain"
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


def test_une_seule_famille_garde_ses_invariants():
    lec = lecture([
        issue(1, titre="[EPIC] Racine", cree="2026-01-01T00:00:00Z"),
        issue(2, body="Part of #1", cree="2026-01-01T00:00:00Z"),
        issue(3, body="Part of #1", cree="2026-03-01T00:00:00Z"),
        issue(4, body="Part of #1", comments=[com(100, f"[CLAIMED] lane {AUTRE} -- paths: a")]),
        issue(5, body="Part of #1", comments=[com(300, f"[CLAIMED] lane {AUTRE} -- paths: b")]),
    ])
    file = tr.ordonner(tr.etats(lec, LANE, NOW), LANE, NOW, 8)
    ordre = [e.numero for e in file]
    # parmi les grains, les jamais visites devant les visites (niveau 0, puis 1)
    assert set(ordre[:2]) == {2, 3}
    # les deux grains visites une fois forment le niveau 1, decale par lane
    # comme le niveau 0 (tapis_equilibre) ; le conteneur, meme jamais visite,
    # en dernier : il demande une lecture et un --paths (#26926)
    assert set(ordre[2:4]) == {4, 5} and ordre[4] == 1


def test_deux_lanes_ne_prennent_pas_la_meme_tete_de_famille():
    """Mesure du 14/11 : deux sieges ont recu les memes grains, parce que
    l'ordre des membres d'une famille ne dependait pas de la lane.

    La tete d'un niveau tourne d'une lane a l'autre (le decalage depend de la
    graine, donc de la lane). Deux lanes particularieres peuvent colliding par
    hasard -- la tete est une FONCTION de la graine, pas un tirage sans
    rappel : l'assertion porte donc sur l'ensemble des lanes, ou la
    diversification est une consequence et non une chance."""
    lec = lecture([issue(1, titre="[EPIC] Racine", cree="2026-01-01T00:00:00Z")]
                  + [issue(k, body="Part of #1", cree=f"2026-02-0{k - 1}T00:00:00Z")
                     for k in (2, 3, 4, 5)])
    etats_ = tr.etats(lec, LANE, NOW)
    lanes = (LANE, AUTRE, "myia-po-2025:CoursIA-2", "myia-po-2026:CoursIA",
             "myia-po-2028:CoursIA", "myia-po-2023:CoursIA", "myia-po-2024:CoursIA")
    tetes = {lane: tr.ordonner(etats_, lane, NOW, 8)[0].numero for lane in lanes}
    assert len(set(tetes.values())) > 1, tetes


def test_le_decalage_est_deterministe_pour_une_lane_et_une_tranche():
    lec = lecture([issue(1, titre="[EPIC] Racine", cree="2026-01-01T00:00:00Z")]
                  + [issue(k, body="Part of #1", cree=f"2026-02-0{k - 1}T00:00:00Z")
                     for k in (2, 3, 4, 5)])
    etats_ = tr.etats(lec, LANE, NOW)
    debut = NOW.replace(hour=12, minute=0)
    premier = [e.numero for e in tr.ordonner(etats_, LANE, debut, 8)]
    # la meme lane, la meme tranche de quatre heures : la meme tete
    assert premier == [e.numero for e in tr.ordonner(etats_, LANE,
                                                     debut.replace(hour=15, minute=59), 8)]
    # la tranche suivante change le tirage, jamais les invariants
    autre = [e.numero for e in tr.ordonner(etats_, LANE, debut.replace(hour=16), 8)]
    assert set(autre[:4]) == {2, 3, 4, 5}
    assert autre.index(1) > max(autre.index(k) for k in (2, 3, 4, 5))


def test_quota_de_conteneurs_puis_complement():
    epics = [issue(100 + k, titre=f"[EPIC] racine {k}") for k in range(10)]
    grains = [issue(200 + k) for k in range(10)]
    file = tr.ordonner(tr.etats(lecture(epics + grains), LANE, NOW), LANE, NOW, 8)
    assert len(file) == 8 and sum(e.conteneur for e in file) == 2  # quota 8 x 0,25
    peu = tr.ordonner(tr.etats(lecture(epics + grains[:3]), LANE, NOW), LANE, NOW, 8)
    assert len(peu) == 8 and sum(not e.conteneur for e in peu) == 3  # les Epics completent


def test_graine_par_lane_et_par_tranche_de_quatre_heures():
    etats_ = tr.etats(lecture(_familles(30)), LANE, NOW)

    def liste(lane: str, quand: datetime) -> list[int]:
        return [e.numero for e in tr.ordonner(etats_, lane, quand, 8)]

    debut = NOW.replace(hour=12, minute=0)
    assert liste(LANE, debut) != liste(AUTRE, debut)
    assert liste(LANE, debut) == liste(LANE, debut.replace(hour=15, minute=59))


# --- CLI --------------------------------------------------------------------

def _panne(argv, timeout):
    raise subprocess.CalledProcessError(1, argv, output="", stderr="HTTP 401")


def test_cli_lecture_en_panne_code_3_sans_tapis_lourd(capsys):
    """Sans secours, rien n'est servi -- et rien ne renvoie au tapis lourd (#26926)."""
    assert tr.main(["--lane", LANE, "--cache-s", "0", "--voie", "lourd"], run=_panne, maintenant=NOW) == 3
    err = capsys.readouterr().err
    assert "Lecture incomplete (issues" in err
    assert "pick_idle_grain" not in err and "Ne tirez pas le tapis lourd" in err


def _cache(dossier: Path, age_s: float, lec: gh_bulk.Lecture) -> None:
    import dataclasses
    import time
    dossier.mkdir(parents=True, exist_ok=True)
    brut = {**dataclasses.asdict(lec), "_epoch": time.time() - age_s}
    (dossier / "lecture-45j.json").write_text(json.dumps(brut), encoding="utf-8")


def test_cli_lecture_en_panne_tire_sur_le_cache_de_secours(tmp_path, monkeypatch, capsysbinary):
    """Une panne reseau tire sur la derniere lecture COMPLETE de moins de 12 h,
    et le dit dans la ligne de lecture ; au-dela de 12 h, sortie 3 (#26926)."""
    lec = lecture([issue(7, titre="Grain du cache")])
    lec.lu_a = tr._iso(NOW - timedelta(hours=2))
    monkeypatch.setattr(tr.gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    monkeypatch.setattr(tr.tapis_origami, "mesurer", lambda *a, **k: (
        {}, {"active": False, "measured": False, "parked": [], "reason": "test"}))
    _cache(tmp_path, 3 * 3600, lec)
    monkeypatch.setattr(tr.gh_bulk, "lire_tout", lambda *a, **k: (_ for _ in ()).throw(
        gh_bulk.LectureIncomplete("issues", 1, "HTTP 502")))
    assert tr.main(["--lane", LANE, "--voie", "lourd"], run=_panne, maintenant=NOW) == 0
    capture = capsysbinary.readouterr()
    out, err = capture.out.decode("utf-8"), capture.err.decode("utf-8")
    assert "#7 Grain du cache" in out and "lecture reseau en echec (issues" in out
    assert "lecture de secours" in err and "pick_idle_grain" not in out + err
    _cache(tmp_path, 13 * 3600, lec)
    assert tr.main(["--lane", LANE, "--voie", "lourd"], run=_panne, maintenant=NOW) == 3


def test_conteneur_servi_apres_les_grains_avec_sa_procedure_paths():
    """Un conteneur ne passe jamais devant un grain, et sa commande porte
    `--paths` : sans elle, check_lane_claim refuse le conteneur entier des
    qu'une autre lane y tient un claim borne (6 sur #19297, 16/11)."""
    borne = com(2, f"[OVERRIDE] lane {AUTRE} -- paths: MyIA.AI.Notebooks/Search/**, "
                   "MyIA.AI.Notebooks/Sudoku/Sudoku-12-Long-Chemin-De-Fichier.ipynb")
    lec = lecture([issue(1, titre="[EPIC] racine", labels=["consolidation"], comments=[borne]),
                   issue(2), issue(3)],
                  prs=[{"number": 900, "title": "Fix(x,#1): y", "body": ""}])
    etats_ = tr.etats(lec, LANE, NOW)
    file = tr.ordonner(etats_, LANE, NOW, 8)
    assert [e.conteneur for e in file] == [False, False, True]
    r = tr.rapport(lec, etats_, file, LANE, NOW, "g")
    g = r["grains"][-1]
    assert g["avant_d_editer"] == f"python scripts/check_lane_claim.py 1 --lane {LANE} " \
                                  "--paths <vos chemins>"
    assert "gh issue view 1 --comments" in g["procedure"]
    assert g["chemins_occupes"][0]["paths"].endswith("Sudoku-12-Long-Chemin-De-Fichier.ipynb")
    assert g["prs_ouvertes"] == [900]
    assert "--paths" not in r["grains"][0]["avant_d_editer"]  # un grain : la commande nue
    sortie = tr.texte(r, "test")
    assert "[CONTENEUR]" in sortie and "Sudoku-12-Long-Chemin-De-Fichier.ipynb" in sortie


def test_cli_mesure_origami_en_panne_sort_0_et_la_cause(monkeypatch, capsysbinary):
    """Une protection auxiliaire en panne n'eteint pas le tirage (#26528).

    Le parcage Origami est une protection **auxiliaire** ; le tapis rapide est
    le tirage de reference de toute la flotte. Une mesure impossible laisse la
    sortie a `0`, la cause nommee, un avertissement sur stderr -- et l'EPIC
    Origami **sert**, parce que rien n'a ete mesure.
    """
    lec = lecture([issue(19309, titre="[EPIC Origami] Le chantier long"),
                   issue(7, titre="Grain ordinaire")])
    monkeypatch.setattr(tr.gh_bulk, "lire_tout", lambda *a, **k: lec)
    monkeypatch.setattr(tr.tapis_origami, "mesurer", lambda *a, **k: (
        {}, {"active": True, "measured": False, "parked": [],
            "reason": "mesure en echec (RuntimeError: reseau indisponible)"}))

    code = tr.main(["--lane", LANE, "--cache-s", "0", "--voie", "lourd"],
                    run=lambda argv, timeout: "",
                    maintenant=NOW)
    capture = capsysbinary.readouterr()
    out, err = capture.out.decode("utf-8"), capture.err.decode("utf-8")
    assert code == 0
    assert "Parcage Origami : NON MESURE" in out and "mesure en echec" in out
    assert "Mesure Origami impossible" in err and "mesure en echec" in err
    assert "#19309" in out  # l'EPIC Origami est servi : rien n'a ete ecarte


def test_cli_json_porte_la_mesure_non_faite(monkeypatch, capsysbinary):
    """Le `--json` nomme la cause : jamais un etat vide qui se lit « rien »."""
    lec = lecture([issue(19309, titre="[EPIC Origami] Le chantier long")])
    monkeypatch.setattr(tr.gh_bulk, "lire_tout", lambda *a, **k: lec)
    monkeypatch.setattr(tr.tapis_origami, "mesurer", lambda *a, **k: (
        {}, {"active": True, "measured": False, "parked": [],
            "reason": "mesure en echec (RuntimeError: reseau indisponible)"}))

    code = tr.main(["--lane", LANE, "--cache-s", "0", "--json", "--voie", "lourd"],
                    run=lambda argv, timeout: "", maintenant=NOW)
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0
    assert sortie["origami_parking"]["measured"] is False
    assert "mesure en echec" in sortie["origami_parking"]["reason"]


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
                                               "votre PR #900 la cite : portez-la au merge",
                                               "feuille": True}]
    assert sortie["lecture"]["issues"] == 7 and sortie["maintenant"] == tr._iso(NOW)
    # L'assiette (#25082) : le tirage dit combien de feuilles il sert.
    assert (sortie["lecture"]["servables_feuilles"] + sortie["lecture"]["servables_conteneurs"]
            == sortie["lecture"]["servables"])
    assert sortie["lecture"]["servables_conteneurs"] == 3  # les 3 familles de l'EPIC
    assert set(sortie) >= {"grains", "vos_prs", "ecartees", "lecture"}


def test_cli_pool_vide_dit_en_clair(tmp_path, capsysbinary):
    dossier = _dossier(tmp_path, [issue(1, labels=["candidate-delivered"])], [])
    assert tr.main(["--lane", LANE, "--lecture", str(dossier)],
                   run=lambda argv, timeout: "") == 0
    sortie = capsysbinary.readouterr().out.decode("utf-8")
    assert "Pool vide" in sortie and "LABEL 1" in sortie
    assert "traitez d'abord leurs nits" in sortie


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
    for nom in ("tapis_rapide.py", "tapis_marqueurs.py", "tapis_hors_flotte.py",
                "gh_cache.py", "gh_cache_fichier.py", "tapis_service.py",
                "tapis_reverif.py"):
        assert _violations((COORD / nom).read_text(encoding="utf-8")) == [], nom
    temoin = "import subprocess\nfrom x import y as gh_bulk\ngh_bulk.run_defaut(['gh'], 9)\n"
    assert set(_violations(temoin)) == {"subprocess", "run_defaut()", "'gh'"}


# Plafonds releves une fois a la livraison (ecart MERGEE corrige, quota de conteneurs) ;
# un depassement se paie en extrayant un module, pas en relevant le plafond.
# tapis_marqueurs.py est la premiere extraction (lecture des marqueurs, 14/11) ;
# gh_cache.py la seconde (cache et verrou de la lecture, #22630, 14/11) ;
# gh_cache_fichier.py la troisieme (le fichier de cache : lire si frais, ecrire
# atomiquement -- extraction demandee par les replis de la review Hermes,
# #22630, 14/11 : le protocole a grandi de 41 lignes) ; tapis_service.py la
# quatrieme (ce que le tapis sert : procedure des conteneurs, secours, sortie
# texte, #26926, 16/11) ; gh_selection.py la cinquieme (le chemin de selection
# leger : metadonnees seules, budget global, #27223, 18/11) ; tapis_avantages.py
# la sixieme (les deux priorites legeres du mandat du 18/11) ; tapis_universel.py
# la septieme (la rotation universelle, #27223) ; tapis_reverif.py la huitieme
# (re-decision des grains servis au fil tronque sur leur fil complet, #27179,
# 18/11) ; gh_issues.py la neuvieme (la lecture ciblee des issues nommees,
# une porte pour tous les lecteurs cibles, #27225, 18/11) ; tapis_leger.py la
# dixieme (la voie LEGERE du tirage : classement sur metadonnees, qualification
# sur fil complet, #27225, 18/11) ; tapis_qualification.py la onzieme (la
# qualification d'un grain servi : corps, fil complet, vagues -- extraite de
# tapis_leger.py pour tenir le plafond, #27225, 18/11) ; tapis_fil_complet.py
# la douzieme (le fil COMPLET des seuls candidats retenus : lever le doute de
# la fenetre, #27225, 18/11) ; tapis_prise_en_charge.py la treizieme (le CLI
# de la prise en charge, extrait pour tenir le plafond, #27225, 18/11) ;
# tapis_fenetre.py la quatorzieme (la FENETRE du pool classe et celle du
# fil : le bloc qui avance et le cas de la fenetre de 12, #27225, 18/11) ;
# tapis_vagues.py la quinzieme (les VAGUES de la prise en charge : la file
# se remplit, 4 vagues au plus, #27225, 18/11) ; tapis_lot.py la seizeieme
# (la lecture d'un LOT de candidats : un VERDICT par numero demande, 19/11) ;
# tapis_rotation.py la dix-septieme (la ROTATION par numero d'issue : le bloc
# servi et le tour qui se ferme, 19/11) ; tapis_diff.py la dix-huitieme (la
# PREUVE par le diff : un marqueur DESIGNE une PR a verifier, 19/11) ;
# tapis_perimetre.py la dix-neuvieme (le PERIMETRE : ce qu'un glob certifie,
# l'attribution de l'issue et la livraison complete -- extrait de tapis_diff.py
# pour tenir le plafond, 19/11) ; tapis_preuve.py la vingtieme (la PREUVE
# elle-meme : le diff ET l'etat de la PR -- extrait de tapis_diff.py pour
# tenir le plafond, 19/11) ; gh_lecture.py la vingt-et-unieme (la LECTURE :
# son conteneur, son echec et la mise a plat d'une issue -- extrait de
# gh_bulk.py pour tenir le plafond, 19/11) ; tapis_non_tente.py la
# vingt-deuxieme (le grain NON TENTE : propose, jamais qualifie -- ni verdict
# terminal, ni refus de lecture ; il ne fige pas le curseur, 19/11) ;
# tapis_etat_schema.py la vingt-troisieme (le SCHEMA de l'etat : les classes,
# l'etat neuf, les accesseurs, extrait de tapis_etat.py pour tenir le
# plafond, 19/11) ; tapis_etat_commit.py la vingt-quatrieme (le COMMIT qui a
# ecrit l'etat : l'etat est lie au code qui l'a produit, 19/11) ;
# tapis_entrelace.py la vingt-cinquieme (le LOT entrelace : primaire et
# reprise alternes, la reprise passe devant un tour sur deux, 19/11).
# gh_bulk.py pour tenir le plafond, 19/11).
# 18/11) ; tapis_dernier_grain.py la vingt-sixieme (le DERNIER GRAIN d'une issue --
# grain, passage, absence etablie ou non mesurable -- et la regle des SEANCES,
# extraite de tapis_equilibre.py pour que le module du classement tienne son
# plafond, #27242, 19/11) ; tapis_citations.py la vingt-septieme (les citations des
# PRs OUVERTES : le travail en cours compte comme une visite, #27338) ;
# belt_equite.py la vingt-quatrieme (l'equite du dispatch : un grain deja servi ne
# passe pas devant les premieres visites, #27338) ; tapis_acceptance.py la
# vingt-cinquieme (les criteres d'acceptation de #25082 mesures sur le service
# effectif, 20/11) ; tapis_assiette.py la vingt-sixieme (la composition du pool :
# feuilles contre conteneurs, #25082, 21/11) ; tapis_attente.py la vingt-septieme
# (les ecarts d'ATTENTE : la remise de main et la pause explicite -- extrait de
# tapis_rapide.py pour tenir le plafond quand la fusion avec main y ajoute les
# ecarts de fond, #27726, 22/11) ; tapis_leger_texte.py la vingt-huitieme (la
# SORTIE TEXTE de la voie leger -- extraite de tapis_leger.py pour que la greffe
# du cap de livraisons tienne le plafond, #21067, 22/11) ;
# tapis_cap_livraisons.py la vingt-neuvieme (le CAP DE LIVRAISONS EPIC rebranche
# sur la voie de tirage reelle, #21067, 22/11) ; tapis_labels.py la
# trentieme (les EXCLUSIONS EN DONNEES : la table des labels qui ecartent un
# grain -- l'urne de cloture et la pause, #28114, 23/11) ;
# tapis_occupation.py la trente-et-unieme (l'OCCUPATION d'un grain : l'urne de
# cloture et la PR qui le tient, #28090, 22/11) ; tapis_leger_rapport.py la
# trente-deuxieme (le RAPPORT du tirage leger -- extrait pour que le cumul des deux
# organes du tapis tienne le plafond, #28090 + #27223, 22/11) ;
# tapis_leger_texte_occupation.py la trente-troisieme (la SECTION OCCUPATION
# de la sortie texte -- meme raison, la fonction `texte` passait 60 lignes,
# 22/11) ; tapis_relache.py la trente-quatrieme (la PORTEE d'un [RELEASED] :
# l'echec d'outil ne gele que la lane qui l'a rendu -- extrait pour que
# `tapis_attente` tienne son plafond, 24/11).

@pytest.mark.parametrize(("nom", "plafond"), [("gh_bulk.py", 260), ("tapis_rapide.py", 520),
                                              ("tapis_marqueurs.py", 130),
                                              ("tapis_hors_flotte.py", 60),
                                              ("gh_cache.py", 130),
                                              ("gh_cache_fichier.py", 60),
                                              ("tapis_service.py", 140),
                                              ("gh_selection.py", 140),
                                              ("tapis_avantages.py", 80),
                                              ("tapis_universel.py", 160),
                                              ("tapis_reverif.py", 120),
                                              ("gh_issues.py", 80),
                                              ("tapis_leger.py", 220),
                                              ("tapis_repli.py", 160),
                                              ("tapis_qualification.py", 140),
                                              ("tapis_fil_complet.py", 100),
                                              ("tapis_prise_en_charge.py", 90),
                                              ("tapis_fenetre.py", 70),
                                              ("tapis_vagues.py", 140),
                                              ("tapis_lot.py", 80),
                                              ("tapis_preuves.py", 80),
                                              ("tapis_rotation.py", 80),
                                              ("tapis_ancre.py", 140),
                                              ("tapis_avance.py", 60),
                                              ("tapis_non_tente.py", 60),
                                              ("tapis_etat.py", 95),
                                              ("tapis_etat_schema.py", 80),
                                              ("tapis_etat_commit.py", 100),
                                              ("tapis_entrelace.py", 40),
                                              ("tapis_retry.py", 50),
                                              ("tapis_tranche.py", 70),
                                              ("tapis_verdict.py", 50),
                                              ("tapis_composition.py", 60),
                                              ("tapis_position.py", 40),
                                              ("gh_lecture.py", 70),
                                              ("tapis_diff.py", 200),
                                              ("tapis_perimetre.py", 110),
                                              ("tapis_preuve.py", 110),
                                              ("tapis_public.py", 40),
                                              ("tapis_dernier_grain.py", 260),
                                              ("tapis_citations.py", 40),
                                              ("belt_equite.py", 110),
                                              ("tapis_tete.py", 30),
                                              ("tapis_ecarts_fond.py", 50),
                                              ("tapis_voie_leger.py", 40),
                                              ("tapis_acceptance.py", 300),
                                              ("tapis_assiette.py", 200),
                                              ("tapis_attente.py", 60),
                                              ("tapis_leger_texte.py", 80),
                                              ("tapis_cap_livraisons.py", 160),
                                              ("tapis_labels.py", 60),
                                              ("tapis_occupation.py", 298),
                                              ("tapis_leger_rapport.py", 50),
                                              ("tapis_leger_texte_occupation.py", 33),
                                              ("tapis_relache.py", 100)])

def test_plafonds_de_lignes(nom, plafond):
    texte = (COORD / nom).read_text(encoding="utf-8")
    assert len(texte.splitlines()) <= plafond
    for noeud in ast.walk(ast.parse(texte)):
        if isinstance(noeud, ast.FunctionDef | ast.AsyncFunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
