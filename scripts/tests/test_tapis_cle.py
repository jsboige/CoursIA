#!/usr/bin/env python3
"""Les temoins de la CLE DE SERVICE (mandat du 19/11, `20261119-picker-date-pr-parent`).

« Remplacer poids/bonus/seances par une voix par issue, ordre de la derniere PR
dont le diff couvre le grain, departage uniforme a egalite ; sans PR,
vieillissement depuis la creation (pas d'anciennete heritee). Une PR enfant
remet aussi le hub en queue, pas les freres ; pas de nouveau service sur
correction de PR existante. »

Le temoin discriminant est le quartet **A / H / E / F** :

- **A** : une issue ancienne, sans PR ;
- **H** : un hub, dont l'enfant **E** a livre une PR ;
- **F** : le **frere** de E, sans PR.

La PR de E repousse **E et H**, **jamais F**. Et un pli **neuf** du meme hub
n'herite pas de l'age du hub : il attend depuis sa propre creation.

Aucun test ne touche le reseau.
"""
import ast
import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_cle, tapis_equilibre, tapis_universel

MAINTENANT = datetime(2026, 11, 19, 12, 0, tzinfo=UTC)
PR_DATE = "2026-11-19T08:00:00Z"


def _meta(n: int, titre: str, cree: str) -> dict:
    return {"number": n, "title": titre, "labels": [], "created_at": cree}


def _pr(n: int, corps: str, cree: str = PR_DATE, mis_a_jour: str | None = None) -> dict:
    return {"number": n, "title": f"PR {n}", "body": corps,
            "created_at": cree, "updated_at": mis_a_jour or cree}


def _etats(metas, prs=(), cites=None):
    """Les etats de la voie LEGERE (metadonnees seules), avec la cle posee."""
    return tapis_universel.etats_leger(metas, cites or {}, MAINTENANT, list(prs))


def _ordre(etats_):
    """L'ordre de la cle de service, rotation FAIR (la fenetre decide, pas le pool)."""
    return [e.numero for e in tapis_equilibre.ordre(
        etats_, etats_, "graine", MAINTENANT, rotation=False)]


# --- le temoin discriminant : A / H / E / F ---------------------------------

def test_la_pr_de_l_enfant_repousse_l_enfant_et_le_hub_jamais_le_frere():
    """Le cas nominal du mandat, sur la voie reelle (metadonnees seules).

    A : issue ancienne sans PR. H : le hub. E : l'enfant livre. F : le frere
    sans PR. La PR de E doit repousser E et H, et **jamais** F.
    """
    metas = [_meta(100, "Ancienne sans PR", "2024-01-01T00:00:00Z"),
             _meta(200, "[EPIC] Hub", "2020-01-01T00:00:00Z"),
             _meta(201, "[#200] Enfant livre", "2024-03-01T00:00:00Z"),
             _meta(202, "[#200] Frere sans PR", "2024-02-01T00:00:00Z")]
    prs = [_pr(900, "Part of #201")]
    etats_ = _etats(metas, prs)
    cles = {e.numero: e.cle_service for e in etats_}
    # E est couvert par la PR ; H, non -- mais il suit son enfant ; F, non.
    assert cles[201] == PR_DATE, "l'enfant livre est couvert par sa PR"
    assert cles[200] == PR_DATE, "le hub suit l'enfant"
    assert cles[202] is None, "le frere n'est pas couvert"
    assert cles[100] is None, "l'issue ancienne sans PR n'est pas couverte"
    ordre = _ordre(etats_)
    assert ordre.index(100) < ordre.index(202), ordre
    assert ordre.index(202) < ordre.index(200), ordre
    assert ordre.index(202) < ordre.index(201), ordre


def test_un_pli_neuf_n_herite_pas_de_l_age_du_hub():
    """« pas d'anciennete heritee » : un pli cree aujourd'hui attend depuis
    aujourd'hui, pas depuis la creation du hub (2020)."""
    metas = [_meta(100, "Ancienne sans PR", "2024-01-01T00:00:00Z"),
             _meta(200, "[EPIC] Hub", "2020-01-01T00:00:00Z"),
             _meta(203, "[#200] Pli neuf", "2026-11-19T00:00:00Z")]
    etats_ = _etats(metas)
    pli = next(e for e in etats_ if e.numero == 203)
    assert pli.cle_service is None
    assert pli.cree_le == "2026-11-19T00:00:00Z"
    ordre = _ordre(etats_)
    assert ordre.index(100) < ordre.index(203), \
        "le pli neuf a herite de l'age du hub (2020) : il passe devant"


# --- la forme canonique : une PR qui COUVRE, une PR qui MENTIONNE -----------

def test_la_forme_canonique_couvre_et_la_prose_non():
    """La distinction qui manquait : une PR qui **parle** de l'issue en prose
    ne la sert pas. C'est elle qui distingue la PR #27368 (qui parle de
    #27338) des huit PRs de travail (qui declarent `Part of #27338`)."""
    assert tapis_cle.est_canonique("Part of #27338", 27338)
    assert tapis_cle.est_canonique("See #27338", 27338)
    assert tapis_cle.est_canonique("Closes #27338", 27338)
    assert tapis_cle.est_canonique("Fix(coordination,#27338): la cle", 27338)
    assert not tapis_cle.est_canonique("Sur #27338, les 8 PRs sont canoniques", 27338)
    assert not tapis_cle.est_canonique("la PR #27368 parle de l'issue", 27338)
    assert not tapis_cle.est_canonique("rien ici", 27338)


def test_la_pr_qui_mentionne_en_prose_ne_couvre_pas():
    metas = [_meta(201, "Grain", "2024-03-01T00:00:00Z")]
    etats_ = _etats(metas, [_pr(900, "Sur #201, la correction avance")])
    assert next(e for e in etats_ if e.numero == 201).cle_service is None


def test_une_correction_d_une_pr_existante_n_est_pas_un_service_neuf():
    """La date d'une PR est sa **creation** : pousser une correction dans une
    PR ouverte ne la recree pas, et ne remet donc pas le grain en tete."""
    metas = [_meta(100, "Ancienne sans PR", "2024-01-01T00:00:00Z"),
             _meta(201, "Grain", "2024-03-01T00:00:00Z")]
    prs = [_pr(900, "Part of #201", cree="2026-11-01T00:00:00Z",
               mis_a_jour="2026-11-19T09:00:00Z")]
    etats_ = _etats(metas, prs)
    grain = next(e for e in etats_ if e.numero == 201)
    assert grain.cle_service == "2026-11-01T00:00:00Z", \
        "la cle suit la creation de la PR, pas sa derniere activite"
    assert _ordre(etats_).index(100) < _ordre(etats_).index(201)


def test_un_commit_merges_canonique_couvre_et_le_loose_non():
    metas = [_meta(201, "Grain", "2024-03-01T00:00:00Z")]
    canon = {201: [{"sha": "a" * 12, "date": "2026-11-18T09:00:00Z",
                    "sujet": "Closes #201", "ferme": True, "canonique": True}]}
    etats_ = _etats(metas, [], canon)
    assert next(e for e in etats_ if e.numero == 201).cle_service == "2026-11-18T09:00:00Z"


# --- la mesure, jamais un bonus ---------------------------------------------

def test_la_densite_est_une_mesure_elle_ne_classe_pas():
    """« Priorite des Epics par densite de 5 a 10 vrais enfants » : la densite
    se LIT, elle ne classe rien et ne declenche aucune creation."""
    metas = [_meta(200, "[EPIC] Hub", "2020-01-01T00:00:00Z"),
             _meta(201, "[#200] Enfant", "2024-03-01T00:00:00Z"),
             _meta(202, "[#200] Frere", "2024-02-01T00:00:00Z")]
    etats_ = _etats(metas)
    assert tapis_cle.densites(etats_) == {200: 2}


def test_module_pur_et_borne():
    """Fonctions pures : aucun import de processus ni de reseau. Plafond releve
    a la livraison ; un depassement se paie en extrayant, pas en relevant."""
    for module, plafond in ((tapis_cle, 150),):
        texte = Path(module.__file__).read_text(encoding="utf-8")
        assert len(texte.splitlines()) <= plafond
        arbre = ast.parse(texte)
        importes = {a.name for n in ast.walk(arbre)
                    if isinstance(n, ast.Import) for a in n.names}
        importes |= {n.module or "" for n in ast.walk(arbre)
                     if isinstance(n, ast.ImportFrom)}
        assert not importes & {"subprocess", "coordination.gh_bulk", "urllib.request"}
        for noeud in ast.walk(arbre):
            if isinstance(noeud, ast.FunctionDef):
                assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
