"""Tests de la publication des check-runs du lot en ombre (P3 tranche 2).

Le lot ne bloque rien : sa publication doit donc etre **advisory**, son
verdict doit porter sur l'arbre et pas sur l'isolement, et ce qui n'a pas
ete mesure ne doit jamais se presenter comme rouge. Les trois proprietes
sont verifiees ici, la premiere par le **predicat du gate lui-meme**
(`scripts/pr_gate.py::is_advisory`) : c'est ce predicat qui decide qu'un
check-run rouge ne bloque pas un merge, le tester ailleurs ne prouverait
rien.

La troncature du pool est verifiee comme un cas nomme : quand la population
inspectee atteint le plafond, le resume dit que la selection peut etre
partielle (demande explicite du coordinateur, 10/11 02:04Z).
"""

from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
SCRIPTS_DIR = Path(__file__).resolve().parents[1]
for _d in (CI_DIR, SCRIPTS_DIR):
    if str(_d) not in sys.path:
        sys.path.insert(0, str(_d))

import lot_check_runs  # noqa: E402
import pr_gate  # noqa: E402


def _plan(selectionnees, **kwargs):
    base = {
        "selectionnees": selectionnees,
        "pool_inspecte": 10,
        "limit": 100,
    }
    base.update(kwargs)
    return base


def _entree(number: int, **kwargs):
    base = {
        "number": number,
        "head_sha": f"sha-{number}",
        "fork": False,
    }
    base.update(kwargs)
    return base


# --- la conclusion ne peut pas survivre a un statut inconnu ---------------


def test_le_statut_vert_donne_un_check_run_vert():
    assert lot_check_runs.conclusion_pour_statut("vert") == "success"


def test_le_statut_rouge_donne_un_check_run_rouge():
    assert lot_check_runs.conclusion_pour_statut("rouge") == "failure"


def test_un_environnement_incomplet_ne_donne_jamais_rouge():
    # Une dependance manquante n'est pas une regression : c'est « non
    # mesurable », pas « rouge ».
    assert lot_check_runs.conclusion_pour_statut("non-mesurable") == "neutral"


def test_un_statut_inconnu_ou_absent_ne_donne_jamais_rouge():
    for statut in ("", None, "bizarre", "echec", "erreur", "simulation-ne-connue"):
        assert lot_check_runs.conclusion_pour_statut(statut) != "failure", statut


def test_la_simulation_est_un_check_run_saute():
    assert lot_check_runs.conclusion_pour_statut("simulation") == "skipped"


# --- le check-run ne bloque aucun merge (controle par le gate lui-meme) -----


def test_le_nom_du_check_run_est_advisory_pour_le_gate():
    # Controle positif : c'est le predicat du PR gate qui decide qu'un check
    # rouge ne bloque pas un merge. Le nom doit donc porter le marqueur.
    assert "advisory" in lot_check_runs.CHECK_RUN_NAME.lower()
    assert pr_gate.is_advisory(lot_check_runs.CHECK_RUN_NAME) is True


def test_un_check_run_rouge_du_lot_ne_passe_pas_dans_les_rouges_du_gate():
    # Le meme predicat, applique au nom que le lot publie : un lot rouge
    # doit rester dans le seau advisory du gate.
    nom = lot_check_runs.CHECK_RUN_NAME
    assert pr_gate.is_advisory(nom)
    assert not pr_gate.is_advisory("Heavy batch lot")


# --- la troncature du pool est nommee --------------------------------------


def test_un_pool_au_plafond_est_tronque():
    assert lot_check_runs.pool_tronque(100, 100) is True


def test_un_pool_sous_le_plafond_n_est_pas_tronque():
    assert lot_check_runs.pool_tronque(99, 100) is False


def test_une_limite_absente_ne_tronque_jamais():
    assert lot_check_runs.pool_tronque(10, None) is False
    assert lot_check_runs.pool_tronque(None, 100) is False


def test_le_resume_nomme_la_troncature():
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(1)], pool_inspecte=100, limit=100),
        {"prs": [{"number": 1, "statut": "vert", "duree_s": 12.0}]},
    )
    resume = payloads[0]["resume"]
    assert "tronquee" in resume
    assert "100" in resume
    assert "partielle" in resume


def test_le_resume_ne_parle_pas_de_troncature_sans_troncature():
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(1)], pool_inspecte=12, limit=100),
        {"prs": [{"number": 1, "statut": "vert", "duree_s": 12.0}]},
    )
    assert "tronquee" not in payloads[0]["resume"]


# --- le verdict porte sur l'arbre, pas sur l'isolement ----------------------


def test_le_resume_dit_que_le_verdict_porte_sur_l_arbre():
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(7)]),
        {
            "prs": [{"number": 7, "statut": "vert", "duree_s": 3.0}],
            "integration": {
                "statut": "rouge",
                "arbre": {"prs_integrees": [7]},
                "bissection": {"statut": "fait", "pr_coupable": 7},
            },
        },
    )
    resume = payloads[0]["resume"]
    assert "arbre d'integration" in resume
    assert "#7" in resume  # la PR coupable isolee par la bissection
    assert "ne bloque aucun merge" in resume


# --- les PRs qui ne peuvent pas etre portees sont nommees ------------------


def test_une_pr_de_fork_n_est_pas_publiee_et_le_motif_est_nomme():
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(3, fork=True)]),
        {"prs": [{"number": 3, "statut": "vert", "duree_s": 1.0}]},
    )
    assert payloads[0]["publie"] is False
    assert "fork" in payloads[0]["motif"]


def test_une_tete_absente_n_est_pas_publiee_silencieusement():
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(4, head_sha="")]),
        {"prs": [{"number": 4, "statut": "vert"}]},
    )
    assert payloads[0]["publie"] is False
    assert payloads[0]["motif"]


def test_une_pr_absente_du_resultat_n_est_pas_rouge():
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(5)]),
        {"prs": []},
    )
    assert payloads[0]["conclusion"] == "neutral"


def test_un_numero_present_meme_sil_faux_est_retrouve():
    # Le numero est lu comme une presence, pas comme une verite : filtre de
    # verite -> resultat ecarte -> verdict neutre sur une mesure faite.
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(0)]),
        {"prs": [{"number": 0, "statut": "vert", "duree_s": 1.0}]},
    )
    assert payloads[0]["conclusion"] == "success"
    assert payloads[0]["statut"] == "vert"


def test_le_corps_de_l_api_porte_le_verdict_et_la_sortie():
    entry = lot_check_runs.construire_payloads(
        _plan([_entree(6)]),
        {"prs": [{"number": 6, "statut": "rouge", "duree_s": 9.0}]},
    )[0]
    corps = lot_check_runs._payload_api(entry, "https://exemple/run/1")
    assert corps["name"] == lot_check_runs.CHECK_RUN_NAME
    assert corps["head_sha"] == "sha-6"
    assert corps["status"] == "completed"
    assert corps["conclusion"] == "failure"
    assert corps["details_url"] == "https://exemple/run/1"
    assert corps["output"]["title"]
    assert corps["output"]["summary"]


def test_le_module_est_importe_par_le_lot():
    # L'organe du lot doit voir le module de publication : c'est lui qui
    # porte la troncature dans le plan.
    import heavy_batch  # noqa: E402

    assert hasattr(heavy_batch, "lot_check_runs")


# --- l'ecriture passe par l'organe natif, pas par un POST duplique --------


def test_la_publication_passe_par_l_organe_natif(monkeypatch):
    # `scripts/ci/fast_lane.py::emit_check_run` est l'organe natif du depot
    # pour emettre un check-run sur une tete. Le lot doit s'en servir : un
    # second POST duplique serait un organe sans enjeu.
    appels = []

    def faux(repo, head_sha, name, conclusion, title, summary, dry_run, details_url=None):
        appels.append(
            {
                "repo": repo,
                "head_sha": head_sha,
                "name": name,
                "conclusion": conclusion,
                "title": title,
                "summary": summary,
                "dry_run": dry_run,
                "details_url": details_url,
            }
        )
        return True

    monkeypatch.setattr(lot_check_runs.fast_lane, "emit_check_run", faux)
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(9)]),
        {"prs": [{"number": 9, "statut": "vert", "duree_s": 1.0}]},
    )
    journal = lot_check_runs.publier(
        "jsboige/CoursIA", payloads, details_url="https://exemple/run/9"
    )
    assert len(appels) == 1
    assert appels[0]["head_sha"] == "sha-9"
    assert appels[0]["name"] == lot_check_runs.CHECK_RUN_NAME
    assert appels[0]["conclusion"] == "success"
    assert appels[0]["details_url"] == "https://exemple/run/9"
    assert journal[0]["statut"] == "publie"


def test_un_echec_de_publication_est_consigne_et_n_interrompt_pas(monkeypatch):
    monkeypatch.setattr(
        lot_check_runs.fast_lane,
        "emit_check_run",
        lambda *args, **kwargs: False,
    )
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(10)]),
        {"prs": [{"number": 10, "statut": "rouge", "duree_s": 1.0}]},
    )
    journal = lot_check_runs.publier("jsboige/CoursIA", payloads)
    assert journal[0]["statut"] == "echec de publication"
    assert journal[0]["conclusion"] == "failure"


def test_la_publication_ne_touche_pas_une_pr_de_fork(monkeypatch):
    appele = {"n": 0}

    def faux(*args, **kwargs):
        appele["n"] += 1
        return True

    monkeypatch.setattr(lot_check_runs.fast_lane, "emit_check_run", faux)
    payloads = lot_check_runs.construire_payloads(
        _plan([_entree(11, fork=True)]),
        {"prs": [{"number": 11, "statut": "vert"}]},
    )
    journal = lot_check_runs.publier("jsboige/CoursIA", payloads)
    assert appele["n"] == 0
    assert journal[0]["statut"] == "non publie"
