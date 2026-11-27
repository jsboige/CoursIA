"""#28114 I6 -- le cap de livraisons est VIVANT et BORNE (#28345).

Avant ce correctif, le cap de livraisons n'etait **jamais evalue** en
production : la voie leger passait le `run` de la COMMANDE
(`gh_bulk.run_defaut` : ``(argv, timeout) -> str``) au fetteur, dont le
contrat est ``(since, until) -> list[dict]``. L'appel levait, l'exception etait
absorbee par `charge_en_vol`, et le rapport portait `cap_livraisons.mesure =
false` : le garde qui plafonne les livraisons EPIC ne plafonnait rien.

Ces tests prennent l'entree reellement utilisee par les lanes
(`coordination.tapis_leger.tirage`) et prouvent trois choses :

1. le cap se MESURE, et sa lecture passe par le FETTEUR (`since`, `until`) ;
2. le cap ECARTE un item livre au cap, avec son temoin ;
3. un cap LENT est coupe a l'echeance : la mesure vaut `None` (fail-OPEN), le
   repli rend la main, et la commande ne depasse pas son budget.

Aucun test ne touche le reseau : le `run` de la commande est un faux, et le
fetteur du cap est monkeypatche sur son organe (`run_gh`).
"""
import json
import re
import sys
import time
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import fetch_merged_prs_since  # noqa: E402
from coordination import gh_bulk, gh_cache_fichier  # noqa: E402
from coordination import tapis_ancre, tapis_etat, tapis_leger  # noqa: E402

NOW = datetime(2026, 11, 25, 21, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
#: La fenetre du cap : sept jours de livraisons mergees.
FENETRE_J = 7


# --- le pool synthetique -------------------------------------------------------

def _meta(n: int, cree: str = "2026-10-01T00:00:00Z") -> dict:
    return {"number": n, "title": f"Grain {n}", "created_at": cree,
            "updated_at": cree, "labels": []}


def _page_metas(metas: list[dict]) -> str:
    nodes = [{"number": m["number"], "title": m["title"], "createdAt": m["created_at"],
              "updatedAt": m["updated_at"],
              "labels": {"nodes": [{"name": lab} for lab in m["labels"]]}}
             for m in metas]
    return json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": False, "endCursor": "c"}, "nodes": nodes}}}})


def _page_issues(metas: list[dict], requete: str) -> str:
    par_numero = {m["number"]: m for m in metas}
    data: dict = {"data": {"repository": {}}}
    for k, n in enumerate(re.findall(r"issue\(number:(\d+)\)", requete)):
        m = par_numero.get(int(n))
        data["data"]["repository"][f"i{k}"] = None if m is None else {
            "number": m["number"], "title": m["title"], "body": "",
            "createdAt": m["created_at"], "updatedAt": m["updated_at"],
            "labels": {"nodes": [{"name": lab} for lab in m["labels"]]},
            "comments": {"totalCount": 0, "nodes": []}}
    return json.dumps(data)


def _run(metas: list[dict]):
    """Le faux `run` de la COMMANDE : pool en metadonnees, aucune PR ouverte."""
    def run(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            return _page_issues(metas, requete)
        if "graphql" in requete:
            return _page_metas(metas)
        if argv[0] == "git":
            return ""
        return "[]"
    return run


def _pr(number: int, cites: str, jours: float = 1.0, lane: str = LANE) -> dict:
    """Une PR mergee : le TAG de lane dans le corps, et l'EPIC cite."""
    body = f"Grain: MED/tooling — lane {lane} — prev: MED/tooling #1\n\n{cites}\n"
    merged = NOW - timedelta(days=jours)
    return {"number": number, "body": body,
            "mergedAt": merged.strftime("%Y-%m-%dT%H:%M:%SZ")}


def _fetteur(corpus: list[dict], appels: list[tuple] | None = None, delai: float = 0.0):
    """Le faux fetteur du cap : le contrat `(since, until) -> list[dict]`."""
    def run_gh(since, until, fields=None, timeout=None, run=None):
        if appels is not None:
            appels.append((since, until, timeout))
        if delai:
            time.sleep(delai)
        return list(corpus)
    return run_gh


def _cache_repli(tmp_path, monkeypatch, numeros: list[int], jours: int = 45):
    """Le cache local que le REPLI CHRONOLOGIQUE lit (invariant I2)."""
    cree = (NOW - timedelta(days=30)).strftime("%Y-%m-%dT%H:%M:%SZ")
    issues = [gh_bulk.issue({"number": n, "title": f"Grain {n}", "body": "",
                             "createdAt": cree, "updatedAt": cree,
                             "labels": {"nodes": []},
                             "comments": {"totalCount": 0, "nodes": []}})
              for n in numeros]
    lecture = gh_bulk.Lecture(issues=issues, prs=[], citations={},
                               lu_a="2026-11-25T20:00:00Z", secondes=0.1, appels=1)
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    gh_cache_fichier.ecrire(tmp_path / f"lecture-{jours}j.json", lecture)


@pytest.fixture(autouse=True)
def _etat_neutre(monkeypatch):
    """Aucun etat de lane : ni ancre, ni visitation, ni ecriture."""
    monkeypatch.setattr(tapis_ancre, "lire", lambda lane: tapis_etat.vide())
    monkeypatch.setattr(tapis_ancre, "proposer", lambda *a, **k: {})
    monkeypatch.setattr(tapis_ancre, "ecrire", lambda lane, etat: etat)


# --- 1 -- le cap se mesure au point d'entree -----------------------------------

def test_le_cap_se_mesure_au_point_d_entree(monkeypatch):
    """Le cap est EVALUE : le rapport porte `mesure = true`.

    C'etait le defaut : le `run` de la commande etait passe au fetteur, dont
    le contrat est different ; l'echec etait absorbe et le rapport portait
    `mesure = false` sur TOUTE la flotte.
    """
    pool = [_meta(5000 + k) for k in range(6)]
    appels: list[tuple] = []
    monkeypatch.setattr(fetch_merged_prs_since, "run_gh", _fetteur([], appels))
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run(pool))
    assert code == 0
    assert rapport["cap_livraisons"]["mesure"] is True, \
        "le cap doit etre evalue : c'etait le defaut corrige ici"
    assert appels, "la lecture du cap doit passer par le fetteur (since, until)"
    for since, until, _timeout in appels:
        assert since < until, "le fetteur attend (since, until)"


def test_le_cap_ecarte_un_item_livre_au_cap(monkeypatch):
    """Le cap ECRATE l'item dont la charge en vol depasse le seuil.

    Deux livraisons mergees de la lane sur le meme EPIC : la charge vaut 2,
    le seuil de l'EPIC vaut 2 -- l'item part, avec son temoin.
    """
    pool = [_meta(5000 + k) for k in range(6)]
    corpus = [_pr(7001, "Closes #5000"), _pr(7002, "See #5000")]
    monkeypatch.setattr(fetch_merged_prs_since, "run_gh", _fetteur(corpus))
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run(pool))
    assert code == 0
    assert rapport["cap_livraisons"]["mesure"] is True
    ecartes = {e["numero"]: e for e in rapport["cap_livraisons"]["ecartes"]}
    assert 5000 in ecartes, "l'item au cap doit etre ecarte, avec son temoin"
    assert ecartes[5000]["motif"]


def test_le_cap_ne_recree_pas_de_budget(monkeypatch):
    """La lecture du cap est bornee par le TEMPS RESTANT de la commande.

    Le cap partage l'echeance de la selection et de la qualification : il ne
    s'attribue pas un plafond neuf (le chemin normal autorisait 60 s par
    tranche, hors delai restant).
    """
    pool = [_meta(5000 + k) for k in range(6)]
    appels: list[tuple] = []
    monkeypatch.setattr(fetch_merged_prs_since, "run_gh", _fetteur([], appels))
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run(pool), budget_s=20.0)
    assert code == 0
    assert appels, "le cap doit avoir lu le reseau"
    for _since, _until, timeout in appels:
        assert timeout is not None, "la tranche doit etre bornee"
        assert 0 < timeout <= 20.0, \
            f"le timeout de la tranche ({timeout}) doit tenir dans le budget"


# --- 2 -- un cap lent ne retarde pas la commande -------------------------------

def test_un_cap_lent_est_coupe_et_le_repli_rend_la_main(monkeypatch, tmp_path):
    """Un cap LENT : la commande rend la main dans son budget, et le repli
    chronologique sert la file (fail-OPEN : la mesure vaut `None`).

    Le fetteur dort plus longtemps que le budget ; la lecture du cap est
    coupee a l'echeance, la mesure echoue (le cap n'ecarte rien) et la
    qualification, qui refuse tout, fait basculer sur le repli.
    """
    from coordination import tapis_qualification as tq

    pool = [_meta(5000 + k) for k in range(6)]
    monkeypatch.setattr(fetch_merged_prs_since, "run_gh",
                        _fetteur([], delai=30.0))

    def faux_qualifier(run, depot, numeros=None):
        return {}

    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    _cache_repli(tmp_path, monkeypatch, [9101, 9102, 9103])
    debut = time.monotonic()
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run(pool), budget_s=2.0)
    ecoule = time.monotonic() - debut
    assert ecoule < 25.0, \
        f"le cap lent doit etre coupe a l'echeance ({ecoule:.1f} s)"
    assert code == 0, "une lecture lente ne doit pas faire echouer la commande"
    assert rapport["cap_livraisons"]["mesure"] is False, \
        "une lecture coupee n'est pas une mesure : fail-OPEN"
    assert rapport["grains"], "le repli doit rendre une file non vide"


# --- 3 -- le contrat, au point de contact ---------------------------------------

def test_le_fetteur_du_cap_porte_le_contrat_du_fetteur(monkeypatch):
    """Le cap appelle le fetteur avec `(since, until)`, jamais avec l'argv.

    Le contrat de la COMMANDE (`(argv, timeout) -> str`) et celui du FETTEUR
    (`(since, until) -> list[dict]`) ne sont pas le meme : l'adaptation se
    fait au point de contact, et le lanceur de la commande reste le seul
    appelee pour l'argv.
    """
    pool = [_meta(5000 + k) for k in range(6)]
    vus: list[list[str]] = []

    def faux_run_gh(since, until, fields=None, timeout=None, run=None):
        vus.append(["run_gh", since, until])
        if run is not None:
            # le lanceur de la commande est appele avec l'ARGUMENT du
            # fetteur -- il ne voit jamais les deux dates.
            vus.append(["run", str(run(["gh", "pr", "list"], 1))])
        return []

    monkeypatch.setattr(fetch_merged_prs_since, "run_gh", faux_run_gh)
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       _run(pool))
    assert code == 0
    assert rapport["cap_livraisons"]["mesure"] is True
    assert vus, "le fetteur doit avoir ete appele"
    dates = [v for v in vus if v[0] == "run_gh"]
    assert dates, "le fetteur du cap est appele avec (since, until)"
    for v in dates:
        assert re.match(r"^\d{4}-\d{2}-\d{2}$", v[1]), v
        assert re.match(r"^\d{4}-\d{2}-\d{2}$", v[2]), v
