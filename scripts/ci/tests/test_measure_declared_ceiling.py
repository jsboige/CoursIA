"""Tests de `measure_declared_ceiling` (organe : le plafond declare bind-il ?).

Contrat verifie ici, dans cet ordre :

1. **extraction des plafonds** depuis le YAML d'un workflow, avec la meme
   regle que la gate (`pr_gate.derive_declared_timeouts`) : un nom de job qui
   resout a plusieurs limites distinctes est **abandonne**, pas devine ;
2. **coupure de la frise** : le plafond en vigueur est celui qui etait declare
   **au demarrage du job** -- pas celui de la version courante du fichier ;
3. **detection de coupe** : fenetre **bilaterale** autour du plafond. Une
   annulation par supersession (`cancel-in-progress`, qui peut durer plus
   longtemps que le plafond) n'est pas une coupe ; une annulation par famine
   de runner non plus ; un `success` jamais ;
4. **coherence avec la gate** : l'extraction de cet organe et celle de la
   gate, sur le repertoire vivant des workflows, ne doivent pas se contredire
   -- la gate est le verificateur independant, cet organe ne reecrit pas sa
   regle ;
5. **histoire reelle** : la frise des plafonds de `scripts-tests.yml` doit
   contenir le passage 30 -> 40 (commit du 2026-11-12), sinon l'historique
   n'est pas lisible et la segmentation par plafond en vigueur est fausse.
"""
import importlib.util
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

_ROOT = Path(__file__).resolve().parents[3]
_SPEC = importlib.util.spec_from_file_location(
    "measure_declared_ceiling",
    Path(__file__).resolve().parents[1] / "measure_declared_ceiling.py",
)
mod = importlib.util.module_from_spec(_SPEC)
sys.modules["measure_declared_ceiling"] = mod
_SPEC.loader.exec_module(mod)

WORKFLOWS_DIR = _ROOT / ".github" / "workflows"


# --- 1. extraction des plafonds ------------------------------------------

YAML_SIMPLE = """
jobs:
  a:
    name: Job A
    timeout-minutes: 30
  b:
    name: Job B
    runs-on: ubuntu-latest
"""


def test_limite_extraite_par_nom_de_job():
    limites = mod.limits_from_yaml(YAML_SIMPLE)
    assert limites == {"Job A": 30}


def test_job_sans_plafond_absent_du_repertoire():
    limites = mod.limits_from_yaml(YAML_SIMPLE)
    assert "Job B" not in limites


def test_nom_ambigu_abandonne_pas_devine():
    """Deux jobs du meme nom, deux limites : le lecteur ne peut pas attribuer."""
    yaml_ambigu = """
jobs:
  a:
    name: Meme Nom
    timeout-minutes: 30
  b:
    name: Meme Nom
    timeout-minutes: 45
"""
    assert mod.limits_from_yaml(yaml_ambigu) == {}


def test_nom_repeated_meme_valeur_conserve():
    yaml_repete = """
jobs:
  a:
    name: Meme Nom
    timeout-minutes: 30
  b:
    name: Meme Nom
    timeout-minutes: 30
"""
    assert mod.limits_from_yaml(yaml_repete) == {"Meme Nom": 30}


def test_yaml_illisible_ne_leve_pas():
    assert mod.limits_from_yaml("jobs: [\n  - pas: du yaml") == {}


# --- 2. plafond en vigueur au demarrage du job ---------------------------


def _frise():
    return [
        (datetime(2026, 11, 1, tzinfo=timezone.utc), {"Job A": 30}),
        (datetime(2026, 11, 12, 19, 29, 58, tzinfo=timezone.utc), {"Job A": 40}),
    ]


def test_plafond_avant_le_changement():
    quand = datetime(2026, 11, 11, 12, 0, tzinfo=timezone.utc)
    assert mod.resolve_limit(_frise(), "Job A", quand) == 30


def test_plafond_apres_le_changement():
    quand = datetime(2026, 11, 13, 12, 0, tzinfo=timezone.utc)
    assert mod.resolve_limit(_frise(), "Job A", quand) == 40


def test_plafond_inconnu_pour_un_nom_absent():
    quand = datetime(2026, 11, 13, 12, 0, tzinfo=timezone.utc)
    assert mod.resolve_limit(_frise(), "Job Z", quand) is None


def test_date_avec_decalage_convertie_en_utc():
    """`git log --format=%cI` rend un decalage local : la frise doit etre en UTC."""
    stamp = mod._parse_iso("2026-11-13T18:55:00+01:00")
    assert stamp == datetime(2026, 11, 13, 17, 55, tzinfo=timezone.utc)


# --- 3. detection de coupe (fenetre bilaterale) --------------------------


def test_annule_au_mur_est_une_coupe():
    assert mod.is_cut(40.5, "cancelled", 40) is True


def test_annule_par_supersession_n_est_pas_une_coupe():
    """`cancel-in-progress` annule un job qui peut tourner bien plus longtemps."""
    assert mod.is_cut(97.0, "cancelled", 40) is False


def test_annule_par_famine_de_runner_n_est_pas_une_coupe():
    assert mod.is_cut(0.2, "cancelled", 40) is False


def test_succes_n_est_jamais_une_coupe():
    assert mod.is_cut(39.9, "success", 40) is False


def test_echec_n_est_jamais_une_coupe():
    assert mod.is_cut(40.1, "failure", 40) is False


def test_coupe_au_mur_de_30_min():
    assert mod.is_cut(30.3, "cancelled", 30) is True


# --- 4. coherence avec la gate (verificateur independant) ----------------


def test_extraction_coherente_avec_la_gate():
    """La gate lit les memes plafonds : les deux lectures ne doivent pas
    diverger sur les noms resolus a une seule limite."""
    pr_gate = pytest.importorskip("pr_gate")
    gate_limits = pr_gate.derive_declared_timeouts(str(WORKFLOWS_DIR))
    disagrees = []
    for yml in sorted(WORKFLOWS_DIR.glob("*.yml")):
        mine = mod.limits_from_yaml(yml.read_text(encoding="utf-8"))
        for name, limit in mine.items():
            if name in gate_limits and gate_limits[name] != limit:
                disagrees.append((yml.name, name, limit, gate_limits[name]))
    assert not disagrees, disagrees


# --- 5. histoire reelle du plafond de la jambe CPU -----------------------


@pytest.fixture(scope="module")
def frise_cpu():
    """Frise des plafonds de `scripts-tests.yml` (lue **une fois**).

    La lecture de l'historique git coute ~6 s ; la repetition par test la
    multipliait par le nombre de tests.
    """
    return mod.limit_timeline(".github/workflows/scripts-tests.yml")


def test_frise_du_plafond_de_scripts_tests(frise_cpu):
    assert frise_cpu, "la frise des plafonds est vide"
    limites_vus = {limit for _, limites in frise_cpu for limit in limites.values()}
    assert 40 in limites_vus, limites_vus
    assert 30 in limites_vus, limites_vus


def test_frise_ordonnee_croissante(frise_cpu):
    dates = [stamp for stamp, _ in frise_cpu]
    assert dates == sorted(dates)


# --- 6. la passe d'annotation : la fenetre propose, l'organe natif tranche -
# La fenetre bilaterale est un PROXY : elle dit qu'un job annule a dure
# assez longtemps pour avoir touche son plafond. La preuve est l'annotation
# que GitHub pose sur le check-run (« The job has exceeded the maximum
# execution time of 40m0s »), lue par l'organe natif
# `classify_job_deaths.py` (classe `TIMEOUT`).
#
# Ces tests verifient que cet organe **branche** sur l'organe natif au lieu
# de reecrire sa classification, et que les deux verdicts sont comptes
# separement -- jamais fusionnes en un chiffre unique qui masquerait le taux
# de faux positifs.

class _FakeClassifyJobDeaths:
    """Module factice : l'organe natif est *appele*, pas reecrit.

    Le contrat verifie ici est celui de l'appel : `classify_job(job,
    annotations)` et `fetch_annotations(job_id)`.
    """

    def __init__(self, classes):
        self.classes = classes
        self.calls = []

    def classify_job(self, job, annotations):
        # L'organe natif lit `conclusion` et `steps` ; l'identifiant du
        # check-run est porte par `job_id` dans la collecte de cet organe.
        ident = job.get("job_id", job.get("id"))
        self.calls.append((ident, len(annotations)))
        return self.classes.get(ident, "CANCELLED_OTHER")

    def fetch_annotations(self, job_id):
        return [{"message": "The job has exceeded the maximum execution time"}]


@pytest.fixture
def fausse_annotations(monkeypatch):
    """Installe un module `classify_job_deaths` factice dans `sys.modules`."""
    import types

    faux = _FakeClassifyJobDeaths({})
    module = types.ModuleType("classify_job_deaths")
    module.classify_job = faux.classify_job
    module.fetch_annotations = faux.fetch_annotations
    monkeypatch.setitem(sys.modules, "classify_job_deaths", module)
    return faux


def _job(job_id, conclusion, started, completed, name="Scripts Tests (CPU)"):
    return {
        "id": job_id,
        "name": name,
        "conclusion": conclusion,
        "started_at": started,
        "completed_at": completed,
        "steps": [{"name": "Run tests", "conclusion": conclusion}],
    }


def test_coupe_confirmee_par_annotation_comptee_a_part(monkeypatch, fausse_annotations):
    """Un job coupe au mur separe par l'organe natif est compte comme tel."""
    fausse_annotations.classes = {11: "TIMEOUT"}
    run = {"id": 900, "created_at": "2026-11-13T10:00:00Z", "head_branch": "main"}
    jobs = [
        _job(11, "cancelled", "2026-11-13T10:00:00Z", "2026-11-13T10:40:30Z"),
        # Annule a 38,6 min : la fenetre (borne basse 38,5) la compte comme
        # une coupe, l'organe natif dit le contraire -- c'est le faux positif
        # mesure de la fenetre, reproduit ici a l'echelle d'un test.
        _job(12, "cancelled", "2026-11-13T11:00:00Z", "2026-11-13T11:38:36Z"),
    ]
    monkeypatch.setattr(mod, "list_runs", lambda *a, **k: [run])
    monkeypatch.setattr(mod, "api", lambda path: {"jobs": jobs})
    rapport = mod.measure("scripts-tests.yml", 48, 1, "", True)
    segment = next(r for r in rapport["segments"] if r["job"] == "Scripts Tests (CPU)")
    # La fenetre voit deux coupes (annule au mur, et annule proche du mur).
    assert segment["coupes"] == 2
    # L'organe natif n'en confirme qu'une : le deuxieme etait une autre cause.
    assert segment["coupes_confirmees_annotation"] == 1
    assert segment["classes_annulation"]["TIMEOUT"] == 1
    assert segment["classes_annulation"]["CANCELLED_OTHER"] == 1


def test_echec_de_lecture_ne_compte_pas_comme_une_coupe(monkeypatch, fausse_annotations):
    """Une annotation illisible ne doit jamais etre comptee comme un succes."""
    import types

    module = types.ModuleType("classify_job_deaths")

    def _boom(job_id):
        raise RuntimeError("403")

    module.classify_job = lambda job, ann: "TIMEOUT"
    module.fetch_annotations = _boom
    monkeypatch.setitem(sys.modules, "classify_job_deaths", module)
    run = {"id": 901, "created_at": "2026-11-13T10:00:00Z", "head_branch": "main"}
    jobs = [_job(21, "cancelled", "2026-11-13T10:00:00Z", "2026-11-13T10:40:30Z")]
    monkeypatch.setattr(mod, "list_runs", lambda *a, **k: [run])
    monkeypatch.setattr(mod, "api", lambda path: {"jobs": jobs})
    rapport = mod.measure("scripts-tests.yml", 48, 1, "", True)
    segment = next(r for r in rapport["segments"] if r["job"] == "Scripts Tests (CPU)")
    assert segment["coupes_confirmees_annotation"] == 0
    assert segment["classes_annulation"]["LECTURE_IMPOSSIBLE"] == 1


def test_le_cache_de_jobs_evite_de_refrapper_lapi(monkeypatch, tmp_path, fausse_annotations):
    """Le cache garde la collecte : re-mesurer ne reboucle pas l'API."""
    cache = tmp_path / "jobs.json"
    run = {"id": 902, "created_at": "2026-11-13T10:00:00Z", "head_branch": "main"}
    jobs = [_job(31, "success", "2026-11-13T10:00:00Z", "2026-11-13T10:05:00Z")]

    monkeypatch.setattr(mod, "list_runs", lambda *a, **k: [run])
    monkeypatch.setattr(mod, "api", lambda path: {"jobs": jobs})
    mod.measure("scripts-tests.yml", 48, 1, str(cache), False)
    assert cache.exists(), "le cache doit etre ecrit"

    # Seconde mesure : le cache doit servir, l'API ne doit plus etre touchee.
    def _api_interdite(path):
        raise AssertionError("l'API ne doit pas etre reappellee avec un cache")

    monkeypatch.setattr(mod, "api", _api_interdite)
    rapport = mod.measure("scripts-tests.yml", 48, 1, str(cache), False)
    assert rapport["jobs_mesures"] == 1


# --- 7. la population ne doit pas etre censuree par les rejeux -------------
# Un job coupe au mur est tres souvent REJOUE (rejeu automatique de la CI, ou
# re-run humain). L'endpoint `runs/<id>/jobs` ne renvoie, par defaut, que la
# DERNIERE tentative : le run ne porte alors plus que la tentative rejouee,
# qui reussit -- et la coupe DISPARAIT de la population. Mesure du 2026-11-14 :
# 26 des 40 coupes au mur du segment 40 min etaient absentes de la
# population collectee sans `filter=all` ; le taux annonce etait alors de
# 2,3 % au lieu de 6,5 %.


def test_la_collecte_prend_toutes_les_tentatives_du_run(monkeypatch, tmp_path, fausse_annotations):
    """La collecte demande `filter=all` : les rejets des coupes ne doivent
    pas pouvoir disparaitre de la population."""
    run = {"id": 903, "created_at": "2026-11-13T10:00:00Z", "head_branch": "main"}
    jobs = [_job(41, "success", "2026-11-13T10:00:00Z", "2026-11-13T10:05:00Z")]
    vues = []

    def _api(path):
        vues.append(path)
        return {"jobs": jobs}

    monkeypatch.setattr(mod, "list_runs", lambda *a, **k: [run])
    monkeypatch.setattr(mod, "api", _api)
    mod.measure("scripts-tests.yml", 48, 1, str(tmp_path / "c.json"), False)
    assert any("filter=all" in p for p in vues), vues


def test_un_cache_d_une_version_anterieure_est_ignore(monkeypatch, tmp_path, fausse_annotations):
    """Un cache collecte sans `filter=all` ne doit pas etre relu tel quel.

    Le relu rendrait le chiffre d'avant le correctif avec l'apparence d'une
    mesure a jour -- c'est precisement la faute qui a produit 2,3 % au lieu
    de 6,5 %. Un cache d'une version anterieure est ignore et recollecte.
    """
    cache = tmp_path / "jobs.json"
    cache.write_text(json.dumps({
        "cache_version": 1,
        "jobs": [_job(51, "success", "2026-11-13T10:00:00Z", "2026-11-13T10:05:00Z")],
        "runs": [{"id": 904, "created_at": "2026-11-13T10:00:00Z",
                  "head_branch": "main"}],
        "runs_sans_jobs": 0,
    }), encoding="utf-8")
    run = {"id": 904, "created_at": "2026-11-13T10:00:00Z", "head_branch": "main"}
    jobs = [_job(52, "success", "2026-11-13T11:00:00Z", "2026-11-13T11:05:00Z")]
    appels = []

    def _api(path):
        appels.append(path)
        return {"jobs": jobs}

    monkeypatch.setattr(mod, "list_runs", lambda *a, **k: [run])
    monkeypatch.setattr(mod, "api", _api)
    mod.measure("scripts-tests.yml", 48, 1, str(cache), False)
    assert appels, "un cache d'une version anterieure doit etre ignore, pas relu"
    relu = json.loads(cache.read_text(encoding="utf-8"))
    assert relu["cache_version"] == mod.CACHE_VERSION
