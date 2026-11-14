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
