"""Tests du predicat d'extinction de `check_runner_starvation.py` (#22183).

L'organe est partage par les trois sondes de label (`coursia-linux`,
`coursia-waiter`, `coursia-lean`) ; le predicat se teste sur ses fonctions
pures (`evaluate`) avec les etats mesures, sans reseau.

  1. controle positif : le cas reel du 2026-10-23 sur `coursia-waiter` --
     0 runner online au label, 126 jobs `PR gate` queued > 2 h, AUCUN job
     in_progress (dernier succes 04:01:30Z, ~10 h sans signal). L'organe
     doit rendre les deux erreurs, EXTINCTION et STARVATION. C'est
     exactement ce qu'il n'a pas dit ce jour-la : le label n'etait mesure
     par aucune sonde (header `runner-starvation-advisory.yml` corrige
     dans la meme PR).
  2. controle negatif : pool vivant (16 slots online) et file profonde qui
     DRAINE -- OK, jamais un rouge (garde anti-FP : une file qui draine est
     un manque de capacite, pas une extinction).
  3. degradation sans PAT : inventaire non lisible -> pas d'EXTINCTION,
     l'organe garde le seul symptome STARVATION.
"""
import importlib.util
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "check_runner_starvation",
    Path(__file__).resolve().parents[1] / "check_runner_starvation.py",
)
mod = importlib.util.module_from_spec(_SPEC)
# Enregistrer AVANT exec : Python 3.14 fait resoudre les annotations de
# @dataclass par `sys.modules[cls.__module__]` -- sans cette ligne la
# collection echoue (AttributeError NoneType sur l'organe, mesure ci-contre).
sys.modules[_SPEC.name] = mod
_SPEC.loader.exec_module(mod)

LABEL = "coursia-waiter"
HOST = "myia-ai-01-wsl"


def _online(n: int) -> list[str]:
    return [f"{HOST}-{i}" for i in range(1, n + 1)]


def _pr_gate_job(run_id: int, age_min: float, status: str = "queued") -> mod.JobRow:
    return mod.JobRow(
        workflow="PR gate",
        run_number=run_id,
        run_id=run_id,
        job_name="gate",
        status=status,
        age_min=age_min,
    )


# ---------- 1. controle positif : le cas reel du 2026-10-23 ----------

def test_cas_2026_10_23_extinction_et_starvation():
    """0 online + 126 jobs PR gate queued > 2 h + 0 in_progress -> 2 erreurs."""
    inv = mod.RunnerInventory(online=[], offline=_online(16))
    st = mod.Starvation(
        starved=[_pr_gate_job(90000 + i, 130.0 + (i % 400)) for i in range(126)],
        in_progress=[],
    )
    v = mod.evaluate(inv, st, warn_floor=2)
    assert v.status == "ERROR"
    assert any("EXTINCTION" in e for e in v.errors)
    starv = [e for e in v.errors if "STARVATION" in e]
    assert starv, "STARVATION doit tirer : file qui ne draine pas"
    assert "126" in starv[0] and "PR gate" in starv[0]


# ---------- 2. controle negatif : pool vivant, file qui draine ----------

def test_pool_vivant_file_profonde_ok():
    """16 slots online, queue > seuil MAIS des jobs in_progress -> OK."""
    inv = mod.RunnerInventory(online=_online(16), offline=[])
    st = mod.Starvation(
        starved=[_pr_gate_job(90000 + i, 200.0) for i in range(126)],
        in_progress=[_pr_gate_job(90126, 10.0, status="in_progress")],
    )
    v = mod.evaluate(inv, st, warn_floor=2)
    assert v.status == "OK"
    assert not v.errors, f"une file qui draine ne rougit pas : {v.errors}"


def test_pool_vivant_queue_vide_ok():
    inv = mod.RunnerInventory(online=_online(16), offline=[])
    v = mod.evaluate(inv, mod.Starvation(), warn_floor=2)
    assert v.status == "OK"
    assert not v.errors


def test_perte_partielle_warning_pas_erreur():
    """15 des 16 slots online avec un floor au-dessus -> warning (perte
    partielle), pas d'erreur. (Le floor est une borne : 15 online passe
    sans avertissement au floor 2 -- c'est le cas nominal du pool de 16
    avec un slot en redemarrage.)"""
    inv = mod.RunnerInventory(online=_online(15), offline=[f"{HOST}-16"])
    v = mod.evaluate(inv, mod.Starvation(), warn_floor=16)
    assert v.status == "OK"
    assert any("perte partielle" in w for w in v.warnings)


# ---------- 3. degradation sans PAT (inventaire non lisible) ----------

def test_sans_pat_pas_extinction_mais_starvation_gardee():
    """Inventaire non lisible : pas d'EXTINCTION (on ne sait pas), mais le
    symptome STARVATION tire quand meme -- degradation propre du docstring."""
    inv = mod.InventoryUnavailable(reason="RUNNERS_READ_PAT absent (test)")
    st = mod.Starvation(
        starved=[_pr_gate_job(90000, 300.0)],
        in_progress=[],
    )
    v = mod.evaluate(inv, st, warn_floor=2)
    assert v.status == "ERROR"
    assert not any("EXTINCTION" in e for e in v.errors)
    assert any("STARVATION" in e for e in v.errors)
