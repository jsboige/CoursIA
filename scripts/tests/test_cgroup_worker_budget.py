# -*- coding: utf-8 -*-
"""Tests du calcul de workers xdist d'apres le plafond memoire du cgroup (#21802).

Couvrent les quatre cas nommes par l'issue : limite absente, limite `max`,
plafond de 1,5 Gio (slots persistants `po-2024`) et plafond de 4 Gio (slots
ephemeres `ai-01-wsl-*`).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

from cgroup_worker_budget import (  # noqa: E402
    DEFAULT_WORKERS,
    MAX_WORKERS,
    RSS_BUDGET_PAR_WORKER_MIB,
    RSS_BUDGET_PAR_WORKER_MIB_ICT,
    RSS_RESERVE_MASTER_MIB,
    budget_for,
    compute_workers,
    describe,
    read_memory_limit_bytes,
)

GIB = 1024 ** 3
MIB = 1024 ** 2


def _ecrire_v2(tmp_path: Path, contenu: str) -> Path:
    (tmp_path / "memory.max").write_text(contenu, encoding="utf-8")
    return tmp_path


def _ecrire_v1(tmp_path: Path, contenu: str) -> Path:
    (tmp_path / "memory").mkdir(parents=True, exist_ok=True)
    (tmp_path / "memory" / "memory.limit_in_bytes").write_text(contenu, encoding="utf-8")
    return tmp_path


# --- lecture de la limite -------------------------------------------------


def test_limite_absente_renvoie_none(tmp_path):
    assert read_memory_limit_bytes(tmp_path) is None


def test_limite_v2_max_renvoie_none(tmp_path):
    _ecrire_v2(tmp_path, "max\n")
    assert read_memory_limit_bytes(tmp_path) is None


def test_limite_v2_illisible_renvoie_none(tmp_path):
    _ecrire_v2(tmp_path, "pas-un-nombre\n")
    assert read_memory_limit_bytes(tmp_path) is None


def test_limite_v2_1_5_gio_est_lue(tmp_path):
    _ecrire_v2(tmp_path, "1610612736\n")
    assert read_memory_limit_bytes(tmp_path) == 1610612736


def test_limite_v1_est_lue(tmp_path):
    _ecrire_v1(tmp_path, "1610612736\n")
    assert read_memory_limit_bytes(tmp_path) == 1610612736


def test_limite_v1_illimite_renvoie_none(tmp_path):
    # cgroup v1 : "illimite" = 9223372036854771712 (2^63 - page)
    _ecrire_v1(tmp_path, "9223372036854771712\n")
    assert read_memory_limit_bytes(tmp_path) is None


def test_v2_prime_sur_v1(tmp_path):
    _ecrire_v2(tmp_path, "4294967296\n")
    _ecrire_v1(tmp_path, "1073741824\n")
    assert read_memory_limit_bytes(tmp_path) == 4294967296


# --- calcul du nombre de workers -----------------------------------------


def test_limite_absente_rend_la_valeur_nominale():
    assert compute_workers(None) == DEFAULT_WORKERS


def test_limite_max_rend_la_valeur_nominale(tmp_path):
    # `max` est lu comme "pas de plafond" par read_memory_limit_bytes.
    _ecrire_v2(tmp_path, "max\n")
    assert read_memory_limit_bytes(tmp_path) is None
    assert compute_workers(read_memory_limit_bytes(tmp_path)) == DEFAULT_WORKERS


def test_plafond_1_5_gio_ne_tue_plus_les_workers():
    # C'est le cas des slots `myia-po-2024-linux-persist-*` (OOM exit 137).
    # 1,5 Gio moins la reserve master, divise par le budget mesure : un seul
    # worker tient dans le conteneur, donc plus de kill groupe.
    n = compute_workers(int(1.5 * GIB))
    attendu = max(1, min(MAX_WORKERS, int((1536 - RSS_RESERVE_MASTER_MIB) // RSS_BUDGET_PAR_WORKER_MIB)))
    assert n == attendu
    assert n == 1


def test_plafond_4_gio_tient_le_budget_mesure():
    # C'est le cas des slots `ai-01-wsl-*` et `po-2024-linux-docker-1`.
    # Mesure : 4 workers ont peaks a 4 605 MiB (arbre complet), soit plus que
    # les 4 Go du conteneur -- le budget par worker (charge CONCURRENTE mesuree)
    # donne donc 3 workers, pas 4. Le passage a 4 demanderait un budget
    # <= 960 MiB, que la mesure ne soutient pas.
    attendu = max(1, min(MAX_WORKERS, int((4096 - RSS_RESERVE_MASTER_MIB) // RSS_BUDGET_PAR_WORKER_MIB)))
    assert compute_workers(4 * GIB) == attendu
    assert compute_workers(4 * GIB) == 3


def test_le_budget_mesure_tient_le_reserve_master():
    """Le budget par worker vient de la charge mesuree par worker au pic de
    l'arbre (4 605,1 MiB / 4 = 1 151,3 MiB) : il ne doit pas descendre sous la
    valeur mesuree, sinon le garde sous-dimensionne le conteneur."""
    assert RSS_BUDGET_PAR_WORKER_MIB >= 1152


def test_plafond_superieur_au_nominal_est_plafonne():
    assert compute_workers(16 * GIB) == MAX_WORKERS


# --- suite ICT (budget propre, mesure le 2026-10-21) ---------------------


def test_ict_utilise_son_propre_budget():
    assert budget_for("ict") == RSS_BUDGET_PAR_WORKER_MIB_ICT
    assert budget_for("scripts") == RSS_BUDGET_PAR_WORKER_MIB
    # Une suite inconnue retombe sur le budget de la suite `scripts`.
    assert budget_for("inconnue") == RSS_BUDGET_PAR_WORKER_MIB


def test_le_budget_ict_vient_du_worker_le_plus_lourd():
    """Sous `--dist loadscope`, un module epingle garde son worker : le
    conteneur doit tenir ce worker la charge, pas sa moyenne. La base
    mesuree de la suite ICT est donc le pic du worker le plus lourd
    (1 181,4 MiB), et elle est plus lourde que la moyenne par worker
    (545,7 MiB)."""
    assert RSS_BUDGET_PAR_WORKER_MIB_ICT == 1181
    assert RSS_BUDGET_PAR_WORKER_MIB_ICT > RSS_BUDGET_PAR_WORKER_MIB


def test_ict_plafond_1_5_gio_ne_tue_plus_les_workers():
    # Meme slots persistants que la suite `scripts` : un seul worker doit
    # tenir, sinon le cgroup tue le job (exit 137).
    assert compute_workers(int(1.5 * GIB), budget_mib=budget_for("ict")) == 1


def test_ict_plafond_4_gio_tient_le_budget_mesure():
    # 4 Gio : (4096 - 256) // 1181 = 3 workers.
    assert compute_workers(4 * GIB, budget_mib=budget_for("ict")) == 3


def test_ict_sans_plafond_rend_la_valeur_nominale():
    assert compute_workers(None, budget_mib=budget_for("ict")) == DEFAULT_WORKERS


def test_plafond_inferieur_au_budget_rend_un_worker():
    # Un conteneur plus petit que le reserve master ne peut pas porter de
    # worker : on rend 1, pas 0.
    assert compute_workers(64 * MIB) == 1


def test_budget_mesure_est_un_entier_positif():
    assert isinstance(RSS_BUDGET_PAR_WORKER_MIB, int)
    assert RSS_BUDGET_PAR_WORKER_MIB > 0


# --- diagnostic ------------------------------------------------------------


def test_describe_nomme_la_limite_et_le_budget():
    texte = describe(int(1.5 * GIB))
    assert "xdist workers:" in texte
    assert "1.50 Gio" in texte
    assert str(RSS_BUDGET_PAR_WORKER_MIB) in texte


def test_describe_sans_plafond_le_dit():
    texte = describe(None)
    assert "absent ou illimite" in texte


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
