"""Tests du cote rust: optionnel de check_twin_parity (#27098 organe 1).

Decision coordinateur ai-01 du 22/11 13:20Z : « Il faut etendre
``check_twin_parity.py`` a un cote ``rust:`` optionnel (empreinte de blob et de
contenu, DRIFT sur le cote Rust), avec ses tests, son controle positif sur un
triplet livre et un controle negatif. »

Invariants eprouves ici (le controle positif/negatif sur le triplet sudoku-02
REEL vit dans le body de la PR -- ces tests unitaires couvrent la mecanique) :

- retro-compatibilite stricte : une paire binaire sans ``rust:`` se comporte
  BYTE-IDENTIQUEMENT a avant (pas de drift_sides "rust", pas de no_baseline
  parasite, pas de cle rust dans l'audit emis par update_pair) ;
- triplet attesté : les trois empreintes de blob -> OK ;
- DRIFT sur le cote Rust : blob et contenu, ``drift_sides == ["rust"]`` -- le
  statut agree ne dit pas QUEL jumeau a bouge, drift_sides le dit (#23020) ;
- no_baseline rust : declarer ``rust:`` sans l'attester = DRIFT (le triplet ne
  passe pas la discipline d'audit par la declaration seule) ;
- MISSING rust : carnet declare absent de git ;
- numbering : le numero de base du Rust s'aligne sur le Python (meme regle que
  py/cs, numbering_exception partage) ;
- update_pair : enregistre rust_sha/content_rust_sha SEULEMENT si la paire
  declare le cote (pas de cle parasite dans les audits des paires binaires) ;
- premiere attestation rust n'est JAMAIS un no-op (_shas_match) ;
- verify_recorded_sha : empreinte rust enregistree divergente = MISMATCH ;
- _pair_paths_diverge / _classify_per_pair : le cote rust participe aux
  verdicts per-pair (deplacement, drift introduit).
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_twin_parity import (  # noqa: E402
    _classify_per_pair,
    _git_blob_sha,
    _pair_paths_diverge,
    _shas_match,
    check_pair,
    update_pair,
    verify_recorded_sha,
)


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-c", "user.name=test", "-c", "user.email=test@example.com", *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=str(repo), check=True,
    )


def _make_repo(tmp_path: Path, files: dict[str, str]) -> Path:
    repo = tmp_path / "mini_repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    for rel, content in files.items():
        f = repo / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(content, encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "fixture")
    return repo


_MINIMAL_NB = '{"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}'


def _triplet(repo: Path, name: str, py: str, cs: str, ru: str | None,
             **extra) -> dict:
    """Paire declaree, avec cote rust optionnel."""
    pair = {"name": name, "family": "Fixture", "python": py, "csharp": cs,
            "parity_level": "surface", **extra}
    if ru is not None:
        pair["rust"] = ru
    return pair


def _attested_triplet(repo: Path, name: str, py: str, cs: str, ru: str,
                      **extra) -> dict:
    """Triplet dont le last_audit enregistre les blob SHAs COURANTS (status OK)."""
    pair = _triplet(repo, name, py, cs, ru, **extra)
    pair["last_audit"] = {
        "date": "2026-11-23",
        "by": "test-fixture",
        "python_sha": _git_blob_sha(repo, py, "HEAD"),
        "csharp_sha": _git_blob_sha(repo, cs, "HEAD"),
        "rust_sha": _git_blob_sha(repo, ru, "HEAD"),
    }
    return pair


# --- retro-compatibilite stricte : la paire binaire ne change pas ------------


def test_paire_binaire_sans_rust_inchangee(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
    })
    pair = {"name": "P-10", "family": "Fixture",
            "python": "nb/py-10.ipynb", "csharp": "nb/cs-10.ipynb",
            "parity_level": "surface",
            "last_audit": {
                "date": "2026-11-23", "by": "t",
                "python_sha": _git_blob_sha(repo, "nb/py-10.ipynb", "HEAD"),
                "csharp_sha": _git_blob_sha(repo, "nb/cs-10.ipynb", "HEAD"),
            }}
    r = check_pair(repo, pair)
    assert r["status"] == "OK", r["details"]
    assert r["drift_sides"] == []
    assert r["no_baseline"] is False
    assert r["rust"] is None
    assert r["current_rust_sha"] is None


def test_update_pair_binaire_n_emet_pas_de_cle_rust(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
    })
    pair = _triplet(repo, "P-10", "nb/py-10.ipynb", "nb/cs-10.ipynb", None)
    audit, _, _ = update_pair(repo, pair, by="t")
    assert "rust_sha" not in audit
    assert "content_rust_sha" not in audit


# --- triplet atteint : OK -----------------------------------------------------


def test_triplet_atteint_ok(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _attested_triplet(
        repo, "T-10", "nb/py-10.ipynb", "nb/cs-10.ipynb", "nb/ru-10.ipynb"))
    assert r["status"] == "OK", r["details"]
    assert r["drift_sides"] == []
    assert r["rust"] == "nb/ru-10.ipynb"
    assert r["current_rust_sha"] == _git_blob_sha(repo, "nb/ru-10.ipynb", "HEAD")


def test_triplet_content_rust_sha_atteint_ok(tmp_path):
    """content_rust_sha (metadata-immune) : la voie privilegiee post--update."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair = _triplet(repo, "T-10c", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                    "nb/ru-10.ipynb")
    audit, _, is_noop = update_pair(repo, pair, by="t")
    assert not is_noop
    assert audit["rust_sha"] == _git_blob_sha(repo, "nb/ru-10.ipynb", "HEAD")
    assert audit["content_rust_sha"]
    pair["last_audit"] = audit
    r = check_pair(repo, pair)
    assert r["status"] == "OK", r["details"]
    assert r["current_content_rust_sha"] == audit["content_rust_sha"]


# --- DRIFT sur le cote Rust ---------------------------------------------------


def test_drift_rust_blob_dit_quel_cote(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair = _attested_triplet(repo, "T-d1", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                             "nb/ru-10.ipynb")
    pair["last_audit"]["rust_sha"] = "0" * 40  # forge : diverge du courant
    r = check_pair(repo, pair)
    assert r["status"] == "DRIFT", r["details"]
    assert r["drift_sides"] == ["rust"], r["drift_sides"]
    assert any("Rust a drift" in d for d in r["details"]), r["details"]


def test_drift_rust_content_dit_quel_cote(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair = _triplet(repo, "T-d2", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                    "nb/ru-10.ipynb")
    audit, _, _ = update_pair(repo, pair, by="t")
    audit["content_rust_sha"] = "1" * 64  # forge : diverge du courant
    pair["last_audit"] = audit
    r = check_pair(repo, pair)
    assert r["status"] == "DRIFT", r["details"]
    assert r["drift_sides"] == ["rust"], r["drift_sides"]
    assert any("Rust a drift (content)" in d for d in r["details"]), r["details"]


def test_drift_rust_isole_python_csharp_intacts(tmp_path):
    """Le drift rust ne contamine pas les cotes binaires (#23020 symetrique)."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair = _attested_triplet(repo, "T-d3", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                             "nb/ru-10.ipynb")
    pair["last_audit"]["rust_sha"] = "0" * 40
    r = check_pair(repo, pair)
    assert r["recorded_python_sha"] == r["current_python_sha"]
    assert r["recorded_csharp_sha"] == r["current_csharp_sha"]
    assert r["drift_sides"] == ["rust"]


# --- no_baseline rust : declarer sans attester --------------------------------


def test_rust_declare_sans_attestation_est_no_baseline(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair = _attested_triplet(repo, "T-nb", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                             "nb/ru-10.ipynb")
    del pair["last_audit"]["rust_sha"]  # la paire declare rust:, l'audit non
    r = check_pair(repo, pair)
    assert r["status"] == "DRIFT", r["details"]
    assert r["no_baseline"] is True
    assert any("Pas de rust_sha enregistre" in d for d in r["details"])


# --- MISSING rust -------------------------------------------------------------


def test_rust_manquant_dans_git(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
    })
    pair = _triplet(repo, "T-m", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                    "nb/ru-10.ipynb")
    r = check_pair(repo, pair)
    assert r["status"] == "MISSING", r["details"]
    assert "rust" in r["drift_sides"]
    assert any("Rust MANQUANT" in d for d in r["details"])


# --- numbering rust ------------------------------------------------------------


def test_numbering_rust_divergent(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-11.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _attested_triplet(
        repo, "T-n1", "nb/py-10.ipynb", "nb/cs-10.ipynb", "nb/ru-11.ipynb"))
    assert r["status"] == "NUMBERING-DRIFT", r["details"]
    assert any("rust=11" in d and "python=10" in d for d in r["details"]), r


def test_numbering_rust_exception_documentee_ok(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-11.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _attested_triplet(
        repo, "T-n2", "nb/py-10.ipynb", "nb/cs-10.ipynb", "nb/ru-11.ipynb",
        numbering_exception="numero 11 deja pris par un companion (2026-11-23)",
    ))
    assert r["status"] == "OK", r["details"]
    assert any("documentee" in d for d in r["details"])


# --- update_pair / no-op / premiere attestation --------------------------------


def test_shas_match_premiere_attestation_rust_pas_un_noop(tmp_path):
    """Ajouter rust: a une paire attestee + --update APPEND (changement reel)."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair_avant = _triplet(repo, "T-u1", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                          None)
    audit_avant, _, _ = update_pair(repo, pair_avant, by="t")
    pair_triplet = _triplet(repo, "T-u1", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                            "nb/ru-10.ipynb")
    audit_apres, _, is_noop = update_pair(repo, pair_triplet, by="t")
    assert not is_noop  # la premiere attestation rust est un changement reel
    assert not _shas_match(audit_avant, audit_apres)
    assert _shas_match(audit_apres, dict(audit_apres))  # identite : no-op


def test_shas_match_rust_divergent_pas_un_noop():
    base = {"python_sha": "a", "csharp_sha": "b",
            "rust_sha": "r1", "content_rust_sha": None}
    other = {"python_sha": "a", "csharp_sha": "b", "rust_sha": "r2"}
    assert not _shas_match(base, other)
    same = {"python_sha": "a", "csharp_sha": "b", "rust_sha": "r1"}
    assert _shas_match(base, same)


def test_update_triplet_orphelin_rust_par_squash(tmp_path):
    """Un blob rust enregistre plus ancre de HEAD casse le no-op (#11919)."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    # Un commit anterieur porte un autre contenu rust, puis reecriture.
    ru = repo / "nb" / "ru-10.ipynb"
    ru.write_text('{"cells": [], "metadata": {"x": 1}, "nbformat": 4}', encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "intermediaire")
    stale = _git_blob_sha(repo, "nb/ru-10.ipynb", "HEAD")
    ru.write_text(_MINIMAL_NB, encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "final")
    pair = _triplet(repo, "T-o", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                    "nb/ru-10.ipynb")
    pair["last_audit"] = {
        "date": "2026-11-23", "by": "t",
        "python_sha": _git_blob_sha(repo, "nb/py-10.ipynb", "HEAD"),
        "csharp_sha": _git_blob_sha(repo, "nb/cs-10.ipynb", "HEAD"),
        "content_python_sha": None, "content_csharp_sha": None,
        "rust_sha": stale,
        "content_rust_sha": None,
    }
    audit, _, is_noop = update_pair(repo, pair, by="t")
    assert not is_noop  # l'orphelin rust doit etre rebaseline, pas no-op


# --- verify_recorded_sha -------------------------------------------------------


def test_verify_recorded_sha_rust_mismatch(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair = _attested_triplet(repo, "T-v", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                             "nb/ru-10.ipynb")
    pair["last_audit"]["rust_sha"] = "0" * 40
    r = verify_recorded_sha(repo, pair)
    assert r["status"] == "MISMATCH", r["mismatches"]
    assert any(m.startswith("rust_sha:") for m in r["mismatches"]), r


def test_verify_recorded_sha_triplet_ok(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/ru-10.ipynb": _MINIMAL_NB,
    })
    pair = _triplet(repo, "T-v2", "nb/py-10.ipynb", "nb/cs-10.ipynb",
                    "nb/ru-10.ipynb")
    audit, _, _ = update_pair(repo, pair, by="t")
    pair["last_audit"] = audit
    r = verify_recorded_sha(repo, pair)
    assert r["status"] == "OK", r["mismatches"]


# --- verdicts per-pair : le cote rust participe --------------------------------


def test_classify_drift_rust_introduit_par_la_pr():
    assert _classify_per_pair(
        "OK", "DRIFT", base_drift=set(), head_drift={"rust"}) == "DRIFT_INTRODUCED"


def test_classify_drift_rust_pre_existant():
    assert _classify_per_pair(
        "DRIFT", "DRIFT", base_drift={"rust"}, head_drift={"rust"}) == "DRIFT_PRE_EXISTING"


def test_pair_paths_diverge_sur_le_cote_rust():
    base_pp = {"python": "nb/py-10.ipynb", "csharp": "nb/cs-10.ipynb",
               "rust": "nb/ru-10.ipynb"}
    head_pp = {"python": "nb/py-10.ipynb", "csharp": "nb/cs-10.ipynb",
               "rust": "nb/ru-12.ipynb"}
    assert _pair_paths_diverge(base_pp, head_pp)
    assert not _pair_paths_diverge(base_pp, base_pp)
