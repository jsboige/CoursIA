#!/usr/bin/env python3
"""Garde anti-corruption silencieuse du registre `--update` (#8508).

Avant c.909 : `python check_twin_parity.py --update` (sans selecteur)
reecrivait le `last_audit` de TOUTES les paires du registre (88 paires
au moment de la PR). Un agent qui suivait la remediation affichee par
la CI twin-parity pour rebaseliner UNE paire marquait « audite
aujourd'hui » TOUTES les paires en derive -- y compris celles qui
derivaient pour une raison qui meritait un examen.

Depuis c.909 : `--update` exige un selecteur explicite (`--family`,
`--pair`, ou opt-in `--yes-all-pairs`). Sans selecteur : argparse
refuse avec un message qui reference l'issue #8508 et les lecons
L963/L974. `--pair <name>` rebaseline une seule paire nommee.

Ces tests couvrent :
    1. `--update` seul -> argparse.error (exit != 0)
    2. `--update --pair <existing>` -> succes sur 1 paire
    3. `--update --pair <unknown>` -> erreur explicite (exit 1)
    4. `--update --pair X --family Y` -> argparse.error (mutuellement exclusifs)
    5. Le registre de reference reste byte-identique apres chaque test
       (chaque test restore via backup).

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_update_guard.py
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

# Make the script importable from the tests dir.
SCRIPT_DIR = (
    Path(__file__).resolve().parent.parent  # scripts/notebook_tools/tests/../
)
SCRIPT = SCRIPT_DIR / "check_twin_parity.py"
REGISTRY = SCRIPT_DIR / "twin_pairs.yaml"

REPO_ROOT = REGISTRY.resolve().parents[2]  # scripts/notebook_tools -> scripts -> repo


@pytest.fixture
def registry_backup():
    """Sauvegarde + restauration du registre autour de chaque test.

    Meme si les tests qui reussissent sont read-only (--update n'ecrit
    que si selecteur OK), cette fixture protege contre les regressions
    silencieuses : si un futur patch casse la garde et que --update
    sans selecteur se met a reecrire, le test est restaure apres
    execution (rollback propre).
    """
    if not REGISTRY.exists():
        pytest.skip(f"registre introuvable : {REGISTRY}")
    backup = REGISTRY.with_suffix(".yaml.bak.c909")
    shutil.copy2(REGISTRY, backup)
    try:
        yield backup
    finally:
        shutil.copy2(backup, REGISTRY)
        backup.unlink(missing_ok=True)


def _run_update(*extra_args: str) -> subprocess.CompletedProcess:
    """Execute le script en sous-processus (subprocess.run) pour capturer
    l'exit code reel et le stderr -- c'est l'integration-test de la garde
    argparse, pas un mock.
    """
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--update", *extra_args],
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )


def test_update_without_selector_refuses(registry_backup):
    """`--update` seul DOIT etre refuse par argparse (cf #8508).

    Avant c.909 : exit 0, registre re-ecrit silencieusement (corruption).
    Apres c.909 : exit != 0, stderr contient une mention de l'issue #8508
    ou des lecons L963/L974.
    """
    result = _run_update()
    assert result.returncode != 0, (
        f"--update sans selecteur aurait du etre refuse (exit != 0). "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    # Le message argparse doit pointer vers la garde pour que l'agent
    # comprenne pourquoi sa commande est refusee (issue + lecons).
    combined = (result.stdout + result.stderr).lower()
    assert any(
        needle in combined
        for needle in ("#8508", "l963", "l974", "selecteur explicite")
    ), f"Message de garde absent. stderr={result.stderr!r} stdout={result.stdout!r}"


def test_update_with_pair_selector_succeeds_on_existing_pair(registry_backup):
    """`--update --pair <existing>` rebaseline exactement 1 paire.

    Verifie qu'apres l'operation, **seule la cible** est affectee :
    ses SHAs `last_audit` correspondent aux blobs git courants, et
    les autres paires sont **byte-identiques** a la sauvegarde pre-test.

    Note : `update_pair` est intentionnellement **idempotent cote
    date** : il ne touche la date que si le SHA a change (cf
    `check_twin_parity.py` l.207 `today = pair.get('last_audit', {})`).
    On ne peut donc pas exiger `date == today` ici -- le bon invariant
    est « les SHAs de la cible sont les blobs courants, les autres
    paires n'ont pas ete modifiees ».
    """
    import subprocess as _sp
    import yaml

    all_pairs_before = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    assert isinstance(all_pairs_before, list) and all_pairs_before, "registre vide"
    # Choisir une cible connue (Search-1 StateSpace existe dans le registre actuel).
    target_entry = next(
        (p for p in all_pairs_before if p.get("name") == "Search-1 StateSpace"),
        all_pairs_before[0],
    )
    target_name = target_entry["name"]
    target_py_path = target_entry["python"]
    target_cs_path = target_entry["csharp"]

    # SHAs courants pour comparaison (HEAD working tree).
    def _cur_sha(rel_path: str) -> str | None:
        r = _sp.run(
            ["git", "ls-tree", "HEAD", "--", rel_path],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
        )
        if r.returncode != 0 or not r.stdout.strip():
            return None
        parts = r.stdout.split()
        return parts[2] if len(parts) >= 3 else None

    expected_py_sha = _cur_sha(target_py_path)
    expected_cs_sha = _cur_sha(target_cs_path)

    result = _run_update("--pair", target_name)
    assert result.returncode == 0, (
        f"--update --pair {target_name!r} aurait du reussir. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    assert "1 paire(s)" in result.stdout or "1 paire" in result.stdout, (
        f"Le script aurait du annoncer 1 paire mise a jour. stdout={result.stdout!r}"
    )

    after = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))

    # 1) La cible a les SHAs courants (= ce que `git rev-parse HEAD:<path>` retourne).
    target_after = next(p for p in after if p.get("name") == target_name)
    a_audit = target_after.get("last_audit") or {}
    assert a_audit.get("python_sha") == expected_py_sha, (
        f"Cible {target_name!r}.python_sha = {a_audit.get('python_sha')!r}, "
        f"attendu {expected_py_sha!r} (git ls-tree HEAD)."
    )
    assert a_audit.get("csharp_sha") == expected_cs_sha, (
        f"Cible {target_name!r}.csharp_sha = {a_audit.get('csharp_sha')!r}, "
        f"attendu {expected_cs_sha!r} (git ls-tree HEAD)."
    )

    # 2) Les AUTRES paires sont byte-identiques (memes SHAs qu'avant).
    by_name_before = {p["name"]: p for p in all_pairs_before}
    drifted = []
    for p in after:
        name = p.get("name")
        if name == target_name:
            continue
        before = by_name_before.get(name)
        if before is None:
            drifted.append(f"{name}: disparu du registre")
            continue
        b_audit = before.get("last_audit") or {}
        a_audit_other = p.get("last_audit") or {}
        for sha_key in ("python_sha", "csharp_sha"):
            if b_audit.get(sha_key) != a_audit_other.get(sha_key):
                drifted.append(
                    f"{name}.{sha_key}: {b_audit.get(sha_key)} -> {a_audit_other.get(sha_key)}"
                )
    assert not drifted, (
        "D'autres paires que la cible ont ete modifiees -- "
        "la garde anti-corruption silencieuse a-t-elle casse ?\n"
        + "\n".join(drifted)
    )


def test_update_with_pair_selector_refuses_on_unknown_pair(registry_backup):
    """`--update --pair <unknown>` retourne une erreur explicite.

    Important : on doit obtenir un message qui liste des noms connus
    pour que l'agent puisse corriger son selecteur.
    """
    result = _run_update("--pair", "ThisPairDoesNotExist-9999")
    assert result.returncode != 0, (
        f"--pair <unknown> aurait du echouer. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    combined = result.stdout + result.stderr
    assert "ThisPairDoesNotExist-9999" in combined, (
        f"Le message devrait citer le nom inconnu. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )


def test_update_with_pair_and_family_is_mutually_exclusive(registry_backup):
    """`--pair` et `--family` ne peuvent pas cohabiter avec `--update`.

    L'intersection des deux filtres peut etre vide par accident ;
    argparse.error les rejette en amont (plus clair que de retourner
    silencieusement 0 paires mises a jour).
    """
    result = _run_update("--pair", "AnyPair", "--family", "AnyFamily")
    assert result.returncode != 0, (
        f"--pair + --family simultanes aurait du etre rejete. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    combined = (result.stdout + result.stderr).lower()
    assert "mutuellement exclusifs" in combined or "incompatible" in combined, (
        f"Message d'incompatibilite attendu. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )
