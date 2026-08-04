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

Depuis #8542 (Option C) le registre est le **repertoire** `twin_pairs.d/`
(un fichier par paire + `_schema.yaml` documentaire). La fixture sauvegarde
donc le repertoire, et l'agregation passe par `load_registry` -- le meme
chargeur que la production, pour que le test ne reimplemente pas la lecture.

Note de conception -- **pas de `pytest.skip` sur registre absent**. #8586 a
repointe la production vers `twin_pairs.d/` en laissant ce module sur
l'ancien `twin_pairs.yaml` : les 4 gardes sont passees en SKIP silencieux et
la suite est restee verte pendant que la garde anti-corruption #8508 ne
gardait plus rien. Un test qui skippe ne signale rien. D'ou `pytest.fail`.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_update_guard.py
"""
from __future__ import annotations

import importlib.util
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
REGISTRY_DIR = SCRIPT_DIR / "twin_pairs.d"

REPO_ROOT = SCRIPT_DIR.parents[1]  # scripts/notebook_tools -> scripts -> repo


def _load_module():
    spec = importlib.util.spec_from_file_location("check_twin_parity", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ctp = _load_module()


@pytest.fixture
def registry_backup():
    """Sauvegarde + restauration du REPERTOIRE de registre autour de chaque test.

    Meme si les tests qui reussissent sont read-only (--update n'ecrit
    que si selecteur OK), cette fixture protege contre les regressions
    silencieuses : si un futur patch casse la garde et que --update
    sans selecteur se met a reecrire, le test est restaure apres
    execution (rollback propre).

    Echoue -- ne skippe pas -- si le registre est introuvable : c'est
    exactement la panne #8586 que ces gardes doivent attraper.
    """
    if not REGISTRY_DIR.is_dir():
        pytest.fail(
            f"registre introuvable : {REGISTRY_DIR}. "
            "Si le registre a demenage, ce module doit suivre : un skip ici "
            "rendrait la suite verte sans rien garder (regression #8586)."
        )
    backup = REGISTRY_DIR.with_name(REGISTRY_DIR.name + ".bak.c909")
    if backup.exists():
        shutil.rmtree(backup)
    shutil.copytree(REGISTRY_DIR, backup)
    try:
        yield backup
    finally:
        shutil.rmtree(REGISTRY_DIR)
        shutil.move(str(backup), str(REGISTRY_DIR))


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

    Note : l'invariant teste ici est « les SHAs de la cible sont les
    blobs courants, les autres paires n'ont pas ete modifiees ». La
    fraicheur de `date`/`by` (rafraichis depuis #8570, ils ne peuvent
    plus heriter de l'audit precedent) est couverte separement par
    `test_check_twin_parity_surgical.py::test_update_pair_stamps_fresh_provenance`.
    """
    import subprocess as _sp

    all_pairs_before = ctp.load_registry(REGISTRY_DIR)
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

    # Rendre la cible DETERMINISTEMENT stale avant --update.
    #
    # Avant ce garde-fou, le test dependait de l'etat reel de la paire hardcoded
    # "Search-1 StateSpace" : il supposait que son `last_audit.date` etait en
    # retard sur aujourd'hui (afin que --update ait du travail -> "1 paire").
    # Mais une PR legitime qui rebaseline cette paire (C868-L : un twin edite =
    # rebaseline meme PR) met son `date` a aujourd'hui -> --update n'a plus rien
    # a faire -> "0 paire" -> faux echec (regression observee : PR #8660 a
    # rebaseline Search-1 avec date=2026-07-28, cassant ce test en CI).
    #
    # Fix robuste : on corrompt DELIBEREMENT la cible (date ancienne + SHAs
    # bogus) AVANT --update. Ainsi --update a TOUJOURS du travail, et les
    # assertions ci-dessous (SHA == HEAD blob apres rebaseline, autres paires
    # intactes) verifient le comportement reel -- pas un accident d'etat.
    import re as _re
    target_yaml = next(
        (yf for yf in sorted(REGISTRY_DIR.glob("*.yaml"))
         if target_name in yf.read_text(encoding="utf-8")),
        None,
    )
    assert target_yaml is not None, (
        f"Aucun yaml dans {REGISTRY_DIR} pour la paire {target_name!r}."
    )
    _BOGUS_SHA = "0" * 40
    _raw = target_yaml.read_text(encoding="utf-8")
    _raw = _re.sub(r'(date: )"?(\d{4}-\d{2}-\d{2})"?', r'\g<1>"2020-01-01"', _raw)
    _raw = _re.sub(r'(python_sha: )[0-9a-f]{40}', rf'\g<1>{_BOGUS_SHA}', _raw)
    _raw = _re.sub(r'(csharp_sha: )[0-9a-f]{40}', rf'\g<1>{_BOGUS_SHA}', _raw)
    target_yaml.write_text(_raw, encoding="utf-8")

    result = _run_update("--pair", target_name)
    assert result.returncode == 0, (
        f"--update --pair {target_name!r} aurait du reussir. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    assert "1 paire(s)" in result.stdout or "1 paire" in result.stdout, (
        f"Le script aurait du annoncer 1 paire mise a jour. stdout={result.stdout!r}"
    )

    after = ctp.load_registry(REGISTRY_DIR)

    # 1) La cible a les SHAs courants (= ce que `git rev-parse HEAD:<path>` retourne).
    # Depuis #9399, la cible drift est MIGREE vers la forme append-only `audits:` ;
    # `_latest_audit` lit le dernier enregistrement quelle que soit la forme
    # (legacy `last_audit:` ou liste `audits:`).
    target_after = next(p for p in after if p.get("name") == target_name)
    a_audit = ctp._latest_audit(target_after)
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
        b_audit = ctp._latest_audit(before)
        a_audit_other = ctp._latest_audit(p)
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
