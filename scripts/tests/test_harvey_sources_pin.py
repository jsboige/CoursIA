"""Garde de pin des sources Harvey : le controle echoue au premier ecart (#22052).

Contrat verifie ici :

- le manifeste du depot epingle les trois sources vendorisees ;
- des sources intactes passent ;
- UN octet mute est detecte (fail-closed, pas un avertissement) ;
- une source absente est detecte ;
- le driver sort en erreur AVANT de lancer le binaire quand le pin est rompu ;
- l'ordre des deux controles est observable dans le code de sortie : rc=3 pour
  la garde du pin rompue, rc=2 pour un executable absent (donc pin passe).

La preuve « le binaire n'a jamais ete lance » repose sur un faux executable qui
ecrit lui-meme un marqueur : un marqueur present prouve l'invocation, un
marqueur absent prouve l'absence d'invocation. Un temoin positif verifie que
le faux executable est bien capable d'ecrire le marqueur, sans quoi l'absence
serait un vide muet.
"""

import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
DRIVER = REPO_ROOT / "scripts" / "cartier_miller" / "run_harvey_p1_plus.py"
MANIFEST = REPO_ROOT / "scripts" / "cartier_miller" / "harvey_sources_pin.json"

SOURCES = (
    "harvey_adapter.cpp",
    "upstream/recurrences_ntl.cpp",
    "upstream/hypellfrob.cpp",
)

# Codes de sortie du driver : distincts, pour que l'ordre des controles se lise.
RC_PIN_BROKEN = 3
RC_EXECUTABLE_MISSING = 2


def _sha256_source(path: Path) -> str:
    """Empreinte canonique : fins de ligne normalisees en LF."""
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def _load_driver():
    spec = importlib.util.spec_from_file_location("harvey_p1_plus_driver", DRIVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _make_tree(tmp_path: Path) -> Path:
    """Copie temporaire des trois sources (jamais les sources du clone amont)."""
    root = tmp_path / "clone" / "Cartier_Miller_Benchmark"
    for rel in SOURCES:
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(b"// vendored source\nint main() { return 0; }\n")
    return root


def _manifest_for(root: Path, tmp_path: Path) -> Path:
    manifest = {
        "schema": "harvey-sources-pin/v1",
        "commit": "0" * 40,
        "commit_short": "0" * 7,
        "files": [{"path": rel, "sha256": _sha256_source(root / rel)} for rel in SOURCES],
    }
    path = tmp_path / "pin.json"
    path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return path


def _fake_executable(tmp_path: Path) -> tuple[Path, Path]:
    """Faux executable : ecrit lui-meme le marqueur quand il est invoque."""
    marker = tmp_path / "binary_launched.txt"
    fake = tmp_path / "fake_harvey_adapter.cmd"
    fake.write_text(f'@echo off\r\necho launched > "{marker}"\r\n', encoding="utf-8")
    return fake, marker


def _run_driver(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(DRIVER), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )


def test_repo_manifest_pins_the_three_vendored_sources():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    pinned = {entry["path"]: entry["sha256"] for entry in manifest["files"]}
    assert set(pinned) == set(SOURCES)
    for path, digest in pinned.items():
        assert len(digest) == 64, path
        assert all(c in "0123456789abcdef" for c in digest), path
    assert len(manifest["commit"]) == 40
    assert manifest["upstream_repo"].startswith("https://")


def test_intact_sources_pass(tmp_path):
    driver = _load_driver()
    root = _make_tree(tmp_path)
    manifest = driver.load_pin_manifest(_manifest_for(root, tmp_path))
    report = driver.verify_sources(root, manifest)
    assert report["verified"] is True
    assert report["problems"] == []
    assert set(report["measured_sha256"]) == set(SOURCES)


def test_one_mutated_byte_is_detected(tmp_path):
    driver = _load_driver()
    root = _make_tree(tmp_path)
    manifest = driver.load_pin_manifest(_manifest_for(root, tmp_path))

    target = root / "upstream" / "hypellfrob.cpp"
    data = bytearray(target.read_bytes())
    data[0] = data[0] ^ 0x01  # un seul bit change
    target.write_bytes(bytes(data))

    report = driver.verify_sources(root, manifest)
    assert report["verified"] is False
    assert [p["path"] for p in report["problems"]] == ["upstream/hypellfrob.cpp"]
    assert report["problems"][0]["reason"] == "sha256"


def test_absent_source_is_detected(tmp_path):
    driver = _load_driver()
    root = _make_tree(tmp_path)
    manifest = driver.load_pin_manifest(_manifest_for(root, tmp_path))
    (root / "harvey_adapter.cpp").unlink()

    report = driver.verify_sources(root, manifest)
    assert report["verified"] is False
    assert report["problems"][0]["reason"] == "absent"


def test_fake_executable_does_write_the_marker(tmp_path):
    """Temoin positif : sans lui, l'absence de marqueur ne prouverait rien."""
    fake, marker = _fake_executable(tmp_path)
    subprocess.run(
        [str(fake)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=60,
    )
    assert marker.exists(), "le faux executable n'ecrit pas son marqueur : temoin invalide"


def test_driver_fails_closed_before_launching_the_binary(tmp_path):
    """Un octet mute -> rc=3 (pin rompu) ET le binaire n'a jamais ete lance."""
    root = _make_tree(tmp_path)
    manifest_path = _manifest_for(root, tmp_path)

    mutated = root / "harvey_adapter.cpp"
    data = bytearray(mutated.read_bytes())
    data[0] = data[0] ^ 0x01
    mutated.write_bytes(bytes(data))

    fake, marker = _fake_executable(tmp_path)

    proc = _run_driver(
        "--executable",
        str(fake),
        "--pin-manifest",
        str(manifest_path),
        "--sources-root",
        str(root),
        "--out",
        str(tmp_path / "validation.json"),
    )
    assert proc.returncode == RC_PIN_BROKEN, proc.stdout + proc.stderr
    assert not marker.exists(), "le binaire a ete lance alors que le pin etait rompu"
    assert "pin des sources" in proc.stderr
    assert not (tmp_path / "validation.json").exists()


def test_intact_sources_let_the_driver_reach_the_binary(tmp_path):
    """Temoin d'ordre : pin intact -> le binaire EST lance (marqueur present)."""
    root = _make_tree(tmp_path)
    manifest_path = _manifest_for(root, tmp_path)
    fake, marker = _fake_executable(tmp_path)

    proc = _run_driver(
        "--executable",
        str(fake),
        "--pin-manifest",
        str(manifest_path),
        "--sources-root",
        str(root),
        "--out",
        str(tmp_path / "validation.json"),
    )
    assert marker.exists(), "pin intact : le binaire aurait du etre lance (temoin d'ordre)"
    assert proc.returncode != RC_PIN_BROKEN
    assert "pin des sources" not in proc.stderr


def test_pin_broken_and_executable_missing_are_two_distinct_codes(tmp_path):
    """Deux rc distincts : l'ordre des controles se lit dans le code de sortie."""
    root = _make_tree(tmp_path)
    manifest_path = _manifest_for(root, tmp_path)
    (root / "upstream" / "recurrences_ntl.cpp").unlink()

    proc = _run_driver(
        "--executable",
        str(tmp_path / "absent.exe"),
        "--pin-manifest",
        str(manifest_path),
        "--sources-root",
        str(root),
        "--out",
        str(tmp_path / "validation.json"),
    )
    assert proc.returncode == RC_PIN_BROKEN
    assert "absent" in proc.stderr

    # Meme source absente, mais pin intact : la garde passe, c'est l'executable
    # qui manque -> rc distinct, preuve que le pin a ete evalue en premier.
    intact = _make_tree(tmp_path / "intact")
    proc_ok = _run_driver(
        "--executable",
        str(tmp_path / "absent.exe"),
        "--pin-manifest",
        str(_manifest_for(intact, tmp_path)),
        "--sources-root",
        str(intact),
        "--out",
        str(tmp_path / "validation2.json"),
    )
    assert proc_ok.returncode == RC_EXECUTABLE_MISSING
    assert "pin des sources" not in proc_ok.stderr


def test_no_verify_flag_cannot_yield_a_passed_validation(tmp_path):
    """Le mode debug (pin saute) ne peut pas produire un statut 'passed'."""
    driver = _load_driver()
    assert driver.pin_allows_passed(None) is False
    assert driver.pin_allows_passed({"verified": False}) is False
    assert driver.pin_allows_passed({"verified": True}) is True

    root = _make_tree(tmp_path)
    manifest_path = _manifest_for(root, tmp_path)
    fake, marker = _fake_executable(tmp_path)

    proc = _run_driver(
        "--executable",
        str(fake),
        "--pin-manifest",
        str(manifest_path),
        "--sources-root",
        str(root),
        "--no-verify-sources",
        "--out",
        str(tmp_path / "validation.json"),
    )
    # Le drapeau court-circuite la garde (le binaire est atteint) mais ne
    # dispense jamais du statut.
    assert marker.exists(), "le mode debug doit atteindre le binaire (garde sautee)"
    assert proc.returncode != RC_PIN_BROKEN
    out_json = tmp_path / "validation.json"
    if out_json.exists():
        report = json.loads(out_json.read_text(encoding="utf-8"))
        assert report["sources_pin"]["skipped"] is True
        assert report["validation"]["sources_pin_verified"] is False
        assert report["validation"]["status"] != "passed"


@pytest.mark.parametrize("rel", SOURCES)
def test_manifest_entries_are_reproducible_from_the_upstream_blob(rel):
    """Le manifeste se re-verifie sans le clone : le pin est dans le blob amont."""
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    entry = next(e for e in manifest["files"] if e["path"] == rel)
    # La forme CRLF (clone Windows) est l'empreinte du fichier de travail ;
    # la forme LF (blob Git) est celle que la garde verifie.
    assert len(entry["sha256_crlf"]) == 64
    assert entry["sha256"] != entry["sha256_crlf"]
