from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

import pytest

MODULE_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MODULE_DIR))

import ucr_anomaly_fetch as ucr


@pytest.fixture(autouse=True)
def clear_memory_cache() -> None:
    ucr._CACHE.clear()


def test_manifest_matches_five_ml10_series() -> None:
    manifest = json.loads((MODULE_DIR / "ucr_anomaly_manifest.json").read_text())

    assert manifest == ucr._MANIFEST
    assert len(manifest) == 5
    for metadata in manifest.values():
        assert isinstance(metadata["size"], int) and metadata["size"] > 0
        assert len(metadata["sha256"]) == 64
        int(metadata["sha256"], 16)


def test_fetch_raw_rejects_corrupted_memory_cache() -> None:
    name = "series.txt"
    expected = b"expected UCR bytes"
    ucr._MANIFEST[name] = {
        "size": len(expected),
        "sha256": hashlib.sha256(expected).hexdigest(),
    }
    ucr._CACHE[name] = b"corrupted cache"

    try:
        with pytest.raises(ucr.UcrFetchError, match="integrite UCR invalide"):
            ucr.fetch_raw(name)
    finally:
        ucr._MANIFEST.pop(name)


def test_fetch_raw_accepts_verified_disk_cache(tmp_path: Path) -> None:
    name = "series.txt"
    blob = b"verified UCR bytes"
    ucr._MANIFEST[name] = {
        "size": len(blob),
        "sha256": hashlib.sha256(blob).hexdigest(),
    }
    (tmp_path / name).write_bytes(blob)

    try:
        assert ucr.fetch_raw(name, cache_dir=str(tmp_path)) == blob
        assert ucr._CACHE[name] == blob
    finally:
        ucr._MANIFEST.pop(name)


def test_fetch_raw_rejects_corrupted_disk_cache(tmp_path: Path) -> None:
    name = "series.txt"
    expected = b"expected UCR bytes"
    ucr._MANIFEST[name] = {
        "size": len(expected),
        "sha256": hashlib.sha256(expected).hexdigest(),
    }
    (tmp_path / name).write_bytes(b"corrupted cache")

    try:
        with pytest.raises(ucr.UcrFetchError, match="integrite UCR invalide"):
            ucr.fetch_raw(name, cache_dir=str(tmp_path))
        assert name not in ucr._CACHE
    finally:
        ucr._MANIFEST.pop(name)


def test_fetch_raw_verifies_network_member_before_caching(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    name = "series.txt"
    expected = b"network UCR bytes"
    ucr._MANIFEST[name] = {
        "size": len(expected),
        "sha256": hashlib.sha256(expected).hexdigest(),
    }
    monkeypatch.setattr(ucr, "_content_length", lambda _url: 42)
    monkeypatch.setattr(
        ucr,
        "_central_directory",
        lambda _url, _total: {f"archive/{name}": (3, 7, 8)},
    )
    monkeypatch.setattr(
        ucr, "_read_member", lambda _url, _offset, _size, _method: expected
    )

    try:
        assert ucr.fetch_raw(name, cache_dir=str(tmp_path)) == expected
        assert (tmp_path / name).read_bytes() == expected
    finally:
        ucr._MANIFEST.pop(name)


def test_fetch_raw_rejects_corrupted_network_member(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    name = "series.txt"
    expected = b"expected network bytes"
    ucr._MANIFEST[name] = {
        "size": len(expected),
        "sha256": hashlib.sha256(expected).hexdigest(),
    }
    monkeypatch.setattr(ucr, "_content_length", lambda _url: 42)
    monkeypatch.setattr(
        ucr,
        "_central_directory",
        lambda _url, _total: {f"archive/{name}": (3, 7, 8)},
    )
    monkeypatch.setattr(
        ucr, "_read_member", lambda _url, _offset, _size, _method: b"changed"
    )

    try:
        with pytest.raises(ucr.UcrFetchError, match="integrite UCR invalide"):
            ucr.fetch_raw(name, cache_dir=str(tmp_path))
        assert name not in ucr._CACHE
        assert not (tmp_path / name).exists()
    finally:
        ucr._MANIFEST.pop(name)


def test_write_cache_cleans_temporary_file_on_publish_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    def fail_replace(_source: str, _destination: str) -> None:
        raise OSError("simulated publish failure")

    monkeypatch.setattr(ucr.os, "replace", fail_replace)

    with pytest.raises(OSError, match="simulated publish failure"):
        ucr._write_cache(str(tmp_path), "series.txt", b"verified")

    assert list(tmp_path.iterdir()) == []


def test_load_manifest_rejects_malformed_entry(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text('{"series.txt": 5}', encoding="utf-8")
    monkeypatch.setattr(ucr, "_MANIFEST_PATH", str(manifest_path))

    with pytest.raises(ucr.UcrFetchError, match="entree invalide"):
        ucr._load_manifest()


def test_fetch_raw_rejects_unmanifested_series() -> None:
    with pytest.raises(ucr.UcrFetchError, match="aucune empreinte"):
        ucr.fetch_raw("unknown.txt")
