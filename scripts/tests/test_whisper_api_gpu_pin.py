#!/usr/bin/env python3
"""Non-regression : epinglage GPU de whisper-api (banc po-2023, WSL2).

Convention d'index du banc (#28423) : `CUDA_DEVICE_ORDER=PCI_BUS_ID`, donc
l'index CUDA est l'index `nvidia-smi` -- GPU0 = RTX 3080 Ti (16 Go),
GPU1 = RTX 3090 (24 Go). Sans cet ordre, l'index CUDA est l'inverse de
`nvidia-smi` sur ce banc : un masque `0` designe alors la 3090.

Sous WSL2, `deploy.resources.reservations.devices` et
`NVIDIA_VISIBLE_DEVICES` n'isolent pas une carte ; seul
`CUDA_VISIBLE_DEVICES` isole. Les trois champs sont donc derives d'une seule
variable, `GPU_PCI_INDEX`, et ne peuvent pas se contredire.

`whisper-api` vise la RTX 3090 (`GPU_PCI_INDEX=1`) : la decision de la regie
GPU du banc (#28423) corrige la documentation qui le placait sur la 3080 Ti.
Le compose ne relit plus `GPU_DEVICE_ID` ni `CUDA_VISIBLE_DEVICES` du `.env` :
ces cles y portent l'ancienne convention (`0` sur ce banc), et le masque `0`
sous `PCI_BUS_ID` designe la 3080 Ti (mesure du 2026-11-24 dans le conteneur).

Sans GPU ni Docker, ces tests lisent les fichiers de configuration.

Run:
    python -m pytest scripts/tests/test_whisper_api_gpu_pin.py
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

SERVICE_DIR = (
    Path(__file__).resolve().parents[2]
    / "docker-configurations"
    / "services"
    / "whisper-api"
)
COMPOSES = [
    SERVICE_DIR / "docker-compose.yml",
    SERVICE_DIR / "docker-compose-hybrid.yml",
]
README = SERVICE_DIR / "README.md"
# Carte visee : GPU1 = RTX 3090 (index nvidia-smi, donc index PCI).
TARGET_INDEX = "1"
KNOB = "${GPU_PCI_INDEX:-1}"

# Cles de l'ancienne convention : le `.env` du banc y porte `0` pour ce service.
LEGACY_KEYS = (
    "${GPU_DEVICE_ID",
    "${CUDA_VISIBLE_DEVICES",
    "${NVIDIA_VISIBLE_DEVICES",
)


def _read(path: Path) -> str:
    assert path.is_file(), f"{path} absent"
    return path.read_text(encoding="utf-8")


def _env_entry(text: str, name: str) -> str:
    """L'entree `environment:` `- NAME=valeur` du fichier de composition."""
    found = re.findall(rf"^\s*- {re.escape(name)}=(.*)$", text, re.MULTILINE)
    assert len(found) == 1, f"{name} : {len(found)} entrees dans le compose"
    return found[0].strip()


def _device_ids(text: str) -> list[str]:
    return re.findall(r"^\s*device_ids:\s*\[(.*)\]\s*$", text, re.MULTILINE)


@pytest.mark.parametrize("compose", COMPOSES, ids=lambda path: path.name)
class TestCompose:
    def test_devices_are_ordered_by_pci_bus_id(self, compose: Path) -> None:
        assert _env_entry(_read(compose), "CUDA_DEVICE_ORDER") == "PCI_BUS_ID"

    def test_the_mask_targets_the_3090(self, compose: Path) -> None:
        assert _env_entry(_read(compose), "CUDA_VISIBLE_DEVICES") == KNOB

    def test_nvidia_visible_devices_mirrors_the_mask(self, compose: Path) -> None:
        """Il n'isole pas la carte, mais doit refleter la cible."""
        assert _env_entry(_read(compose), "NVIDIA_VISIBLE_DEVICES") == KNOB

    def test_device_ids_mirror_the_mask(self, compose: Path) -> None:
        """Pareil : declaratif sur ce banc, il doit refleter la cible."""
        assert _device_ids(_read(compose)) == [f"'{KNOB}'"]

    def test_legacy_keys_are_no_longer_read(self, compose: Path) -> None:
        text = _read(compose)
        for key in LEGACY_KEYS:
            assert key not in text, key


@pytest.mark.parametrize("compose", COMPOSES, ids=lambda path: path.name)
def test_header_and_labels_name_the_target_card(compose: Path) -> None:
    """La ligne d'en-tete GPU nomme la 3090 ; le label legacy a disparu."""
    text = _read(compose)
    header = [line for line in text.splitlines() if line.startswith("# GPU:")]
    assert len(header) == 1, header
    assert "RTX 3090" in header[0], header[0]
    assert "rtx-3080ti" not in text


def test_readme_declares_the_target_card() -> None:
    gpu_rows = re.findall(r"^\| GPU \|(.*)\|$", _read(README), re.MULTILINE)
    assert len(gpu_rows) == 1, gpu_rows
    assert "GPU 1" in gpu_rows[0] and "RTX 3090" in gpu_rows[0], gpu_rows[0]


def test_readme_documents_the_knob() -> None:
    rows = re.findall(r"^\| `GPU_PCI_INDEX` \|(.*)\|$", _read(README), re.MULTILINE)
    assert len(rows) == 1, rows
    assert rows[0].strip().startswith("`1`"), rows[0]


def test_readme_file_table_names_the_target_card() -> None:
    """La table des fichiers decrit chaque compose avec sa carte."""
    text = _read(README)
    assert "GPU 0" not in text, [line for line in text.splitlines() if "GPU 0" in line]
    rows = re.findall(r"^\| `docker-compose[^`]*` \|(.*)\|$", text, re.MULTILINE)
    assert len(rows) == 2, rows
    for row in rows:
        assert "RTX 3090" in row, row


@pytest.mark.parametrize("compose", COMPOSES, ids=lambda path: path.name)
def test_labels_match_the_target_card(compose: Path) -> None:
    labels = re.findall(r'^\s*- "com\.myia\.gpu=(.*)"$', _read(compose), re.MULTILINE)
    assert labels == ["rtx-3090"], labels
