#!/usr/bin/env python3
"""Non-regression : epinglage GPU de tts-fishaudio (banc po-2023, WSL2).

Convention d'index du banc (#28423) : `CUDA_DEVICE_ORDER=PCI_BUS_ID`, donc
l'index CUDA est l'index `nvidia-smi` -- GPU0 = RTX 3080 Ti (16 Go),
GPU1 = RTX 3090 (24 Go). Sans cet ordre, l'index CUDA est l'inverse de
`nvidia-smi` sur ce banc : un masque `0` designe alors la 3090.

Sous WSL2, `deploy.resources.reservations.devices` et
`NVIDIA_VISIBLE_DEVICES` n'isolent pas une carte ; seul
`CUDA_VISIBLE_DEVICES` isole. Les trois champs sont donc derives d'une seule
variable, `GPU_PCI_INDEX`, et ne peuvent pas se contredire.
La cible de ce service est GPU1 = RTX 3090 (24 Go), partagee avec les
autres services d'inference du banc (decision de la regie, #28423
paragraphe 2). Mesure du 2026-11-24 dans le conteneur en service : aucune
isolation -- torch voit deux cartes -- et cuda:0 = RTX 3090 par
l'inversion de l'ordre, pas par construction. Sous l'ordre PCI sans
masque, cuda:0 deviendrait la 3080 Ti (16 Go), insuffisante pour le
snapshot fp16 (~20,3 Go de VRAM) : le compose fixe l'ordre et derive les
trois champs du noeud cible.

Sans GPU ni Docker, ces tests lisent les fichiers de configuration.

Run:
    python -m pytest scripts/tests/test_tts_fishaudio_gpu_pin.py
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

SERVICE_DIR = (
    Path(__file__).resolve().parents[2]
    / "docker-configurations"
    / "services"
    / "tts-fishaudio"
)
COMPOSES = [
    SERVICE_DIR / "docker-compose.yml",
    SERVICE_DIR / "docker-compose.int4.yml",
]
ENV_EXAMPLE = SERVICE_DIR / ".env.example"
# Carte visee : GPU1 = RTX 3090 (index nvidia-smi, donc index PCI).
TARGET_INDEX = "1"
KNOB = "${GPU_PCI_INDEX:-1}"

# Cles de l'ancienne convention : `FISHAUDIO_GPU_ID`, portee par le `.env.example` (aucune cle GPU dans
# le `.env` du banc).
LEGACY_KEYS = (
    "${FISHAUDIO_GPU_ID",
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

def _assignments(text: str) -> dict[str, str]:
    """Les affectations actives d'un `.env.example` (hors commentaires)."""
    values = {}
    for line in text.splitlines():
        if line.strip() and not line.startswith("#") and "=" in line:
            key, value = line.split("=", 1)
            values[key] = value
    return values


@pytest.mark.parametrize("compose", COMPOSES, ids=lambda path: path.name)
class TestCompose:
    def test_devices_are_ordered_by_pci_bus_id(self, compose: Path) -> None:
        assert _env_entry(_read(compose), "CUDA_DEVICE_ORDER") == "PCI_BUS_ID"

    def test_the_mask_targets_the_gpu_1(self, compose: Path) -> None:
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
    """L'en-tete nomme la carte cible, et le label reste celui de la 3090."""
    text = _read(compose)
    header = "\n".join(text.splitlines()[:12])
    assert "RTX 3090" in header, header
    assert "GPU_PCI_INDEX 1" in header, header
    labels = re.findall(r"com\.myia\.gpu=([\w.-]+)", text)
    assert labels == ["rtx-3090"], labels
    assert "rtx-3080ti" not in text


def test_both_composes_pin_the_same_card() -> None:
    """Les deux variantes du service epinglent la meme carte."""
    found = {compose.name: _device_ids(_read(compose)) for compose in COMPOSES}
    assert found == {compose.name: [f"'{KNOB}'"] for compose in COMPOSES}, found


def test_env_example_documents_the_knob() -> None:
    """Le .env.example ne porte plus que GPU_PCI_INDEX et sa convention."""
    values = _assignments(_read(ENV_EXAMPLE))
    assert values.get("GPU_PCI_INDEX") == "1", values.get("GPU_PCI_INDEX")
    assert "FISHAUDIO_GPU_ID" not in values


def test_env_example_declares_the_convention() -> None:
    """Le .env.example nomme l'ordre PCI et la carte cible."""
    text = _read(ENV_EXAMPLE)
    assert "PCI_BUS_ID" in text
    assert "RTX 3090" in text
