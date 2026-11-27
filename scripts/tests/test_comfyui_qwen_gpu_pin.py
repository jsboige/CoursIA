#!/usr/bin/env python3
"""Non-regression : epinglage GPU de comfyui-qwen (banc po-2023, WSL2).

Convention d'index du banc (#28423) : `CUDA_DEVICE_ORDER=PCI_BUS_ID`, donc
l'index CUDA est l'index `nvidia-smi` -- GPU0 = RTX 3080 Ti (16 Go),
GPU1 = RTX 3090 (24 Go). Sans cet ordre, l'index CUDA est l'inverse de
`nvidia-smi` sur ce banc : un masque `0` designe alors la 3090.

Sous WSL2, `deploy.resources.reservations.devices` et
`NVIDIA_VISIBLE_DEVICES` n'isolent pas une carte ; seul
`CUDA_VISIBLE_DEVICES` isole. Les trois champs sont donc derives d'une seule
variable, `GPU_PCI_INDEX`, et ne peuvent pas se contredire.
La cible de ce service est GPU0 = RTX 3080 Ti (16 Go) : il partage la
carte avec tts-api et le serveur d'embeddings vLLM (decision de la regie,
#28423 paragraphe 2). Le .env du banc rend aujourd'hui le triplet 0/0/0
sans ordre, ce qui placerait une re-creation sur la 3090 : le compose fixe
desormais l'ordre et derive les trois champs du meme noeud.

Sans GPU ni Docker, ces tests lisent les fichiers de configuration.

Run:
    python -m pytest scripts/tests/test_comfyui_qwen_gpu_pin.py
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

SERVICE_DIR = (
    Path(__file__).resolve().parents[2]
    / "docker-configurations"
    / "services"
    / "comfyui-qwen"
)
COMPOSES = [
    SERVICE_DIR / "docker-compose.yml",
    SERVICE_DIR / "docker-compose-no-auth.yml",
]
README = SERVICE_DIR / "README.md"
ENV_EXAMPLE = SERVICE_DIR / ".env.example"
# Carte visee : GPU0 = RTX 3080 Ti (index nvidia-smi, donc index PCI).
TARGET_INDEX = "0"
KNOB = "${GPU_PCI_INDEX:-0}"

# Cles de l'ancienne convention : le `.env` du banc y porte `GPU_DEVICE_ID=0`, `CUDA_VISIBLE_DEVICES=0` et `NVIDIA_VISIBLE_DEVICES=0`.
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

    def test_the_mask_targets_the_gpu_0(self, compose: Path) -> None:
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
    """L'en-tete nomme la carte cible, et le label ne l'annonce plus en 3090."""
    text = _read(compose)
    header = "\n".join(text.splitlines()[:6])
    assert "RTX 3080 Ti" in header, header
    assert "GPU_PCI_INDEX 0" in header, header
    labels = re.findall(r"com\.myia\.gpu=([\w.-]+)", text)
    assert labels == ["rtx-3080ti"], labels
    assert "rtx-3090" not in text


def test_readme_intro_names_the_target_card() -> None:
    """L'introduction du README annonce la carte de la decision (GPU0)."""
    intro = "\n".join(_read(README).splitlines()[:5])
    assert "RTX 3080 Ti" in intro, intro


def test_readme_architecture_puts_the_service_on_the_target_card() -> None:
    """Le bloc Architecture place Qwen sur GPU 0, pas sur GPU 1."""
    lines = _read(README).splitlines()
    gpu0 = [line for line in lines if line.startswith("GPU 0 (RTX")]
    gpu1 = [line for line in lines if line.startswith("GPU 1 (RTX")]
    assert len(gpu0) == 1 and len(gpu1) == 1, (gpu0, gpu1)
    assert "Qwen Image-Edit" in gpu0[0], gpu0[0]
    assert "Qwen Image-Edit" not in gpu1[0], gpu1[0]


def test_readme_does_not_claim_an_inverted_index() -> None:
    """Aucune ligne ne declare un index PyTorch inverse de nvidia-smi."""
    for line in _read(README).splitlines():
        found = re.search(r"nvidia-smi GPU (\d) = PyTorch GPU (\d)", line)
        if found:
            assert found.group(1) == found.group(2), line


def test_readme_documents_the_knob() -> None:
    """Le README documente GPU_PCI_INDEX et la convention, sans les cles legacy."""
    values = _assignments(_read(README))
    assert values.get("GPU_PCI_INDEX") == "0", values.get("GPU_PCI_INDEX")
    assert "CUDA_DEVICE_ORDER=PCI_BUS_ID" in _read(README)
    for legacy in ("GPU_DEVICE_ID", "CUDA_VISIBLE_DEVICES", "NVIDIA_VISIBLE_DEVICES"):
        assert legacy not in values, legacy


def test_env_example_documents_the_knob() -> None:
    """Le .env.example ne porte plus que GPU_PCI_INDEX et sa convention."""
    values = _assignments(_read(ENV_EXAMPLE))
    assert values.get("GPU_PCI_INDEX") == "0", values.get("GPU_PCI_INDEX")
    for legacy in ("GPU_DEVICE_ID", "CUDA_VISIBLE_DEVICES", "NVIDIA_VISIBLE_DEVICES"):
        assert legacy not in values, legacy


def test_env_example_declares_the_convention() -> None:
    """Le .env.example nomme l'ordre PCI et la carte cible."""
    text = _read(ENV_EXAMPLE)
    assert "PCI_BUS_ID" in text
    assert "RTX 3080 Ti" in text
