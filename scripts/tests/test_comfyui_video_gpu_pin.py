#!/usr/bin/env python3
"""Non-regression: epinglage GPU de comfyui-video (banc po-2023, WSL2).

Sous WSL2, `deploy.resources.reservations.devices` et
`NVIDIA_VISIBLE_DEVICES` n'isolent pas une carte : un conteneur declare avec
`device_ids=["1"]` voit encore les cartes du banc (mesure du 2026-11-24).
Seul `CUDA_VISIBLE_DEVICES` isole. Or le compose de comfyui-video portait la
valeur litterale `CUDA_VISIBLE_DEVICES=0,1`, qui ignore le `.env` du service :
les cartes restaient visibles alors que ce fichier visait la RTX 3090.

Sans GPU ni Docker, ces tests verifient :

1. la traduction carte nvidia-smi -> index PyTorch de l'entrypoint
   (`cuda_index_for`), sur la fonction reelle, extraite du fichier ;
2. que l'entrypoint passe cet index a `--cuda-device` et s'arrete si la carte
   visee est hors du masque ;
3. que le compose lise le masque dans le `.env` au lieu de l'ecraser, et garde
   l'ordre `PCI_BUS_ID`, sans lequel le pre-filtrage remappe les index
   (#3204).

Le temoin sur machine reelle est la lecture des cartes vues de CUDA depuis le
conteneur (torch). `nvidia-smi -L` ne le donne pas : il ignore le masque.

Run:
    python -m pytest scripts/tests/test_comfyui_video_gpu_pin.py
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pytest

from ._bash_resolution import resolve_bash

SERVICE_DIR = (
    Path(__file__).resolve().parents[2]
    / "docker-configurations"
    / "services"
    / "comfyui-video"
)
ENTRYPOINT = SERVICE_DIR / "entrypoint.sh"
COMPOSE = SERVICE_DIR / "docker-compose.yml"
ENV_EXAMPLE = SERVICE_DIR / ".env.example"

# Resolve bash ONCE, explicitly (cf test_bash_e_rc_capture.py, #17201).
BASH = resolve_bash()

_NO_BASH = pytest.mark.skipif(BASH is None, reason="no sane bash available (#17201)")

# Le corps de la fonction, de sa ligne de declaration a son accolade fermante.
_FUNCTION = re.compile(r"^cuda_index_for\(\) \{\n.*?^\}\n", re.DOTALL | re.MULTILINE)


def _run_index(gpu_id: str, visible: str) -> subprocess.CompletedProcess[str]:
    """Run the real `cuda_index_for` under `bash -e` and capture its index."""
    match = _FUNCTION.search(ENTRYPOINT.read_text(encoding="utf-8"))
    assert match, "cuda_index_for absent de entrypoint.sh"
    script = (
        match.group(0)
        + "\n"
        + 'if ! CUDA_INDEX=$(cuda_index_for "$1" "$2"); then exit 1; fi\n'
        + 'printf "%s" "$CUDA_INDEX"\n'
    )
    return subprocess.run(
        [BASH, "-e", "-c", script, "test", gpu_id, visible],
        capture_output=True,
        text=True,
        encoding="utf-8", errors="replace",
    )


def _compose_entry(name: str) -> str:
    """The `environment:` entry `- NAME=value` of the compose file."""
    found = re.findall(
        rf"^\s*- {re.escape(name)}=(.*)$",
        COMPOSE.read_text(encoding="utf-8"),
        re.MULTILINE,
    )
    assert len(found) == 1, f"{name} : {len(found)} entrees dans le compose"
    return found[0].strip()


@_NO_BASH
@pytest.mark.parametrize(
    ("gpu_id", "visible", "expected"),
    [
        pytest.param("1", "1", "0", id="carte-seule"),
        pytest.param("1", "0,1", "1", id="masque-large"),
        pytest.param("0", "", "0", id="sans-masque"),
        pytest.param("1", "1,0", "0", id="ordre-du-masque"),
        pytest.param("0", " 1, 0 ", "1", id="espaces"),
    ],
)
def test_cuda_index_is_the_position_in_the_mask(
    gpu_id: str, visible: str, expected: str
) -> None:
    """PyTorch attend la position de la carte dans la liste visible."""
    r = _run_index(gpu_id, visible)
    assert r.returncode == 0, r.stderr
    assert r.stdout == expected


@_NO_BASH
@pytest.mark.parametrize(
    ("gpu_id", "visible"),
    [
        pytest.param("2", "0,1", id="carte-inexistante"),
        pytest.param("1", "0", id="carte-hors-masque"),
    ],
)
def test_cuda_index_refuses_a_card_outside_the_mask(
    gpu_id: str, visible: str
) -> None:
    """La carte visee absente du masque : echec, sans repli vers une autre
    carte."""
    assert _run_index(gpu_id, visible).returncode == 1


def test_entrypoint_passes_the_translated_index_to_pytorch() -> None:
    """L'ecriture anterieure (`--cuda-device ${GPU_ID}`) donnait a PyTorch un
    identifiant nvidia-smi : avec un masque a une seule carte, l'index 1
    n'existe pas."""
    exec_lines = [
        line
        for line in ENTRYPOINT.read_text(encoding="utf-8").splitlines()
        if line.startswith("exec ")
    ]
    assert len(exec_lines) == 1, exec_lines
    assert "--cuda-device ${CUDA_INDEX}" in exec_lines[0]
    assert "--cuda-device ${GPU_ID}" not in exec_lines[0]


def test_entrypoint_stops_when_the_card_is_outside_the_mask() -> None:
    text = ENTRYPOINT.read_text(encoding="utf-8")
    call = (
        'if ! CUDA_INDEX=$(cuda_index_for "$GPU_ID" '
        '"${CUDA_VISIBLE_DEVICES:-}"); then'
    )
    assert call in text
    branch = text.split(call, 1)[1]
    assert re.match(r"\n[^\n]*\n\s*exit 1\n", branch), branch


def test_compose_reads_the_mask_from_the_env_file() -> None:
    """Le litteral `CUDA_VISIBLE_DEVICES=0,1` ignorait le `.env`, ou la carte
    visee est posee."""
    assert (
        _compose_entry("CUDA_VISIBLE_DEVICES")
        == "${CUDA_VISIBLE_DEVICES:-${GPU_DEVICE_ID:-0}}"
    )


def test_compose_keeps_the_pci_bus_id_order() -> None:
    """Sans cet ordre, l'index CUDA est l'inverse de nvidia-smi sur ce banc :
    le masque `1` designait alors la RTX 3080 Ti (#3204)."""
    assert _compose_entry("CUDA_DEVICE_ORDER") == "PCI_BUS_ID"


def test_env_example_shows_only_the_targeted_card() -> None:
    values = {}
    for line in ENV_EXAMPLE.read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.startswith("#") and "=" in line:
            key, value = line.split("=", 1)
            values[key] = value
    assert values["GPU_DEVICE_ID"] == values["CUDA_VISIBLE_DEVICES"]
