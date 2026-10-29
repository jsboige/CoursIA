"""Tests de l'organe doc <-> quantification réelle (#23252).

Un test par verdict, et deux tests de non-régression payés par la mesure :

- le cas fondateur (`tts-fishaudio` : `NF4` dans les commentaires, `--half` dans la
  commande) doit rendre `DIVERGENT-HEAVIER` — un organe qui lit le fichier entier
  rendrait `nf4` et donc l'inverse ;
- `UNKNOWN` ne doit jamais être compté comme `OK`, et ne doit pas faire échouer la
  sortie (advisory).
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

_MODULE_PATH = Path(__file__).resolve().parents[1] / "genai-stack" / "check_quant_doc_divergence.py"
_spec = importlib.util.spec_from_file_location("check_quant_doc_divergence", _MODULE_PATH)
assert _spec and _spec.loader
organ = importlib.util.module_from_spec(_spec)
sys.modules["check_quant_doc_divergence"] = organ
_spec.loader.exec_module(organ)


# ------------------------------------------------------------------ classement


@pytest.mark.parametrize(
    "text,expected",
    [
        ("--half", "fp16"),
        ("BnB 4-bit NF4", "nf4"),
        ("load_in_4bit", "nf4"),
        ("int8_float16", "int8"),
        ("bfloat16 (fp8 opt via VLLM_QUANTIZATION=fp8)", "bf16"),
        ("xformers fp16", "fp16"),
        ("float32", "fp32"),
        ("aucune indication", "unknown"),
    ],
)
def test_classify(text: str, expected: str) -> None:
    assert organ.classify(text)[0] == expected


def test_classify_par_position_pas_par_priorite_de_table() -> None:
    """`bfloat16 (fp8 opt)` annonce du bf16 dont le fp8 est une option."""
    assert organ.classify("bfloat16 (fp8 opt)")[0] == "bf16"
    assert organ.classify("fp8 fallback, bfloat16 par defaut")[0] == "fp8"


# ---------------------------------------------------------------- lecture YAML


def test_strip_comments_ignore_les_commentaires_mais_garde_les_diese_guillemetes() -> None:
    raw = "# image bnb4 historique\nkey: value  # fp16 en fait\npass: \"a#b\"\n"
    out = organ.strip_comments(raw)
    assert "bnb4" not in out
    assert "fp16" not in out
    assert '"a#b"' in out


def test_effective_blocks_lit_la_commande_imbriquee_et_ignore_l_entete() -> None:
    """Le cas fondateur : NF4 dans l'en-tete commente, --half dans la commande."""
    compose = (
        "# FishAudio S2-Pro - official snapshot, fp16 (--half) on GPU1\n"
        "#   - The former custom image ...-bnb4 (~5GB VRAM), checkpoints/s2-pro-bnb4/\n"
        "services:\n"
        "  tts-fishaudio:\n"
        "    image: fishaudio/fish-speech:latest\n"
        "    command:\n"
        "      - --listen\n"
        "      - 0.0.0.0:8080\n"
        "      - --half\n"
        "    ports:\n"
        "      - 8080:8080\n"
    )
    blocks = organ.effective_blocks(compose)
    assert "--half" in blocks
    assert "bnb4" not in blocks.lower()
    assert "ports" not in blocks
    assert organ.classify(blocks)[0] == "fp16"


def test_effective_blocks_ne_prend_pas_les_cles_voisines() -> None:
    compose = (
        "services:\n"
        "  s:\n"
        "    image: x:fp8\n"
        "    command: [\"python\", \"run.py\", \"--dtype\", \"bfloat16\"]\n"
        "    environment:\n"
        "      - MODEL=x\n"
    )
    blocks = organ.effective_blocks(compose)
    assert organ.classify(blocks)[0] == "bf16"
    assert "image" not in blocks


# --------------------------------------------------------------------- doc


def test_parse_doc_lit_les_lignes_de_la_table() -> None:
    doc = (
        "# Doc\n"
        "### Quantization Settings per Service\n"
        "\n"
        "| Service | Hote | Model | Quantization | Idle VRAM |\n"
        "|---------|------|-------|-------------|-----------|\n"
        "| tts-fishaudio | po-2023 | S2-Pro | BnB 4-bit NF4 | ~5 GB |\n"
        "| whisper-api | po-2023 | large | int8_float16 | ~4 GB |\n"
        "\n"
        "### Section suivante\n"
        "| a | b | c | d | e |\n"
    )
    rows = organ.parse_doc(doc)
    assert [r["service"] for r in rows] == ["tts-fishaudio", "whisper-api"]
    assert rows[0]["declared"] == "BnB 4-bit NF4"
    assert rows[0]["idle_vram"] == "~5 GB"


# ------------------------------------------------------------------ verdicts


def _make_repo(tmp_path: Path, services: dict[str, str], doc_rows: str) -> Path:
    (tmp_path / "docs" / "genai").mkdir(parents=True)
    (tmp_path / "docs" / "genai" / "genai-services.md").write_text(
        "### Quantization Settings per Service\n\n"
        "| Service | Hote | Model | Quantization | Idle VRAM |\n"
        "|---|---|---|---|---|\n" + doc_rows,
        encoding="utf-8",
    )
    for name, compose in services.items():
        d = tmp_path / "docker-configurations" / "services" / name
        d.mkdir(parents=True)
        (d / "docker-compose.yml").write_text(compose, encoding="utf-8")
    return tmp_path


def _verdicts(repo: Path) -> dict[str, str]:
    findings = organ.evaluate(organ.Loader(repo))
    return {f["service"]: f["verdict"] for f in findings}


def test_verdict_divergence_lourde_et_ok(tmp_path: Path) -> None:
    repo = _make_repo(
        tmp_path,
        {
            "tts-fishaudio": "services:\n  s:\n    command:\n      - --half\n",
            "whisper-api": "services:\n  s:\n    environment:\n      - COMPUTE_TYPE=int8_float16\n",
        },
        "| tts-fishaudio | po-2023 | S2 | BnB 4-bit NF4 | ~5 GB |\n"
        "| whisper-api | po-2023 | large | int8_float16 | ~4 GB |\n",
    )
    v = _verdicts(repo)
    assert v["tts-fishaudio"] == "DIVERGENT-HEAVIER"
    assert v["whisper-api"] == "OK"


def test_verdict_divergence_legere(tmp_path: Path) -> None:
    repo = _make_repo(
        tmp_path,
        {"svc": "services:\n  s:\n    command:\n      - --load-in-4bit\n"},
        "| svc | po-2023 | m | fp16 | ~4 GB |\n",
    )
    assert _verdicts(repo)["svc"] == "DIVERGENT-LIGHTER"


def test_verdict_unknown_n_est_jamais_ok(tmp_path: Path) -> None:
    repo = _make_repo(
        tmp_path,
        {"svc": "services:\n  s:\n    image: quelquechose\n"},
        "| svc | po-2023 | m | fp16 | ~4 GB |\n",
    )
    findings = organ.evaluate(organ.Loader(repo))
    assert findings[0]["verdict"] == "UNKNOWN"
    # advisory : un UNKNOWN seul ne fait pas echouer l'organe
    assert organ.main(["--repo", str(repo), "--quiet"]) == 0


def test_verdict_orphelin_row_et_orphelin_service(tmp_path: Path) -> None:
    repo = _make_repo(
        tmp_path,
        {
            "fantome": "services:\n  s:\n    command:\n      - --half\n",
            "gpu-absent-de-la-table": (
                "services:\n  s:\n    deploy:\n      resources:\n"
                "        reservations:\n          devices:\n"
                "            - driver: nvidia\n              capabilities: [gpu]\n"
            ),
        },
        "| service-disparu | po-2023 | m | fp16 | ~4 GB |\n",
    )
    v = _verdicts(repo)
    assert v["service-disparu"] == "ORPHAN-ROW"
    assert v["gpu-absent-de-la-table"] == "ORPHAN-SERVICE"
    assert organ.main(["--repo", str(repo), "--quiet"]) == 1


def test_resolution_par_appartenance_evite_un_faux_orphelin(tmp_path: Path) -> None:
    """`tts-kokoro` vit dans `services/tts-api/` : pas un orphelin.

    Le nom n'y est pas un répertoire mais un service du compose hybride : c'est
    exactement la forme rencontrée dans l'arbre réel, et c'est elle qui rend le
    faux `ORPHAN-ROW` d'une résolution 1:1.
    """
    repo = _make_repo(
        tmp_path,
        {"tts-api": "services:\n  s:\n    command:\n      - --half\n"},
        "| tts-kokoro | po-2023 | Kokoro | fp16 | ~1 GB |\n",
    )
    hybrid = repo / "docker-configurations" / "services" / "tts-api" / "docker-compose-hybrid.yml"
    hybrid.write_text(
        "services:\n  tts-kokoro:\n    image: kokoro:latest\n    command:\n      - --fp16\n",
        encoding="utf-8",
    )
    findings = organ.evaluate(organ.Loader(repo))
    assert findings[0]["verdict"] != "ORPHAN-ROW"
    assert "tts-api" in findings[0]["source"]
