"""Tests pour build_golden_set.py -- sortie stable par chemin FR (#22015).

Avant le fix, la table etait serialisee dans l'ordre d'iteration
(`sorted(by_rel)`, donc un tri par chemin EN). Un deplacement de chemin
(iit_lean, PR #22008) decaulait tous les indices : 459/460 paires
changeaient dans le diff pour deux chemins deplaces. Le fix trie la table
par le chemin FR (cle stable) ; ces tests verifient la propriete.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest

_MODULE = Path(__file__).resolve().parents[1] / "build_golden_set.py"
_spec = importlib.util.spec_from_file_location("build_golden_set", _MODULE)
bgs = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(bgs)


def _serialize(data: dict) -> str:
    """Meme serialisation que main() : indent=1, ensure_ascii=False, \\n final."""
    return json.dumps(data, ensure_ascii=False, indent=1) + "\n"


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _build_fixture(root: Path) -> None:
    """Trois paires lean (FR + _en) dans le meme dossier d1/."""
    for base in ("A", "B", "C"):
        _write(root / "d1" / f"{base}.lean", f"-- fr {base}\n")
        _write(root / "d1" / f"{base}_en.lean", f"-- en {base}\n")


@pytest.fixture()
def gen(tmp_path, monkeypatch):
    """Redirige collect() vers tmp_path ; rend (data, serialized)."""
    monkeypatch.setattr(bgs, "REPO_ROOT", tmp_path)

    def _gen() -> tuple[dict, str]:
        data = bgs.collect()
        return data, _serialize(data)

    return _gen


def test_pairs_sorted_by_fr(tmp_path, gen):
    """Critere 1 : la table est serialisee triee par chemin FR (cle stable)."""
    _build_fixture(tmp_path)
    data, _ = gen()
    frs = [p["fr"] for p in data["pairs"]]
    assert frs == sorted(frs), "la table doit etre triee par chemin FR"
    # Controle positif : l'ordre par chemin EN n'est PAS le tri (sinon le
    # test ne distinguerait pas le fix) -- verifie sur un cas ou les deux
    # ordres divergent (memes basenames, extensions .md et .lean).
    _write(tmp_path / "d1" / "R.lean", "-- fr R\n")
    _write(tmp_path / "d1" / "R_en.lean", "-- en R\n")
    _write(tmp_path / "d1" / "R.md", "fr readme R\n")
    _write(tmp_path / "d1" / "R.en.md", "en readme R\n")
    data2, _ = gen()
    frs2 = [p["fr"] for p in data2["pairs"]]
    en2 = [p["en"] for p in data2["pairs"] if p["en"].startswith("d1/R")]
    assert frs2 == sorted(frs2)
    assert en2 == ["d1/R_en.lean", "d1/R.en.md"], "le tri par FR place R_en avant R.en"
    assert en2 != sorted(en2), "le tri par FR doit differir du tri par EN ici"


def test_move_only_touches_moved_lines(tmp_path, gen):
    """Critere 2 : un deplacement de chemin ne change que les lignes deplacées.

    Deplacement LOCAL de la paire B (renommage B -> B2 dans d1/ : B2 se trie
    entre A et C, donc aucun autre index ne decale). Les lignes des paires A
    et C restent byte-identiques a la meme position ; seules les lignes du
    bloc B different.
    """
    _build_fixture(tmp_path)
    _, text_before = gen()

    (tmp_path / "d1" / "B.lean").rename(tmp_path / "d1" / "B2.lean")
    (tmp_path / "d1" / "B_en.lean").rename(tmp_path / "d1" / "B2_en.lean")
    _, text_after = gen()

    before = text_before.splitlines()
    after = text_after.splitlines()
    assert len(before) == len(after)

    changed = [i for i, (a, b) in enumerate(zip(before, after)) if a != b]
    assert changed, "le deplacement doit modifier au moins les lignes de B"
    # Toute ligne modifiee doit citer la paire deplacee (B ancien / B2 nouveau).
    for i in changed:
        assert "B" in before[i] or "B" in after[i], (
            f"ligne hors-paire-B modifiee (index {i}): "
            f"{before[i]!r} -> {after[i]!r}"
        )


def test_regeneration_is_deterministic(tmp_path, gen):
    """Soutient le critere 3 : la regeneration est byte-identique (diff = 0)."""
    _build_fixture(tmp_path)
    _, text1 = gen()
    _, text2 = gen()
    assert text1 == text2, "la regeneration doit etre byte-identique"
