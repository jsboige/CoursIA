"""Temoins du correctif #25370 : le cache chaud se juge PAR GRAPHE.

Le defaut : `prepare_lake()` comparait `lake-manifest.json` **octet pour
octet** avec celui du cache pivot. Or deux manifestes de lakes differents
decrivent le meme graphe de dependances alors que le fichier differe sur
deux champs qui ne le decrivent pas :

- le `name` racine (`"conway"` contre `"decision_theory_lean"`) : il differe
  PAR CONSTRUCTION d'un lake a l'autre ;
- l'`inputRev` d'un paquet (`"v4.33.0"` contre le SHA qui le resout) : c'est
  la revision DEMANDEE, pas le commit resolu.

La comparaison octet rendait donc le cache chaud inapplicable a tout lake
hors du pivot, et bloquait toute PR `.lean` qui ne touche pas le pivot.

Ces tests sont les temoins positifs du correctif : ils rougissent sur le
code casse (comparaison octet) et restent verts sur le code corrige
(comparaison par graphe). Chaque refus doit NOMMER le paquet et les deux
valeurs divergentes -- un refus muet ne dit pas quoi corriger.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import attest_local_build as alb  # noqa: E402

TOOLCHAIN = "leanprover/lean4:v4.33.0\n"

MATHLIB = {
    "name": "mathlib",
    "url": "https://github.com/leanprover-community/mathlib4.git",
    "rev": "db584cd6d46c92f209a44c0f1c829460d327499d",
    "inputRev": "v4.33.0",
    "subDir": None,
}
AESOP = {
    "name": "aesop",
    "url": "https://github.com/leanprover-community/aesop",
    "rev": "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e",
    "inputRev": "master",
    "subDir": None,
}


def _manifest(name: str, packages: list[dict]) -> dict:
    return {
        "version": "1.2.0",
        "packagesDir": ".lake/packages",
        "name": name,
        "packages": packages,
    }


def _write_lake(root: Path, manifest: dict, toolchain: str = TOOLCHAIN) -> Path:
    lake = root / "lake"
    lake.mkdir(parents=True, exist_ok=True)
    (lake / "lean-toolchain").write_text(toolchain, encoding="utf-8")
    (lake / "lake-manifest.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8"
    )
    return lake


def _write_cache(root: Path, manifest: dict, toolchain: str = TOOLCHAIN) -> Path:
    cache = root / "cache"
    cache.mkdir(parents=True, exist_ok=True)
    (cache / "lean-toolchain").write_text(toolchain, encoding="utf-8")
    (cache / "lake-manifest.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8"
    )
    return cache


def test_root_name_and_input_rev_do_not_break_compatibility(tmp_path):
    """`name` racine different et `inputRev` differents : meme graphe, donc
    le cache chaud s'applique. C'est le cas mesure de `decision_theory_lean`
    contre le pivot `conway_lean`."""
    mine = _manifest("decision_theory_lean", [
        dict(MATHLIB, inputRev="db584cd6d46c92f209a44c0f1c829460d327499d"),
        AESOP,
    ])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine)
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.check_cache_compatibility(lake, cache)

    assert verdict["ok"], (
        "le cache chaud doit s'appliquer : meme graphe de dependances "
        "(le `name` racine et les `inputRev` ne sont pas le graphe) -- "
        "raison rendue : {}".format(verdict.get("reason"))
    )
    assert verdict["checks"] == ["lean-toolchain", "lake-manifest.json"]


def test_different_rev_refuses_naming_package_and_both_revs(tmp_path):
    """Un `rev` different refuse, et le refus NOMME le paquet et les deux
    `rev` -- sans cela le correctif ne dit pas quoi corriger."""
    mine = _manifest("other", [dict(MATHLIB, rev="1111111111111111111111111111111111111111"), AESOP])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine)
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.check_cache_compatibility(lake, cache)

    assert not verdict["ok"], "un rev different doit refuser"
    reason = verdict["reason"]
    assert "mathlib" in reason, "le refus doit nommer le paquet : {}".format(reason)
    assert "1111111111111111111111111111111111111111" in reason, (
        "le refus doit nommer le rev du lake : {}".format(reason)
    )
    assert "db584cd6d46c92f209a44c0f1c829460d327499d" in reason, (
        "le refus doit nommer le rev du cache : {}".format(reason)
    )


def test_extra_package_refuses(tmp_path):
    """Un paquet de plus dans le lake refuse : le graphe n'est plus le meme."""
    mine = _manifest("other", [MATHLIB, AESOP, {
        "name": "batteries",
        "url": "https://github.com/leanprover-community/batteries",
        "rev": "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d",
        "inputRev": "main",
        "subDir": None,
    }])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine)
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.check_cache_compatibility(lake, cache)

    assert not verdict["ok"], "un paquet de plus doit refuser"
    assert "batteries" in verdict["reason"], (
        "le refus doit nommer le paquet en trop : {}".format(verdict["reason"])
    )


def test_missing_package_refuses(tmp_path):
    """Un paquet en moins dans le lake refuse aussi."""
    mine = _manifest("other", [MATHLIB])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine)
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.check_cache_compatibility(lake, cache)

    assert not verdict["ok"], "un paquet en moins doit refuser"
    assert "aesop" in verdict["reason"], (
        "le refus doit nommer le paquet manquant : {}".format(verdict["reason"])
    )


def test_different_toolchain_refuses(tmp_path):
    """La toolchain se compare au CONTENU : un ecart refuse, meme si le
    graphe est identique."""
    mine = _manifest("other", [MATHLIB, AESOP])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine, toolchain="leanprover/lean4:v4.19.0\n")
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.check_cache_compatibility(lake, cache)

    assert not verdict["ok"], "une toolchain differente doit refuser"
    assert "lean-toolchain" in verdict["reason"], verdict["reason"]


def test_unreadable_manifest_refuses_closed(tmp_path):
    """Un manifeste illisible refuse (fail-closed) : l'absence de mesure
    n'est jamais un accord."""
    mine = _manifest("other", [MATHLIB, AESOP])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine)
    (lake / "lake-manifest.json").write_text("{ pas du json", encoding="utf-8")
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.check_cache_compatibility(lake, cache)

    assert not verdict["ok"], "un manifeste illisible doit refuser"
    assert "illisible" in verdict["reason"], verdict["reason"]


def test_different_manifest_version_refuses(tmp_path):
    """Un `version` de manifeste different refuse : il decrit le format du
    graphe, pas seulement son contenu."""
    mine = _manifest("other", [MATHLIB, AESOP])
    theirs = _manifest("conway", [MATHLIB, AESOP])
    theirs["version"] = "1.1.0"

    lake = _write_lake(tmp_path / "mine", mine)
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.check_cache_compatibility(lake, cache)

    assert not verdict["ok"], "un `version` differente doit refuser"
    assert "version" in verdict["reason"], verdict["reason"]


def test_prepare_lake_accepts_a_lake_outside_the_pivot(tmp_path):
    """TEMOIN DU DEFAUT, au niveau de l'entree publique.

    Sur le code casse (comparaison octet pour octet), ce lake est REFUSE
    ("lake-manifest.json different du cache") alors qu'il decrit le meme
    graphe que le cache ; sur le code corrige, il passe.

    `.lake/packages` est pre-cree pour que la jonction ne soit pas posee :
    le test reste hermetique et ne touche a aucun cache reel.
    """
    mine = _manifest("decision_theory_lean", [
        dict(MATHLIB, inputRev="db584cd6d46c92f209a44c0f1c829460d327499d"),
        AESOP,
    ])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine)
    (lake / ".lake" / "packages").mkdir(parents=True)
    cache = _write_cache(tmp_path / "cache", theirs)

    verdict = alb.prepare_lake(lake, cache)

    assert verdict["ok"], (
        "un lake hors pivot qui decrit le MEME graphe doit obtenir le cache "
        "chaud -- raison rendue : {}".format(verdict.get("reason"))
    )
    assert verdict.get("junction") is False


def test_prepare_lake_refuses_before_touching_the_cache(tmp_path):
    """Un refus de cache ne laisse AUCUNE trace : la jonction n'est posee
    qu'apres le verdict (fail-closed, pas de mutation a l'aveugle)."""
    mine = _manifest("other", [dict(MATHLIB, rev="1111111111111111111111111111111111111111"), AESOP])
    theirs = _manifest("conway", [MATHLIB, AESOP])

    lake = _write_lake(tmp_path / "mine", mine)
    cache = _write_cache(tmp_path / "cache", theirs)
    (cache / ".lake" / "packages").mkdir(parents=True)

    verdict = alb.prepare_lake(lake, cache)

    assert not verdict["ok"]
    assert not (lake / ".lake").exists(), (
        "aucune jonction ne doit etre posee quand le cache ne s'applique pas")
