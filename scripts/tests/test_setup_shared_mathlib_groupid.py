"""Tests de la desambiguation de groupId de setup_shared_mathlib.ps1 (#13962).

Defaut fondateur : deux groupes de manifests distincts (graphs de dependances
differents) partageant le MEME couple (toolchain, revision mathlib) recevaient
le MEME groupId historique ``toolchain-rev8`` -- donc le MEME cache
``.mathlib-cache/<id>/`` et le MEME share-state.json. Le Scan le constatait par
un simple avertissement ; l'Apply, lui, jonctionnait le second groupe dans le
cache du premier (Test-CacheValid ne compare que la revision mathlib, identique
ici) et fusionnait les membres des deux groupes dans un seul etat, alors que
les traces .lake/build du cache ont ete compilees contre les dependances du
premier groupe seulement.

Le correctif epingle par ces tests :

- quand le bucket (toolchain, revision mathlib) porte PLUSIEURS groupes de
  manifests, chaque groupe recoit un suffixe = 8 premiers hex du SHA-256 de
  son GroupKey (cle portant TOUT le graphe de dependances) ;
- sans collision, l'ID historique non suffixe est PRESERVE -- les caches
  deja en place sur les machines restent atteignables ;
- la formule du suffixe est recalculée cote Python : c'est une spec pincee,
  pas seulement "deux IDs differents" ;
- l'Apply ne fusionne plus les groupes collidants : un groupe sans donneur est
  skip AVANT toute jonction au lieu d'etre jonctionne dans le cache du voisin.

Les tests executent le VRAI script sur des fixtures git minimales, comme
test_setup_shared_mathlib.py et test_setup_shared_mathlib_scan.py.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

# pwsh (script #Requires -Version 7.0) pour Scan ; junctions NTFS en plus pour
# Apply -- memes gardes que les fichiers freres.
requires_pwsh = pytest.mark.skipif(
    shutil.which("pwsh") is None,
    reason="pwsh requis pour executer setup_shared_mathlib.ps1 (#13962)",
)
requires_windows = pytest.mark.skipif(
    os.name != "nt" or shutil.which("pwsh") is None,
    reason="junctions NTFS + pwsh requis (#13962)",
)

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "lean" / "setup_shared_mathlib.ps1"

TOOLCHAIN = "tc-test"
MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
BATTERIES_R1 = "1111111111111111111111111111111111111111"
BATTERIES_R2 = "2222222222222222222222222222222222222222"


def _pkg(name: str, rev: str, url: str = "https://example.invalid/pkg.git",
         pkg_type: str = "git") -> dict:
    return {
        "url": url,
        "type": pkg_type,
        "subDir": None,
        "scope": "",
        "rev": rev,
        "name": name,
        "manifestFile": "lake-manifest.json",
        "inputRev": rev,
        "inherited": False,
        "configFile": "lakefile.lean",
    }


def _make_project(root: Path, name: str, packages: list[dict],
                  *, with_checkout: bool = False,
                  toolchain: str = TOOLCHAIN) -> Path:
    proj = root / name
    proj.mkdir(parents=True, exist_ok=True)
    if with_checkout:
        ml = proj / ".lake" / "packages" / "mathlib"
        ml.mkdir(parents=True, exist_ok=True)
        (ml / "Mathlib.lean").write_text("-- fake mathlib\n", encoding="utf-8")
        (ml / f"marker-{name}.txt").write_text(name, encoding="utf-8")
    (proj / "lake-manifest.json").write_text(
        json.dumps({"version": "1.2.0", "packages": packages}), encoding="utf-8"
    )
    (proj / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
    return proj


def _git(cmd: list[str], cwd: Path) -> str:
    proc = subprocess.run(["git", *cmd], cwd=cwd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    assert proc.returncode == 0, f"git {cmd} failed:\n{proc.stdout}\n{proc.stderr}"
    return proc.stdout.strip()


def _expected_group_id(packages: list[dict], mathlib_rev: str,
                       toolchain: str = TOOLCHAIN) -> str:
    """Reconstruit le groupId attendu cote Python (spec pincee).

    Meme construction que Get-LeanProjects / Get-GroupId : paires
    ``name=rev`` triees par nom, jointes par ';' avec le toolchain en prefixe,
    suffixe = 8 premiers hex du SHA-256 de cette cle.
    """
    pairs = sorted(f"{p['name']}={p['rev']}" for p in packages)
    group_key = f"{toolchain}|{';'.join(pairs)}"
    suffix = hashlib.sha256(group_key.encode("utf-8")).hexdigest()[:8]
    return f"{toolchain}-{mathlib_rev[:8]}-{suffix}"


def _run_scan(root: Path) -> str:
    proc = subprocess.run(
        ["pwsh", "-NoProfile", "-NonInteractive", "-File", str(SCRIPT), "-Mode", "Scan"],
        cwd=root, capture_output=True, text=True, encoding="utf-8",
        errors="replace", timeout=300,
    )
    assert proc.returncode == 0, f"Scan en echec:\n{proc.stdout}\n{proc.stderr}"
    # Sortie COMBINEE : Write-Warning (stream 3) n'atterrit pas de facon stable
    # sur stdout sous pwsh -File -- les assertions sur les warnings se font sur
    # l'union, celles sur les en-tetes Write-Host y figurent aussi.
    return proc.stdout + "\n" + proc.stderr


def _run_apply(root: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["pwsh", "-NoProfile", "-NonInteractive", "-File", str(SCRIPT), "-Mode", "Apply"],
        cwd=root, capture_output=True, text=True, encoding="utf-8",
        errors="replace", timeout=300,
    )


G1_PACKAGES = [_pkg("mathlib", MATHLIB_REV,
                    "https://github.com/leanprover-community/mathlib4.git"),
               _pkg("batteries", BATTERIES_R1)]
G2_PACKAGES = [_pkg("mathlib", MATHLIB_REV,
                    "https://github.com/leanprover-community/mathlib4.git"),
               _pkg("batteries", BATTERIES_R2)]


def _colliding_repo(tmp_path: Path) -> Path:
    """Un bucket (toolchain, rev mathlib), DEUX groupes de manifests.

    projA/projB : batteries R1. projC/projD : batteries R2 (divergence reelle).
    """
    root = tmp_path / "repo"
    root.mkdir()
    _git(["init", "-q"], root)
    for name in ("projA", "projB"):
        _make_project(root, name, G1_PACKAGES)
    for name in ("projC", "projD"):
        _make_project(root, name, G2_PACKAGES)
    return root


@requires_pwsh
def test_colliding_groups_get_distinct_deterministic_ids(tmp_path: Path) -> None:
    """Deux groupes partagent le bucket : IDs distincts, suffixe = SHA-256 du
    GroupKey recalcule cote test (spec pincee), avertissement remplace."""
    out = _run_scan(_colliding_repo(tmp_path))

    id1 = _expected_group_id(G1_PACKAGES, MATHLIB_REV)
    id2 = _expected_group_id(G2_PACKAGES, MATHLIB_REV)
    assert id1 != id2, "les deux suffixes doivent differer (graphs distincts)"
    # Les deux en-tetes de groupe portent l'ID complet attendu.
    assert f"--- Groupe {id1} [MUTUALISABLE" in out
    assert f"--- Groupe {id2} [MUTUALISABLE" in out
    # Le rapport nomme les IDs desambiguises du bucket fragmente.
    assert "groupId desambiguises" in out
    assert id1 in out.rsplit("groupId desambiguises", 1)[-1]
    # L'avertissement historique (constat sans reparation) a disparu.
    assert "Collision de groupId" not in out


@requires_pwsh
def test_unique_bucket_keeps_legacy_group_id(tmp_path: Path) -> None:
    """Controle NEGATIF : sans collision, l'ID historique non suffixe est
    preserve -- les caches deja en place restent atteignables."""
    root = tmp_path / "repo"
    root.mkdir()
    _git(["init", "-q"], root)
    for name in ("projA", "projB", "projC"):
        _make_project(root, name, G1_PACKAGES)

    out = _run_scan(root)
    legacy = f"{TOOLCHAIN}-{MATHLIB_REV[:8]}"
    assert f"--- Groupe {legacy} [MUTUALISABLE" in out
    # Aucun suffixe hex ne doit apparaitre sur l'ID unique du bucket.
    assert f"{legacy}-" not in out


@requires_windows
def test_apply_does_not_merge_colliding_groups_into_one_cache(
    tmp_path: Path,
) -> None:
    """L'Apply ne jonctionne plus le second groupe dans le cache du premier.

    Fixture : groupe 1 = projA (donneur, vrai mini-depot git a HEAD = la rev du
    manifest) + projB (checkout physique) ; groupe 2 = projC/projD (memes
    toolchain et rev mathlib, batteries divergentes, AUCUN checkout). Avant
    correctif, le groupe 2 trouvait le cache du groupe 1 valide (Test-CacheValid
    ne compare que la revision mathlib) et y jonctionnait projC/projD ; les
    deux groupes fusionnaient dans un seul share-state.json. Apres correctif,
    le groupe 2 a son propre groupId suffixe, sans cache ni donneur : il est
    skip AVANT toute jonction.
    """
    root = _colliding_repo(tmp_path)
    # Le donneur porte un VRAI depot git dans son checkout mathlib : HEAD = la
    # rev du manifest des DEUX groupes (meme mathlib, c'est la collision).
    # On remplace les manifests par la HEAD reelle apres creation du depot.
    proj_a = root / "projA"
    _make_project(root, "projA", G1_PACKAGES, with_checkout=True)
    ml_a = proj_a / ".lake" / "packages" / "mathlib"
    _git(["init", "-q"], ml_a)
    _git(["add", "-A"], ml_a)
    _git(["-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "fake mathlib"], ml_a)
    head = _git(["rev-parse", "HEAD"], ml_a)
    _make_project(root, "projB", G1_PACKAGES, with_checkout=True)
    for name, pkgs in (("projA", G1_PACKAGES), ("projB", G1_PACKAGES),
                       ("projC", G2_PACKAGES), ("projD", G2_PACKAGES)):
        manifest = [dict(p, rev=head if p["name"] == "mathlib" else p["rev"])
                    for p in pkgs]
        (root / name / "lake-manifest.json").write_text(
            json.dumps({"version": "1.2.0", "packages": manifest}), encoding="utf-8"
        )
    # Poids .lake/build du donneur : candidat le plus gros, donneur deterministe.
    build_a = ml_a / ".lake" / "build"
    build_a.mkdir(parents=True, exist_ok=True)
    (build_a / "artifact.bin").write_bytes(b"x" * (4 * 1024 * 1024))

    proc = _run_apply(root)
    assert proc.returncode == 0, f"Apply stdout tail:\n{proc.stdout[-1500:]}"

    # Exactement UN cache sur disque : celui du groupe 1, sous son ID suffixe.
    cache_root = root / ".mathlib-cache"
    group_dirs = sorted(d.name for d in cache_root.iterdir() if d.is_dir())
    id1 = _expected_group_id(
        [dict(p, rev=head if p["name"] == "mathlib" else p["rev"]) for p in G1_PACKAGES], head)
    id2 = _expected_group_id(
        [dict(p, rev=head if p["name"] == "mathlib" else p["rev"]) for p in G2_PACKAGES], head)
    assert group_dirs == [id1], f"caches crees : {group_dirs} (attendu : seulement {id1})"

    # L'etat du groupe 1 ne declare QUE ses membres ; le groupe 2 a ete skip
    # AVANT toute jonction (warning nominatif sur son ID suffixe).
    state = json.loads((cache_root / id1 / "share-state.json").read_text(encoding="utf-8-sig"))
    assert sorted(m["relPath"] for m in state["members"]) == ["projA", "projB"]
    combined = proc.stdout + "\n" + proc.stderr
    assert id2 in combined, "le skip du groupe 2 doit nommer son groupId suffixe"
    assert "skip AVANT toute jonction" in combined

    # Verite disque : projC/projD ne portent NI jonction NI cache.
    for name in ("projC", "projD"):
        ml = root / name / ".lake" / "packages" / "mathlib"
        assert not ml.exists(), f"{name} ne doit rien porter (ni jonction ni cache)"
