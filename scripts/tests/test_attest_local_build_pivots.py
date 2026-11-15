"""Temoins du correctif #26630 -- le cache chaud se RESOUT par toolchain.

Le defaut : `attest_local_build.py` connaissait UN SEUL pivot de cache chaud,
`JeuDeLaVie/conway_lean` (toolchain `v4.33.0`). Tout lake dont la toolchain differe
etait donc refuse AVANT tout build -- `lean-toolchain different du cache --
cache chaud non applicable` -- et les PRs qui touchaient ces lakes etaient
inmergeables par construction. Mesure sur `origin/main` le 14/11 : sur les 36
lakes du manifeste, 33 en `v4.33.0`, mais `formal_logic` en `v4.33.1`,
`socialchoicepeters` en `v4.32.1` et `conwaycgt` en `v4.33.0-rc1`. Instance :
#25236, dont `formal_logic` etait refuse avant tout build alors que les trois
autres lakes de la meme PR etaient verts en local.

Le correctif :

1. le pivot n'est plus un chemin fige mais un lake du clone courant dont la
   toolchain est la MEME et dont le `.lake/packages` est chaud -- la table se
   resout a l'execution ;
2. une toolchain sans cache chaud rend le motif DISTINCT
   `no-warm-cache-for-toolchain`, avec la commande de prechauffage ;
3. le manifeste lu est celui de la TETE de la PR, et la selection porte sur
   les lakes touches + les lakes ajoutes -- pas sur les 36 lakes du
   manifeste.

Ces tests sont les temoins : ils rougissent sur le code casse (pivot fige,
motif indistinct, manifeste de `main`) et restent verts sur le code corrige.
"""

from __future__ import annotations

import base64
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import attest_local_build as alb  # noqa: E402

V4330 = "leanprover/lean4:v4.33.0\n"
V4331 = "leanprover/lean4:v4.33.1\n"
V4321 = "leanprover/lean4:v4.32.1\n"


def _lake(root: Path, name: str, toolchain: str, *, warm: bool = False,
          packages: list[str] | None = None) -> Path:
    """Repertoire de lake minimal : `lean-toolchain` (+ `.lake/packages`).

    `warm=True` materialise un paquet **resolu** (son `.git` present) :
    depuis #26639, un `.lake/packages` VIDE ne vaut plus un cache chaud --
    lake y re-resoudrait les dependances, donc lancerait git dans le depot
    englobant (incident mesure le 14/11 sur ai-01).
    """
    lake = root / name
    lake.mkdir(parents=True, exist_ok=True)
    (lake / "lean-toolchain").write_text(toolchain, encoding="utf-8")
    if warm:
        packages_dir = lake / ".lake" / "packages"
        packages_dir.mkdir(parents=True, exist_ok=True)
        for pkg in (packages if packages is not None else ["batteries"]):
            materialized = packages_dir / pkg
            materialized.mkdir(parents=True, exist_ok=True)
            (materialized / ".git").mkdir(exist_ok=True)
    return lake


def _manifest_de_paquets(lake: Path, packages: list[str]) -> Path:
    """Ecrit le `lake-manifest.json` qui declare les paquets du lake."""
    payload = {
        "version": "1.1.0",
        "packagesDir": ".lake/packages",
        "packages": [
            {
                "name": name,
                "type": "git",
                "url": "https://example.invalid/{}".format(name),
                "rev": "0" * 40,
                "scope": "",
            }
            for name in packages
        ],
    }
    manifest = lake / "lake-manifest.json"
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    return manifest


# --- 1. la resolution du pivot ---------------------------------------------


def test_pivot_de_meme_toolchain_est_resolu(tmp_path):
    """POSITIF : un lake dont la toolchain a un cache chaud trouve son pivot."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    pivot = _lake(tmp_path / "pivots", "warm", V4331, warm=True)

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is True
    assert Path(verdict["pivot"]) == pivot
    assert verdict["toolchain"] == V4331.strip()


def test_toolchain_sans_cache_chaud_rend_le_motif_distinct(tmp_path):
    """NEGATIF : une toolchain sans cache chaud n'est pas un echec de build.
    Le motif est DISTINCT et nomme la toolchain qui manque."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    autre = _lake(tmp_path / "pivots", "chaud_v4330", V4330, warm=True)

    verdict = alb.resolve_cache_pivot(lake, [autre])

    assert verdict["ok"] is False
    assert verdict["reason"] == alb.NO_WARM_CACHE
    assert verdict["toolchain"] == V4331.strip()


def test_un_cache_d_une_autre_toolchain_n_est_pas_un_pivot(tmp_path):
    """NEGATIF : le cache d'une autre toolchain ne s'emprunte pas -- le build
    est produit par la toolchain du lake."""
    lake = _lake(tmp_path / "lakes", "socialchoice", V4321)
    pivot = _lake(tmp_path / "pivots", "chaud_v4330", V4330, warm=True)

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is False
    assert verdict["reason"] == alb.NO_WARM_CACHE


def test_un_cache_froid_n_est_pas_un_pivot(tmp_path):
    """NEGATIF : meme toolchain, mais `.lake/packages` absent -- le cache
    n'est pas chaud, il n'est pas un pivot."""
    lake = _lake(tmp_path / "lakes", "conwaycgt", V4330)
    froid = _lake(tmp_path / "pivots", "froid", V4330, warm=False)

    verdict = alb.resolve_cache_pivot(lake, [froid])

    assert verdict["ok"] is False
    assert verdict["reason"] == alb.NO_WARM_CACHE


def test_le_lake_ne_sert_pas_de_pivot_a_lui_meme(tmp_path):
    """NEGATIF : un lake chaud ne peut pas etre son propre pivot -- la
    junction se poserait sur elle-meme."""
    lake = _lake(tmp_path / "lakes", "conway", V4330, warm=True)

    verdict = alb.resolve_cache_pivot(lake, [lake])

    assert verdict["ok"] is False
    assert verdict["reason"] == alb.NO_WARM_CACHE


def test_cas_v4330_inchange(tmp_path):
    """Le cas historique reste couvert : la toolchain `v4.33.0` trouve son
    pivot comme avant (#25370 : le cache chaud s'applique)."""
    lake = _lake(tmp_path / "lakes", "conway", V4330)
    pivot = _lake(tmp_path / "pivots", "conway_lean", V4330, warm=True)

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is True
    assert Path(verdict["pivot"]) == pivot


def test_lake_sans_toolchain_rend_un_refus_nomme(tmp_path):
    """NEGATIF : un lake sans `lean-toolchain` est refuse par un motif qui
    le nomme (fail-closed)."""
    lake = tmp_path / "lakes" / "vide"
    lake.mkdir(parents=True)

    verdict = alb.resolve_cache_pivot(lake, [])

    assert verdict["ok"] is False
    assert "lean-toolchain" in verdict["reason"]


# --- 1 bis. « chaud » se MESURE : le cache doit etre COMPLET -----------------
#
# Un `.lake/packages` vide ou partiel passe pour un cache chaud, et lake va
# alors re-resoudre les dependances manquantes : il lance git DANS le depot
# englobant et ecrit, a travers la junction, dans le clone principal
# (incident mesure le 14/11 sur ai-01 : fetch et checkout tentes dans
# `D:/CoursIA`). Un candidat incomplet est donc ecarte, AVEC son motif.


def test_un_cache_a_packages_vides_est_refuse(tmp_path):
    """NEGATIF : `.lake/packages` existe mais est vide -- ce n'est pas un
    cache chaud. Avant le correctif, ce dossier passait pour chaud."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    pivot = _lake(tmp_path / "pivots", "vide", V4331)
    (pivot / ".lake" / "packages").mkdir(parents=True, exist_ok=True)

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is False
    assert verdict["reason"] == alb.NO_WARM_CACHE
    assert any("packages vides" in r for r in verdict["rejects"])


def test_un_cache_qui_omet_un_paquet_declare_est_refuse(tmp_path):
    """NEGATIF : le pivot declare `mathlib` et `batteries`, mais seul
    `batteries` est materialise : le pivot est ecarte et le motif NOMME le
    paquet manquant."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    pivot = _lake(tmp_path / "pivots", "partiel", V4331, warm=True,
                  packages=["batteries"])
    _manifest_de_paquets(pivot, ["batteries", "mathlib"])

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is False
    assert verdict["reason"] == alb.NO_WARM_CACHE
    assert any("mathlib absent" in r for r in verdict["rejects"])
    assert "mathlib absent" in verdict["detail"]


def test_mathlib_sans_build_est_refuse(tmp_path):
    """NEGATIF : Mathlib est present (checkout fait) mais pas COMPILE. Sans
    `.lake/packages/mathlib/.lake/build`, le cache ne vaut rien : lake
    recompile, donc re-resout, donc va chercher."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    pivot = _lake(tmp_path / "pivots", "mathlib_sans_build", V4331, warm=True,
                  packages=["batteries", "mathlib"])
    _manifest_de_paquets(pivot, ["batteries", "mathlib"])

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is False
    assert any("mathlib incomplet" in r for r in verdict["rejects"])


def test_le_pivot_complet_et_resolu_est_retenu(tmp_path):
    """POSITIF : le pivot declare `mathlib` et `batteries`, les deux sont
    materialises, Mathlib est compile -> le pivot est retenu."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    pivot = _lake(tmp_path / "pivots", "complet", V4331, warm=True,
                  packages=["batteries", "mathlib"])
    _manifest_de_paquets(pivot, ["batteries", "mathlib"])
    build = pivot / ".lake" / "packages" / "mathlib" / ".lake" / "build"
    build.mkdir(parents=True)

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is True
    assert Path(verdict["pivot"]) == pivot
    assert verdict["rejects"] == []


def test_un_paquet_demande_par_le_lake_et_non_servi_ecarte_le_pivot(tmp_path):
    """NEGATIF : le pivot est complet POUR LUI-MEME, mais il ne sert pas le
    paquet que le LAKE demande (`mathlib`). C'est le chemin de l'incident
    du 14/11 : lake chercherait le paquet manquant et l'ecrirait dans le
    repertoire vise par la junction -- c'est-a-dire dans le clone
    principal."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    _manifest_de_paquets(lake, ["batteries", "mathlib"])
    pivot = _lake(tmp_path / "pivots", "sans_mathlib", V4331, warm=True,
                  packages=["batteries"])
    _manifest_de_paquets(pivot, ["batteries"])

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["ok"] is False
    assert any("mathlib absent" in r for r in verdict["rejects"])


def test_le_verdict_dit_pourquoi_aucun_pivot_n_a_ete_retenu(tmp_path):
    """Le verdict nomme le motif de l'ecart : sans lui, « aucun cache chaud »
    ne dit pas pourquoi aucun pivot n'a ete retenu."""
    lake = _lake(tmp_path / "lakes", "formal_logic", V4331)
    pivot = _lake(tmp_path / "pivots", "partiel", V4331, warm=True,
                  packages=["batteries"])
    _manifest_de_paquets(pivot, ["batteries", "mathlib"])

    verdict = alb.resolve_cache_pivot(lake, [pivot])

    assert verdict["reason"] == alb.NO_WARM_CACHE
    assert verdict["rejects"]
    assert "partiel" in verdict["detail"]


# --- 2. le plan de prechauffage --------------------------------------------


def test_le_plan_de_prechauffage_passe_par_lean_exec(tmp_path):
    """Le prechauffage passe par l'organe canonique (`lean_exec.py`), dans un
    worktree DETACHE : sur un lac au paquet vide, `lake` re-resout et lance
    git dans le depot englobant."""
    lake = {"lake": "formal_logic", "project-path": "MyIA.AI.Notebooks/Lean/formal_logic_lean"}

    plan = alb.prewarm_plan(lake, head="a" * 40, timeout=900.0)

    assert plan["cache_get"][-4:] == ["lake", "exe", "cache", "get"]
    assert plan["build"][-2:] == ["lake", "build"]
    assert any("lean_exec.py" in str(part) for part in plan["cache_get"])
    assert "--detach" in plan["worktree"]
    assert "a" * 40 in plan["worktree"]


# --- 3. le manifeste de la tete et la selection des lakes -------------------


def _manifest(lakes: list[dict]) -> dict:
    return {"lakes": lakes}


def _entry(name: str, project_path: str, patterns: list[str]) -> dict:
    return {
        "lake": name,
        "project-path": project_path,
        "paths": patterns,
    }


def test_select_lakes_ne_developpe_pas_le_gate():
    """Le dispatcher CI developpe « un fichier du gate -> TOUS les lakes » ;
    l'attestation, non : elle atteste les lakes TOUCHES. Mesure : le
    dry-run de #26399 echouait sur onze lakes que la PR ne touche pas."""
    head = _manifest([
        _entry("a", "lakes/a", ["lakes/a/**.lean"]),
        _entry("b", "lakes/b", ["lakes/b/**.lean"]),
        _entry("c", "lakes/c", ["lakes/c/**.lean"]),
    ])

    selected = alb.select_lakes(
        ["scripts/lean/ci_lakes.json", "lakes/a/A.lean"], head, head
    )

    assert [e["lake"] for e in selected] == ["a"]


def test_select_lakes_inclut_les_lakes_ajoutes_par_la_pr():
    """Un lake declare par la PR et absent de `main` est atteste, meme
    sans fichier touche : c'est precisement le lake que la PR construit
    (#26399)."""
    head = _manifest([
        _entry("a", "lakes/a", ["lakes/a/**.lean"]),
        _entry("combinators", "lakes/combinators", ["lakes/combinators/**.lean"]),
    ])
    base = _manifest([_entry("a", "lakes/a", ["lakes/a/**.lean"])])

    selected = alb.select_lakes(["scripts/lean/ci_lakes.json"], head, base)

    assert [e["lake"] for e in selected] == ["combinators"]


def test_select_lakes_touche_les_lakes_du_diff():
    """Les lakes dont un fichier change sont la selection de base."""
    head = _manifest([
        _entry("a", "lakes/a", ["lakes/a/**.lean"]),
        _entry("b", "lakes/b", ["lakes/b/**.lean"]),
    ])

    selected = alb.select_lakes(["lakes/b/B.lean"], head, head)

    assert [e["lake"] for e in selected] == ["b"]


def test_manifest_at_head_eleve_le_manifeste_de_la_tete(monkeypatch):
    """Le manifeste lu est celui de la TETE : une PR qui ajoute un lake
    n'est plus invisible a l'organe."""
    payload = {"lakes": [_entry("combinators", "lakes/combinators", [])]}
    encode = base64.b64encode(json.dumps(payload).encode("utf-8")).decode("ascii")
    vu = {}

    def fake_gh_json(repo, path):
        vu["path"] = path
        return {"content": encode, "encoding": "base64"}

    monkeypatch.setattr(alb, "gh_json", fake_gh_json)

    manifest = alb.manifest_at_head("jsboige/CoursIA", "b" * 40)

    assert manifest is not None
    assert manifest["lakes"][0]["lake"] == "combinators"
    assert "ref=" in vu["path"]
    assert "b" * 40 in vu["path"]


def test_manifest_at_head_rend_none_sur_un_contenu_illisible(monkeypatch):
    """NEGATIF : un manifeste illisible a la tete rend `None` -- l'appelant
    refute, il n'invente pas de manifeste."""
    monkeypatch.setattr(alb, "gh_json", lambda repo, path: {"content": "pas-du-base64"})

    assert alb.manifest_at_head("jsboige/CoursIA", "c" * 40) is None


# --- 4. le lake AJOUTE par la PR -------------------------------------------


def test_toolchain_at_head_eleve_le_contenu(monkeypatch):
    """La toolchain d'un lake ajoute par la PR se lit sur le CONTENU de la
    tete : le lake n'existe pas dans le clone courant."""
    encode = base64.b64encode(b"leanprover/lean4:v4.33.0\n").decode("ascii")
    monkeypatch.setattr(alb, "gh_json", lambda repo, path: {"content": encode})

    toolchain = alb._toolchain_at_head("jsboige/CoursIA", "d" * 40, "lakes/neuf")

    assert toolchain == "leanprover/lean4:v4.33.0"


def test_le_lake_ajoute_rend_le_motif_dedie_au_dry_run(monkeypatch):
    """Un lake declare par la PR et absent du clone n'est PAS un echec de
    build : le motif est dedie, la toolchain est nommee, et la commande de
    prechauffage est fournie."""
    lake = {"lake": "combinators", "project-path": "lakes/ajoute_par_la_pr"}
    head_manifest = {"lakes": [dict(lake, paths=["lakes/ajoute_par_la_pr/**.lean"])]}

    def fake_gh_json(repo, path):
        if path.endswith("ci_lakes.json?ref=" + "e" * 40):
            encode = base64.b64encode(
                json.dumps(head_manifest).encode("utf-8")
            ).decode("ascii")
            return {"content": encode}
        if path.endswith("lean-toolchain?ref=" + "e" * 40):
            return {
                "content": base64.b64encode(b"leanprover/lean4:v4.33.0\n").decode("ascii")
            }
        return {}

    monkeypatch.setattr(alb, "gh_json", fake_gh_json)
    monkeypatch.setattr(alb, "current_login", lambda: "myia-ai-01")
    monkeypatch.setattr(alb, "pr_head", lambda repo, pr: "e" * 40)
    monkeypatch.setattr(alb, "pr_files", lambda repo, pr: ["lakes/ajoute_par_la_pr/A.lean"])
    monkeypatch.setattr(alb, "select_lakes", lambda files, head, base: [lake])

    result = alb.attest(26399, "jsboige/CoursIA", 30.0, dry_run=True)

    entree = result["cache_check"][0]
    assert entree["reason"] == alb.LAKE_NOT_IN_CLONE
    assert entree["toolchain"] == "leanprover/lean4:v4.33.0"
    assert entree["prewarm"]["cache_get"][-4:] == ["lake", "exe", "cache", "get"]
    assert result["ok"] is False
    assert "combinators" in result["reason"]
    assert "echec de build" not in result["reason"]
