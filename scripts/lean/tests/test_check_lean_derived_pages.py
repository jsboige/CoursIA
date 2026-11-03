#!/usr/bin/env python3
"""Tests du garde des pages derivees de l'arbre Lean (#24183, #23097).

Le garde est **lui-meme** un predicat de derive : il doit donc etre teste sur
des **jeux synthetiques** (un faux generateur dans un depot temporaire), et
non sur l'etat live du depot. Un test qui verifie l'etat live n'a pas de
valeur : il reproduirait exactement le defaut qu'on veut supprimer (un test
global qui rougit selon l'etat de `main`).

Les cas couverts :
  * une page conforme ne derive pas ;
  * une page divergente derive, et le motif est nomme ;
  * un generateur absent, une page absente : « je n'ai pas pu lire » n'est pas
    « c'est conforme » ;
  * un generateur qui expire est traite comme une divergence, pas comme un
    succes.

Usage :
    python scripts/lean/tests/test_check_lean_derived_pages.py
    python -m pytest scripts/lean/tests/test_check_lean_derived_pages.py -q
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]


def _load_module():
    """Charge le garde par son chemin (le script vit hors du paquet)."""
    path = REPO_ROOT / "scripts" / "lean" / "check_lean_derived_pages.py"
    spec = importlib.util.spec_from_file_location("check_lean_derived_pages", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_lean_derived_pages"] = module
    spec.loader.exec_module(module)
    return module


mod = _load_module()

GEN = "scripts/lean/lean_theorem_duplicates.py"
PAGE = "docs/reference/lean-theorem-duplicates.md"


def _fake_repo(tmp_path: Path, *, rc: int, with_page: bool = True,
               with_generator: bool = True) -> Path:
    """Depot temporaire avec un faux generateur et (ou non) sa page."""
    repo = tmp_path / "repo"
    repo.mkdir()
    if with_generator:
        gen = repo / GEN
        gen.parent.mkdir(parents=True, exist_ok=True)
        gen.write_text(
            "import sys\n"
            "sys.exit(%d)\n" % rc,
            encoding="utf-8")
    if with_page:
        page = repo / PAGE
        page.parent.mkdir(parents=True, exist_ok=True)
        page.write_text("page de test\n", encoding="utf-8")
    return repo


def test_une_page_conforme_ne_derive_pas(tmp_path):
    repo = _fake_repo(tmp_path, rc=0)
    got = mod._run_check(GEN, timeout=30, repo_root=repo)
    assert got["drifted"] is False
    assert got["rc"] == 0
    assert got["page"].endswith("lean-theorem-duplicates.md")


def test_une_page_divergente_derive_et_le_motif_est_nomme(tmp_path):
    repo = _fake_repo(tmp_path, rc=1)
    got = mod._run_check(GEN, timeout=30, repo_root=repo)
    assert got["drifted"] is True
    assert got["rc"] == 1
    assert got["detail"], "le motif de la divergence doit etre nomme"


def test_un_generateur_absent_n_est_pas_conforme(tmp_path):
    """« je n'ai pas pu lire » n'est pas « c'est conforme » : un generateur
    absent ne rend pas la page conforme."""
    repo = _fake_repo(tmp_path, rc=0, with_generator=False)
    got = mod._run_check(GEN, timeout=30, repo_root=repo)
    assert got["drifted"] is True
    assert "absent" in got["detail"]


def test_une_page_absente_derive(tmp_path):
    repo = _fake_repo(tmp_path, rc=0, with_page=False)
    got = mod._run_check(GEN, timeout=30, repo_root=repo)
    assert got["drifted"] is True
    assert "absente" in got["detail"]


def test_un_generateur_qui_expire_est_signale_sans_bloquer(tmp_path):
    """Un generateur qui depasse le delai n'est PAS un defaut de la page : le
    verdict doit dire qu'il n'a pas pu verifier, sans condamner la PR. C'est
    la distinction entre « la page diverge » et « la machine n'a pas eu le
    temps » -- sans elle, une page lente bloquerait les PRs Lean sans dire
    pourquoi."""
    repo = _fake_repo(tmp_path, rc=0)
    # Un generateur qui dort plus longtemps que le delai accorde.
    gen = repo / GEN
    gen.write_text("import time\ntime.sleep(30)\n", encoding="utf-8")
    got = mod._run_check(GEN, timeout=1, repo_root=repo)
    assert got["status"] == "expiree"
    assert got["drifted"] is False
    assert "expiree" in got["detail"]


def test_le_garde_couvre_les_pages_attendues():
    """Le garde doit couvrir les pages derivees de l'arbre Lean : une page
    ajoutee sans etre cablee ne serait jamais verifiee."""
    covered = {page for _, page in mod.PAGES}
    assert "docs/reference/lean-theorem-duplicates.md" in covered
    assert "docs/reference/lean-material-map.md" in covered
    for generator, page in mod.PAGES:
        assert generator.endswith(".py")
        assert page.startswith("docs/reference/")


def main() -> int:
    import inspect
    import tempfile

    failures = []
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for test in tests:
        # Les tests qui demandent un `tmp_path` (fixture pytest) en recoivent un
        # equivalent dans le runner direct ; ceux qui n'en veulent pas sont
        # appeles tels quels.
        kwargs = {}
        if "tmp_path" in inspect.signature(test).parameters:
            kwargs["tmp_path"] = Path(tempfile.mkdtemp())
        try:
            test(**kwargs)
        except AssertionError as exc:
            failures.append((test.__name__, str(exc)))
            print("ECHEC %s : %s" % (test.__name__, exc))
        else:
            print("OK    %s" % test.__name__)
    print("")
    print("%d/%d tests passent." % (len(tests) - len(failures), len(tests)))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
