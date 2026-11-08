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
    succes ;
  * sur un clone **shallow**, la mesure est `non_mesurable` pour les
    generateurs qui lisent l'historique -- et pour eux seuls (mesure du
    2026-11-05 : la page et sa verification partagent la troncature, donc le
    `--check` local s'auto-confirme pendant que la porte CI rougit).

Usage :
    python scripts/lean/tests/test_check_lean_derived_pages.py
    python -m pytest scripts/lean/tests/test_check_lean_derived_pages.py -q
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import subprocess
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


# --- le prealable d'historique : un clone shallow ne mesure rien -------------

IMMUNE = "scripts/lean/lean_theorem_duplicates.py"


def _git(cwd: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(cwd), *args], capture_output=True,
                   text=True, encoding="utf-8", errors="replace", check=True)


def _git_repo_with_history(tmp_path: Path, name: str = "origin") -> Path:
    """Un depot git a deux commits (donc clonable en profondeur 1)."""
    ident = ("-c", "user.email=test@example.invalid", "-c", "user.name=test")
    repo = tmp_path / name
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, *ident, "commit", "-q", "--allow-empty", "-m", "premier")
    (repo / "trace.txt").write_text("x\n", encoding="utf-8")
    _git(repo, "add", "trace.txt")
    _git(repo, *ident, "commit", "-q", "-m", "second")
    return repo


def _shallow_clone(origin: Path, dest: Path) -> Path:
    subprocess.run(["git", "clone", "--depth", "1", "-q",
                    origin.as_uri(), str(dest)],
                   capture_output=True, text=True, encoding="utf-8",
                   errors="replace", check=True)
    return dest


def _write_page_pair(root: Path, generator: str, rc: int = 0) -> None:
    gen = root / generator
    gen.parent.mkdir(parents=True, exist_ok=True)
    gen.write_text("import sys\nsys.exit(%d)\n" % rc, encoding="utf-8")
    page = root / dict(mod.PAGES)[generator]
    page.parent.mkdir(parents=True, exist_ok=True)
    page.write_text("page de test\n", encoding="utf-8")


def test_un_clone_shallow_rend_la_mesure_non_mesurable(tmp_path):
    """Mesure du 2026-11-05 : une page regeneree sur un clone shallow portait
    35 fois la date de frontiere a la place des vraies dates de naissance, et
    le `--check` local rendait CONFORME -- le generateur et la page partageaient
    la troncature. Le garde doit refuser de conclure, et nommer la reparation
    (reparer l'historique, pas regenerer la page)."""
    origin = _git_repo_with_history(tmp_path)
    assert mod.shallow_clone_detail(origin) is None, \
        "un historique complet ne doit pas etre declare tronque"
    shallow = _shallow_clone(origin, tmp_path / "shallow")
    assert mod.shallow_clone_detail(shallow) is not None

    by_gen = {r["generator"]: r for r in
              mod.check_all(timeout=30, repo_root=shallow)}
    assert mod.READS_HISTORY, "au moins un generateur lit l'historique"
    for generator in mod.READS_HISTORY:
        got = by_gen[generator]
        assert got["status"] == "non_mesurable"
        assert got["drifted"] is True, "« je n'ai pas pu mesurer » bloque"
        assert "unshallow" in got["detail"], \
            "le motif doit nommer la reparation"


def test_un_clone_shallow_ne_bloque_que_les_generateurs_qui_lisent_l_historique(
        tmp_path):
    """La troncature ne rend fausse que la lecture de `git log` : un generateur
    qui ne lit que `git ls-files` reste mesurable et ne doit pas etre bloque --
    le garde ne dit jamais plus fort que ce qu'il a mesure."""
    origin = _git_repo_with_history(tmp_path)
    shallow = _shallow_clone(origin, tmp_path / "shallow")
    _write_page_pair(shallow, IMMUNE, rc=0)
    _write_page_pair(shallow, "scripts/lean/lean_material_map.py", rc=0)

    by_gen = {r["generator"]: r for r in
              mod.check_all(timeout=30, repo_root=shallow)}
    assert by_gen[IMMUNE]["status"] == "conforme"
    assert by_gen[IMMUNE]["drifted"] is False
    assert by_gen["scripts/lean/lean_material_map.py"]["status"] == \
        "non_mesurable"


def test_un_depot_non_git_laisse_les_generateurs_conclure(tmp_path):
    """« je n'ai pas pu lire l'historique » n'est pas « l'historique est
    tronque » : hors depot git, la mesure revient aux generateurs."""
    repo = _fake_repo(tmp_path, rc=0)
    assert mod.shallow_clone_detail(repo) is None


def test_le_verdict_d_un_historique_tronque_n_accuse_pas_la_page():
    """Le verdict doit dire ce qui a ete mesure. « DIVERGENCE » accuserait la
    page d'un defaut dont la seule cause mesuree est la troncature -- et le
    geste `--write` enverrait la lane ecrire des dates fabriquees."""
    tronquee = [{"generator": "scripts/lean/lean_material_map.py",
                 "page": "docs/reference/lean-material-map.md",
                 "status": "non_mesurable", "drifted": True, "rc": None,
                 "duration_s": 0.0,
                 "detail": "historique TRONQUE : clone shallow -- `git fetch "
                           "--unshallow`, puis regenere la page."}]
    rc, out, err = _run_main([], tronquee)
    assert rc == 1
    assert "VERDICT: NON MESURABLE" in out
    assert "DIVERGENCE" not in out
    assert "--write" not in out, "ne jamais envoyer la lane regenerer ici"
    assert "unshallow" in out


def test_le_garde_couvre_les_pages_attendues():
    """Le garde doit couvrir les pages derivees de l'arbre Lean : une page
    ajoutee sans etre cablee ne serait jamais verifiee."""
    covered = {page for _, page in mod.PAGES}
    assert "docs/reference/lean-theorem-duplicates.md" in covered
    assert "docs/reference/lean-material-map.md" in covered
    for generator, page in mod.PAGES:
        assert generator.endswith(".py")
        assert page.startswith("docs/reference/")


# --- la sortie machine doit etre un FICHIER, pas un flux melange -----------

def _run_main(argv, monkeypatched_results):
    """Lance `main()` sur des resultats synthetiques.

    Les generateurs reels ne sont pas appeles : le test porte sur la FORME de
    la sortie, pas sur l'etat de l'arbre.
    """
    saved = mod.check_all
    mod.check_all = lambda timeout=900, repo_root=None: monkeypatched_results
    out, err = io.StringIO(), io.StringIO()
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = mod.main(list(argv))
    finally:
        mod.check_all = saved
    return rc, out.getvalue(), err.getvalue()


def _one_conforme():
    return [{"generator": GEN, "page": PAGE, "status": "conforme",
             "drifted": False, "rc": 0, "duration_s": 0.1,
             "detail": "A JOUR : 41 lacs"}]


def test_le_mode_json_ecrit_un_json_PARSABLE_sur_stdout():
    """Regression (mesure du 2026-11-03) : la porte CI a echoue sur un
    `json.load` alors que le verdict etait « CONFORME (2 pages) » -- la ligne
    de verdict sortait sur stdout, APRES le JSON. Le rapport ecrit sur disque
    etait donc un fichier casse : un garde vert, une porte rouge.

    stdout doit etre un JSON parsable, et rien d'autre."""
    rc, out, err = _run_main(["--json"], _one_conforme())
    assert rc == 0
    data = json.loads(out)  # leve si stdout est contamine
    assert data["n_pages"] == 1
    assert data["drifted"] is False
    assert "VERDICT" not in out
    assert "VERDICT" in err, "le verdict reste lisible (stderr)"


def test_le_verdict_dune_divergence_part_sur_stderr_en_mode_json():
    """Meme contrat pour le verdict bloquant : il ne doit jamais contaminer
    le rapport machine."""
    divergente = [{"generator": GEN, "page": PAGE, "status": "divergente",
                   "drifted": True, "rc": 1, "duration_s": 0.1,
                   "detail": "la page ne suit plus l'arbre"}]
    rc, out, err = _run_main(["--json"], divergente)
    assert rc == 1
    data = json.loads(out)
    assert data["drifted"] is True
    assert "DIVERGENCE" in err
    assert "DIVERGENCE" not in out


def test_le_mode_humain_ecrit_le_verdict_sur_stdout():
    """Hors mode `--json`, le verdict reste sur stdout : c'est la sortie
    lue par un humain."""
    rc, out, err = _run_main([], _one_conforme())
    assert rc == 0
    assert "VERDICT: CONFORME" in out
    assert err == ""


def test_un_generateur_qui_ne_pas_mesurer_est_classe_mesure_impossible(tmp_path):
    """rc=2 : le generateur a dit « je n'ai pas pu mesurer » (organe amont
    injoignable). Ce n'est PAS une divergence de l'arbre.

    Le geste propose compte autant que la classification : la page sur disque
    n'a pas ete modifiee, donc la regeneree y ecrirait une MESURE DEGRADEE
    (colonne de couverture a `hors matrice` pour tous les lacs). Nommer
    `--write` ici renverrait la lane droit dans le piege."""
    repo = _fake_repo(tmp_path, rc=2)
    got = mod._run_check(GEN, timeout=30, repo_root=repo)
    assert got["status"] == "mesure_impossible"
    assert got["drifted"] is True
    assert got["rc"] == 2


def test_le_verdict_n_accuse_pas_l_arbre_quand_la_mesure_est_impossible():
    """Une mesure impossible ne se lit pas comme une divergence : le verdict
    doit nommer la machine, pas la page."""
    impossible = [{"generator": GEN, "page": PAGE,
                   "status": "mesure_impossible", "drifted": True, "rc": 2,
                   "duration_s": 0.1,
                   "detail": "Cause : timeout de 1800 s"}]
    rc, out, err = _run_main(["--json"], impossible)
    assert rc == 1
    data = json.loads(out)
    assert data["mesure_impossible"] is True
    assert "MESURE IMPOSSIBLE" in err
    assert "DIVERGENCE" not in err
    assert "NON MESURABLE" not in err, "le clone shallow n'est pas la cause"


def test_le_mode_humain_propose_le_bon_geste_quand_la_mesure_est_impossible():
    """Le geste doit etre « ne pas regenerer ici », jamais `--write`."""
    impossible = [{"generator": GEN, "page": PAGE,
                   "status": "mesure_impossible", "drifted": True, "rc": 2,
                   "duration_s": 0.1,
                   "detail": "Cause : timeout de 1800 s"}]
    rc, out, err = _run_main([], impossible)
    assert rc == 1
    assert "MESURE IMPOSSIBLE" in out
    assert err == "", "en mode humain, le verdict reste sur stdout"
    assert "--write" not in out, "ne jamais envoyer la lane regenerer ici"
    assert "NE PAS regenerer" in out


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
