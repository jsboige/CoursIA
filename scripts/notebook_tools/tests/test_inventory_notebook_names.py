#!/usr/bin/env python3
"""Tests pour inventory_notebook_names.py (W0 #15488).

Couvre les 7 cas demandés par le body #15488 :
  00, base implicite `a`, `b/c`, sous-série, variants multi-kernel,
  exception plateforme, suffix ambigu.

Plus : tests de cohérence de dénombrement et de partage de grammaire.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

REPO_ROOT = subprocess.check_output(
    ["git", "rev-parse", "--show-toplevel"],
    cwd=os.path.dirname(os.path.abspath(__file__)) + "/../..",
    text=True,
    encoding="utf-8",
).strip()


def run(cmd, **kw):
    """Lance un sous-process avec cwd=repo root."""
    return subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True,
                         encoding="utf-8", errors="replace", **kw)


def test_self_test_returns_zero():
    """Le --self-test interne rend 0 + tous les cas OK."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--self-test"])
    assert r.returncode == 0, "self-test failed: %s" % r.stdout
    assert "SUCCES" in r.stdout, "expected SUCCES, got: %s" % r.stdout
    assert "ECHEC" not in r.stdout, "unexpected ECHEC: %s" % r.stdout


def test_self_test_covers_7_required_cases():
    """Le self-test couvre les 7 cas exigés par le body #15488."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--self-test"])
    required = [
        "00_Introduction",            # 00
        "Foo.ipynb",                  # base implicite `a` (pas d'index)
        "2.3b-Naive-Bayes",           # b/c (accretion lettre)
        "03_Structured_Outputs",      # sous-série (idx=3)
        "-Csharp",                    # variant multi-kernel
        "QuantConnect/projects",      # exception plateforme
        "-Rust",                      # suffix ambigu
    ]
    for needle in required:
        assert needle in r.stdout, "missing required case '%s' in self-test output" % needle


def test_inventory_human_output_origin_main():
    """L'inventaire sur origin/main imprime dénombrement réel + comptages."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--base", "origin/main"])
    assert r.returncode == 0
    assert "denominator=" in r.stdout, "missing denominator line: %s" % r.stdout[:500]
    assert "baseline=" in r.stdout
    assert "conforme" in r.stdout
    assert "rename_proposed" in r.stdout
    assert "exception" in r.stdout
    assert "ambigu" in r.stdout


def test_inventory_json_origin_main():
    """Sortie JSON parseable avec les 4 clés top-level attendues."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--base", "origin/main", "--json"])
    assert r.returncode == 0
    inv = json.loads(r.stdout)
    for key in ("ref", "denominator", "baseline", "by_classification", "entries"):
        assert key in inv, "missing key '%s' in inventory" % key
    assert isinstance(inv["entries"], list)
    assert inv["denominator"] == inv["baseline"], (
        "denominator %d != baseline %d (delta=%+d) — documenter l'écart"
        % (inv["denominator"], inv["baseline"],
           inv["denominator"] - inv["baseline"])
    )


def test_inventory_excludes_output_artifacts():
    """Les artefacts `_output/` sont exclus (jamais source canonique)."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--base", "origin/main", "--json"])
    inv = json.loads(r.stdout)
    for e in inv["entries"]:
        assert "/_output/" not in e["path"], \
            "_output artifact should be excluded: %s" % e["path"]


def test_inventory_no_silent_absorption():
    """Vérifie qu'aucune entrée n'est classée comme « non conforme » silencieux."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--base", "origin/main", "--json"])
    inv = json.loads(r.stdout)
    classes = {e["classification"] for e in inv["entries"]}
    # Les 4 classes canoniques doivent exister (au moins potentiellement).
    # Si une est vide sur origin/main, c'est un signal à documenter mais
    # pas un KO automatique — d'où le ≥0 ci-dessous.
    for cls in ("conforme", "rename_proposed", "exception", "ambigu"):
        assert cls in inv["by_classification"], "missing class '%s' in counts" % cls
    # Aucune absorption silencieuse : la somme des 4 classes == dénombrement.
    assert sum(inv["by_classification"].values()) == inv["denominator"], (
        "by_classification sum %d != denominator %d — silent absorption?"
        % (sum(inv["by_classification"].values()), inv["denominator"])
    )


def test_inventory_classifies_qc_platform_as_exception():
    """Un notebook sous QuantConnect/projects/ est classifié `exception`."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--base", "origin/main", "--json"])
    inv = json.loads(r.stdout)
    qc_entries = [e for e in inv["entries"]
                  if e["path"].startswith("MyIA.AI.Notebooks/QuantConnect/projects/")]
    if not qc_entries:
        return  # Si origin/main n'a plus de QC projects, on skip.
    for e in qc_entries[:3]:  # spot-check 3
        assert e["classification"] == "exception", \
            "QC platform notebook should be 'exception', got %s for %s" \
            % (e["classification"], e["path"])


def test_inventory_classifies_vendored_as_exception():
    """Les chemins vendored (foundry-lib / _peters / Z3.Linq) sont `exception`."""
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--base", "origin/main", "--json"])
    inv = json.loads(r.stdout)
    vendored = [e for e in inv["entries"]
                if any(h in e["path"] for h in ("foundry-lib", "_peters", "Z3.Linq"))]
    if not vendored:
        return
    for e in vendored[:3]:
        assert e["classification"] == "exception", \
            "vendored should be 'exception', got %s for %s" \
            % (e["classification"], e["path"])


def test_grammar_shared_with_check_duplicate():
    """L'inventaire partage sa grammaire avec check_duplicate_notebook_index.

    Vérifie que `_INDEX_RE` et `index_key` sont importés, pas dupliqués —
    c'est l'exigence explicite du body #15488.
    """
    inv_src = open(os.path.join(REPO_ROOT,
                                "scripts/notebook_tools/inventory_notebook_names.py"),
                   encoding="utf-8").read()
    # L'import doit provenir du voisin, pas redéclaré.
    assert "from scripts.notebook_tools.check_duplicate_notebook_index import" in inv_src, \
        "inventory_notebook_names.py must import grammar from check_duplicate_notebook_index"
    # Aucune redéclaration de _INDEX_RE ou LANG_SUFFIXES.
    assert "_INDEX_RE = re.compile" not in inv_src, \
        "_INDEX_RE must be imported, not redefined"
    assert "LANG_SUFFIXES = " not in inv_src, \
        "LANG_SUFFIXES must be imported, not redefined"


def test_kernelspec_distinct_from_lang_suffix():
    """`kernel inconnu` est distinct de `suffixe absent` — exigence #15488."""
    # Le cas `MGS-26-Equilibrium.ipynb` = nom non parsé (idx=None),
    # kernelspec python3 (connu). Il doit être `ambigu` pour cause d'index,
    # pas pour cause de kernel/suffixe.
    r = run([sys.executable,
             "scripts/notebook_tools/inventory_notebook_names.py",
             "--self-test"])
    # Le self-test doit explicitement montrer ce cas.
    assert "MGS-26-Equilibrium" in r.stdout, \
        "self-test missing MGS-26-Equilibrium case"


def _git(repo, *args):
    """git dans un depot temporaire (cwd=repo)."""
    return subprocess.run(["git"] + list(args), cwd=repo, capture_output=True,
                          text=True, encoding="utf-8", errors="replace")


def _notebook_json(kernelspec="python3"):
    """Carnet minimal : le kernelspec est ce que l'inventaire mesure."""
    return json.dumps({
        "cells": [],
        "metadata": {"kernelspec": {"name": kernelspec,
                                    "display_name": "Python 3",
                                    "language": "python"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }, ensure_ascii=False, indent=1)


def _inventory_at(repo, ref):
    """Lance l'instrument sur `ref`, dans le depot `repo` (cwd=repo)."""
    r = subprocess.run(
        [sys.executable,
         os.path.join(REPO_ROOT, "scripts/notebook_tools/inventory_notebook_names.py"),
         "--base", ref, "--json"],
        cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace")
    assert r.returncode == 0, "inventory failed on %s: %s%s" % (ref, r.stdout, r.stderr)
    return json.loads(r.stdout)


def _repo_two_revisions_with_a_renamed_notebook():
    """Depot jetable : rev1 = carnet `MGS-26-Equilibrium`, rev2 = renomme.

    Le nom est choisi sans index parsable (`MGS-26-...` -> idx=None, cf la
    nomenclature du depot) : c'est le cas ou un kernelspec NON LU fait basculer
    l'entree de `conforme` a `ambigu` (naming : base implicite non verifie).
    """
    repo = tempfile.mkdtemp(prefix="inv-revision-")
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    d = os.path.join(repo, "MyIA.AI.Notebooks", "GenAI", "Texte")
    os.makedirs(d)
    p1 = os.path.join(d, "MGS-26-Equilibrium.ipynb")
    with open(p1, "w", encoding="utf-8") as f:
        f.write(_notebook_json())
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "rev1")
    rev1 = _git(repo, "rev-parse", "HEAD").stdout.strip()
    # rev2 : le carnet est renome -> son chemin disparait de l'ARBRE LOCAL.
    os.replace(p1, os.path.join(d, "MGS-27-Equilibrium.ipynb"))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "rev2")
    rev2 = _git(repo, "rev-parse", "HEAD").stdout.strip()
    return repo, rev1, rev2


def test_inventory_reads_content_in_the_named_revision():
    """#23623 — la mesure est une fonction de la revision seule.

    Un carnet renomme entre deux revisions : l'inventaire de rev1 doit lire
    le kernelspec DANS rev1. Avant le correctif, le contenu etait lu dans
    l'arbre local -> le chemin de rev1 est absent du checkout -> kernel non
    lu -> l'entree tombait en `ambigu` au lieu de `conforme`.
    """
    repo, rev1, _rev2 = _repo_two_revisions_with_a_renamed_notebook()
    try:
        inv = _inventory_at(repo, rev1)
        rel = "MyIA.AI.Notebooks/GenAI/Texte/MGS-26-Equilibrium.ipynb"
        entries = {e["path"]: e for e in inv["entries"]}
        assert rel in entries, \
            "le carnet de rev1 doit figurer dans l'inventaire de rev1 : %s" % sorted(entries)
        e = entries[rel]
        assert e["kernelspec"] == "python3", \
            "kernelspec non lu dans la revision mesuree (lu : %r) — " \
            "le contenu est lu dans l'arbre local, pas dans la revision" % (e["kernelspec"],)
        assert e["classification"] == "conforme", \
            "classement attendu 'conforme', obtenu '%s' (kernel : %r)" \
            % (e["classification"], e["kernelspec"])
    finally:
        shutil.rmtree(repo, ignore_errors=True)


def test_inventory_is_identical_across_revisions_of_the_same_notebook():
    """#23623 — renomme entre deux revisions : les deux revisions se classent
    de facon identique (le contenu de CHAQUE revision est lu dans SA revision)."""
    repo, rev1, rev2 = _repo_two_revisions_with_a_renamed_notebook()
    try:
        i1 = _inventory_at(repo, rev1)
        i2 = _inventory_at(repo, rev2)
        e1 = {e["path"]: e for e in i1["entries"]}
        e2 = {e["path"]: e for e in i2["entries"]}
        a = e1["MyIA.AI.Notebooks/GenAI/Texte/MGS-26-Equilibrium.ipynb"]
        b = e2["MyIA.AI.Notebooks/GenAI/Texte/MGS-27-Equilibrium.ipynb"]
        assert (a["kernelspec"], a["classification"]) == \
               (b["kernelspec"], b["classification"]) == ("python3", "conforme"), \
            "les deux revisions doivent classer le carnet identiquement : %r vs %r" \
            % (a, b)
    finally:
        shutil.rmtree(repo, ignore_errors=True)


def test_json_output_is_utf8_even_when_pipe_is_cp1252():
    """#23175 -- `--json` pipe est de l'UTF-8, meme sous page cp1252.

    Le registre anti-entropie consomme cet instrument via subprocess
    (encoding="utf-8", strict). Sous Windows, un stdout pipe herite de la
    page de code locale (cp1252) : sans reconfigure, le premier accent
    d'un chemin casse le decodeur cote consommateur -> INSTRUMENT
    ILLEGIBLE (mesure 2026-11-02 : byte 0xe9 en position 192169).

    PYTHONIOENCODING=cp1252 force la page du pipe sur TOUTE plateforme :
    le temoin mord partout, pas seulement sur les sieges Windows.
    """
    repo = tempfile.mkdtemp(prefix="inv-utf8-")
    try:
        _git(repo, "init", "-q")
        _git(repo, "config", "user.email", "test@example.invalid")
        _git(repo, "config", "user.name", "test")
        d = os.path.join(repo, "MyIA.AI.Notebooks", "GameTheory")
        os.makedirs(d)
        # Nom avec accent : c'est lui qui produisait le byte cp1252 dans
        # le JSON emis.
        with open(os.path.join(d, "GT-01-Théorie-Python.ipynb"),
                  "w", encoding="utf-8") as f:
            f.write(_notebook_json())
        _git(repo, "add", "-A")
        _git(repo, "commit", "-qm", "accent")
        env = dict(os.environ, PYTHONIOENCODING="cp1252")
        # bytes bruts : on decode nous-memes, comme le consommateur strict.
        r = subprocess.run(
            [sys.executable,
             os.path.join(REPO_ROOT,
                          "scripts/notebook_tools/inventory_notebook_names.py"),
             "--base", "HEAD", "--json"],
            cwd=repo, capture_output=True, env=env)
        assert r.returncode == 0, r.stderr.decode("utf-8", "replace")
        brut = r.stdout.decode("utf-8")  # UnicodeDecodeError avant correctif
        inv = json.loads(brut)
        assert "é" in brut, "l'accent du chemin a disparu du JSON emis"
        assert inv["by_classification"], "JSON sans contenu"
    finally:
        shutil.rmtree(repo, ignore_errors=True)


def _load_inventory_module():
    """Charge inventory_notebook_names.py comme module (test unitaire direct)."""
    import importlib.util
    script = os.path.join(REPO_ROOT,
                          "scripts/notebook_tools/inventory_notebook_names.py")
    spec = importlib.util.spec_from_file_location(
        "inventory_notebook_names_under_test", script)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_kernel_env_named_coursia_py313_is_known():
    """#5081 — `coursia-py313-argu` (et le prefixe `coursia-py313`) est un
    kernel d'env MESURE et publie du depot, pas un kernel inconnu.

    Mesure fondatrice : la table des kernels de `kernels-runtime.md` publie
    `coursia-py313-argu` (python 3.13.16 / numpy 2.5.2, executable
    `coursia-canonical`) et documente « po-2023 python3 ==
    coursia-py313-argu » — plusieurs noms, un seul environnement. Le carnet
    `Argumentation-08b-Executor-Python.ipynb` (nom canonique, suffixe
    `-python` reconnu, index absent = base implicite) etait classe `ambigu`
    uniquement parce que la liste des prefixes ignorait ce nom — meme classe
    d'artefact que le bloc #23193 (`.net-csharp`, `coursia-ml-training`,
    `pyphi`).

    Controle negatif : un kernel d'env HORS liste (`gametheory-wsl`, reel
    dans le depot mais pas encore measure/publie) reste `ambigu` — la liste
    ne s'elargit pas par sympathie, seulement par mesure publiee.
    """
    mod = _load_inventory_module()
    #idx=None (base implicite), kernel d'env connu, suffixe reconnu -> conforme.
    assert mod._classify(
        "MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/"
        "Argumentation-08b-Executor-Python.ipynb",
        "MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/"
        "Argumentation-08b-Executor-Python",
        None, "coursia-py313-argu", "-python", None,
    ) == mod._CLASSIF_CONFORME
    #Prefixe nu, meme famille : connu lui aussi.
    assert mod._kernel_known("coursia-py313")
    #Controle negatif : kernel env-nomme hors liste reste inconnu.
    assert not mod._kernel_known("gametheory-wsl")
    #Et None reste inconnu (jamais enregistre).
    assert not mod._kernel_known(None)


def test_inventory_archive_revision_no_kernelspec_is_not_broken_protocol():
    """#23655 branche 1 : blobs lus, aucun kernelspec -> inventaire publie.

    Une revision d'archives (carnets JSON sans metadata.kernelspec) doit
    produire un inventaire avec kernel None partout et une note sur stderr —
    pas une exception « protocole rompu ». Avant le correctif, la garde
    comptait les kernelspec trouves au lieu des blobs lus : ce cas legitime
    levait a tort.
    """
    repo = tempfile.mkdtemp(prefix="inv-archives-")
    try:
        _git(repo, "init", "-q")
        _git(repo, "config", "user.email", "test@example.invalid")
        _git(repo, "config", "user.name", "test")
        d = os.path.join(repo, "MyIA.AI.Notebooks", "GenAI", "Texte")
        os.makedirs(d)
        # Archives : JSON de carnet VALIDE mais sans metadata.kernelspec.
        with open(os.path.join(d, "MGS-26-Equilibrium.ipynb"), "w",
                  encoding="utf-8") as f:
            f.write(json.dumps({"cells": [], "metadata": {}, "nbformat": 4,
                                "nbformat_minor": 5}))
        _git(repo, "add", "-A")
        _git(repo, "commit", "-qm", "archives")
        r = subprocess.run(
            [sys.executable,
             os.path.join(REPO_ROOT,
                          "scripts/notebook_tools/inventory_notebook_names.py"),
             "--base", "HEAD", "--json"],
            cwd=repo, capture_output=True, text=True,
            encoding="utf-8", errors="replace")
        assert r.returncode == 0, \
            "revision d'archives ne doit pas lever : %s%s" % (r.stdout, r.stderr)
        inv = json.loads(r.stdout)
        entries = {e["path"]: e for e in inv["entries"]}
        rel = "MyIA.AI.Notebooks/GenAI/Texte/MGS-26-Equilibrium.ipynb"
        assert rel in entries, \
            "entree absente de l'inventaire : %s" % sorted(entries)
        assert entries[rel]["kernelspec"] is None, \
            "kernel attendu None (archives), obtenu %r" % entries[rel]["kernelspec"]
        assert "revision d'archives" in r.stderr, \
            "note stderr attendue, obtenu : %r" % r.stderr
    finally:
        shutil.rmtree(repo, ignore_errors=True)


def test_kernelspecs_at_zero_blob_read_still_raises():
    """#23655 branche 2 : zero blob lu -> RuntimeError, quel que soit le motif.

    Des chemins absents de la revision font repondre `<object> missing` a
    cat-file --batch : zero blob lu. C'est l'etat que la garde doit
    attraper (protocole rompu) — le correctif comptant les blobs lus ne
    l'a pas affaiblie.
    """
    mod = _load_inventory_module()
    repo = tempfile.mkdtemp(prefix="inv-zeroblob-")
    old = os.getcwd()
    try:
        _git(repo, "init", "-q")
        _git(repo, "config", "user.email", "test@example.invalid")
        _git(repo, "config", "user.name", "test")
        _git(repo, "commit", "-q", "--allow-empty", "-m", "vide")
        # _kernelspecs_at lance git SANS cwd : il herite du processus.
        os.chdir(repo)
        try:
            mod._kernelspecs_at("HEAD", ["inexistant.ipynb"])
        except RuntimeError as e:
            assert "protocole rompu" in str(e), \
                "message inattendu : %s" % e
        else:
            raise AssertionError(
                "zero blob lu doit lever RuntimeError (protocole rompu)")
        finally:
            os.chdir(old)
    finally:
        shutil.rmtree(repo, ignore_errors=True)


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    ko = 0
    for t in tests:
        name = t.__name__
        try:
            t()
            print("  OK   %s" % name)
        except AssertionError as e:
            print("  FAIL %s: %s" % (name, e))
            ko += 1
        except Exception as e:
            print("  ERR  %s: %s" % (name, e))
            ko += 1
    print("")
    print("%s : %d tests, %d echec(s)" % ("ECHEC" if ko else "SUCCES", len(tests), ko))
    sys.exit(1 if ko else 0)
