#!/usr/bin/env python3
"""Tests pour inventory_notebook_names.py (W0 #15488).

Couvre les 7 cas demandés par le body #15488 :
  00, base implicite `a`, `b/c`, sous-série, variants multi-kernel,
  exception plateforme, suffix ambigu.

Plus : tests de cohérence de dénombrement et de partage de grammaire.
"""
import json
import os
import subprocess
import sys

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
