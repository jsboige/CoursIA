"""Tests for the UTF-8 environment passed to pick_idle_grain.py's Python child.

Le picker lance ``check_lane_claim.py`` en sous-process et lit son stdout en
UTF-8. Le parametre ``encoding="utf-8"`` de ``subprocess.run`` ne dit que
comment le PARENT decode -- il ne dit rien de ce que l'ENFANT encode. Un
`python` enfant dont stdout est un tube choisit
``locale.getpreferredencoding()``, soit **cp1252** sur un Windows francais.

Incident fondateur (2026-09-01, lane myia-po-2027:CoursIA-2) : le picker est
mort en ``UnicodeDecodeError: 'utf-8' codec can't decode byte 0x97`` -- 0x97
est le tiret cadratin en cp1252, invalide en UTF-8. ``check_lane_claim.py``
rend des verdicts en francais accentue ("claim perime", "deja claim par cette
lane"), donc le crash n'est pas un cas de bord : c'est la sortie nominale.

Le hook pre-commit du depot ("refuse NEW text=True without encoding=") ne peut
pas attraper ce defaut : il regarde l'appel du parent, qui est *deja* correct.
Seule ``PYTHONIOENCODING`` traverse la frontiere de process.

Un detecteur se valide par ses faux negatifs : T3 ci-dessous est le gate qui
rougit si le ``env=`` disparait du site d'appel. T2 seul ne suffirait pas --
la CI tourne sous Linux, ou l'encodage par defaut est deja UTF-8, donc T2 y
passerait meme sans le correctif.
"""

import ast
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts"))

import pick_idle_grain as pig  # noqa: E402

# Caracteres que check_lane_claim.py emet reellement (verdicts francais) plus
# le tiret cadratin, dont l'octet cp1252 0x97 a produit le crash fondateur.
NON_ASCII_SAMPLE = "verdict: claim perime — deja claim par cette lane"


def test_child_env_forces_utf8_and_preserves_environment():
    """T1 -- la variable est posee, et le reste de l'environnement survit."""
    import os

    env = pig._utf8_child_env()
    assert env["PYTHONIOENCODING"] == "utf-8"
    # Ne pas repartir d'un environnement vide : un enfant Python prive de PATH
    # ou de SYSTEMROOT ne demarre pas sous Windows.
    missing = [k for k in os.environ if k not in env]
    assert not missing, f"variables perdues : {missing[:5]}"


def test_child_round_trips_non_ascii_through_a_pipe():
    """T2 -- bout en bout : l'enfant ecrit, le parent decode, rien ne casse.

    C'est la reproduction litterale du crash. Sous Windows FR sans le
    correctif, ce test leve UnicodeDecodeError.
    """
    r = subprocess.run(
        [sys.executable, "-c", f"print({NON_ASCII_SAMPLE!r})"],
        capture_output=True, text=True, encoding="utf-8", timeout=60,
        env=pig._utf8_child_env(),
    )
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == NON_ASCII_SAMPLE


def test_call_site_passes_the_utf8_env():
    """T3 -- le gate anti-regression, et le seul qui rougisse sous Linux.

    On lit l'AST plutot que le texte : un ``grep`` sur "env=" passerait au
    vert sur une occurrence en commentaire ou dans une autre fonction.
    """
    tree = ast.parse((REPO / "scripts" / "pick_idle_grain.py").read_text(encoding="utf-8"))

    fn = next(n for n in tree.body
              if isinstance(n, ast.FunctionDef) and n.name == "check_claims")

    runs = [n for n in ast.walk(fn)
            if isinstance(n, ast.Call)
            and isinstance(n.func, ast.Attribute)
            and n.func.attr == "run"]
    assert len(runs) == 1, f"attendu 1 subprocess.run dans check_claims, vu {len(runs)}"

    kwargs = {kw.arg for kw in runs[0].keywords}
    assert "env" in kwargs, (
        "check_claims lance un enfant Python sans env= : son stdout sera encode "
        "en cp1252 sous Windows FR et le decodage UTF-8 du parent plantera"
    )

    env_kw = next(kw for kw in runs[0].keywords if kw.arg == "env")
    assert isinstance(env_kw.value, ast.Call), "env= doit appeler _utf8_child_env()"
    assert env_kw.value.func.id == "_utf8_child_env"


def test_helper_is_defined_at_module_scope():
    """T4 -- le helper est reutilisable par tout futur enfant Python.

    Garde contre une re-insertion accidentelle a l'interieur d'une fonction
    (elle parserait sans erreur tout en rendant le helper inatteignable).
    """
    tree = ast.parse((REPO / "scripts" / "pick_idle_grain.py").read_text(encoding="utf-8"))
    top_level = {n.name for n in tree.body if isinstance(n, ast.FunctionDef)}
    assert "_utf8_child_env" in top_level


# ---------------------------------------------------------------------------
# T5-T6 : l'invocation DIRECTE de check_lane_claim.py
#
# T1-T4 couvrent le chemin d'appel du picker. Mais lane-claim-protocol.md
# prescrit d'appeler check_lane_claim.py *directement* avant d'editer -- et ce
# chemin-la n'a pas de parent pour lui poser PYTHONIOENCODING.
#
# Le mode de defaillance y est pire que le crash du picker : une fleche U+2192
# n'existe pas dans cp1252, donc le print leve UnicodeEncodeError et le script
# sort en exit 1. Or un exit non-nul se lit, dans la regle, "claim d'une autre
# lane, ne pas commencer". Un plantage d'encodage se deguisait en verrou.
# Mesure du 2026-09-01 (Windows FR) : #13614 rendait rc=1 sur ce seul motif.
# ---------------------------------------------------------------------------

CLAIM_SCRIPT = REPO / "scripts" / "check_lane_claim.py"

# L'idiome d'auto-protection, tel qu'il doit apparaitre en tete de main().
RECONFIGURE_SNIPPET = (
    "for _stream in (sys.stdout, sys.stderr):\n"
    "    if hasattr(_stream, 'reconfigure'):\n"
    "        _stream.reconfigure(encoding='utf-8', errors='replace')\n"
)
ARROW_LINE = "print('verdict -> \u2192 claim perime, deja claim')\n"


def _run_under_cp1252(code: str) -> subprocess.CompletedProcess:
    """Enfant Python dont stdout est un tube force en cp1252.

    Rend le defaut reproductible sur TOUTE plateforme : sans cela le test
    passerait en CI Linux (UTF-8 par defaut) meme correctif retire.
    """
    import os

    env = {**os.environ, "PYTHONIOENCODING": "cp1252", "PYTHONUTF8": "0"}
    return subprocess.run([sys.executable, "-c", code],
                          capture_output=True, env=env, timeout=60)


def test_t5_check_lane_claim_reconfigures_its_own_streams():
    """T5 -- main() se protege lui-meme, avant tout parsing d'arguments."""
    tree = ast.parse(CLAIM_SCRIPT.read_text(encoding="utf-8"))
    fn = next(n for n in tree.body
              if isinstance(n, ast.FunctionDef) and n.name == "main")

    calls = [n for n in ast.walk(fn)
             if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Attribute)
             and n.func.attr == "reconfigure"]
    assert calls, (
        "main() de check_lane_claim.py ne reconfigure pas ses flux : sous "
        "Windows FR un verdict portant une fleche sortira en exit 1, que la "
        "regle lira comme un claim d'une autre lane"
    )
    kwargs = {kw.arg for c in calls for kw in c.keywords}
    assert {"encoding", "errors"} <= kwargs, f"attendu encoding= et errors=, vu {kwargs}"


def test_t6_negative_control_the_defect_is_detectable():
    """T6a -- SANS l'idiome, un flux cp1252 plante bien sur la fleche.

    Controle negatif : si celui-ci passait, T6b ne prouverait rien.
    """
    out = _run_under_cp1252(ARROW_LINE)
    assert out.returncode != 0, (
        "le controle negatif n'a pas plante : ce test ne peut pas detecter "
        "le defaut qu'il pretend garder"
    )
    assert b"UnicodeEncodeError" in out.stderr


def test_t6_the_idiom_actually_repairs_it():
    """T6b -- AVEC l'idiome, le meme flux rend de l'UTF-8 valide, exit 0."""
    out = _run_under_cp1252("import sys\n" + RECONFIGURE_SNIPPET + ARROW_LINE)
    assert out.returncode == 0, out.stderr.decode("utf-8", "replace")
    out.stdout.decode("utf-8")  # leve UnicodeDecodeError si ce n'est pas de l'UTF-8
    assert "→" in out.stdout.decode("utf-8")
