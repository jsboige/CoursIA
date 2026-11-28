"""Tests de `check_cli_help_coverage`.

Issue de reference : #28964 (tranche 1 de #27071). Contrat de l'organe :

  1. detection : un outil dont le parseur n'a pas de `description=` doit etre
     rendu `NO_DESCRIPTION` -- et un outil qui en a une doit etre rendu `OK`.
     Le couple est mesure sur une arborescence synthetique, donc le verdict ne
     depend pas de l'etat du depot.
  2. extraction : la description est le texte situe entre le bloc `usage:` et
     le premier en-tete de groupe argparse. Un enonce qui se termine par ":"
     reste une description ; un epilogue posterior ne peut pas la confondre.
  3. codes de sortie distincts : `EXIT_NONZERO` (l'outil echoue), `TIMEOUT`
     (delai borne), et le controle positif `--expect-missing` qui rend 2 quand
     le nombre attendu d'outils sans description n'est pas atteint -- c'est le
     temoin qui distingue "tout est couvert" d'un chemin de detection mort.
"""

import importlib.util
import subprocess
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "check_cli_help_coverage",
    Path(__file__).resolve().parents[1] / "check_cli_help_coverage.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)

SCRIPT_UNDER_TEST = Path(__file__).resolve().parents[1] / "check_cli_help_coverage.py"

# Gabarits d'outils synthetiques. Chacun est un point d'entree argparse
# complet : la detection s'appuie sur `def main(` et `argparse`.
OUTIL_AVEC_DESCRIPTION = '''
import argparse


def main() -> int:
    parser = argparse.ArgumentParser(description="Verifie un contrat de test.")
    parser.add_argument("--cible", default="x", help="Cible du test.")
    args = parser.parse_args()
    print(args.cible)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''

OUTIL_SANS_DESCRIPTION = '''
import argparse


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cible", default="x")
    args = parser.parse_args()
    print(args.cible)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''

OUTIL_EN_ERREUR = '''
import argparse
import module_qui_nexiste_pour_le_test


def main() -> int:
    parser = argparse.ArgumentParser(description="Echoue exprimes.")
    parser.parse_args()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''

# L'echec doit survenir AVANT que argparse ne traite `--help` : sinon
# l'outil rend son aide et sort en 0, et le defaut est invisible. C'est la
# realite mesuree -- `--help` court-circuite le corps de l'outil.
OUTIL_BLOQUANT = '''
import argparse
import time

time.sleep(60)


def main() -> int:
    parser = argparse.ArgumentParser(description="Se bloque exprimes.")
    parser.parse_args()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''

OUTIL_SANS_ARGPARSE = '''
import sys


def main() -> int:
    print(sys.argv)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''


def _arbre(tmp_path: Path, outils: dict[str, str]) -> Path:
    """Ecrit un arbre d'outils synthetiques et rend le dossier `scripts/`."""
    scripts_dir = tmp_path / "scripts"
    scripts_dir.mkdir(parents=True, exist_ok=True)
    for nom, source in outils.items():
        (scripts_dir / nom).write_text(source, encoding="utf-8")
    return scripts_dir


# ---------- 1. detection sur arbre synthetique ----------


def test_detection_description_absente_et_presente(tmp_path):
    """Un parseur sans `description=` est `NO_DESCRIPTION`, avec description c'est `OK`."""
    scripts_dir = _arbre(
        tmp_path,
        {
            "avec.py": OUTIL_AVEC_DESCRIPTION,
            "sans.py": OUTIL_SANS_DESCRIPTION,
        },
    )
    outils = mod.decouvrir_outils(scripts_dir)
    assert len(outils) == 2, "les deux scripts ont un point d'entree"

    verdicts = {m["path"].split("/")[-1]: m["verdict"] for m in
                (mod.mesurer_outil(o, timeout=30.0) for o in outils)}
    assert verdicts["avec.py"] == "OK"
    assert verdicts["sans.py"] == "NO_DESCRIPTION"


def test_detection_ignore_les_scripts_sans_point_entree(tmp_path):
    """Sans `def main(` ni `argparse`, le script n'est pas un outil CLI."""
    scripts_dir = _arbre(tmp_path, {"plat.py": OUTIL_SANS_ARGPARSE})
    assert mod.decouvrir_outils(scripts_dir) == []


def test_detection_ignore_le_stock_archive(tmp_path):
    """`_archive/` est un stock a vider, pas une surface d'action."""
    archive = tmp_path / "scripts" / "_archive"
    archive.mkdir(parents=True)
    (archive / "vieux.py").write_text(OUTIL_AVEC_DESCRIPTION, encoding="utf-8")
    assert mod.decouvrir_outils(tmp_path / "scripts") == []


def test_verdict_exit_nonzero(tmp_path):
    """Un outil dont `--help` sort en erreur est `EXIT_NONZERO`, pas `OK`."""
    scripts_dir = _arbre(tmp_path, {"casse.py": OUTIL_EN_ERREUR})
    outil = mod.decouvrir_outils(scripts_dir)[0]
    mesure = mod.mesurer_outil(outil, timeout=30.0)
    assert mesure["verdict"] == "EXIT_NONZERO"
    assert mesure["rc"] != 0


def test_verdict_timeout_borne(tmp_path):
    """Le delai est borne : un outil qui bloque donne `TIMEOUT`, pas une attente."""
    scripts_dir = _arbre(tmp_path, {"bloquant.py": OUTIL_BLOQUANT})
    outil = mod.decouvrir_outils(scripts_dir)[0]
    mesure = mod.mesurer_outil(outil, timeout=3.0)
    assert mesure["verdict"] == "TIMEOUT"
    assert mesure["rc"] is None


# ---------- 2. extraction de la description ----------


def test_extraction_description_apres_usage():
    texte = (
        "usage: outil [-h] [--cible CIBLE]\n"
        "\n"
        "Verifie un contrat de test.\n"
        "\n"
        "options:\n"
        "  -h, --help  show this help message and exit\n"
    )
    assert mod.extraire_description(texte) == "Verifie un contrat de test."


def test_extraction_absente_quand_le_usage_est_suivi_du_groupe():
    texte = (
        "usage: outil [-h]\n"
        "\n"
        "positional arguments:\n"
        "  cible  une cible\n"
    )
    assert mod.extraire_description(texte) == ""


def test_extraction_enonce_terminant_par_deux_points_reste_une_description():
    """Un enonce qui se termine par ':' n'est pas un en-tete de groupe argparse."""
    texte = (
        "usage: outil [-h]\n"
        "\n"
        "Mesures disponibles:\n"
        "\n"
        "options:\n"
        "  -h, --help  show this help message and exit\n"
    )
    assert mod.extraire_description(texte) == "Mesures disponibles:"


def test_extraction_sans_usage_rend_vide():
    assert mod.extraire_description("rien a voir ici\n") == ""


def test_extraction_description_multiligne():
    texte = (
        "usage: outil [-h]\n"
        "\n"
        "Premiere ligne.\n"
        "Seconde ligne.\n"
        "\n"
        "options:\n"
        "  -h, --help  show this help message and exit\n"
    )
    assert mod.extraire_description(texte) == "Premiere ligne. Seconde ligne."


# ---------- 3. agregation et controle positif ----------


def test_agregation_par_dossier():
    mesures = [
        {"path": "scripts/ci/a.py", "verdict": "OK"},
        {"path": "scripts/ci/b.py", "verdict": "NO_DESCRIPTION"},
        {"path": "scripts/lean/c.py", "verdict": "OK"},
    ]
    dossiers = {d["dossier"]: d for d in mod.agreger(mesures)}
    assert dossiers["scripts/ci"]["total"] == 2
    assert dossiers["scripts/ci"]["couverts"] == 1
    assert dossiers["scripts/ci"]["part"] == 50.0
    assert dossiers["scripts/lean"]["part"] == 100.0


def test_controle_positif_non_tenu_rend_2(tmp_path):
    """Armer `--expect-missing` sur un arbre sans defaut rend 2 : le temoin."""
    scripts_dir = _arbre(tmp_path, {"avec.py": OUTIL_AVEC_DESCRIPTION})
    resultat = subprocess.run(
        [sys.executable, str(SCRIPT_UNDER_TEST),
         "--dir", str(scripts_dir),
         "--expect-missing", "1"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert resultat.returncode == mod.EXIT_CONTROL_OR_ERROR


def test_controle_positif_tenu_rend_0(tmp_path):
    """Le controle tient quand le defaut attendu est bien la : rc=0."""
    scripts_dir = _arbre(
        tmp_path,
        {"avec.py": OUTIL_AVEC_DESCRIPTION, "sans.py": OUTIL_SANS_DESCRIPTION},
    )
    resultat = subprocess.run(
        [sys.executable, str(SCRIPT_UNDER_TEST),
         "--dir", str(scripts_dir),
         "--expect-missing", "1"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert resultat.returncode == mod.EXIT_OK, resultat.stderr


def test_code_de_sortie_sous_seuil():
    """`--min-coverage` non atteint rend 1, distinct du code de controle."""
    assert mod.EXIT_OK == 0
    assert mod.EXIT_BELOW_THRESHOLD == 1
    assert mod.EXIT_CONTROL_OR_ERROR == 2
