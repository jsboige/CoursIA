"""Le garde markdown-rendering doit NOMMER sa reparation (#12089).

Pourquoi ce test existe
-----------------------
Le garde a bloque 14 PRs sur 5 lanes le matin du 2026-08-21, puis 11 PRs sur
3 lanes l'apres-midi — toutes sur la meme regle `yaml_block_open_no_close`,
toutes reparables par la meme commande. Cette commande n'etait nommee nulle
part : `grep -rn fix_hr_separator .github/workflows/` rendait zero. Chaque
auteur devait la redecouvrir, et le coordinateur la rediffusait a la main.

Une regle non appliquee ne se corrige pas par plus de vigilance : elle demande
un organe. L'organe est le hint ; ce test est ce qui l'empeche de disparaitre.

Ce que le test verrouille, et ce qu'il ne verrouille PAS
--------------------------------------------------------
Il verrouille (a) que la regle a fixer nomme sa commande, (b) que les regles
SANS fixer soient listees comme telles au lieu de recevoir une suggestion
inoperante, (c) que le rappel de portee (notebook entier, pas la tranche)
accompagne la commande.

Il ne verifie pas que `fix_hr_separator.py` repare effectivement — c'est la
responsabilite de cet outil-la, pas du hint.
"""
import pathlib
import sys

import pytest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "notebook_tools"))

import detect_markdown_rendering as dmr  # noqa: E402


def _hints(capsys, rules):
    dmr._print_repair_hints([{"rule": r} for r in rules])
    return capsys.readouterr().err


def test_regle_a_fixer_nomme_sa_commande(capsys):
    err = _hints(capsys, ["yaml_block_open_no_close"])
    assert "fix_hr_separator.py --apply" in err
    assert "yaml_block_open_no_close" in err


def test_le_rappel_de_portee_accompagne_la_commande(capsys):
    """Le gating par baseline fait resurgir une cellule dont le hash a change :
    reparer la seule tranche touchee laisse le garde rouge. Sans ce rappel, la
    commande seule envoie l'auteur dans un deuxieme aller-retour."""
    err = _hints(capsys, ["yaml_block_open_no_close"])
    assert "ENTIER" in err


def test_regle_sans_fixer_ne_recoit_aucune_commande(capsys):
    """Suggerer une commande inoperante coute plus cher que le silence."""
    err = _hints(capsys, ["setext_oversized"])
    assert "fix_hr_separator" not in err
    assert "Sans reparation outillee" in err
    assert "setext_oversized" in err


def test_mixte_separe_les_deux_familles(capsys):
    err = _hints(capsys, ["yaml_block_open_no_close", "frontmatter_rawyaml"])
    assert "fix_hr_separator.py --apply" in err
    assert "Sans reparation outillee" in err
    assert "frontmatter_rawyaml" in err


def test_aucun_finding_aucune_sortie(capsys):
    assert _hints(capsys, []) == ""


@pytest.mark.parametrize("rule", sorted(dmr.RULE_REPAIR))
def test_toute_entree_de_la_table_est_une_regle_connue(rule):
    """Garde anti-derive : une entree de RULE_REPAIR qui ne correspond a aucune
    regle du detecteur serait un conseil pour un defaut qui n'est jamais
    signale — invisible, donc jamais corrige."""
    assert rule in dmr.RULE_SEVERITY


# --- #14590 : sortie SIGPIPE-safe + --max-findings ---------------------------

def _run_driver(tmp_path):
    """Execute un driver dans un processus isole : le wrapper __main__ fait un
    dup2 de stdout vers devnull, on ne veut pas empoisonner le fd 1 de la
    session pytest."""
    import subprocess
    driver = tmp_path / "driver_14590.py"
    driver.write_text(
        "import sys\n"
        f"sys.path.insert(0, r'{pathlib.Path(dmr.__file__).parent}')\n"
        "import detect_markdown_rendering as d\n"
        "def boom(): raise BrokenPipeError()\n"
        "d.main = boom\n"
        "src = open(d.__file__, encoding='utf-8').read()\n"
        "import textwrap\n"
        "block = textwrap.dedent(src.split('if __name__ == \"__main__\":', 1)[1])\n"
        "exec(block, d.__dict__)\n",
        encoding="utf-8",
    )
    return subprocess.run(
        [sys.executable, str(driver)], capture_output=True, text=True, timeout=60
    )


def test_tube_ferme_rend_141_sans_traceback(tmp_path):
    """Un appelant qui borne la sortie (| head) fermait le tube APRES le
    verdict et tuait le script sur BrokenPipeError non gere (#14590, log CI
    du 2026-09-04 : traceback dans la boucle d'affichage des findings).
    Le wrapper doit rendre 141 (128 + SIGPIPE) -- pas une traceback, et pas
    non plus le 'Exception ignored' du flush final."""
    proc = _run_driver(tmp_path)
    assert proc.returncode == 141, proc.stderr
    assert "Traceback" not in proc.stderr
    assert "Exception ignored" not in proc.stderr


def test_max_findings_remplace_le_cap_dur(tmp_path):
    """--max-findings N doit exister et cappeer la liste des findings :
    le workflow appelait | head -8, ce qui masquait tout (y compris les
    plantages) derriere || true. Un cap interne rend le tube inutile."""
    import json as _json
    import subprocess
    nb_dir = tmp_path / "nbs"
    nb_dir.mkdir()
    for i in range(3):
        nb = {
            "cells": [{"cell_type": "markdown", "metadata": {},
                       "source": ["---\n", "title: unclosed block\n"]}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }
        (nb_dir / f"fixture_{i}.ipynb").write_text(
            _json.dumps(nb), encoding="utf-8")
    script = pathlib.Path(dmr.__file__)
    proc = subprocess.run(
        [sys.executable, str(script), "--report", "--max-findings", "2", str(nb_dir)],
        capture_output=True, text=True, timeout=120,
    )
    assert proc.returncode == 0, proc.stderr
    finding_lines = [l for l in proc.stdout.splitlines() if "[yaml_block_open_no_close]" in l]
    assert len(finding_lines) == 2, proc.stdout
    assert "1 more" in proc.stdout
