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
