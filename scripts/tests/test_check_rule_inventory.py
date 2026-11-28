"""Tests de scripts/ci/check_rule_inventory.py (#15204).

Controles positifs ancres sur l'instance fondatrice mesuree le 2026-11-23
(lane `myia-po-2028:CoursIA`, issue #15204) : `lean-lakes-doctrine` et
`feedback_comment_action_link` presentes sur disque et absentes de la table
d'inventaire de `docs/reference/claude-code-config.md` ; `lean-lakes-doctrine`
path-gatee et citee nulle part dans le `CLAUDE.md`.

Les controles positifs sont ancres sur un **mini-depot synthetique** : chaque
classe de defaut est posee puis retiree, l'organe doit la voir et la voir
disparaitre. Aucun test ne depend de l'etat reel du depot (la seule exception
est le test d'integrite, qui lit l'arbre vivant et doit etre vert).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts" / "ci"))

from check_rule_inventory import (  # noqa: E402
    announced_block,
    collect,
    collect_base,
    delta,
    etat,
    inventory_names,
    main,
    parse_frontmatter_paths,
    self_test,
)

INVENTORY = """# Config

## Rules (`.claude/rules/`)

**Auto-chargees** -- inventaire.

| Regle | Ce qu'elle porte |
|---|---|
| `alpha` | premier |
| `beta` · `gamma` | deux et trois |
"""

CLAUDE = """# Projet

## Regles modulaires

- **Notebooks** (`alpha` · `beta`) : la synthese par famille.

## RULES CRITIQUES

### A. Coordination
"""


def _ecrire_regle(dossier: Path, nom: str, gatee: bool = False) -> None:
    frontmatter = "---\npaths: '**/*.ipynb'\n---\n\n" if gatee else ""
    (dossier / f"{nom}.md").write_text(frontmatter + f"# {nom}\n", encoding="utf-8")


@pytest.fixture
def mini_depot(tmp_path: Path) -> Path:
    """Mini-depot : deux regles (une gatee), un inventaire et un CLAUDE.md."""
    rules = tmp_path / ".claude" / "rules"
    rules.mkdir(parents=True)
    _ecrire_regle(rules, "alpha", gatee=True)
    _ecrire_regle(rules, "beta")
    _ecrire_regle(rules, "gamma")
    (tmp_path / "docs" / "reference").mkdir(parents=True)
    (tmp_path / "docs" / "reference" / "claude-code-config.md").write_text(
        INVENTORY, encoding="utf-8"
    )
    (tmp_path / "CLAUDE.md").write_text(CLAUDE, encoding="utf-8")
    return tmp_path


def test_mini_depot_sain(mini_depot: Path) -> None:
    """Un depot coherent ne produit aucun finding."""
    resultat = collect(mini_depot)
    assert resultat["on_disk_not_cited"] == []
    assert resultat["gated_not_announced"] == []
    assert resultat["cited_not_on_disk"] == []
    assert resultat["rules_sur_disque"] == 3
    assert resultat["rules_path_gatees"] == 1


def test_regle_sur_disque_absente_de_l_inventaire(mini_depot: Path) -> None:
    """Classe 1 : une regle sur disque, absente de l'inventaire -> rouge."""
    _ecrire_regle(mini_depot / ".claude" / "rules", "delta")
    resultat = collect(mini_depot)
    assert resultat["on_disk_not_cited"] == ["delta"]
    assert main(["--repo-root", str(mini_depot)]) == 1

    # Le retrait rend le depot vert : le finding suit bien la presence.
    (mini_depot / ".claude" / "rules" / "delta.md").unlink()
    assert collect(mini_depot)["on_disk_not_cited"] == []


def test_regle_gatee_non_annoncee_dans_le_claude_md(mini_depot: Path) -> None:
    """Classe 2 : une regle path-gatee, citee nulle part dans le CLAUDE.md."""
    _ecrire_regle(mini_depot / ".claude" / "rules", "epsilon", gatee=True)
    doc = mini_depot / "docs" / "reference" / "claude-code-config.md"
    doc.write_text(
        INVENTORY.replace("| `beta` · `gamma` |", "| `beta` · `gamma` · `epsilon` |"),
        encoding="utf-8",
    )
    resultat = collect(mini_depot)
    assert resultat["gated_not_announced"] == ["epsilon"]
    assert main(["--repo-root", str(mini_depot)]) == 1


def test_entree_d_inventaire_poignant_vers_une_regle_absente(mini_depot: Path) -> None:
    """Classe 3 : l'inventaire cite une regle qui n'existe plus sur disque."""
    doc = mini_depot / "docs" / "reference" / "claude-code-config.md"
    doc.write_text(
        INVENTORY.replace("| `alpha` |", "| `alpha` · `zeta` |"), encoding="utf-8"
    )
    resultat = collect(mini_depot)
    assert resultat["cited_not_on_disk"] == ["zeta"]
    assert main(["--repo-root", str(mini_depot)]) == 1


def test_frontmatter_paths_est_detecte() -> None:
    """La cle `paths:` du frontmatter suffit a marquer une regle gatee."""
    assert parse_frontmatter_paths("---\npaths: '**/*.ipynb'\n---\n\ncorps\n")
    assert parse_frontmatter_paths("---\npaths:\n  - 'a/**'\n---\n\ncorps\n")
    assert not parse_frontmatter_paths("---\nname: x\n---\n\ncorps\n")
    assert not parse_frontmatter_paths("corps sans frontmatter\n")


def test_inventaire_ignore_les_mentions_en_prose() -> None:
    """Un nom cite en prose historique n'est pas une entree d'inventaire."""
    markdown = INVENTORY + "\nLa regle `secrets-roosync-policy` a ete fusionnee.\n"
    assert inventory_names(markdown) == {"alpha", "beta", "gamma"}


def test_bloc_annonce_borne_au_bloc_regles_modulaires() -> None:
    """La recherche est bornee au bloc "Regles modulaires" du CLAUDE.md."""
    markdown = "# P\n\n## Regles modulaires\n\n- (`alpha`)\n\n## Apres\n\n- (`beta`)\n"
    bloc = announced_block(markdown)
    assert "alpha" in bloc
    assert "beta" not in bloc


def test_verdict_du_depot_vivant_est_vert() -> None:
    """Integrite : l'arbre vivant ne porte aucun finding (apres le correctif)."""
    resultat = collect(REPO)
    assert resultat["on_disk_not_cited"] == [], resultat["on_disk_not_cited"]
    assert resultat["gated_not_announced"] == [], resultat["gated_not_announced"]
    assert resultat["cited_not_on_disk"] == [], resultat["cited_not_on_disk"]


def test_delta_ignore_la_dette_heritee_de_la_base() -> None:
    """Le cliquet : un finding deja present sur la base n'est pas rejoue."""
    base = etat({"alpha": True}, {"alpha"}, "- (`alpha`)\n")
    head = etat({"alpha": True, "beta": False}, {"alpha"}, "- (`alpha`)\n")
    assert delta(base, base) == []
    assert delta(base, head) == [("ON_DISK_NOT_CITED", "beta")]


def test_delta_voit_le_finding_qui_disparait() -> None:
    """Un finding corrige par la PR n'est pas rouge non plus."""
    base = etat({"alpha": True}, set(), "")
    head = etat({"alpha": True}, {"alpha"}, "- (`alpha`)\n")
    assert delta(base, head) == []


def test_auto_controle_de_l_organe_passe() -> None:
    """`--self` prouve que l'organe voit ses trois classes."""
    assert self_test() == 0


def _git(repo: Path, *args: str) -> str:
    import subprocess

    proc = subprocess.run(
        ["git", *args], cwd=str(repo), capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, proc.stderr
    return proc.stdout


def test_collect_base_lit_le_commit_de_reference(tmp_path: Path) -> None:
    """`collect_base` lit l'etat dans les objets git, sans toucher l'arbre."""
    import subprocess

    repo = tmp_path / "depot"
    (repo / ".claude" / "rules").mkdir(parents=True)
    (repo / "docs" / "reference").mkdir(parents=True)
    _ecrire_regle(repo / ".claude" / "rules", "alpha", gatee=True)
    _ecrire_regle(repo / ".claude" / "rules", "beta")
    (repo / "docs" / "reference" / "claude-code-config.md").write_text(
        INVENTORY, encoding="utf-8")
    (repo / "CLAUDE.md").write_text(CLAUDE, encoding="utf-8")
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    base_sha = _git(repo, "rev-parse", "HEAD").strip()

    etat_base = collect_base(repo, base_sha)
    assert etat_base["rules_sur_disque"] == 2
    assert etat_base["rules_path_gatees"] == 1
    assert etat_base["gated_not_announced"] == []

    # la tete ajoute une regle absente de l'inventaire
    _ecrire_regle(repo / ".claude" / "rules", "delta")
    etat_tete = collect(repo)
    assert etat_tete["on_disk_not_cited"] == ["delta"]
    assert delta(etat_base, etat_tete) == [("ON_DISK_NOT_CITED", "delta")]

