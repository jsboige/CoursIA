"""Tests du mode `--merged` de `check_twin_index_collisions.py`.

Le mode `--merged` juge l'ARBRE DE FUSION (base x tete) plutot que la
seule union base+tete. C'est la seule revision qui repond a la question qui
compte au merge : « `main` sera-t-il rouge apres ce merge ? ».

Trois predicats sont testes :
  * le merge INTRODUIT un doublon -> il bloque (le concurrent est arrive sur
    `main` entre le push et le merge ; l'union base+tete, elle, ne le voit pas) ;
  * le doublon est une DETTE DE LA BASE, que la tete REPAIRE -> il ne bloque
    pas (une PR de renumerotation ne peut pas etre bloquee par la dette
    qu'elle supprime) ;
  * le merge n'introduit rien -> il ne bloque pas.

Le test d'integration rejoue le cas historique mesure le 2026-11-03 :
#23832 et #24010 ont alloue les memes ordinals 0024-0026 sur
`search-05-geneticalgorithms`, et les deux PRs sont passees.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_twin_index_collisions import (  # noqa: E402
    GitError,
    merged_gate_reasons,
    merge_tree_sha,
)

ORG = "scripts/notebook_tools/twin_pairs.d"
PAIR = "app"


def _reg(spec: dict) -> dict:
    """{paire: [(index, nom), ...]} -> {paire: {index: [noms]}}."""
    out: dict = {}
    for pair, entries in spec.items():
        d: dict = {}
        for idx, name in entries:
            d.setdefault(idx, []).append(name)
        out[pair] = {k: sorted(v) for k, v in d.items()}
    return out


# --- predicat pur ------------------------------------------------------------


def test_le_merge_qui_introduit_un_doublon_bloque():
    """La base porte 0007 ; la tete ajoute un AUTRE nom au meme index. Le
    merge porte deux noms a 0007 : c'est une introduction, donc un refus."""
    base = _reg({PAIR: [("0007", "0007-a.yaml")]})
    merged = _reg({PAIR: [("0007", "0007-a.yaml"), ("0007", "0007-b.yaml")]})
    reasons = merged_gate_reasons(base, merged)
    assert len(reasons) == 1
    assert reasons[0]["pair"] == PAIR
    assert reasons[0]["index"] == "0007"
    assert reasons[0]["added"] == ["0007-b.yaml"]
    assert "git mv" in reasons[0]["gist"]


def test_la_dette_de_la_base_non_reperee_ne_bloque_pas():
    """La base porte deja deux noms a 0007 ; le merge ne change rien. C'est
    une dette de la base : la PR qui ne la touche pas ne doit pas etre
    bloquee par elle."""
    base = _reg({PAIR: [("0007", "0007-a.yaml"), ("0007", "0007-b.yaml")]})
    merged = _reg({PAIR: [("0007", "0007-a.yaml"), ("0007", "0007-b.yaml")]})
    assert merged_gate_reasons(base, merged) == []


def test_la_pr_qui_repare_la_dette_ne_bloque_pas():
    """La base porte deux noms a 0007 ; la tete en renumerote un. L'arbre de
    fusion ne porte plus qu'un nom a 0007 : la PR REPAIRE, elle passe."""
    base = _reg({PAIR: [("0007", "0007-a.yaml"), ("0007", "0007-b.yaml")]})
    merged = _reg({PAIR: [("0007", "0007-b.yaml"), ("0009", "0009-a.yaml")]})
    assert merged_gate_reasons(base, merged) == []


def test_un_index_libre_reste_libre():
    """Le cas nominal : la tete ajoute un nom a un index que personne ne
    porte. Le merge n'introduit rien."""
    base = _reg({PAIR: [("0007", "0007-a.yaml")]})
    merged = _reg({PAIR: [("0007", "0007-a.yaml"), ("0009", "0009-a.yaml")]})
    assert merged_gate_reasons(base, merged) == []


def test_aggraver_un_doublon_existant_bloque():
    """La base porte deux noms a 0007 ; la tete en ajoute un troisieme. Le
    merge aggrave la dette : l'introduction est le nom nouveau, et elle
    bloque."""
    base = _reg({PAIR: [("0007", "0007-a.yaml"), ("0007", "0007-b.yaml")]})
    merged = _reg({PAIR: [("0007", "0007-a.yaml"), ("0007", "0007-b.yaml"),
                           ("0007", "0007-c.yaml")]})
    reasons = merged_gate_reasons(base, merged)
    assert len(reasons) == 1
    assert reasons[0]["added"] == ["0007-c.yaml"]


# --- integration : un vrai depot, un vrai merge ------------------------------

def _git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=lane",
         "-c", "user.email=lane@example.invalid", *args],
        capture_output=True, text=True, encoding="utf-8",
        errors="replace", check=True).stdout


def _write_registry(repo: Path, entries: dict[str, str]) -> None:
    for rel, content in entries.items():
        path = repo / ORG / PAIR / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")


def _make_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _write_registry(repo, {"0007-2026-10-01-a.yaml": "date: '2026-10-01'\n"})
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    return repo


def _run_organ(repo: Path, base: str, head: str) -> dict:
    out = subprocess.run(
        [sys.executable,
         str(Path(__file__).resolve().parents[1] /
             "check_twin_index_collisions.py"),
         "--repo", str(repo), "--base", base, "--head", head,
         "--merged", "--gate", "--json"],
        capture_output=True, text=True, encoding="utf-8",
        errors="replace")
    return json.loads(out.stdout)


def test_le_mode_merged_signale_le_doublon_que_le_merge_cree(tmp_path):
    """Scenario de concurrence de lanes : la base porte 0007, la tete ajoute
    un second nom a 0007. L'arbre de fusion porte les deux -> le mode
    `--merged` refuse."""
    repo = _make_repo(tmp_path)
    _git(repo, "checkout", "-q", "-b", "pr")
    _write_registry(repo, {"0007-2026-10-02-b.yaml": "date: '2026-10-02'\n"})
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "commit")

    data = _run_organ(repo, "main", "pr")
    assert data["merged_checked"] is True
    assert data["merged_unreadable"] is None
    assert data["gate_fail"] is True, data
    pairs = {(r["pair"], r["index"]) for r in data["merged_reasons"]}
    assert pairs == {(PAIR, "0007")}
    # Le classique jugement base+tete voit la MEME collision ici (la base ne
    # porte qu'un nom) : les deux jugements concordent sur ce scenario.
    assert data["gate_reasons"], data


def test_le_mode_merged_laisse_passer_la_pr_qui_repare(tmp_path):
    """La base porte deux noms a 0007 (dette) ; la tete renumerote l'un. Le
    merge ne porte plus qu'un nom a 0007 : la porte reste verte."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _write_registry(repo, {
        "0007-2026-10-01-a.yaml": "date: '2026-10-01'\n",
        "0007-2026-10-02-b.yaml": "date: '2026-10-02'\n",
    })
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    _git(repo, "checkout", "-q", "-b", "pr")
    _git(repo, "mv", f"{ORG}/{PAIR}/0007-2026-10-01-a.yaml",
         f"{ORG}/{PAIR}/0009-2026-10-01-a.yaml")
    _git(repo, "commit", "-q", "-m", "renumerotation")

    data = _run_organ(repo, "main", "pr")
    assert data["gate_fail"] is False, data
    assert data["merged_reasons"] == []


def test_un_merge_en_conflit_reste_illisible_et_ne_pretend_pas_etre_propre(tmp_path):
    """« je n'ai pas pu lire » n'est pas « c'est propre » : l'arbre de fusion
    d'un merge en conflit n'est pas definissable, et l'organe le dit.

    Le conflit est construit comme un vrai conflit : les DEUX cotes modifient
    le meme fichier depuis la meme base (une seule partie modifiee se fusionne
    sans conflit, et ne prouverait rien)."""
    repo = _make_repo(tmp_path)
    # La branche `pr` part de la base, avant que `main` ne modifie le fichier.
    _git(repo, "branch", "pr")
    _write_registry(repo, {"0007-2026-10-01-a.yaml": "date: 'main'\n"})
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "main modifie")
    _git(repo, "checkout", "-q", "pr")
    _write_registry(repo, {"0007-2026-10-01-a.yaml": "date: 'pr'\n"})
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "pr modifie")

    with pytest.raises(GitError):
        merge_tree_sha("main", "pr", repo)

    data = _run_organ(repo, "main", "pr")
    assert data["merged_unreadable"], data
    assert data["merged_reasons"] == []
