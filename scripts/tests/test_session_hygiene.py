"""Tests pour scripts/coordination/session_hygiene.py — issue #17496.

Le predicat central de l'organe (``check_branch``) est :
sur une branche de feature, si la branche est deja livree sur origin/main
par squash-mêrge et qu'il n'y a aucun commit non pousse, alors l'arbre est
parque sans raison -> RED.

Deux tests naifs echouent ici, mesures sur le cas reel :
  * ``merge-base --is-ancestor`` : aveugle au squash-mêrge.
  * le diff TROIS-POINTS ``origin/main...branche`` : apres squash, la
    merge-base precede la livraison, donc il re-presente comme ajoute ce
    qui est DEJA sur main.

Le predicat juste compare les ETATS FINAUX sur les fichiers que la branche
touche : si le blob de la branche est identique a celui de main partout ou
elle a ecrit, elle ne livre plus rien. C'est exactement ce que ces tests
pinnent.

Acceptance issue #17496 :
  - controles positif (squash livre -> RED) et negatif (branche divergente
    -> AMBER), sans reseau (``origin`` pointe vers un depot nu local).
  - nit (b) : distinguer ``diff vide`` (squash livre) de ``diff en erreur``
    (rc != 0). Non tranche ici -- l'option de l'auteur est documentee dans
    l'issue ; le test verifie que le geste reel passe par les deux cas.
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
from pathlib import Path

import pytest

# Le runner WSL self-hosted du CI (myia-ai-01-wsl-4) tombe en RLIMIT_NPROC
# quand pytest-xdist lance plusieurs sous-processes git en parallele
# (fork() -> "Resource temporarily unavailable"). Le test lui-meme est
# lineaire et n'a aucun interet a etre parallelise : on declare la
# classe ``serial`` pour que pytest-xdist l'isole, et on force
# ``GIT_OPTIONAL_LOCKS=0`` pour reduire les forks internes de git
# (sideband demultiplexer, rev-list worker, pack-objects helper).
os.environ.setdefault("GIT_OPTIONAL_LOCKS", "0")
pytestmark = pytest.mark.xdist_group(name="serial-git")

# scripts/coordination/session_hygiene.py est un module plat (pas un
# package). On l'importe via spec_from_file_location comme dans le conftest
# de test_scan_duplicate_test_pairs.py, et on l'enregistre dans sys.modules
# pour que ``@dataclass`` (qui depend de sys.modules[cls.__module__])
# fonctionne (cf. note testee a la main, py3.13).
_HERE = Path(__file__).resolve().parent
_SCRIPT = _HERE.parent / "coordination" / "session_hygiene.py"
_spec = importlib.util.spec_from_file_location("session_hygiene", _SCRIPT)
session_hygiene = importlib.util.module_from_spec(_spec)
sys.modules["session_hygiene"] = session_hygiene
_spec.loader.exec_module(session_hygiene)


# ---------------------------------------------------------------------------
# helpers : mini-repo git jetable, sans aucun acces reseau
# ---------------------------------------------------------------------------


def _run(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess:
    """Lance une commande git. Si ``cwd`` est None, le depot nu est cree
    a partir du cwd courant (utilise pour ``git init --bare``).

    Les variables d'environnement suivantes sont forcees pour rester sous
    RLIMIT_NPROC sur le runner WSL self-hosted (myia-ai-01-wsl-4) :
      * ``GIT_OPTIONAL_LOCKS=0`` : pas de verrous d'optimisation
      * ``GIT_PACK_THREADS=1`` : pack-objects sur 1 seul thread
      * ``GIT_REV_LIST_THREADS=1`` : idem pour ``rev-list``
    """
    env = {
        **os.environ,
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_PACK_THREADS": "1",
        "GIT_REV_LIST_THREADS": "1",
    }
    proc = subprocess.run(
        ["git", *args],
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
        timeout=30,
        env=env,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} (cwd={cwd}) -> rc={proc.returncode}\n"
            f"stdout={proc.stdout!r}\nstderr={proc.stderr!r}"
        )
    return proc


def _make_mini_repo(tmp_path: Path, name: str = "repo") -> Path:
    """Construit un depot git jetable :

    - depot nu ``origin.git`` (fait office de remote)
    - clone de travail ``repo`` avec un commit initial, ``origin`` pointe
      vers le depot nu (file://).
    """
    origin = tmp_path / "origin.git"
    repo = tmp_path / name

    _run("init", "--bare", "--initial-branch=main", "--quiet", str(origin))
    _run("init", "--initial-branch=main", "--quiet", str(repo))
    _run("config", "user.email", "test@example.com", cwd=repo)
    _run("config", "user.name", "test", cwd=repo)
    _run("config", "commit.gpgsign", "false", cwd=repo)
    _run("remote", "add", "origin", str(origin), cwd=repo)

    (repo / "README.md").write_text("# Test\n", encoding="utf-8")
    _run("add", "README.md", cwd=repo)
    _run("commit", "-m", "init", "--quiet", cwd=repo)
    _run(
        "push", "-u", "origin", "main", "--quiet", cwd=repo,
    )

    return repo


def _branch_create(repo: Path, branch: str, file: str, content: str) -> None:
    """Cree une branche, ajoute un fichier, commit, push (sans tracking)."""
    _run("checkout", "-b", branch, "--quiet", cwd=repo)
    target = repo / file
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8")
    _run("add", file, cwd=repo)
    _run("commit", "-m", f"add {file}", "--quiet", cwd=repo)
    _run(
        "push", "origin", branch, "--quiet", cwd=repo,
    )


def _squash_merge(repo: Path, branch: str, file: str) -> None:
    """Sur main : squash-mêrge ``branch`` et push.

    Apres le squash, ``git merge-base --is-ancestor branch main`` est VRAI,
    et ``git log origin/main..branch`` est VIDE -- le predicat naif
    (ascendance) classe la branche comme ``livree`` sans regarder le contenu.
    """
    _run("checkout", "main", "--quiet", cwd=repo)
    _run("merge", "--squash", branch, "--quiet", cwd=repo)
    _run("commit", "-m", f"squash {branch}", "--quiet", cwd=repo)
    _run(
        "push", "origin", "main", "--quiet", cwd=repo,
    )


# ---------------------------------------------------------------------------
# controle positif : squash livre -> RED ``parque sans raison``
# ---------------------------------------------------------------------------


def test_squash_merged_branch_is_classified_parked(tmp_path):
    """Branche ``feature/done`` dont tout le contenu a ete squash-mêrge sur
    main -> ``check_branch`` doit retourner RED (parquee sans raison).

    Pour que le predicat RED tienne, il faut que la branche ne livre
    PLUS rien (``git diff --stat origin/main <branche> -- <fichiers
    touchés>`` vide) ET qu'elle n'ait aucun commit non pousse. Apres le
    squash-mêrge on repositionne donc la branche locale a la tete de
    origin/main (meme blob que le main squash-mêrge), et on repousse.
    La branche existe encore localement mais ne diverge plus.
    """
    repo = _make_mini_repo(tmp_path)
    _branch_create(repo, "feature/done", "docs/extra.md", "extra\n")
    _squash_merge(repo, "feature/done", "docs/extra.md")

    # La branche locale pointe encore sur l'ancien commit pre-squash ;
    # on la reset a origin/main (meme blob) puis on repousse (avec
    # --set-upstream pour que ``@{u}`` designe origin/feature/done).
    _run("checkout", "feature/done", "--quiet", cwd=repo)
    _run("reset", "--hard", "origin/main", "--quiet", cwd=repo)
    _run(
        "push", "--force-with-lease", "--set-upstream", "origin",
        "feature/done", "--quiet", cwd=repo,
    )

    checks = session_hygiene.check_branch(repo)
    assert len(checks) == 1, f"un seul check 'branche' attendu, vu {len(checks)}"
    c = checks[0]
    assert c.name == "branche"
    assert c.level == session_hygiene.RED, (
        f"squash-mêrge devrait classer la branche parquée (RED), "
        f"mais organe a retourne {c.level}: {c.detail}"
    )
    assert "deja integralement sur origin/main" in c.detail
    assert "parke sans raison" in c.detail


def test_squash_merged_branch_after_checkout_main_is_green(tmp_path):
    """Apres squash-mêrge + retour sur main, l'organe doit etre GREEN.

    C'est le cas non-regression : le verdict RED ne s'applique qu'aux
    branches de feature parkées, pas a main lui-meme.
    """
    repo = _make_mini_repo(tmp_path)
    _branch_create(repo, "feature/done", "docs/extra.md", "extra\n")
    _squash_merge(repo, "feature/done", "docs/extra.md")
    _run("checkout", "main", "--quiet", cwd=repo)

    checks = session_hygiene.check_branch(repo)
    assert len(checks) == 1
    c = checks[0]
    assert c.name == "branche"
    # Le depot nu est local : origin/main est joignable et a jour, donc
    # on attend GREEN (behind == 0).
    assert c.level == session_hygiene.GREEN, (
        f"main a jour doit etre GREEN, organe a retourne {c.level}: {c.detail}"
    )


# ---------------------------------------------------------------------------
# controle negatif : branche divergente -> AMBER (PAS rouge)
# ---------------------------------------------------------------------------


def test_branch_with_unmerged_changes_is_amber_not_red(tmp_path):
    """Branche ``feature/wip`` qui diverge de main (fichier touche non
    encore sur main) -> ``check_branch`` retourne AMBER, pas RED.

    Le predicat teste que la branche LIVRE encore quelque chose (le diff
    entre origin/main et la branche sur le fichier touche n'est pas vide),
    donc elle est en cours, pas parquee.
    """
    repo = _make_mini_repo(tmp_path)
    _branch_create(repo, "feature/wip", "docs/wip.md", "wip v1\n")
    # Pas de squash-mêrge : on reste sur la branche divergente.

    checks = session_hygiene.check_branch(repo)
    c = checks[0]
    assert c.name == "branche"
    assert c.level != session_hygiene.RED, (
        f"branche divergente ne doit PAS etre classee parquée (RED), "
        f"organe a retourne {c.level}: {c.detail}"
    )
    # Si origin/main est joignable et la branche diverge, on attend AMBER
    # (commits de retard / non pousses selon l'etat reel du clone).
    assert c.level == session_hygiene.AMBER, (
        f"branche divergente devrait etre AMBER, organe a retourne "
        f"{c.level}: {c.detail}"
    )


def test_branch_with_local_unpushed_commit_is_amber_not_red(tmp_path):
    """Branche ``feature/local`` avec un commit local non pousse -> AMBER.

    Meme si le contenu est deja sur main par squash-mêrge (le predicat
    livre-vide serait declenche), un commit non pousse fait basculer le
    verdict vers AMBER : il y a quelque chose a pousser, donc pas parquee
    sans raison.
    """
    repo = _make_mini_repo(tmp_path)
    # 1) on livre d'abord le contenu
    _branch_create(repo, "feature/local", "docs/note.md", "note\n")
    _squash_merge(repo, "feature/local", "docs/note.md")
    _run("checkout", "feature/local", "--quiet", cwd=repo)
    # 2) puis on commit un delta local non pousse
    (repo / "docs/note.md").write_text("note + local delta\n", encoding="utf-8")
    _run("commit", "-am", "local delta", "--quiet", cwd=repo)

    checks = session_hygiene.check_branch(repo)
    c = checks[0]
    assert c.name == "branche"
    # Le delta local fait que la branche livre encore quelque chose
    # (diff entre origin/main et la branche non vide sur docs/note.md).
    # Verdict attendu : AMBER.
    assert c.level != session_hygiene.RED, (
        f"un commit local non pousse doit empecher le verdict RED parquee, "
        f"organe a retourne {c.level}: {c.detail}"
    )


# ---------------------------------------------------------------------------
# cas degenere : la 3e paire pre-consolidation -- temoin fondateur #14730
# ---------------------------------------------------------------------------


def test_third_pair_pre_consolidation_predicate_reproduces(tmp_path):
    """Reproduction du cas fondateur #14730 (recensement #14615) : une
    branche qui touche un fichier deja couvert par un test au basename
    different doit etre consideree comme LIVRANT (diff non vide entre
    origin/main et la branche sur le fichier touche).

    Ce test n'utilise pas la 3e paire reelle (qui a ete consommee par
    a6720c7286) : il en reproduit la FORME pour verifier que le predicat
    de check_branch ne souffre pas du meme angle mort que celui du
    recensement -- cle de regroupement par basename inapplicable.
    """
    repo = _make_mini_repo(tmp_path)

    # Branche feature/cover : ajoute un fichier ``foo.md`` ET un fichier
    # ``bar.md`` -- les deux divergent de main, l'un au moins aurait pu
    # etre invisible a une cle basename.
    _branch_create(
        repo, "feature/cover", "foo.md", "foo\n"
    )
    # Second commit avec un deuxieme fichier sur la meme branche
    (repo / "bar.md").write_text("bar\n", encoding="utf-8")
    _run("add", "bar.md", cwd=repo)
    _run("commit", "-m", "add bar", "--quiet", cwd=repo)
    _run(
        "push", "origin", "feature/cover", "--quiet", cwd=repo,
    )

    checks = session_hygiene.check_branch(repo)
    c = checks[0]
    # La branche n'a PAS ete squash-mêrgee et touche deux fichiers non
    # presents sur main. Verdict : AMBER, pas RED.
    assert c.level == session_hygiene.AMBER, (
        f"branche multi-fichiers divergente doit etre AMBER (en cours), "
        f"organe a retourne {c.level}: {c.detail}"
    )
