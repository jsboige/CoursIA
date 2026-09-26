"""Tests pour la justification par body des pertes de navigation (#17727).

L'organe signale `LOST_NAV_LINKS` quand une cible de navigation VIVANTE de la
base disparait de la tete ; depuis l'option (a) du 2026-09-24, un libelle
generique qui survit sur une cible deja pointee en base n'excuse plus la perte.
Le grain #17727 ouvre la porte que le dispositif #13491 ne lisait pas (il ne
connaissait que `TRUNCATED_CELL`) :

  1. marker keye sur le couple (notebook, CIBLE) ;
  2. finding reecrit en `LOST_NAV_LINKS_JUSTIFIED_BY_BODY`, trace preservee ;
  3. justification PARTIELLE : une cible non nommee laisse le finding bloquant ;
  4. un marker sans raison n'est pas valide.

Controles : 1 positif (la forme de #17392, deux cibles « Index » divergentes
fusionnees) + 3 negatifs (marker absent, marker sur une autre cible, marker
sans raison), plus la robustesse (em-dash, chemin prefixe, autre notebook,
backticks, identite normalisee) et les unitaires du parser.
"""
import json
import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import detect_md_content_loss as dml  # noqa: E402


# Notebook a 4 niveaux de profondeur : `../../../../README.md` y resout vers le
# README de la RACINE du depot, donc la cible est VIVANTE a la base -- sans quoi
# la regle (e1) la classerait « reparee » (cible morte) au lieu de perdue. C'est
# exactement la geometrie de #17392.
NB_REL = "A/B/C/D/Lab6-First-Agent.ipynb"

# Prose constante entre base et head : la chute de volume vient des SEULS liens
# de navigation retires (le notebook doit rester au-dessus du seuil de 75 %,
# sans quoi on testerait un TRUNCATED_CELL au lieu du LOST_NAV_LINKS).
PROSE = textwrap.dedent("""\
    ## Lab 6 : premier agent

    Ce laboratoire introduit la boucle d'agent minimale : une consigne, un
    appel d'outil, une observation reinjectee dans le contexte, puis un critere
    d'arret. Le scenario choisit volontairement une tache courte pour que toute
    la trajectoire tienne dans une fenetre de contexte raisonnable et reste
    lisible dans la sortie d'execution.

    Les etudiants implementent d'abord la boucle a la main, puis comparent leur
    version a celle du framework. La comparaison porte sur trois points : le
    nombre d'appels au modele, la robustesse au message d'erreur de l'outil, et
    la maniere dont le contexte est tronque quand la fenetre se remplit.
""").strip()

# Barre de navigation fondatrice (#17392) : deux cibles « Index » divergentes
# (deux README de profondeur differente), plus un lien de suite. Le libelle
# « Index » SURVIT en tete, sur la cible qu'il pointait deja en base -- c'est ce
# qui interdit l'excuse (e2) et rend la perte visible.
NAV_BASE_17392 = (
    "[Index](../../../../README.md) | [Index](../../../README.md) | "
    "[Lab 5](../../../Lab5/Lab5-Reflexion.ipynb)"
)
NAV_HEAD_17392 = "[Index](../../../README.md) | [Lab 5](../../../Lab5/Lab5-Reflexion.ipynb)"

# Variante a DEUX cibles perdues (controle de justification partielle) : la
# seconde cible est un README de docs, vivant a la base, dont le libelle ne
# survit pas du tout en tete.
NAV_BASE_TWO_LOST = (
    "[Index](../../../../README.md) | [Index](../../../README.md) | "
    "[Cours](../../../../docs/README.md) | [Lab 5](../../../Lab5/Lab5-Reflexion.ipynb)"
)
NAV_HEAD_TWO_LOST = "[Index](../../../README.md) | [Lab 5](../../../Lab5/Lab5-Reflexion.ipynb)"

# Fichiers presents a la base pour que les cibles perdues soient VIVANTES.
LIVE_FILES = {"README.md": "# Depot\n", "docs/README.md": "# Docs\n"}


def _md(src, cell_id="mdcell-1"):
    return {"cell_type": "markdown", "source": src, "metadata": {}, "id": cell_id}


def _nb(md_cells):
    return {"cells": list(md_cells), "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _git_commit(repo, rel, content, message):
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")
    subprocess.run(["git", "add", rel], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-q", "-m", message], cwd=repo, check=True)


def _make_repo(tmp_path, base_nav, head_nav, name="repo"):
    """Repo git a deux commits : la barre de navigation base puis head."""
    rp = tmp_path / name
    rp.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=rp, check=True)
    subprocess.run(["git", "config", "user.email", "test@x"], cwd=rp, check=True)
    subprocess.run(["git", "config", "user.name", "test"], cwd=rp, check=True)
    for rel, content in LIVE_FILES.items():
        _git_commit(rp, rel, content, f"base {rel}")
    _git_commit(rp, NB_REL,
                json.dumps(_nb([_md(PROSE + "\n\n" + base_nav)]), ensure_ascii=False),
                "base notebook")
    _git_commit(rp, NB_REL,
                json.dumps(_nb([_md(PROSE + "\n\n" + head_nav)]), ensure_ascii=False),
                "head notebook")
    return rp, rp / NB_REL


def _run(repo, nb_abs, body_file=None, pr_body=None, json_out=False, capsys=None):
    """Invoque dml.main (cwd = repo : le detecteur utilise des refs git relatives).

    Retourne (rc, stdout) -- stdout n'est rempli qu'avec ``json_out`` : le
    verdict machine sert a verifier la TRACE, pas seulement le rc.
    """
    argv = ["--base", "HEAD~1", "--head", "HEAD", "--check",
            str(nb_abs.relative_to(repo))]
    if json_out:
        argv.append("--json")
    if body_file is not None:
        argv += ["--pr-body-file", str(body_file)]
    if pr_body is not None:
        argv += ["--pr-body", pr_body]
    old_cwd = Path.cwd()
    try:
        os.chdir(repo)
        rc = dml.main(argv)
    finally:
        os.chdir(old_cwd)
    return rc, (capsys.readouterr().out if (json_out and capsys) else "")


def _finding(stdout, kind):
    findings = json.loads(stdout)["findings"]
    return next((f for f in findings if f.get("kind") == kind), None)


@pytest.fixture
def repo_17392(tmp_path):
    return _make_repo(tmp_path, NAV_BASE_17392, NAV_HEAD_17392)


@pytest.fixture
def repo_two_lost(tmp_path):
    return _make_repo(tmp_path, NAV_BASE_TWO_LOST, NAV_HEAD_TWO_LOST, name="repo2")


def _body(repo, text):
    f = repo / "pr-body.md"
    f.write_text(text, encoding="utf-8")
    return f


# ---------------------------------------------------------------------------
# 0. Le finding nu : les cibles perdues sont nommees (sans quoi la cle du
#    marker n'existe pas et la porte ne peut pas s'ouvrir).
# ---------------------------------------------------------------------------
class TestLostTargetsExposed:
    def test_finding_carries_lost_targets(self, repo_17392, capsys):
        repo, nb_abs = repo_17392
        rc, out = _run(repo, nb_abs, json_out=True, capsys=capsys,
                       pr_body="# Mon PR\n\nrien a declarer\n")
        assert rc == 1
        f = _finding(out, "LOST_NAV_LINKS")
        assert f is not None, "la perte de cible vivante doit etre signalee"
        assert f["before_count"] == 3 and f["after_count"] == 2, f
        assert f["lost_targets"] == ["../../../../README.md"], f

    def test_surviving_target_is_not_declared_lost(self, repo_17392, capsys):
        repo, nb_abs = repo_17392
        _, out = _run(repo, nb_abs, json_out=True, capsys=capsys,
                      pr_body="# Mon PR\n")
        f = _finding(out, "LOST_NAV_LINKS")
        assert "../../../README.md" not in f["lost_targets"], (
            "la cible qui SURVIT en tete n'est pas une perte : la cle de la "
            "porte est la cible divergente, pas le libelle"
        )


# ---------------------------------------------------------------------------
# 1. Controle positif : la forme de #17392 + marker -> vert, trace preservee.
# ---------------------------------------------------------------------------
class TestNavMarkerPositive:
    def test_marker_on_lost_target_turns_green(self, repo_17392, capsys):
        repo, nb_abs = repo_17392
        body = _body(repo,
                     "md-content-loss: navigation assumee -- "
                     f"{nb_abs.name} target ../../../../README.md : "
                     "les deux Index pointaient deux README concurrents, "
                     "fusion sur le plus proche\n")
        rc, out = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 0, f"un marker valide sur la cible perdue doit rendre vert. rc={rc}"
        f = _finding(out, "LOST_NAV_LINKS_JUSTIFIED_BY_BODY")
        assert f is not None, "la trace doit rester visible en sortie machine"
        assert f["lost_targets"] == ["../../../../README.md"], f
        assert json.loads(out)["stats"]["findings_count"] == 0

    def test_marker_with_em_dash_and_backticked_target(self, repo_17392, capsys):
        repo, nb_abs = repo_17392
        body = _body(repo,
                     "md-content-loss: navigation assumée — "
                     f"{nb_abs.name} target `../../../../README.md` : "
                     "cible retiree volontairement\n")
        rc, _ = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 0, "les backticks autour de la cible sont une decoration, pas la cible"

    def test_marker_with_unormalized_target_identity(self, repo_17392, capsys):
        """La cible se compare en IDENTITE canonique : un `/./` intercale ne
        change pas la cible du lien, donc ne change pas la cle de la porte."""
        repo, nb_abs = repo_17392
        body = _body(repo,
                     "md-content-loss: navigation assumee -- "
                     f"{nb_abs.name} target ./../../../../README.md : cible retiree\n")
        rc, _ = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 0

    def test_marker_with_repo_path_prefix_matches_basename(self, repo_17392, capsys):
        repo, nb_abs = repo_17392
        body = _body(repo,
                     "md-content-loss: navigation assumee -- "
                     f"MyIA.AI.Notebooks/{NB_REL} "
                     "target ../../../../README.md : cible retiree\n")
        rc, _ = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 0

    def test_all_lost_targets_named_turns_green(self, repo_two_lost, capsys):
        repo, nb_abs = repo_two_lost
        body = _body(repo,
                     "md-content-loss: navigation assumee -- "
                     f"{nb_abs.name} target ../../../../README.md : remontee au sommaire\n"
                     "md-content-loss: navigation assumee -- "
                     f"{nb_abs.name} target ../../../../docs/README.md : idem\n")
        rc, out = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 0, "les deux cibles perdues sont nommees -> vert"
        assert _finding(out, "LOST_NAV_LINKS_JUSTIFIED_BY_BODY") is not None


# ---------------------------------------------------------------------------
# 2. Controles negatifs : aucun assouplissement en marche.
# ---------------------------------------------------------------------------
class TestNavMarkerNegative:
    def test_no_marker_keeps_rc_1(self, repo_17392):
        repo, nb_abs = repo_17392
        body = _body(repo, "# Mon PR\n\nAucune justification ici.\n")
        rc, _ = _run(repo, nb_abs, body_file=body)
        assert rc == 1, "pas de marker -> le rouge est inchange"

    def test_marker_on_another_target_keeps_rc_1(self, repo_17392, capsys):
        repo, nb_abs = repo_17392
        body = _body(repo,
                     "md-content-loss: navigation assumee -- "
                     f"{nb_abs.name} target ../../../README.md : "
                     "cette cible a SURVECU, elle n'est pas perdue\n")
        rc, out = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 1, "un marker qui ne nomme pas la cible perdue reste inerte"
        f = _finding(out, "LOST_NAV_LINKS")
        assert f is not None and f["lost_targets"] == ["../../../../README.md"], f

    def test_marker_without_reason_keeps_rc_1(self, repo_17392, capsys):
        repo, nb_abs = repo_17392
        body = _body(repo,
                     "md-content-loss: navigation assumee -- "
                     f"{nb_abs.name} target ../../../../README.md :\n")
        rc, out = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 1, "une raison vide n'est pas un marker valide"
        assert _finding(out, "LOST_NAV_LINKS_JUSTIFIED_BY_BODY") is None

    def test_marker_for_another_notebook_keeps_rc_1(self, repo_17392):
        repo, nb_abs = repo_17392
        body = _body(repo,
                     "md-content-loss: navigation assumee -- Another-Notebook.ipynb "
                     "target ../../../../README.md : pas ce notebook\n")
        rc, _ = _run(repo, nb_abs, body_file=body, json_out=True, capsys=None)
        assert rc == 1

    def test_partial_justification_stays_red_for_remaining(self, repo_two_lost, capsys):
        """Cible 3 du grain : une seule des deux cibles perdues est nommee.

        Le finding reste BLOQUANT et se reduit aux cibles restantes ; la cible
        couverte reste visible dans la trace (justified_targets)."""
        repo, nb_abs = repo_two_lost
        body = _body(repo,
                     "md-content-loss: navigation assumee -- "
                     f"{nb_abs.name} target ../../../../docs/README.md : "
                     "seule celle-la est assumee\n")
        rc, out = _run(repo, nb_abs, body_file=body, json_out=True, capsys=capsys)
        assert rc == 1, "une cible non nommee doit laisser le finding bloquant"
        f = _finding(out, "LOST_NAV_LINKS")
        assert f is not None, "le finding partiellement justifie garde son kind bloquant"
        assert f["lost_targets"] == ["../../../../README.md"], f
        assert f["justified_targets"] == ["../../../../docs/README.md"], f
        assert f["delta"] == 1, "le delta est re-ancre sur les cibles restantes"

    def test_empty_body_keeps_default_behavior(self, repo_17392):
        repo, nb_abs = repo_17392
        body = _body(repo, "")
        rc, _ = _run(repo, nb_abs, body_file=body)
        assert rc == 1


# ---------------------------------------------------------------------------
# 3. Unitaires : le parser et le fail-closed.
# ---------------------------------------------------------------------------
class TestNavMarkerParsing:
    NB = Path(NB_REL)

    def test_valid_marker_yields_target(self):
        body = ("md-content-loss: navigation assumee -- "
                f"{self.NB.name} target ../../../README.md : raison\n")
        assert dml._parse_pr_body_nav_markers(body, self.NB) == {"../../../README.md"}

    def test_full_path_notebook_token(self):
        # NB_REL (str, slashes avant) et non f"{self.NB}" : sous Windows, la
        # forme Path rend des antislashs, que le marker — ecrit par un agent sur
        # la CI Linux — n'emploie pas.
        body = ("md-content-loss: navigation assumee -- "
                f"{NB_REL} target a/b.ipynb : raison\n")
        assert dml._parse_pr_body_nav_markers(body, self.NB) == {"a/b.ipynb"}

    def test_reason_required(self):
        body = ("md-content-loss: navigation assumee -- "
                f"{self.NB.name} target ../../../README.md :   \n")
        assert dml._parse_pr_body_nav_markers(body, self.NB) == set()

    def test_other_notebook_ignored(self):
        body = ("md-content-loss: navigation assumee -- Other.ipynb "
                "target ../../../README.md : raison\n")
        assert dml._parse_pr_body_nav_markers(body, self.NB) == set()

    def test_empty_body(self):
        assert dml._parse_pr_body_nav_markers("", self.NB) == set()

    def test_cell_marker_is_not_read_as_nav_marker(self):
        """Les deux formats sont etanches : une porte qui lirait l'autre format
        excuserait un finding que personne n'a declare."""
        body = ("md-content-loss: reecriture assumee -- "
                f"{self.NB.name} cell 3 : raison\n")
        assert dml._parse_pr_body_nav_markers(body, self.NB) == set()

    def test_nav_marker_is_not_read_as_cell_marker(self):
        body = ("md-content-loss: navigation assumee -- "
                f"{self.NB.name} target ../../../README.md : raison\n")
        assert dml._parse_pr_body_markers(body, self.NB) == set()

    def test_finding_without_targets_is_never_justified(self):
        """Fail-closed : un finding sans `lost_targets` n'a pas de cle, donc
        aucune porte ne peut s'ouvrir dessus."""
        findings = [{"kind": "LOST_NAV_LINKS", "motif": "nav_links",
                     "before_count": 3, "after_count": 2, "delta": 1}]
        out = dml._apply_body_justifications(findings, set(), {"../../../README.md"})
        assert out == findings

    def test_cell_justification_leaves_nav_finding_untouched(self):
        findings = [{"kind": "LOST_NAV_LINKS", "lost_targets": ["a.ipynb"],
                     "delta": 1, "before_count": 2, "after_count": 1}]
        out = dml._apply_body_justifications(findings, {3}, set())
        assert out == findings