"""Tests de la resolution des renommages (#26883) — les 6 organes porteurs.

Defaut mesure sur la tete de #26381 (pur renommage CamelCase : 44 renommages,
dont 32 R100) : ``changed_notebooks`` ne rend que le chemin de TETE d'un
carnet renomme, et la base lue a ce chemin rend ``None``. Chaque organe
reagissait alors a un renommage comme a un carnet NEUF :

* ``check_uncommented_code`` : ``changed_keys(None, head)`` rend ``None`` ->
  le carnet juge entier -> 8 carnets / 18 cellules PREEXISTANTES signalees ->
  faux ROUGE bloquant (l'incident qui a fonde #26883) ;
* les quatre cliquets (``check_output_failure_text``, ``check_output_flood``,
  ``check_output_collapse``, ``check_source_collapse``) : ``added=True`` ->
  ligne advisory ET exemption de gate -> un renommage qui degrade passait
  vert (faux vert) ;
* ``detect_svg_html_only`` : toutes les occurrences du stock comptaient
  comme ajouts.

La reparation : ``renamed_notebooks`` (``git diff -M --name-status
--diff-filter=R``) + lecture de la base a l'ANCIEN chemin. Les tests
construisent de vrais petits depots git (``tmp_path``) et passent par les
``main`` des organes : le cablage du main compte autant que la fonction,
c'est lui que la CI execute.

Les trois cas exigés par le dispatch, par organe :

1. **pur renommage** (contenu identique, R100) -> silencieux ;
2. **renommage + defaut propre a l'organe** -> SEUL ce defaut est signale,
   avec ``new_notebook``/``added`` a False (le carnet a une base) ;
3. **pur ajout** -> comportement « carnet neuf » INCHANGE (jamais gate,
   sauf l'organe uncommented qui juge un carnet neuf entier -- c'est son
   contrat).

Plus deux controles retro ("sans resolution, le defaut revient") qui
documentent ce que le monde d'avant rendait, et un test unitaire du
parseur ``renamed_notebooks``.
"""
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_output_collapse as out_collapse
import check_output_failure_text as failure_text
import check_output_flood as flood
import check_source_collapse as src_collapse
import check_uncommented_code as uncommented
import detect_svg_html_only as svg


# ---------------------------------------------------------------------------
# Attelage : petits depots git reels dans tmp_path.
# ---------------------------------------------------------------------------

def _git(repo: Path, *args: str) -> str:
    """git -C repo ... echouant BRUYAMMENT (un fixture muet fabrique des
    faux verdicts verts)."""
    proc = subprocess.run(
        ["git", "-C", str(repo),
         "-c", "user.email=t@example.org", "-c", "user.name=T",
         "-c", "core.autocrlf=false", *args],
        capture_output=True, text=True, encoding="utf-8", check=False)
    if proc.returncode != 0:
        raise AssertionError(f"git {args} -> rc={proc.returncode}: "
                             f"{proc.stderr.strip()}")
    return proc.stdout


def _dump(nb: dict) -> str:
    """JSON multi-lignes, comme nbformat (indent=1) : la detection de
    renommage git est LIGNEE -- un carnet mono-ligne n'est jamais rapproche
    des qu'une ligne change (A/D au lieu de R0xx), et les carnets reels du
    depot sont pretty-printes."""
    return json.dumps(nb, ensure_ascii=False, indent=1)


def _commit_nb(repo: Path, rel: str, nb: dict, msg: str) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_dump(nb), encoding="utf-8", newline="\n")
    _git(repo, "add", rel)
    _git(repo, "commit", "-q", "-m", msg)


def _cell(cid: str, *lines: str, outputs: list | None = None) -> dict:
    return {"cell_type": "code", "id": cid,
            "source": [line + "\n" for line in lines], "metadata": {},
            "execution_count": 1, "outputs": outputs or []}


def _stream(*lines: str) -> list[dict]:
    return [{"output_type": "stream", "name": "stdout",
             "text": [line + "\n" for line in lines]}]


def _display_html(payload: str) -> list[dict]:
    return [{"output_type": "display_data",
             "data": {"text/html": [payload]}, "metadata": {}}]


def _nb(*cells: dict) -> dict:
    return {"cells": list(cells),
            "metadata": {"kernelspec": {"language": "python",
                                        "name": "python3"}},
            "nbformat": 4, "nbformat_minor": 5}


def _pad(n: int = 300) -> dict:
    """Cellule markdown de remplissage, IDENTIQUE base et tete : la detection
    de renommage git est ligneE et exige > 50 % de lignes communes -- une
    edition massive (60 objets ajoutes, 6000 caracteres retires) ferait
    basculer le renommage en A/D. Le remplissage est markdown : aucun organe
    de la famille ne juge les cellules non-code."""
    return {"cell_type": "markdown", "id": "pad",
            "source": [f"Ligne de contexte pedagogique numero {i}, stable.\n"
                       for i in range(n)],
            "metadata": {}}


#: 11 lignes de code sans commentaire (meme corps que le module de tests de
#: l'organe) -- le defaut que check_uncommented_code doit attraper.
BODY_12 = (
    "def cout_total(commandes, prix, taxes):",
    "    total = 0.0",
    "    for commande in commandes:",
    "        ligne = commande['quantite'] * prix[commande['article']]",
    "        total = total + ligne",
    "    total = total * (1.0 + taxes)",
    "    return round(total, 2)",
    "",
    "resultat = cout_total(commandes, prix, 0.2)",
    "assert resultat > 0",
    "print(resultat)",
    "print(cout_total([], prix, 0.2))",
)


def _repo(tmp_path, monkeypatch) -> Path:
    """Depot neuf, cwd = depot : les main() des organes lisent le cwd."""
    _git(tmp_path, "init", "-q")
    monkeypatch.chdir(tmp_path)
    return tmp_path


def _repo_pure_rename(tmp_path, monkeypatch, base_nb: dict) -> Path:
    """old.ipynb a BASE, renomme R100 en new.ipynb a HEAD, contenu identique."""
    repo = _repo(tmp_path, monkeypatch)
    _commit_nb(repo, "old.ipynb", base_nb, "base")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    _git(repo, "commit", "-q", "-m", "renomme")
    return repo


def _repo_rename_edit(tmp_path, monkeypatch, base_nb: dict,
                      head_nb: dict) -> Path:
    """old.ipynb a BASE, renomme ET edite (R0xx) en new.ipynb a HEAD, dans
    le MEME commit -- diff base..HEAD = un renommage avec edition, la forme
    R0xx que la resolution doit mapper."""
    repo = _repo(tmp_path, monkeypatch)
    _commit_nb(repo, "old.ipynb", base_nb, "base")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    (repo / "new.ipynb").write_text(_dump(head_nb), encoding="utf-8",
                                    newline="\n")
    _git(repo, "add", "new.ipynb")
    _git(repo, "commit", "-q", "-m", "renomme et edite")
    return repo


def _repo_pure_add(tmp_path, monkeypatch, base_nb: dict,
                   added_nb: dict) -> Path:
    """old.ipynb sain a BASE ; brandnew.ipynb ajoute a HEAD (aucun renommage)."""
    repo = _repo(tmp_path, monkeypatch)
    _commit_nb(repo, "old.ipynb", base_nb, "base")
    _commit_nb(repo, "brandnew.ipynb", added_nb, "ajoute")
    return repo


def _run_json(capsys) -> dict:
    return json.loads(capsys.readouterr().out)


# ---------------------------------------------------------------------------
# 1. Le parseur renamed_notebooks (unitaire, sur un vrai depot).
# ---------------------------------------------------------------------------

def test_renamed_notebooks_mappe_tete_vers_base(tmp_path, monkeypatch):
    repo = _repo_pure_rename(tmp_path, monkeypatch,
                             _nb(_cell("c1", "x = 1")))
    assert failure_text.renamed_notebooks("HEAD~1", cwd=str(repo)) == {
        "new.ipynb": "old.ipynb"}


def test_renamed_notebooks_renomme_et_edite_reste_mappe(tmp_path, monkeypatch):
    repo = _repo_rename_edit(
        tmp_path, monkeypatch,
        _nb(_cell("c1", "x = 1")),
        _nb(_cell("c1", "x = 2")))
    # R0xx : le contenu a change pendant le renommage, l'ANCIEN chemin reste
    # la base -- c'est lui qu'on cherche, pas la qualite du rapprochement.
    assert failure_text.renamed_notebooks("HEAD~1", cwd=str(repo)) == {
        "new.ipynb": "old.ipynb"}


def test_renamed_notebooks_copie_et_non_carnet_exclus(tmp_path, monkeypatch):
    repo = _repo(tmp_path, monkeypatch)
    _commit_nb(repo, "old.ipynb", _nb(_cell("c1", "x = 1")), "base")
    _git(repo, "mv", "old.ipynb", "new.ipynb")
    # Copie non byte-identique (une byte-identique rend le rapprochement
    # source->cible ambigu entre copie.ipynb et new.ipynb).
    (repo / "copie.ipynb").write_text(
        _dump(_nb(_cell("c1", "x = 2"))), encoding="utf-8", newline="\n")
    (repo / "outil.py").write_text("x = 1\n", encoding="utf-8", newline="\n")
    _git(repo, "add", "copie.ipynb", "outil.py")
    _git(repo, "commit", "-q", "-m", "renomme, copie, touche un py")
    renames = failure_text.renamed_notebooks("HEAD~1", cwd=str(repo))
    # Une COPIE garde sa source vivante a la tete : c'est un vrai ajout.
    # Un .py n'est pas un carnet livre.
    assert renames == {"new.ipynb": "old.ipynb"}


# ---------------------------------------------------------------------------
# 2. check_uncommented_code — le faux ROUGE bloquant de #26381.
# ---------------------------------------------------------------------------

def test_uncommented_pur_renommage_silencieux(tmp_path, monkeypatch, capsys):
    # Le shape EXACT de #26381 : du code preexistant NON COMMENTE (un defaut
    # pour l'organe), ne change que le chemin. Le carnet a une base : seules
    # les cellules CHANGEES seraient jugees -- il n'y en a aucune.
    base = _nb(_cell("c1", *BODY_12))
    _repo_pure_rename(tmp_path, monkeypatch, base)
    rc = uncommented.main(["--diff", "HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 0
    assert payload["flagged_cells"] == 0


def test_uncommented_renomme_et_decommente_signale_cette_cellule(
        tmp_path, monkeypatch, capsys):
    base = _nb(_cell("c1", "# Cout total, taxes incluses.", *BODY_12))
    head = _nb(_cell("c1", *BODY_12))
    _repo_rename_edit(tmp_path, monkeypatch, base, head)
    rc = uncommented.main(["--diff", "HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 1
    assert payload["flagged_cells"] == 1
    row = payload["rows"][0]
    assert row["notebook"] == "new.ipynb"
    # Le carnet RENOMME a une base : il n'est pas juge comme neuf.
    assert row["new_notebook"] is False


def test_uncommented_carnet_neuf_juge_entier(tmp_path, monkeypatch, capsys):
    sain = _nb(_cell("c1", "# explique", *BODY_12))
    neuf = _nb(_cell("c1", *BODY_12))
    _repo_pure_add(tmp_path, monkeypatch, sain, neuf)
    rc = uncommented.main(["--diff", "HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 1
    row = payload["rows"][0]
    assert row["notebook"] == "brandnew.ipynb"
    assert row["new_notebook"] is True


def test_uncommented_sans_resolution_le_defaut_revient(
        tmp_path, monkeypatch):
    """Controle retro : sur le meme depot, compare() SANS renames reproduit
    le faux rouge de #26381 -- c'est la preuve que les tests ci-dessus
    mordent bien la reparation."""
    base = _nb(_cell("c1", *BODY_12))
    repo = _repo_pure_rename(tmp_path, monkeypatch, base)
    paths = failure_text.changed_notebooks("HEAD~1", cwd=str(repo))
    rows = uncommented.compare("HEAD~1", paths, cwd=str(repo))
    assert rows and rows[0]["new_notebook"] is True


# ---------------------------------------------------------------------------
# 3. check_output_failure_text — TOOL_FAILURE exonere par le renommage.
# ---------------------------------------------------------------------------

def _ft_sain() -> dict:
    return _nb(_cell("c1", "print('ok')", outputs=_stream("ok")))


def _ft_degrade() -> dict:
    return _nb(_cell("c1", "print('ok')",
                     outputs=_stream("bash: foo: command not found")))


def test_failure_text_pur_renommage_silencieux(tmp_path, monkeypatch, capsys):
    _repo_pure_rename(tmp_path, monkeypatch, _ft_sain())
    rc = failure_text.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 0
    row = payload["rows"][0]
    assert row["added"] is False
    assert row["regressed"] is False


def test_failure_text_renomme_et_banner_signale(tmp_path, monkeypatch, capsys):
    _repo_rename_edit(tmp_path, monkeypatch, _ft_sain(), _ft_degrade())
    rc = failure_text.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 1
    row = payload["rows"][0]
    assert row["added"] is False
    assert row["classes"]["TOOL_FAILURE"]["delta"] == 1
    assert row["regressed"] is True


def test_failure_text_carnet_neuf_rest_advisory(tmp_path, monkeypatch, capsys):
    _repo_pure_add(tmp_path, monkeypatch, _ft_sain(), _ft_degrade())
    rc = failure_text.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    row = payload["rows"][0]
    assert row["notebook"] == "brandnew.ipynb"
    assert row["added"] is True
    # Contrat inchange : un carnet neuf est advisory, jamais gate.
    assert row["regressed"] is False
    assert rc == 0


def test_failure_text_sans_resolution_le_renommage_pour_neuf(
        tmp_path, monkeypatch):
    repo = _repo_pure_rename(tmp_path, monkeypatch, _ft_sain())
    paths = failure_text.changed_notebooks("HEAD~1", cwd=str(repo))
    rows = failure_text.compare("HEAD~1", None, paths, cwd=str(repo))
    assert rows[0]["added"] is True


# ---------------------------------------------------------------------------
# 4. check_output_flood — croissance exoneree par le renommage.
# ---------------------------------------------------------------------------

def _fl_base() -> dict:
    return _nb(_cell("c1", "print('ok')", outputs=_stream(*["ok"] * 5)),
               _pad())


def _fl_flooded() -> dict:
    # Flood compte des OBJETS de sortie, pas des lignes : 60 objets separes
    # contre 5 a la base franchissent CELL_CAP.
    outputs = [{"output_type": "stream", "name": "stdout",
                "text": [f"ligne {i}\n"]} for i in range(60)]
    return _nb(_cell("c1", "print('ok')", outputs=outputs), _pad())


def test_flood_pur_renommage_silencieux(tmp_path, monkeypatch, capsys):
    _repo_pure_rename(tmp_path, monkeypatch, _fl_base())
    rc = flood.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 0
    assert payload["rows"][0]["added"] is False


def test_flood_renomme_et_grossi_signale(tmp_path, monkeypatch, capsys):
    _repo_rename_edit(tmp_path, monkeypatch, _fl_base(), _fl_flooded())
    rc = flood.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 1
    row = payload["rows"][0]
    assert row["added"] is False
    assert row["cells"][0]["kind"] == "grew"
    assert row["regressed"] is True


def test_flood_carnet_neuf_rest_advisory(tmp_path, monkeypatch, capsys):
    _repo_pure_add(tmp_path, monkeypatch, _fl_base(), _fl_flooded())
    rc = flood.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    row = payload["rows"][0]
    assert row["added"] is True
    assert row["regressed"] is False
    assert rc == 0


# ---------------------------------------------------------------------------
# 5. check_output_collapse — effondrement de sortie exonerre par renommage.
# ---------------------------------------------------------------------------

def _oc_base() -> dict:
    return _nb(_cell("c1", "print('tab')",
                     outputs=_stream("x" * 6000)), _pad())


def _oc_vide() -> dict:
    return _nb(_cell("c1", "print('tab')", outputs=[]), _pad())


def test_output_collapse_pur_renommage_silencieux(tmp_path, monkeypatch,
                                                  capsys):
    _repo_pure_rename(tmp_path, monkeypatch, _oc_base())
    rc = out_collapse.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 0
    assert payload["rows"][0]["added"] is False


def test_output_collapse_renomme_et_vide_signale(tmp_path, monkeypatch,
                                                 capsys):
    _repo_rename_edit(tmp_path, monkeypatch, _oc_base(), _oc_vide())
    rc = out_collapse.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 1
    row = payload["rows"][0]
    assert row["added"] is False
    assert row["cells"][0]["kind"] == "magnitude"
    assert row["regressed"] is True


def test_output_collapse_carnet_neuf_rest_advisory(tmp_path, monkeypatch,
                                                   capsys):
    _repo_pure_add(tmp_path, monkeypatch, _oc_base(), _oc_vide())
    rc = out_collapse.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert payload["rows"][0]["added"] is True
    assert rc == 0


# ---------------------------------------------------------------------------
# 6. check_source_collapse — source videe pendant le renommage.
# ---------------------------------------------------------------------------

def _sc_base() -> dict:
    return _nb(_cell("c1", "x = 1", "print(x)",
                     outputs=_stream("1")))


def _sc_videe() -> dict:
    # Source reduite a un commentaire seul (0 instructions Python mesurees),
    # sortie conservee : le signal STRUCTURE #16110. Une source VIDE rend
    # ``_python_statements`` a None (« pas de verdict »), pas 0 -- ce n'est
    # pas la forme que l'organe juge.
    return _nb(_cell("c1", "# vidage pendant le renommage",
                     outputs=_stream("1")))


def test_source_collapse_pur_renommage_silencieux(tmp_path, monkeypatch,
                                                  capsys):
    _repo_pure_rename(tmp_path, monkeypatch, _sc_base())
    rc = src_collapse.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 0
    assert payload["rows"][0]["added"] is False


def test_source_collapse_renomme_et_videe_signale(tmp_path, monkeypatch,
                                                  capsys):
    _repo_rename_edit(tmp_path, monkeypatch, _sc_base(), _sc_videe())
    rc = src_collapse.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 1
    row = payload["rows"][0]
    assert row["added"] is False
    assert row["cells"][0]["kind"] == "structure"
    assert row["regressed"] is True


def test_source_collapse_carnet_neuf_rest_advisory(tmp_path, monkeypatch,
                                                   capsys):
    _repo_pure_add(tmp_path, monkeypatch, _sc_base(), _sc_videe())
    rc = src_collapse.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert payload["rows"][0]["added"] is True
    assert rc == 0


# ---------------------------------------------------------------------------
# 7. detect_svg_html_only — le stock compte comme ajouts.
# ---------------------------------------------------------------------------

_SVG_A = "<svg width='10'><path d='M0 0'/></svg>"
_SVG_B = "<svg width='20'><rect width='10'/></svg>"


def _svg_base() -> dict:
    return _nb(_cell("c1", "display(html)",
                     outputs=_display_html(_SVG_A)))


def _svg_avec_occurrence_neuve() -> dict:
    return _nb(_cell("c1", "display(html)", outputs=_display_html(_SVG_A)),
               _cell("c2", "display(html)", outputs=_display_html(_SVG_B)))


def test_svg_pur_renommage_aucun_ajout(tmp_path, monkeypatch, capsys):
    _repo_pure_rename(tmp_path, monkeypatch, _svg_base())
    rc = svg.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 0
    assert payload["added_total"] == 0
    assert payload["notebooks_flagged"] == 0


def test_svg_renomme_et_occurrence_neuve_seule_compte(
        tmp_path, monkeypatch, capsys):
    _repo_rename_edit(tmp_path, monkeypatch, _svg_base(),
                      _svg_avec_occurrence_neuve())
    rc = svg.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    # L'occurrence PREEXISTENTE (c1, meme sha) est du stock, pas un ajout :
    # seule la nouvelle cellule c2 compte.
    assert rc == 1
    assert payload["added_total"] == 1
    assert payload["rows"][0]["added"][0]["cell_id"] == "c2"


def test_svg_carnet_neuf_compte_entier(tmp_path, monkeypatch, capsys):
    _repo_pure_add(tmp_path, monkeypatch, _svg_base(),
                   _svg_avec_occurrence_neuve())
    rc = svg.main(["HEAD~1", "--json"])
    payload = _run_json(capsys)
    assert rc == 1
    assert payload["added_total"] == 2
    assert payload["rows"][0]["notebook"] == "brandnew.ipynb"
