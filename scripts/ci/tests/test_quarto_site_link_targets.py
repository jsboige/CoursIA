"""Tests de `quarto_site_link_targets` (#10921, sous-grain garde/series).

Contrat verifie ici, dans cet ordre :

1. **controle positif** : chaque classe de decision rend la reecriture
   attendue -- repertoire avec README.html rendu (reecriture RELATIVE),
   repertoire du depot sans rendu (URL tree), fichier du depot hors
   render-list (URL blob) ;
2. **intacts** : cible servable, .ipynb (forme de reference), URL absolue,
   ancre, cible absente du depot ET du site -- jamais masquees ;
3. **regression du 2026-11-10** : un repertoire PRESENT dans _site/ n'est
   pas servable (Pages sert des fichiers) -- un lien de repertoire dont le
   dossier existe cote _site doit quand meme partir en README.html ;
4. **idempotence** : une seconde passe ne reecrit rien ;
5. **CLI** : --check rend rc 1 tant que des reecritures sont dues, 0 apres
   application, 2 si _site/ est introuvable ;
6. **href relatifs cross-serie** : la cible se calcule depuis le dossier de
   la page source (``../GenAI/Audio/`` depuis Search/) ;
7. **cible cachee** : une cible cachee (``.claude/``, ``.github/``,
   ``.env.example``) copiee dans _site/ par Quarto n'est PAS servable --
   l'artefact Pages exclut les fichiers caches -- elle part en blob/main
   (fichier) ou tree/main (repertoire).
"""
import importlib.util
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "quarto_site_link_targets",
    Path(__file__).resolve().parents[1] / "quarto_site_link_targets.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)


def _tree(tmp_path):
    """Fixture minimale mirrorant les deux familles mesurees sur le site.

    Rendu (_site/) : GenAI/README.html, GenAI/Audio/README.html,
    Search/README.html, Search/Part1-Foundations/README.html, plus un
    fichier non-lien (le dossier GenAI/Audio existe donc dans _site SANS
    qu'un href ``Audio/`` soit servable -- cf regression point 3).
    Depot : les README sources + Part2-CSP/ (sans rendu) +
    .claude/rules/x.md (hors render-list).
    """
    site = tmp_path / "_site"
    for rel in (
        "MyIA.AI.Notebooks/GenAI/README.html",
        "MyIA.AI.Notebooks/GenAI/Audio/README.html",
        "MyIA.AI.Notebooks/Search/README.html",
        "MyIA.AI.Notebooks/Search/Part1-Foundations/README.html",
    ):
        p = site / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("<html></html>", encoding="utf-8")
    (tmp_path / "MyIA.AI.Notebooks/Search/Part2-CSP").mkdir(parents=True)
    x = tmp_path / ".claude/rules/x.md"
    x.parent.mkdir(parents=True)
    x.write_text("regle", encoding="utf-8")
    return site


def _write(site, rel, hrefs):
    p = site / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    body = "".join(f'<a href="{h}">x</a>' for h in hrefs)
    p.write_text(f"<html>{body}</html>", encoding="utf-8")


def test_positive_control_each_decision_class(tmp_path):
    site = _tree(tmp_path)
    _write(site, "MyIA.AI.Notebooks/GenAI/README.html", [
        "Audio/",                                  # dir rendu -> relatif
        "../../.claude/rules/x.md",                # fichier depot -> blob
        "Audio/deja-servable.html",                # existe dans _site -> intact
        "Audio/01-Introduction.ipynb",             # forme de reference -> intact
        "https://github.com/jsboige/CoursIA",      # absolue -> intact
        "#ancre",                                  # ancre -> intact
        "Nope/",                                   # absent partout -> intact
    ])
    (site / "MyIA.AI.Notebooks/GenAI/Audio/deja-servable.html").write_text(
        "<html></html>", encoding="utf-8")
    _write(site, "MyIA.AI.Notebooks/Search/README.html", [
        "Part2-CSP/",                              # dir depot sans rendu -> tree
        "../GenAI/Audio/",                         # dir rendu, cross-serie -> relatif
    ])

    changes = {}
    for rel in ("MyIA.AI.Notebooks/GenAI/README.html",
                "MyIA.AI.Notebooks/Search/README.html"):
        n, page = mod.process_html(
            site / rel, site, tmp_path, apply=False)
        changes[rel] = {c.split(" -> ")[0]: c.split(" -> ")[1] for c in page}

    genai = changes["MyIA.AI.Notebooks/GenAI/README.html"]
    assert genai["Audio/"] == "Audio/README.html"
    assert genai["../../.claude/rules/x.md"] == (
        "https://github.com/jsboige/CoursIA/blob/main/.claude/rules/x.md")
    assert "Audio/deja-servable.html" not in genai
    assert "Audio/01-Introduction.ipynb" not in genai
    assert "https://github.com/jsboige/CoursIA" not in genai
    assert "#ancre" not in genai
    assert "Nope/" not in genai

    search = changes["MyIA.AI.Notebooks/Search/README.html"]
    assert search["Part2-CSP/"] == (
        "https://github.com/jsboige/CoursIA/tree/main/"
        "MyIA.AI.Notebooks/Search/Part2-CSP")
    assert search["../GenAI/Audio/"] == "../GenAI/Audio/README.html"


def test_regression_dir_in_site_tree_is_not_servable(tmp_path):
    """Le dossier GenAI/Audio EXISTE dans _site (son README y est rendu) :
    un href ``Audio/`` n'est pas moins casse pour autant -- Pages ne sert
    pas d'index de repertoire. La reecriture doit partir en README.html."""
    site = _tree(tmp_path)
    _write(site, "MyIA.AI.Notebooks/GenAI/README.html", ["Audio/"])
    n, page = mod.process_html(
        site / "MyIA.AI.Notebooks/GenAI/README.html",
        site, tmp_path, apply=False)
    assert n == 1
    assert page[0].endswith("Audio/ -> Audio/README.html")


def test_regression_dir_href_with_fragment_is_still_a_dir(tmp_path):
    """Un href ancre ``Audio/#creer`` reste un lien de REPERTOIRE : le test
    doit s'entendre sur le chemin epice de son fragment (un rstrip("#") sur
    une chaine finissant par "creer" ne detectait rien), et le fragment se
    reconduit sur la cible -- le perdre casserait la navigation."""
    site = _tree(tmp_path)
    _write(site, "MyIA.AI.Notebooks/GenAI/README.html", ["Audio/#creer"])
    n, page = mod.process_html(
        site / "MyIA.AI.Notebooks/GenAI/README.html",
        site, tmp_path, apply=False)
    assert n == 1
    assert page[0].endswith("Audio/#creer -> Audio/README.html#creer")


def test_hidden_target_copied_in_site_is_not_servable(tmp_path):
    """Regression du 2026-11-11 : Quarto copie dans ``_site/`` les fichiers
    locaux lies depuis les README rendus -- y compris les chemins caches
    (``.claude/``, ``.github/``, ``.env.example``). Or l'artefact Pages
    exclut les fichiers caches (``upload-artifact@v4``,
    ``include-hidden-files: false``) : une cible cachee n'est jamais
    servable et part en ``blob/main``, comme tout fichier du depot hors
    render-list."""
    site = _tree(tmp_path)
    copied = site / ".claude/rules/x.md"
    copied.parent.mkdir(parents=True, exist_ok=True)
    copied.write_text("regle", encoding="utf-8")
    # la cible existe dans le depot ET dans _site/ (copie Quarto)
    repo_env = tmp_path / "MyIA.AI.Notebooks/GenAI/.env.example"
    repo_env.parent.mkdir(parents=True, exist_ok=True)
    repo_env.write_text("X=1", encoding="utf-8")
    (site / "MyIA.AI.Notebooks/GenAI/.env.example").write_text(
        "X=1", encoding="utf-8")
    _write(site, "MyIA.AI.Notebooks/GenAI/README.html", [
        "../../.claude/rules/x.md",
        ".env.example",
    ])
    n, page = mod.process_html(
        site / "MyIA.AI.Notebooks/GenAI/README.html",
        site, tmp_path, apply=False)
    assert n == 2
    changes = {c.split(" -> ")[0]: c.split(" -> ")[1] for c in page}
    assert changes["../../.claude/rules/x.md"] == (
        "https://github.com/jsboige/CoursIA/blob/main/.claude/rules/x.md")
    assert changes[".env.example"] == (
        "https://github.com/jsboige/CoursIA/blob/main/"
        "MyIA.AI.Notebooks/GenAI/.env.example")


def test_hidden_directory_with_rendered_readme_is_not_servable(tmp_path):
    """Meme raison pour un repertoire cache : meme copie Quarto dans
    ``_site/``, meme exclusion de l'artefact -- la cible part en
    ``tree/main`` (le repertoire n'a pas de page servable)."""
    site = _tree(tmp_path)
    readme = site / ".claude/rules/README.html"
    readme.parent.mkdir(parents=True, exist_ok=True)
    readme.write_text("<html></html>", encoding="utf-8")
    _write(site, "MyIA.AI.Notebooks/GenAI/README.html", ["../../.claude/rules/"])
    n, page = mod.process_html(
        site / "MyIA.AI.Notebooks/GenAI/README.html",
        site, tmp_path, apply=False)
    assert n == 1
    assert page[0].endswith(
        "https://github.com/jsboige/CoursIA/tree/main/.claude/rules")


def test_idempotence_second_pass_rewrites_nothing(tmp_path):
    site = _tree(tmp_path)
    _write(site, "MyIA.AI.Notebooks/Search/README.html",
           ["Part2-CSP/", "../GenAI/Audio/"])
    n1, _ = mod.process_html(
        site / "MyIA.AI.Notebooks/Search/README.html",
        site, tmp_path, apply=True)
    assert n1 == 2
    n2, page2 = mod.process_html(
        site / "MyIA.AI.Notebooks/Search/README.html",
        site, tmp_path, apply=False)
    assert n2 == 0 and not page2


def test_cli_check_then_apply_then_clean(tmp_path, capsys, monkeypatch):
    site = _tree(tmp_path)
    _write(site, "MyIA.AI.Notebooks/GenAI/README.html", ["Audio/"])
    common = ["--site-dir", str(site), "--repo-root", str(tmp_path)]
    monkeypatch.setattr(sys, "argv", [mod.__name__, *common, "--check"])
    assert mod.main() == 1
    assert "1 reecriture(s) DUES" in capsys.readouterr().out
    monkeypatch.setattr(sys, "argv", [mod.__name__, *common])
    assert mod.main() == 0
    assert "1 reecriture(s) APPLIQUEES" in capsys.readouterr().out
    monkeypatch.setattr(sys, "argv", [mod.__name__, *common, "--check"])
    assert mod.main() == 0


def test_cli_instrument_broken_missing_site(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(sys, "argv", [
        mod.__name__, "--site-dir", str(tmp_path / "absent"),
        "--repo-root", str(tmp_path)])
    assert mod.main() == 2
    assert "introuvable" in capsys.readouterr().out
