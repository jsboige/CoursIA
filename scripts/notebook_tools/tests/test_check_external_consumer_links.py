"""Tests for scripts/notebook_tools/check_external_consumer_links.py.

Pourquoi ce fichier de tests existe
-----------------------------------
La surface « referents hors depot » etait la seule du tableau de
`notebook-accretion-numbering` sans organe : les liens absolus
`github.com/jsboige/CoursIA/blob/main/...` poses par un depot consommateur
externe (premier cas connu : `jsboigeEPF/2026-MSMIN5IN52-GenAI`,
`docs/CATALOGUE.md`, #15289) cassent en silence lors d'un renommage. Les tests
pinned ici couvrent l'extraction des cinq formes d'URL, le classement contre
un arbre (ok / moved / missing / pinned), les deux voies de relocalisation
(registre avec chaines et cycles, basename unique), la reecriture `--apply`
(orthogonalite moved/missing/pinned, fins de ligne CRLF, style
d'encodage pourcent, idempotence), les codes de sortie, et un integre sur un
vrai depot git temporaire.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_external_consumer_links as organ  # noqa: E402

BASE = "https://github.com/jsboige/CoursIA/blob/main/"
TREE_FILES = {
    "MyIA.AI.Notebooks/GenAI/Texte/01-Intro.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-Voix/04-7-TTS-Voice-Benchmark.ipynb",
    "Other/Series/Rapport.ipynb",
    "Rapport.ipynb",
    "new/dossier/a.ipynb",
}
TREE_DIRS = organ.dirs_of(TREE_FILES)


def links_of(text: str, **kw) -> list[organ.Link]:
    return organ.extract_links(text, **kw)


def one_link(text: str, **kw) -> organ.Link:
    got = links_of(text, **kw)
    assert len(got) == 1, f"attendu 1 lien, obtenu {len(got)} : {got}"
    return got[0]


# ---------------------------------------------------------------------------
# Extraction
# ---------------------------------------------------------------------------

def test_extracts_each_url_kind_with_lines():
    text = (
        "voir [blob](" + BASE + "MyIA.AI.Notebooks/GenAI/Texte/01-Intro.ipynb)\n"
        "et [tree](https://github.com/jsboige/CoursIA/tree/main/MyIA.AI.Notebooks/GenAI)\n"
        "et [raw](https://raw.githubusercontent.com/jsboige/CoursIA/main/a/b.ipynb)\r\n"
        "et [colab](https://colab.research.google.com/github/jsboige/CoursIA"
        "/blob/main/a/b.ipynb)\n"
        "et [nbviewer](https://nbviewer.org/github/jsboige/CoursIA/blob/main/a/b.ipynb)\n"
    )
    links = links_of(text)
    assert [l.kind for l in links] == ["blob", "tree", "raw", "colab", "nbviewer"]
    # CRLF compte comme une seule fin de ligne (ligne 3 -> 4 en CRLF).
    assert [l.line for l in links] == [1, 2, 3, 4, 5]
    assert links[1].path == "MyIA.AI.Notebooks/GenAI"
    assert links[2].path == "a/b.ipynb"
    assert links[3].path == "a/b.ipynb"
    assert links[4].path == "a/b.ipynb"
    assert all(l.branch == "main" for l in links)


def test_owner_repo_is_case_insensitive_host_and_repo():
    text = "https://GITHUB.COM/Jsboige/coursIA/blob/main/a/b.ipynb"
    assert one_link(text).path == "a/b.ipynb"


def test_other_repos_and_bare_repo_links_are_ignored():
    text = (
        "https://github.com/Netflix/vmaf/blob/main/x.ipynb\n"
        "https://github.com/jsboige/CoursIA\n"
        "https://github.com/jsboige/CoursIA/compare/v1...v2\n"
        "https://docs.github.com/en/actions\n"
    )
    assert links_of(text) == []


def test_markdown_paren_and_trailing_punctuation():
    text = (
        "voir [le notebook](" + BASE + "a/b.ipynb), puis la note.\n"
        "enfin <" + BASE + "a/c.ipynb>.\n"
        "\"" + BASE + "a/d.ipynb\".\n"
    )
    got = links_of(text)
    assert [l.path for l in got] == ["a/b.ipynb", "a/c.ipynb", "a/d.ipynb"]


def test_fragment_and_query_are_stripped():
    for suffix in ("#L12", "?raw=true", "#section.", "?q=1."):
        link = one_link(BASE + "a/b.ipynb" + suffix)
        assert link.path == "a/b.ipynb", suffix


def test_percent_decoding_keeps_raw_form():
    link = one_link(BASE + "MyIA.AI.Notebooks/Texte/01%20Intro.ipynb")
    assert link.path == "MyIA.AI.Notebooks/Texte/01 Intro.ipynb"
    assert link.path_raw == "MyIA.AI.Notebooks/Texte/01%20Intro.ipynb"


# ---------------------------------------------------------------------------
# Classement
# ---------------------------------------------------------------------------

def test_ok_file_and_ok_directory():
    ok_file = one_link(BASE + "MyIA.AI.Notebooks/GenAI/Texte/01-Intro.ipynb")
    v = organ.classify(ok_file, TREE_FILES, TREE_DIRS, {})
    assert v.status == "ok"
    # Un lien tree vise un prefixe de repertoire -- ou un fichier.
    ok_dir = one_link("https://github.com/jsboige/CoursIA/tree/main/MyIA.AI.Notebooks/GenAI")
    assert organ.classify(ok_dir, TREE_FILES, TREE_DIRS, {}).status == "ok"
    ok_dir_file = one_link(
        "https://github.com/jsboige/CoursIA/tree/main/Other/Series/Rapport.ipynb")
    assert organ.classify(ok_dir_file, TREE_FILES, TREE_DIRS, {}).status == "ok"


def test_pinned_for_sha_and_other_branch():
    for branch in ("develop", "0ddc1e46fdf",
                   "0ddc1e46fdfaa11bb22cc33dd44ee55ff66aa77bb"):
        link = one_link(BASE.replace("main", branch) + "a/b.ipynb")
        v = organ.classify(link, TREE_FILES, TREE_DIRS, {}, branch="main")
        assert v.status == "pinned", branch
        assert v.suggestion is None


def test_moved_via_ledger_two_step_chain():
    ledger = {
        "a/Old.ipynb": "b/Mid.ipynb",
        "b/Mid.ipynb": "c/New.ipynb",
    }
    link = one_link(BASE + "a/Old.ipynb")
    v = organ.classify(link, {"c/New.ipynb"}, organ.dirs_of({"c/New.ipynb"}), ledger)
    assert v.status == "moved"
    assert v.suggestion == "c/New.ipynb"
    assert v.via == "ledger"


def test_ledger_cycle_does_not_hang():
    ledger = {
        "x/A.ipynb": "y/B.ipynb",
        "y/B.ipynb": "x/A.ipynb",
        "z/z.ipynb": "z/z.ipynb",  # auto-boucle : garde aussi
    }
    link = one_link(BASE + "x/A.ipynb")
    v = organ.classify(link, {"unrelated/Far.ipynb"},
                       organ.dirs_of({"unrelated/Far.ipynb"}), ledger)
    # Pas de relocalisation, pas de boucle infinie : missing sec.
    assert v.status == "missing"
    assert v.suggestion is None


def test_moved_via_unique_basename():
    link = one_link(BASE + "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/"
                    "04-7-TTS-Voice-Benchmark.ipynb")
    v = organ.classify(link, TREE_FILES, TREE_DIRS, {})
    assert v.status == "moved"
    assert v.suggestion == ("MyIA.AI.Notebooks/GenAI/Audio/04-Applications/"
                            "04-Voix/04-7-TTS-Voice-Benchmark.ipynb")
    assert v.via == "basename"


def test_missing_with_ambiguous_basename_lists_candidates():
    link = one_link(BASE + "Elsewhere/Rapport.ipynb")
    v = organ.classify(link, TREE_FILES, TREE_DIRS, {})
    assert v.status == "missing"
    assert v.suggestion is None
    # Liste triee pour un rendu deterministe.
    assert v.candidates == ["Other/Series/Rapport.ipynb", "Rapport.ipynb"]


def test_tree_link_relocated_via_unique_dir_basename():
    link = one_link("https://github.com/jsboige/CoursIA/tree/main/old/dossier")
    v = organ.classify(link, TREE_FILES, TREE_DIRS, {})
    assert v.status == "moved"
    assert v.suggestion == "new/dossier"
    assert v.via == "basename"


def test_missing_without_any_candidate_has_empty_list():
    link = one_link(BASE + "nowhere/Gone.ipynb")
    v = organ.classify(link, TREE_FILES, TREE_DIRS, {})
    assert v.status == "missing"
    assert v.candidates == []


# ---------------------------------------------------------------------------
# apply_fixes (unite)
# ---------------------------------------------------------------------------

def _verdict_for(text: str, tree_files: set[str], ledger: dict[str, str]) -> organ.Verdict:
    link = one_link(text)
    return organ.classify(link, tree_files, organ.dirs_of(tree_files), ledger)


def test_apply_fixes_rewrites_only_moved_spans():
    text = (
        "old: " + BASE + "a/Old.ipynb  et hors-URL: a/Old.ipynb\n"
        "ok : " + BASE + "c/New.ipynb\n"
    )
    tree = {"c/New.ipynb"}
    ledger = {"a/Old.ipynb": "b/Mid.ipynb", "b/Mid.ipynb": "c/New.ipynb"}
    verdicts = [organ.classify(l, tree, organ.dirs_of(tree), ledger)
                for l in links_of(text)]
    new_text, n = organ.apply_fixes(text, verdicts)
    assert n == 1
    assert (BASE + "c/New.ipynb") in new_text
    # L'occurrence hors URL n'est pas touchee : le remplacement vise le span
    # du chemin DANS son URL.
    assert "hors-URL: a/Old.ipynb" in new_text
    assert new_text.count(BASE + "c/New.ipynb") == 2


def test_apply_fixes_preserves_percent_encoding_style():
    text = BASE + "old/My%20Notebook.ipynb"
    tree = {"new/My Notebook.ipynb"}
    ledger = {"old/My Notebook.ipynb": "new/My Notebook.ipynb"}
    v = _verdict_for(text, tree, ledger)
    assert v.status == "moved"
    new_text, n = organ.apply_fixes(text, [v])
    assert n == 1
    assert new_text == BASE + "new/My%20Notebook.ipynb"


# ---------------------------------------------------------------------------
# main() : depot git temporaire, codes de sortie, --apply de bout en bout
# ---------------------------------------------------------------------------

def _git(repo: Path, *argv: str) -> None:
    r = subprocess.run(["git", "-C", str(repo), *argv],
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert r.returncode == 0, f"git {argv} : {r.stderr}"


def _make_repo(tmp_path: Path, files: dict[str, bytes],
               ledger: str | None = None) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    for rel, content in files.items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(content)
    if ledger is not None:
        d = repo / "docs" / "reference"
        d.mkdir(parents=True, exist_ok=True)
        (d / "rename-ledger.tsv").write_text(ledger, encoding="utf-8")
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "add", "-A")
    _git(repo, "-c", "user.email=t@example.org", "-c", "user.name=t",
         "commit", "-q", "-m", "init")
    return repo


def _make_consumer(tmp_path: Path, files: dict[str, bytes]) -> Path:
    consumer = tmp_path / "consumer"
    for rel, content in files.items():
        p = consumer / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(content)
    return consumer


CHAIN_LEDGER = (
    "ancien\tnouveau\tdate\tlane\n"
    "a/Old.ipynb\tb/Mid.ipynb\t2026-01-01\ttest\n"
    "b/Mid.ipynb\tc/New.ipynb\t2026-01-01\ttest\n"
)


def test_exit_zero_when_all_ok(tmp_path):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"})
    consumer = _make_consumer(tmp_path, {
        "docs/CATALOGUE.md": ("voir " + BASE + "c/New.ipynb\n").encode("utf-8"),
    })
    rc = organ.main(["--consumer", str(consumer), "--repo-root", str(repo)])
    assert rc == 0


def test_exit_one_on_missing(tmp_path):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"})
    consumer = _make_consumer(tmp_path, {
        "docs/CATALOGUE.md": ("voir " + BASE + "nowhere/Gone.ipynb\n").encode("utf-8"),
    })
    rc = organ.main(["--consumer", str(consumer), "--repo-root", str(repo)])
    assert rc == 1


def test_exit_two_on_absent_consumer(tmp_path):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"})
    rc = organ.main(["--consumer", str(tmp_path / "absent"),
                     "--repo-root", str(repo)])
    assert rc == 2


def test_exit_two_on_unknown_ref(tmp_path):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"})
    consumer = _make_consumer(tmp_path, {"docs/a.md": b"x"})
    rc = organ.main(["--consumer", str(consumer), "--repo-root", str(repo),
                     "--ref", "no-such-ref"])
    assert rc == 2


def test_apply_rewrites_only_moved_and_is_idempotent(tmp_path, capsys):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"}, ledger=CHAIN_LEDGER)
    consumer = _make_consumer(tmp_path, {
        "docs/CATALOGUE.md": (
            "moved " + BASE + "a/Old.ipynb\n"
            "ok    " + BASE + "c/New.ipynb\n"
            "epingle https://github.com/jsboige/CoursIA/blob/develop/x/y.ipynb\n"
        ).encode("utf-8"),
    })
    cat = consumer / "docs" / "CATALOGUE.md"

    rc1 = organ.main(["--consumer", str(consumer), "--repo-root", str(repo),
                      "--apply"])
    out1 = capsys.readouterr().out
    assert rc1 == 0, out1
    assert "1 remplacement(s) ecrit(s)" in out1
    body = cat.read_bytes().decode("utf-8")
    assert (BASE + "c/New.ipynb") in body
    assert "a/Old.ipynb" not in body
    assert "blob/develop/x/y.ipynb" in body  # pinned : jamais touchee

    # Second passage : plus rien a recrire, sortie 0, contenu identique.
    before = cat.read_bytes()
    rc2 = organ.main(["--consumer", str(consumer), "--repo-root", str(repo),
                      "--apply"])
    out2 = capsys.readouterr().out
    assert rc2 == 0, out2
    assert "remplacement(s) ecrit(s)" not in out2
    assert cat.read_bytes() == before


def test_apply_keeps_crlf_files_crlf(tmp_path):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"}, ledger=CHAIN_LEDGER)
    content = (
        "ligne un\r\nmoved " + BASE + "a/Old.ipynb\r\nligne trois\r\n"
    ).encode("utf-8")
    consumer = _make_consumer(tmp_path, {"docs/CATALOGUE.md": content})
    cat = consumer / "docs" / "CATALOGUE.md"

    rc = organ.main(["--consumer", str(consumer), "--repo-root", str(repo),
                     "--apply"])
    assert rc == 0
    after = cat.read_bytes()
    assert after.count(b"\r\n") == content.count(b"\r\n") == 3
    assert after.count(b"\n") == after.count(b"\r\n")  # aucun \n solitaire
    assert (BASE + "c/New.ipynb").encode("utf-8") in after


def test_json_output_shape_and_totals(tmp_path, capsys):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"}, ledger=CHAIN_LEDGER)
    consumer = _make_consumer(tmp_path, {
        "docs/CATALOGUE.md": (
            "moved " + BASE + "a/Old.ipynb\n"
            "ok    " + BASE + "c/New.ipynb\n"
            "miss  " + BASE + "nowhere/Gone.ipynb\n"
        ).encode("utf-8"),
    })
    import json
    rc = organ.main(["--consumer", str(consumer), "--repo-root", str(repo),
                     "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert payload["owner_repo"] == "jsboige/CoursIA"
    assert payload["branch"] == "main"
    assert payload["ref"] == "HEAD"
    (c,) = payload["consumers"]
    assert c["files_scanned"] == 1
    assert c["totals"] == {"occurrences": 3, "ok": 1, "moved": 1,
                           "missing": 1, "pinned": 0}
    # Defaut : seules les occurrences non-ok sont listees.
    assert [o["status"] for o in c["occurrences"]] == ["moved", "missing"]
    assert c["occurrences"][0]["suggestion"] == "c/New.ipynb"
    assert c["occurrences"][0]["via"] == "ledger"
    assert payload["totals"] == c["totals"]


def test_markdown_output_lists_non_ok_rows(tmp_path, capsys):
    repo = _make_repo(tmp_path, {"c/New.ipynb": b"{}"}, ledger=CHAIN_LEDGER)
    consumer = _make_consumer(tmp_path, {
        "docs/CATALOGUE.md": ("moved " + BASE + "a/Old.ipynb\n").encode("utf-8"),
    })
    rc = organ.main(["--consumer", str(consumer), "--repo-root", str(repo),
                     "--markdown"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "| Fichier | Ligne | Statut | Cible | Suggestion | Via |" in out
    assert "| docs/CATALOGUE.md | 1 | moved | a/Old.ipynb | c/New.ipynb | ledger |" in out


def test_load_tree_on_a_real_git_repo(tmp_path):
    repo = _make_repo(tmp_path, {
        "MyIA.AI.Notebooks/Serie/A.ipynb": b"{}",
        "sous/dossier/B.md": b"x",
    })
    files, dirs = organ.load_tree(repo, "HEAD")
    assert files == {"MyIA.AI.Notebooks/Serie/A.ipynb", "sous/dossier/B.md"}
    assert {"MyIA.AI.Notebooks", "MyIA.AI.Notebooks/Serie", "sous",
            "sous/dossier"} <= dirs
    # Ref inconnue : OrganError, jamais un arbre vide silencieux.
    with pytest.raises(organ.OrganError):
        organ.load_tree(repo, "no-such-ref")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
