"""Sondes de sémantique Lake communes aux trois consommateurs."""
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lake_selectors import LakefileError, _without_comments, lake_selectors, selected
from check_i18n_siblings import check_en_built
from check_lean_orphans import main as orphan_main


def test_toml_defaults_and_roots(tmp_path):
    (tmp_path / "lakefile.toml").write_text(
        '[[lean_lib]]\nname="Alpha"\n[[lean_lib]]\nname="Beta"\n'
        'roots=["Beta.Main", "Beta.Main_en"]\n', encoding="utf-8")
    assert lake_selectors(tmp_path) == [("one", "Alpha"), ("one", "Beta.Main"),
                                       ("one", "Beta.Main_en")]


def test_dsl_explicit_glob_replaces_default(tmp_path):
    (tmp_path / "lakefile.lean").write_text(
        'lean_lib Gamma where\n  globs := #[`Gamma.Sub.*]\n', encoding="utf-8")
    selectors = lake_selectors(tmp_path)
    assert not selected("Gamma", selectors)
    assert selected("Gamma.Sub", selectors)
    assert selected("Gamma.Sub.Child", selectors)


def test_toml_strict_submodules_and_consumers(tmp_path, capsys):
    lakefile = tmp_path / "lakefile.toml"
    lakefile.write_text('[[lean_lib]]\nname="Delta"\nglobs=["Delta.Sub.+"]\n', encoding="utf-8")
    (tmp_path / "Delta").mkdir()
    (tmp_path / "Delta" / "Sub.lean").write_text("", encoding="utf-8")
    (tmp_path / "Delta" / "Sub").mkdir()
    child = tmp_path / "Delta" / "Sub" / "Child_en.lean"
    child.write_text("", encoding="utf-8")
    assert check_en_built(child, tmp_path)[0] is True
    assert orphan_main(["--project-path", str(tmp_path), "--lakefile", str(lakefile), "--strict"]) == 1
    assert "Sub.lean" in capsys.readouterr().out
    selectors = lake_selectors(tmp_path)
    assert not selected("Delta.Sub", selectors)
    assert selected("Delta.Sub.Child_en", selectors)
    assert selected("Foo", [("all", "Foo")])
    assert not selected("Foo", [("sub", "Foo")])


def test_dsl_comments_and_explicit_directives(tmp_path):
    (tmp_path / "lakefile.lean").write_text(
        '-- globs := #[`Ghost]\nlean_lib Foo where\n'
        '  globs := #[.submodules `Foo, `Foo_en]\n'
        'lean_lib Bar where\n  globs := #[`Bar.*]\n', encoding="utf-8")
    selectors = lake_selectors(tmp_path)
    assert selectors == [("sub", "Foo"), ("one", "Foo_en"), ("all", "Bar")]
    assert not selected("Foo", selectors)
    assert selected("Foo.Child", selectors)
    assert selected("Bar", selectors)
    assert not selected("Ghost", selectors)


def test_nested_comments_do_not_leak_selectors(tmp_path):
    (tmp_path / "lakefile.lean").write_text(
        'lean_lib Foo where\n'
        ' /- outer /- inner -/ globs := #[`Ghost] -/\n'
        ' globs := #[`Foo] -- /- not a block comment\n', encoding="utf-8")
    assert lake_selectors(tmp_path) == [("one", "Foo")]


@pytest.mark.parametrize("text", [
    '"/- literal -/ -- literal"',
    r'"escaped \" /- still literal -/"',
    r'"escaped \\" /- removed -/',
])
def test_comment_scanner_preserves_strings(text):
    masked = _without_comments(text, Path("lakefile.lean"))
    assert len(masked) == len(text)
    literal_end = text.rfind('"') + 1
    assert masked[:literal_end] == text[:literal_end]
    assert not masked[literal_end:].strip()


@pytest.mark.parametrize("comment", ['/- unfinished', '/- outer /- inner -/'])
def test_unterminated_comments_fail_closed(tmp_path, comment):
    (tmp_path / "lakefile.lean").write_text(
        'lean_lib Foo where\n' + comment, encoding="utf-8")
    with pytest.raises(LakefileError, match="commentaire Lean non fermé"):
        lake_selectors(tmp_path)


def test_invalid_dsl_and_toml_fail_closed(tmp_path):
    lakefile = tmp_path / "lakefile.lean"
    lakefile.write_text('lean_lib Foo where\n  globs := calculated\n', encoding="utf-8")
    with pytest.raises(LakefileError):
        lake_selectors(tmp_path)
    assert orphan_main(["--project-path", str(tmp_path), "--lakefile", str(lakefile)]) == 2
    lakefile.unlink()
    (tmp_path / "lakefile.toml").write_text('[[lean_lib]]\nname = [', encoding="utf-8")
    with pytest.raises(LakefileError):
        lake_selectors(tmp_path)
