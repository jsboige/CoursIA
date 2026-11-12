"""Contrat du prétraitement temporaire des README Quarto."""
import importlib.util
import json
from pathlib import Path

import pytest

spec = importlib.util.spec_from_file_location('titres', Path(__file__).parents[1] / 'quarto_readme_titles.py')
titres = importlib.util.module_from_spec(spec)
spec.loader.exec_module(titres)


def project(tmp_path, files):
    for name, content in files.items():
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding='utf-8')
    (tmp_path / '_quarto.yml').write_text('project:\n  render:\n' + ''.join('    - ' + json.dumps(p) + '\n' for p in files), encoding='utf-8')
    return tmp_path


def test_apply_check_restore_and_explicit(tmp_path):
    files = {
        'a/README.md': '# [Été **brillant**](url)\n',
        'b/README.md': '---\ndescription: exemple\n---\n# Été brillant\n',
        'c/README.md': '---\npagetitle: "Titre explicite"\n---\n# Autre\n',
        'd/README.md': 'Sans titre\n',
        'd/autre_README.md': '```md\n# Faux\n```\n# Vrai\n',
    }
    root = project(tmp_path, files)
    original = {p: (root / p).read_bytes() for p in files}
    backup = root / 'backup.json'
    titres.apply(root, backup)
    titres.check(root)
    result = {p: titres.explicit((root / p).read_text()) for p in files}
    assert result['a/README.md'] == 'Été brillant (a/README.md)'
    assert result['b/README.md'] == 'Été brillant (b/README.md)'
    assert result['c/README.md'] == 'Titre explicite'
    assert result['d/README.md'] == 'd/README.md'
    assert result['d/autre_README.md'] == 'Vrai'
    assert (root / 'c/README.md').read_bytes() == original['c/README.md']
    titres.restore(root, backup)
    assert {p: (root / p).read_bytes() for p in files} == original


def test_explicit_crlf_is_preserved_and_restored(tmp_path):
    root = project(tmp_path, {'a/README.md': '# placeholder\n'})
    path = root / 'a/README.md'
    original = b'---\r\npagetitle: "Titre explicite"\r\n---\r\n# Autre\r\n'
    path.write_bytes(original)
    backup = root / 'backup.json'
    assert titres.explicit(original.decode('utf-8')) == 'Titre explicite'
    titres.apply(root, backup)
    titres.check(root)
    assert path.read_bytes() == original
    assert path.read_bytes().count(b'pagetitle:') == 1
    titres.restore(root, backup)
    assert path.read_bytes() == original


def test_explicit_collision_with_derived(tmp_path):
    root = project(tmp_path, {'a/README.md': '---\npagetitle: "Même"\n---\n', 'b/README.md': '# Même\n'})
    result = titres.plan(root, titres.readmes(root))
    assert result[Path('a/README.md')] == 'Même'
    assert result[Path('b/README.md')] == 'Même (b/README.md)'


def test_bom_titles_frontmatter_and_exact_restore(tmp_path):
    files = {
        'h1/README.md': '\ufeff# Titre H1\n',
        'metadata/README.md': '\ufeff---\ndescription: exemple\n---\n# Titre metadata\n',
        'explicit/README.md': '\ufeff---\npagetitle: "Titre explicite"\n---\n# Autre\n',
    }
    root = project(tmp_path, files)
    original = {p: (root / p).read_bytes() for p in files}
    backup = root / 'backup.json'
    assert titres.plan(root, titres.readmes(root)) == {
        Path('h1/README.md'): 'Titre H1',
        Path('metadata/README.md'): 'Titre metadata',
        Path('explicit/README.md'): 'Titre explicite',
    }
    titres.apply(root, backup)
    titres.check(root)
    assert (root / 'h1/README.md').read_text(encoding='utf-8') == '---\npagetitle: "Titre H1"\n---\n\n# Titre H1\n'
    assert (root / 'metadata/README.md').read_text(encoding='utf-8') == '---\npagetitle: "Titre metadata"\ndescription: exemple\n---\n# Titre metadata\n'
    assert (root / 'explicit/README.md').read_bytes() == original['explicit/README.md']
    titres.restore(root, backup)
    assert {p: (root / p).read_bytes() for p in files} == original


def test_guard_rejects_missing_duplicate_and_no_targets(tmp_path):
    root = project(tmp_path, {'a/README.md': '# A\n', 'b/README.md': '# B\n'})
    with pytest.raises(ValueError, match='absent'):
        titres.check(root)
    for p in ('a/README.md', 'b/README.md'):
        (root / p).write_text('---\npagetitle: "Identique"\n---\n')
    with pytest.raises(ValueError, match='dupliqué'):
        titres.check(root)
    (root / '_quarto.yml').write_text('project:\n  render:\n    - "index.qmd"\n')
    with pytest.raises(ValueError, match='vide'):
        titres.check(root)


def test_restore_refuses_external_edits(tmp_path):
    root = project(tmp_path, {'a/README.md': '# Bonjour\n'})
    backup = root / 'backup.json'
    titres.apply(root, backup)
    (root / 'a/README.md').write_text('intervention\n')
    with pytest.raises(ValueError, match='modifiée'):
        titres.restore(root, backup)


@pytest.mark.parametrize('field', [
    'pagetitle:',
    'pagetitle:   ',
    'pagetitle :',
    '"pagetitle":',
    "'pagetitle': # commentaire",
    'pagetitle: # commentaire',
    'pagetitle: ""',
    "pagetitle: ''",
    'pagetitle: "   "',
    'pagetitle: null',
    'pagetitle: "guillemet non fermé',
    "pagetitle: 'guillemet non fermé",
    'pagetitle: autre: valeur',
])
def test_invalid_pagetitle_never_consumes_next_key(tmp_path, field):
    root = project(tmp_path, {'a/README.md': '---\n' + field + '\ndescription: exemple\n---\n# Vrai titre\n'})
    with pytest.raises(ValueError):
        titres.check(root)
    with pytest.raises(ValueError):
        titres.apply(root, root / 'backup.json')


def test_unterminated_frontmatter_rejected(tmp_path):
    root = project(tmp_path, {'a/README.md': '---\npagetitle: Exemple\n# Vrai titre\n'})
    with pytest.raises(ValueError, match='non terminé'):
        titres.check(root)


def test_render_list_path_with_apostrophe_is_not_skipped(tmp_path):
    root = project(tmp_path, {"docs/l'apprentissage/README.md": '# Apprentissage\n'})
    assert titres.readmes(root) == [Path("docs/l'apprentissage/README.md")]
    titres.apply(root, root / 'backup.json')
    titres.check(root)
    titres.restore(root, root / 'backup.json')


def test_unrecognised_readme_entry_fails_closed(tmp_path):
    (tmp_path / '_quarto.yml').write_text('project:\n  render:\n    - "valide/README.md"\n    - "aut"re/README.md"\n')
    (tmp_path / 'valide').mkdir()
    (tmp_path / 'valide/README.md').write_text('# Valide\n')
    with pytest.raises(ValueError, match='non reconnue'):
        titres.readmes(tmp_path)
