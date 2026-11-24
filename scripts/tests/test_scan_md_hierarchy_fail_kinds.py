"""Tests de --fail-kinds (#22012) : code de sortie bloquant par classe (rc=4).

Bascule graduelle documentee en #22012 option 4 : un drift HINT-AS-HEADING
sort en 4 (le workflow fait echouer le check), un drift des autres classes
garde la sortie advisory 2, une classe typoee echoue bruyamment (rc=1) au lieu
de ne rien matcher en silence. Cette suite EST le controle par faux negatif du
criterere d'acceptance 3 de #22012 : injecter un indice-en-titre -> rouge ;
le corriger en gras -> vert.
"""
import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / 'notebook_tools' / 'scan_md_hierarchy.py'

CLEAN = [['# Titre du carnet'], ['## Une section'], ['Du prose sans defaut.']]
HINT = [['# Titre du carnet'], ['## Une section'], ['### Indice : calculez la derive']]
H1_DEEP = [['# Titre du carnet'], ['## Une section'], ['# Deuxieme titre H1']]
HINT_FIXED = [['# Titre du carnet'], ['## Une section'],
              ['- **Indice :** calculez la derive']]


def _write(path, cells):
    doc = {
        'cells': [
            {'cell_type': 'markdown', 'id': f'cell-{i}', 'metadata': {}, 'source': src}
            for i, src in enumerate(cells)
        ],
        'metadata': {},
        'nbformat': 4,
        'nbformat_minor': 5,
    }
    path.write_text(json.dumps(doc, ensure_ascii=False), encoding='utf-8')


def _seed_baseline(tmp_path):
    """Pose un carnet propre et enregistre la baseline dessus (etat vert)."""
    nb = tmp_path / 'nb.ipynb'
    _write(nb, CLEAN)
    r = subprocess.run(
        [sys.executable, str(SCRIPT), str(tmp_path), '--baseline',
         str(tmp_path / 'baseline.json'), '--update-baseline'],
        capture_output=True, text=True, encoding='utf-8', errors='replace')
    assert r.returncode == 0, r.stderr
    return nb


def _run(tmp_path, *extra):
    return subprocess.run(
        [sys.executable, str(SCRIPT), str(tmp_path), '--baseline',
         str(tmp_path / 'baseline.json'), '--diff', *extra],
        capture_output=True, text=True, encoding='utf-8', errors='replace')


def test_hint_drift_blocks_with_fail_kinds(tmp_path):
    nb = _seed_baseline(tmp_path)
    _write(nb, HINT)
    r = _run(tmp_path, '--fail-kinds', 'HINT-AS-HEADING')
    assert r.returncode == 4
    assert 'HINT-AS-HEADING' in r.stdout


def test_hint_drift_stays_advisory_without_flag(tmp_path):
    nb = _seed_baseline(tmp_path)
    _write(nb, HINT)
    r = _run(tmp_path)
    assert r.returncode == 2


def test_other_kinds_stay_advisory_with_fail_kinds(tmp_path):
    nb = _seed_baseline(tmp_path)
    _write(nb, H1_DEEP)
    r = _run(tmp_path, '--fail-kinds', 'HINT-AS-HEADING')
    assert r.returncode == 2


def test_multi_kind_flag_blocks_on_either_class(tmp_path):
    nb = _seed_baseline(tmp_path)
    _write(nb, H1_DEEP)
    r = _run(tmp_path, '--fail-kinds', 'HINT-AS-HEADING,H1-DEEP')
    assert r.returncode == 4


def test_fixed_hint_exits_zero(tmp_path):
    nb = _seed_baseline(tmp_path)
    _write(nb, HINT)
    _write(nb, HINT_FIXED)
    r = _run(tmp_path, '--fail-kinds', 'HINT-AS-HEADING')
    assert r.returncode == 0


def test_unknown_kind_fails_loud_not_silent(tmp_path):
    _seed_baseline(tmp_path)
    r = _run(tmp_path, '--fail-kinds', 'BOGUS-KIND')
    assert r.returncode == 1
    assert 'BOGUS-KIND' in r.stderr


def _git(repo, *args):
    r = subprocess.run(['git', '-C', str(repo), *args],
                       capture_output=True, text=True,
                       encoding='utf-8', errors='replace')
    assert r.returncode == 0, r.stderr
    return r


def test_base_ref_attributes_drift_to_diff(tmp_path):
    """--base-ref (sucre voie rapide) : le drift mesure est imputable au diff."""
    import subprocess as sp
    repo = tmp_path / 'repo'
    (repo / 'MyIA.AI.Notebooks').mkdir(parents=True)
    _git(repo, 'init', '-q')
    _git(repo, 'config', 'user.email', 't@example.com')
    _git(repo, 'config', 'user.name', 't')
    _write(repo / 'MyIA.AI.Notebooks' / 'nb.ipynb', CLEAN)
    _git(repo, 'add', '-A')
    _git(repo, 'commit', '-qm', 'base')
    base = _git(repo, 'rev-parse', 'HEAD').stdout.strip()
    _write(repo / 'MyIA.AI.Notebooks' / 'nb.ipynb', HINT)
    _git(repo, 'add', '-A')
    _git(repo, 'commit', '-qm', 'head')
    r = sp.run(
        [sys.executable, str(SCRIPT), 'MyIA.AI.Notebooks/', '--baseline',
         '--diff', '--fail-kinds', 'HINT-AS-HEADING', '--base-ref', base],
        capture_output=True, text=True, encoding='utf-8', errors='replace',
        cwd=str(repo))
    assert r.returncode == 4, (r.stdout, r.stderr)


def test_base_ref_never_flags_inherited_drift(tmp_path):
    """Bornage I1 (#12735) : un defaut present a la BASE, hors du diff, ne
    rougit jamais la tete."""
    import subprocess as sp
    repo = tmp_path / 'repo'
    (repo / 'MyIA.AI.Notebooks').mkdir(parents=True)
    _git(repo, 'init', '-q')
    _git(repo, 'config', 'user.email', 't@example.com')
    _git(repo, 'config', 'user.name', 't')
    _write(repo / 'MyIA.AI.Notebooks' / 'nb.ipynb', HINT)
    _git(repo, 'add', '-A')
    _git(repo, 'commit', '-qm', 'base avec defaut herite')
    base = _git(repo, 'rev-parse', 'HEAD').stdout.strip()
    _write(repo / 'MyIA.AI.Notebooks' / 'autre.ipynb', CLEAN)
    _git(repo, 'add', '-A')
    _git(repo, 'commit', '-qm', 'head ajoute un carnet propre')
    r = sp.run(
        [sys.executable, str(SCRIPT), 'MyIA.AI.Notebooks/', '--baseline',
         '--diff', '--fail-kinds', 'HINT-AS-HEADING', '--base-ref', base],
        capture_output=True, text=True, encoding='utf-8', errors='replace',
        cwd=str(repo))
    assert r.returncode == 0, (r.stdout, r.stderr)
