"""Garde des aretes inter-dossiers de l'aire de veille (#22468, review 5867133827).

La derivation parent-dir de ``watch_areas`` ne voit pas les suites qui
testent un module d'un AUTRE dossier : ``tests/test_release_parked_runs.py``
teste ``scripts/ci/release_parked_runs.py`` via un chemin construit depuis
``__file__``, et modifier le module ne selectionnait pas la suite racine
``tests`` -- la casse passait verte, sur PR comme sur le push main restreint
(diff ``HEAD~1``).

Mesure bornee basse (celle de la review, assumee telle) : pour chaque suite
du workflow, chaque fichier de test est relu ; les ancres ``__file__`` et
leurs chaines ``parents[N] / "seg"...`` sont resolues vers un chemin du
depot ; tout chemin resolu hors de l'aire de veille de sa suite DOIT etre
couvert par une entree d'``EXTRA_SELECTORS``. Reciproquement, chaque entree
repertoirique d'``EXTRA_SELECTORS`` doit correspondre a au moins un chemin
relu -- retirer une declaration rougit la garde (controle positif du
retrait).

Hors perimetre assume : imports transitifs, chemins construits autrement
(f-strings, variables non ancrees a ``__file__``), insertions hors depot, et
ancres NUES vers un ancetre du fichier (plomberie ``sys.path`` -- ce qu'elles
rendent importable est invisible a cette borne basse). Le filet qui borne ces
angles morts reste le point 1 de la review : le push sur ``main`` joue la
pleine suite.
"""
import importlib.util
import re
import sys
from pathlib import Path

_CI = Path(__file__).resolve().parents[1]
_SPEC = importlib.util.spec_from_file_location(
    "changed_scripts_tests", _CI / "changed_scripts_tests.py"
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)

_SPEC_GTR = importlib.util.spec_from_file_location(
    "guard_test_root", _CI / "guard_test_root.py"
)
gtr = importlib.util.module_from_spec(_SPEC_GTR)
_SPEC_GTR.loader.exec_module(gtr)

REPO_ROOT = Path(__file__).resolve().parents[3]

# Ancre directe : Path(__file__).resolve().parents[N] / "seg" / ...
_DIRECT_RE = re.compile(
    r"Path\(__file__\)(?:\.resolve\(\))?\.parents\[(\d+)\]"
    r"((?:\s*/\s*\"[^\"]+\")*)"
)
# Ancre variable : VAR = Path(__file__).resolve().parent, puis VAR.parents[N]
_VAR_DEF_RE = re.compile(
    r"(\w+)\s*=\s*Path\(__file__\)(?:\.resolve\(\))?\.parent\b"
)
_VAR_USE_TMPL = r"%s\.parents\[(\d+)\]((?:\s*/\s*\"[^\"]+\")*)"


def _segments(chain: str) -> list[str]:
    return re.findall(r"\"([^\"]+)\"", chain)


def _resolve_targets(src: str, file: Path) -> set[str]:
    """Chemins du depot resolus depuis les ancres ``__file__`` de ``src``.

    Borne basse volontaire : ``parents[N]`` direct, variable posee a
    ``Path(__file__).parent`` (les ``parents[N]`` de la variable valent les
    ``parents[N+1]`` du fichier), et segments litteraux appendus.

    Les ancres NUES (aucun segment appendu) qui resolvent vers un ancetre du
    fichier lui-meme ne sont pas des dependances : c'est la plomberie
    d'import (``sys.path.insert(0, str(Path(__file__).resolve().parents[2]))``
    pour importer un paquet voisin), pas la lecture d'un module d'un autre
    dossier. Elles sont ecartees ici ; ce qu'elles rendent importable reste
    hors perimetre assume (docstring du module).
    """
    targets: set[str] = set()

    def _add(depth: int, segs: list[str], f: Path) -> None:
        base = f.resolve().parents[depth] if depth < len(f.resolve().parents) else None
        if base is None:
            return
        resolved = base.joinpath(*segs) if segs else base
        if not segs and f.resolve().parent.is_relative_to(resolved):
            return  # ancre d'ancetre nue : plomberie d'import, pas une arete
        try:
            resolved.relative_to(REPO_ROOT)
        except ValueError:
            return  # hors depot : hors perimetre de la garde
        rel = resolved.relative_to(REPO_ROOT).as_posix()
        if rel and rel != ".":
            targets.add(rel)

    for m in _DIRECT_RE.finditer(src):
        _add(int(m.group(1)), _segments(m.group(2)), file)
    for vm in _VAR_DEF_RE.finditer(src):
        var = vm.group(1)
        for m in re.finditer(_VAR_USE_TMPL % re.escape(var), src):
            _add(int(m.group(1)) + 1, _segments(m.group(2)), file)
    return targets


def _suite_files(suite: str) -> list[Path]:
    entry = REPO_ROOT / suite
    if entry.is_file():
        return [entry]
    if entry.is_dir():
        return sorted(entry.rglob("test_*.py"))
    return []


def _base_areas(suite: str) -> tuple[str, ...]:
    """Aires de veille SANS les selecteurs additionnels (overrides/parent)."""
    if suite in mod.WATCH_OVERRIDES:
        return mod.WATCH_OVERRIDES[suite]
    if suite.endswith("/tests"):
        return (suite[: -len("/tests")] + "/",)
    return (suite + "/",)


def _real_edges() -> dict[tuple[str, str], list[str]]:
    """Aretes relues : (suite, extra_couvrant) -> chemins resolus.

    Une arete n'est DANGEREUSE que si sa cible tombe dans l'aire de veille
    d'une AUTRE suite : la modification selectionne cette suite-la, la
    portee reste restreinte, et les tests de la suite qui lit la cible ne
    tournent pas. Une cible hors de toute aire declenche le repli pleine
    suite (fail-open) ; une cible sous ``FULL_TRIGGERS`` force la pleine
    suite -- l'une et l'autre protegent deja, aucune declaration requise.
    """
    suites = gtr.parse_collected_paths(mod.DEFAULT_WORKFLOW)
    assert suites, "liste de suites du workflow illisible : garde aveugle"
    others: list[tuple[str, tuple[str, ...]]] = [
        (s, _base_areas(s)) for s in suites
    ]
    edges: dict[tuple[str, str], list[str]] = {}
    for suite in suites:
        extras = mod.EXTRA_SELECTORS.get(suite, ())
        for f in _suite_files(suite):
            try:
                src = f.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for target in _resolve_targets(src, f):
                if any(mod._selects(a, target) for a in _base_areas(suite)):
                    continue  # arete interne a l'aire de veille
                if not any(
                    mod._selects(a, target)
                    for s, areas in others
                    if s != suite
                    for a in areas
                ):
                    continue  # hors de toute aire : fail-open pleine suite
                for extra in extras:
                    if mod._selects(extra, target):
                        edges.setdefault((suite, extra), []).append(
                            f"{f.as_posix()} -> {target}"
                        )
                        break
                else:
                    edges.setdefault((suite, "<NON DECLAREE>"), []).append(
                        f"{f.as_posix()} -> {target}"
                    )
    return edges


def test_les_aretes_inter_dossiers_sont_declarees():
    """Toute arete resolue hors aire doit etre couverte par EXTRA_SELECTORS."""
    bad = [
        line for (suite, extra), lines in _real_edges().items()
        if extra == "<NON DECLAREE>" for line in lines
    ]
    assert not bad, (
        "arete(s) inter-dossiers hors aire de veille non declaree(s) dans "
        "EXTRA_SELECTORS -- une PR qui casse la cible passe verte (review "
        f"5867133827) : {bad[:6]}"
    )


def test_chaque_arete_declaree_est_relue():
    """Reciprocite : une entree repertoirique morte = declaration perimee.

    Controle positif du retrait : retirer une entree d'EXTRA_SELECTORS rend
    l'arete qu'elle couvrait non declaree -> le test precedent rougit, et
    celui-ci nomme l'entree morte.
    """
    edges = _real_edges()
    dead = [
        f"{suite}: {extra}"
        for suite, extras in mod.EXTRA_SELECTORS.items()
        for extra in extras
        if extra.endswith("/") and (suite, extra) not in edges
    ]
    assert not dead, (
        "entree(s) EXTRA_SELECTORS repertoirique(s) sans arete relue -- "
        f"declaration perimee a retirer : {dead}"
    )


def test_resolveur_borne_basse_sur_cas_synthetiques():
    """Le resolveur voit les deux formes d'ancre et le bon decalage."""
    src_direct = (
        "import sys\nfrom pathlib import Path\n"
        "SCRIPT = Path(__file__).resolve().parents[1] / \"scripts\" / \"ci\""
        " / \"release_parked_runs.py\"\n"
    )
    probe = REPO_ROOT / "tests" / "_tmp_guard_probe_a.py"
    probe.write_text(src_direct, encoding="utf-8")
    try:
        got = _resolve_targets(src_direct, probe)
        assert "scripts/ci/release_parked_runs.py" in got
    finally:
        probe.unlink()

    src_var = (
        "from pathlib import Path\n"
        "HERE = Path(__file__).resolve().parent\n"
        "CI = HERE.parents[1] / \"ci\"\n"
    )
    probe2 = REPO_ROOT / "scripts" / "translation" / "tests" / "_tmp_guard_probe_b.py"
    probe2.write_text(src_var, encoding="utf-8")
    try:
        got = _resolve_targets(src_var, probe2)
        # HERE = scripts/translation/tests ; HERE.parents[1] = scripts -> ci
        assert "scripts/ci" in got
    finally:
        probe2.unlink()
