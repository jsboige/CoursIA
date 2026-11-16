"""Tests de l'organe des versions de bibliotheques (#23073).

L'organe repond a une question simple : « quelle version de bibliotheque
charge un carnet, et est-elle celle que la serie de reference a fixee ? ».
Trois classes de defaut justifient l'organe :

1. **Retrogradation** -- une PR abaisse un epinglage (le carnet passe de
   IKVM 8.15.0 a 8.14.0) ;
2. **Divergence historique** -- l'epinglage etait deja la, la PR n'y touche
   pas : ce n'est pas une regression introduite, c'est une derive a
   traiter par la convergence ;
3. **Provisionnement etranger** -- le carnet telecharge depuis une source
   hors de l'organe de serie (le cas #23047 : `tweetyproject.org/builds/1.28/`
   repond 404 et l'organe de serie telecharge depuis Maven Central).

Les tests ci-dessous pinnent les trois, plus les invariants du manifeste
(la version d'un organe de serie n'est jamais recopie) et le contrat de
l'allowlist (une entree sans motif ecrit est refusee).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
TOOLS_DIR = REPO_ROOT / "scripts" / "notebook_tools"
sys.path.insert(0, str(TOOLS_DIR))

import check_lib_versions as clv  # noqa: E402

MANIFEST_PATH = TOOLS_DIR / "lib_versions_manifest.json"

# Digest de 64 hexadecimaux : la forme historique (#24520) exige desormais le
# marqueur ET le digest, un `SHA256 = "abc123"` ne suffit plus (#24943).
SHA256_DIGEST = "2cde56fdd6e3b10eb89b2ee90a7c4cb39af446e6f0f6fee09268a48e9ea9731f"


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------
def _notebook(cells: list[str]) -> dict:
    """Construit un carnet minimal (cellules code)."""
    return {
        "cells": [
            {"cell_type": "code", "source": [text], "metadata": {}, "outputs": []}
            for text in cells
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_notebook(tmp_path: Path, name: str, cells: list[str]) -> Path:
    path = tmp_path / name
    path.write_text(json.dumps(_notebook(cells)), encoding="utf-8")
    return path


def _manifest_with(tmp_path: Path, libraries: list[dict], allowlist: list[dict] | None = None):
    path = tmp_path / "manifest.json"
    path.write_text(
        json.dumps({"schema_version": 1, "libraries": libraries, "allowlist": allowlist or []}),
        encoding="utf-8",
    )
    return clv.load_manifest(path)


# --------------------------------------------------------------------------
# Comparaison de versions
# --------------------------------------------------------------------------
def test_version_comparison_is_numeric_not_lexicographic():
    assert clv.compare_versions("8.14.0", "8.15.0") < 0
    assert clv.compare_versions("9.11.4210", "9.15.6755") < 0
    assert clv.compare_versions("3.1.0", "3.0.5") > 0
    assert clv.compare_versions("8.15.0", "8.15.0") == 0


def test_version_comparison_handles_non_numeric_segment():
    assert clv.compare_versions("1.0.0-preview", "1.0.0") < 0
    # Comparaison segment par segment, comme NuGet : 4 < 23, donc 0.4.x est
    # inferieur a 0.23.0 (les versions 0.x ne se comparent pas comme des
    # decimaux).
    assert clv.compare_versions("0.4.2504.701", "0.23.0") < 0
    assert clv.compare_versions("0.23.0", "0.22.3") > 0


# --------------------------------------------------------------------------
# Manifeste
# --------------------------------------------------------------------------
def test_manifest_points_to_the_series_organ_without_copying_its_value():
    """Le manifeste NE recopie pas la version d'un organe de serie."""
    raw = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    tweety = next(e for e in raw["libraries"] if e["id"] == "Tweety")
    assert tweety["canonical_source"] == "organ"
    assert "canonical" not in tweety
    assert tweety["organ_symbol"] == "TWEETY_VERSION"

    manifest = clv.load_manifest(MANIFEST_PATH)
    canonical, error = manifest.libraries["Tweety"].resolve_canonical(REPO_ROOT)
    assert error is None
    assert canonical == "1.30"


def test_manifest_covers_the_libraries_required_by_the_issue():
    manifest = clv.load_manifest(MANIFEST_PATH)
    required = {
        "Tweety",
        "IKVM",
        "IKVM.Image",
        "pythonnet",
        "Google.OrTools",
        "dotNetRDF",
        "Microsoft.ML",
        "SkiaSharp",
    }
    assert required <= set(manifest.libraries)


def test_every_declared_divergence_carries_a_written_reason():
    raw = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    for entry in raw["libraries"]:
        for divergence in entry.get("divergences", []):
            assert divergence.get("decision") in {"to_converge", "justified"}
            assert divergence.get("reason", "").strip(), (
                f"{entry['id']} {divergence.get('version')} : motif manquant"
            )


def test_allowlist_entry_without_a_reason_is_refused():
    """Une allowlist sans motif ecrit n'est pas une justification."""
    raw = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    allowlist = raw.get("allowlist", [])
    for entry in allowlist:
        assert entry.get("reason", "").strip(), "une entree d'allowlist porte un motif"


# --------------------------------------------------------------------------
# Collecte des epinglages
# --------------------------------------------------------------------------
def test_nuget_pin_is_collected_with_or_without_space():
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook(['#r "nuget:IKVM,8.14.0"', '#r "nuget: pythonnet, 3.1.0"'])
    pins = clv.pins_from_payload(payload, manifest)
    found = {(p.library, p.version) for p in pins}
    assert ("IKVM", "8.14.0") in found
    assert ("pythonnet", "3.1.0") in found


def test_unknown_package_is_not_a_pin():
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook(['#r "nuget: ClosedXML, 0.102.3"'])
    assert clv.pins_from_payload(payload, manifest) == []


def test_local_redeclaration_of_the_series_symbol_is_collected():
    """Un carnet qui reecrit TWEETY_VERSION porte un epinglage a part entiere."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook(['TWEETY_VERSION = "1.28"', 'BASE = "https://x/"'])
    pins = clv.pins_from_payload(payload, manifest)
    local = [p for p in pins if p.ecosystem == "local_const"]
    assert len(local) == 1
    assert local[0].version == "1.28"


# --------------------------------------------------------------------------
# Controles positifs et negatifs (criteres d'acceptation de #23073)
# --------------------------------------------------------------------------
def test_positive_control_tweety_stale_pin_and_dead_path_are_red():
    """Le cas declencheur de #23047, rejoue sur une charge utile synthetique.

    Le cas CORPUS (le carnet `SymbolicAI/_archive/Tweety.ipynb` qui
    redeclarait `TWEETY_VERSION = "1.28"` et pointait sur
    `tweetyproject.org/builds/1.28/`) a ete **repare sur `main`** par #23047
    (commit `d5e44a0919d6`) : le carnet est desormais provisionne par
    l'organe de la serie, et la mention de 1.28 ne subsiste que dans un
    commentaire. Un controle positif pose sur ce carnet-la tomberait donc
    au sol sans que l'organe ait change -- c'est le symptome d'un controle
    depose sur un corpus convergent, pas d'une regression.

    Le controle est donc **rejoue sur la classe de defaut** (un carnet qui
    redeclare 1.28 ET provisionne depuis le chemin mort), ce qui garde la
    capacite de detection verifiee quelle que soit l'etat du corpus.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    assert not errors
    payload = _notebook([
        'TWEETY_VERSION = "1.28"',
        'BASE_URL = "https://tweetyproject.org/builds/1.28/"',
    ])
    pins = clv.pins_from_payload(payload, manifest)
    findings = clv.state_findings("synthetic-tweety.ipynb", pins, manifest, canonicals)
    kinds = {f["kind"] for f in findings}
    assert "foreign_provisioning" in kinds
    assert "downgrade" in kinds
    versions = {f["version"] for f in findings if f["kind"] == "downgrade"}
    assert "1.28" in versions


def test_le_cas_corpus_de_l_archive_est_repare_sur_main():
    """Le carnet archive de #23047 ne porte plus l'epinglage 1.28.

    Ce test **constate** l'etat converge du corpus (le cas declencheur a ete
    repare par #23047). Il ne fige pas une classe de defaut : si l'epinglage
    1.28 revenait un jour dans un carnet, c'est l'organe -- advisory, sur
    les carnets modifies -- qui le signalerait, et ce constat-ci devrait
    alors etre reecrit avec la nouvelle reference.
    """
    notebook = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "_archive" / "Tweety.ipynb"
    assert notebook.is_file(), "le carnet archive doit exister dans le depot"
    payload = json.loads(notebook.read_text(encoding="utf-8"))
    code = "\n".join(
        "".join(cell.get("source", []))
        for cell in payload.get("cells", [])
        if cell.get("cell_type") == "code"
    )
    assert 'TWEETY_VERSION = "1.28"' not in code, (
        "le carnet archive redeclare 1.28 : le cas declencheur de #23047 est "
        "revenu, l'argument du manifeste et le controle positif doivent etre "
        "reescrits"
    )



def test_positive_control_ikvm_814_is_red():
    """Un carnet en IKVM 8.14.0 s'ecarte de la canonique 8.15.0.

    L'ecart 8.14.0 est **justifie** (les six carnets Tweety chargent une DLL
    ombree compilee en 8.14.0) : le constat reste visible et porte son motif
    pour tout carnet qui n'est pas dans l'allowlist -- il ne disparait pas.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook(['#r "nuget:IKVM,8.14.0"'])
    findings = clv.state_findings("x.ipynb", clv.pins_from_payload(payload, manifest), manifest, canonicals)
    assert any(f["kind"] == "divergence" and f["version"] == "8.14.0" for f in findings)
    assert any(f["reason"].strip() for f in findings if f["version"] == "8.14.0")


def test_les_six_carnets_tweety_sont_allowlistes():
    """Le motif d'allowlist porte les six carnets dont l'artefact est lie a 8.14.0."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook(['#r "nuget:IKVM,8.14.0"'])
    pins = clv.pins_from_payload(payload, manifest)
    for name in ("Tweety-10-MLN-CSharp.ipynb", "Tweety-03-QBF-CSharp.ipynb"):
        assert clv.state_findings(name, pins, manifest, canonicals) == []
    assert clv.state_findings("Autre-Carnet.ipynb", pins, manifest, canonicals) != []


def test_negative_control_aligned_notebook_is_green():
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook(['#r "nuget:IKVM,8.15.0"', '#r "nuget:IKVM.Image,8.15.0"'])
    findings = clv.state_findings("x.ipynb", clv.pins_from_payload(payload, manifest), manifest, canonicals)
    assert findings == []


# --------------------------------------------------------------------------
# Semantique du delta base -> tete
# --------------------------------------------------------------------------
def test_delta_ignores_a_legacy_pin_the_pr_does_not_touch():
    """Une derive historique ne rougit pas une PR qui ne touche pas l'epinglage."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    legacy = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    head = clv.pins_from_payload(
        _notebook(['#r "nuget:IKVM,8.14.0"', 'print("contenu sans rapport")']), manifest
    )
    assert clv.delta_findings("x.ipynb", legacy, head, manifest, canonicals) == []


def test_delta_flags_a_downgrade_introduced_by_the_pr():
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = clv.pins_from_payload(_notebook(['#r "nuget:pythonnet,3.1.0"']), manifest)
    head = clv.pins_from_payload(_notebook(['#r "nuget:pythonnet,3.0.5"']), manifest)
    findings = clv.delta_findings("x.ipynb", base, head, manifest, canonicals)
    assert any(f["kind"] == "downgrade" and f["version"] == "3.0.5" for f in findings)


def test_base_illisible_est_un_incident_nomme_pas_un_carnet_neuf(tmp_path):
    """Point 6 -- base illisible et base absente ne sont pas la meme chose.

    Avant correctif, `notebook_at` rendait `None` pour les deux : un `git
    show` en echec faisait degenerer le delta en etat, et la derive
    historique rougissait sans cause nommee.
    """
    import subprocess

    repo = tmp_path / "r"
    repo.mkdir()

    def git(*args: str) -> None:
        subprocess.run(
            ["git", *args], cwd=repo, check=True, capture_output=True
        )

    git("init")
    git("config", "user.email", "t@example.invalid")
    git("config", "user.name", "t")
    (repo / "casse.ipynb").write_text("{ ceci n'est pas du JSON", encoding="utf-8")
    (repo / "sain.ipynb").write_text(
        json.dumps(_notebook(['#r "nuget:IKVM,8.15.0"'])), encoding="utf-8"
    )
    git("add", ".")
    git("commit", "-m", "x")

    # Present mais illisible : incident nomme, pas une absence.
    with pytest.raises(clv.BaseReadError):
        clv.notebook_at(repo, "HEAD", "casse.ipynb")

    # Controles positifs : absent reste une absence, et un carnet sain se lit.
    assert clv.notebook_at(repo, "HEAD", "absent.ipynb") is None
    assert clv.notebook_at(repo, "HEAD", "sain.ipynb") is not None


def test_delta_compare_les_multiplicites_pas_les_ensembles():
    """Point 5 -- un carnet a DEUX versions ne fait pas rougir une PR muette.

    Avant correctif, la base etait lue comme un ensemble : une base portant
    `{8.14.0, 8.15.0}` ne reconnaissait aucun des deux epinglages comme
    inchange, et la PR heritait d'un faux `downgrade` sur un epinglage
    qu'elle n'avait pas touche.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    # pythonnet, PAS IKVM : IKVM 8.14.0 est sur l'allowlist du manifeste
    # livre, donc il ne peut structurellement pas produire de downgrade --
    # un controle positif ecrit dessus passerait pour la mauvaise raison.
    deux_versions = ['#r "nuget:pythonnet,3.0.5"', '#r "nuget:pythonnet,3.1.0"']

    base = clv.pins_from_payload(_notebook(deux_versions), manifest)
    head = clv.pins_from_payload(_notebook(deux_versions), manifest)
    assert clv.delta_findings("x.ipynb", base, head, manifest, canonicals) == []

    # Controle positif : la PR ajoute un TROISIEME epinglage, non present en
    # base -- celui-la est bien une introduction, et doit rougir.
    head_plus = clv.pins_from_payload(
        _notebook(deux_versions + ['#r "nuget:pythonnet,3.0.5"']), manifest
    )
    findings = clv.delta_findings("x.ipynb", base, head_plus, manifest, canonicals)
    assert any(f["kind"] == "downgrade" for f in findings)


def test_delta_flags_a_new_notebook_carrying_a_divergent_pin():
    """Un carnet ajoute par la PR n'a pas de base : tous ses epinglages sont nouveaux."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    head = clv.pins_from_payload(_notebook(['#r "nuget:pythonnet,3.0.5"']), manifest)
    findings = clv.delta_findings("x.ipynb", [], head, manifest, canonicals)
    assert any(f["kind"] == "downgrade" for f in findings)


def test_delta_stays_green_when_the_pr_aligns_a_legacy_pin():
    """La convergence d'un carnet legacy vers la canonique ne doit pas rougir."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    head = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.15.0"']), manifest)
    assert clv.delta_findings("x.ipynb", base, head, manifest, canonicals) == []


def test_foreign_provisioning_is_reported_even_when_the_pr_does_not_touch_it():
    """Le provisionnement etranger pese a l'execution : il est signale sur l'etat."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    cells = ['BASE = "https://tweetyproject.org/builds/1.28/"']
    base = clv.pins_from_payload(_notebook(cells), manifest)
    head = clv.pins_from_payload(_notebook(cells + ['print("x")']), manifest)
    findings = clv.delta_findings("x.ipynb", base, head, manifest, canonicals)
    assert any(f["kind"] == "foreign_provisioning" for f in findings)


# --------------------------------------------------------------------------
# Allowlist
# --------------------------------------------------------------------------
def test_allowlist_suppresses_the_finding_for_the_named_notebook(tmp_path):
    libraries = [
        {
            "id": "IKVM",
            "ecosystem": "nuget",
            "canonical": "8.15.0",
            "canonical_source": "manifest",
        }
    ]
    allowlist = [
        {
            "library": "IKVM",
            "version": "8.14.0",
            "notebooks": ["serie/legacy.ipynb"],
            "reason": "Le carnet teste volontairement l'API 8.14 (cf issue #1234).",
        }
    ]
    manifest = _manifest_with(tmp_path, libraries, allowlist)
    canonicals, _errors = clv.resolve_canonicals(manifest, tmp_path)
    pins = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    assert clv.state_findings("serie/legacy.ipynb", pins, manifest, canonicals) == []
    assert clv.state_findings("serie/autre.ipynb", pins, manifest, canonicals) != []


# --------------------------------------------------------------------------
# Recensement
# --------------------------------------------------------------------------
def test_census_returns_rc_zero_and_reports_the_dispersion():
    manifest = clv.load_manifest(MANIFEST_PATH)
    report = clv.run_census(REPO_ROOT, manifest)
    assert report["mode"] == "census"
    assert not report["errors"]
    by_library = {lib["library"]: lib for lib in report["libraries"]}
    ikvm = by_library["IKVM"]
    assert ikvm["multiple_versions"] is True
    versions = {row["version"]: row for row in ikvm["versions"]}
    assert "8.14.0" in versions and "8.15.0" in versions
    assert versions["8.14.0"]["decision"] == "justified"
    assert versions["8.15.0"]["decision"] == "canonique"
    # le classement porte un motif ecrit
    assert versions["8.14.0"]["reason"].strip()


def test_le_recensement_ne_classe_pas_un_ecart_justifie_comme_a_converger():
    """Un ecart justifie ne doit pas apparaitre dans la liste « a converger »."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    rendered = clv.render_census(clv.run_census(REPO_ROOT, manifest))
    section = rendered.split("## IKVM ")[1].split("## ")[0]
    assert "**8.14.0**" not in section


def test_census_cli_exits_zero():
    assert clv.main(["--census", "--repo-root", str(REPO_ROOT)]) == 0


def test_le_recensement_nomme_un_carnet_illisible(tmp_path, monkeypatch):
    """Point 3 (relecture #23079) : un carnet illisible est **nomme**.

    `pins_from_file` rendait `[]` pour un carnet illisible comme pour un carnet
    sans epinglage : le recensement ne pouvait pas distinguer les deux, et le
    carnet disparaisait silencieusement de la mesure.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    broken = tmp_path / "Broken.ipynb"
    broken.write_text("{ ceci n'est pas du JSON", encoding="utf-8")
    monkeypatch.setattr(clv, "tracked_notebooks", lambda root: [broken])
    report = clv.run_census(REPO_ROOT, manifest)
    assert report["unreadable_notebooks"], "le carnet illisible doit etre nomme"
    assert broken.as_posix() in report["unreadable_notebooks"]
    rendered = clv.render_census(report)
    assert "Carnets illisibles" in rendered


def test_divergence_declaree_pour_une_version_absente_est_signalee(tmp_path):
    """Point 9 -- un fantome declare se lit comme un ecart reel.

    Cas fondeur : le manifeste livrait « dotNetRDF 3.2.0 » au classement,
    alors qu'aucun carnet du depot ne l'epinglait. Rien ne le mesurait, donc
    la doc le comptait comme une divergence a traiter.
    """
    import subprocess

    repo = tmp_path / "r"
    repo.mkdir()

    def git(*args: str) -> None:
        subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)

    git("init")
    git("config", "user.email", "t@example.invalid")
    git("config", "user.name", "t")
    (repo / "a.ipynb").write_text(
        json.dumps(_notebook(['#r "nuget:dotNetRDF,3.2.1"'])), encoding="utf-8"
    )
    git("add", ".")
    git("commit", "-m", "x")

    libraries = [
        {
            "id": "dotNetRDF",
            "ecosystem": "nuget",
            "canonical": "3.4.1",
            "canonical_source": "manifest",
            "divergences": [
                {"version": "3.2.1", "decision": "to_converge", "reason": "r"},
                {"version": "3.2.0", "decision": "to_converge", "reason": "r"},
            ],
        }
    ]
    report = clv.run_census(repo, _manifest_with(tmp_path, libraries))
    # Controle positif : l'ecart reellement epingle n'est pas un fantome.
    assert [p["version"] for p in report["phantom_divergences"]] == ["3.2.0"]
    assert "Divergences declarees mais absentes" in clv.render_census(report)

    # Et le carnet livre ne porte plus de fantome.
    shipped = clv.run_census(REPO_ROOT, clv.load_manifest(MANIFEST_PATH))
    assert shipped["phantom_divergences"] == []


# --------------------------------------------------------------------------
# Cablage dans la voie rapide
# --------------------------------------------------------------------------
def _registry():
    sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
    import fast_lane_registry as registry

    return registry


def test_guard_is_registered_as_advisory():
    """Le garde est enregistre, en advisory, et son nom porte la mention."""
    registry = _registry()
    guards = {g.name: g for g in registry.TRANCHE31}
    guard = guards["Library versions guard (advisory, #23073)"]
    assert guard.blocking is False
    assert guard.needs_base is True
    assert "advisory" in guard.name.lower()
    assert "scripts/notebook_tools/check_lib_versions.py" in " ".join(guard.argv)


def test_guard_is_aggregated_by_the_fast_lane_engine():
    """Un groupe non cable n'est jamais execute : le geste doit etre dans l'engine."""
    engine = (REPO_ROOT / "scripts" / "ci" / "fast_lane.py").read_text(encoding="utf-8")
    assert "TRANCHE31" in engine, "le groupe TRANCHE31 n'est pas cable dans fast_lane.py"


# --------------------------------------------------------------------------
# Mentions residuelles de version (corpus desynchronise)
# --------------------------------------------------------------------------
def _notebook_with(cells: list[dict]) -> dict:
    """Carnet minimal a cellules libres (markdown, sorties)."""
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code(source: str, outputs: list[dict] | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "metadata": {},
        "outputs": outputs or [],
    }


def _markdown(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source], "metadata": {}}


# --------------------------------------------------------------------------
# Fixture explicite pour les tests de MENTIONS
#
# Un test de mention ne doit pas dependre de l'etat courant du manifeste
# LIVRE. Le manifeste livre declare les ecarts REELS du corpus : la
# convergence de `pythonnet` (#23073) a retire 3.0.5 de ses divergences --
# ce carnet ne l'epingle plus -- donc un test adosse au manifeste livre ne
# mordrait plus : il passerait sans jamais signaler de mention, et
# l'echec qu'il doit.watch serait invisible.
#
# Le fixture declare donc explicitement l'ecart surveille. Meme convention
# que `_LIB_IKVM` plus bas, et meme raison qu'il y donne : « un test qui
# passe sans declencher son constat ne prouve rien ».
# --------------------------------------------------------------------------
_LIB_PYTHONNET_AVEC_ECART = [
    {
        "id": "pythonnet",
        "ecosystem": "nuget",
        "canonical": "3.1.0",
        "canonical_source": "manifest",
        "divergences": [
            {
                "version": "3.0.5",
                "decision": "to_converge",
                "reason": "ecart surveille par le fixture",
            },
        ],
    },
    {
        "id": "dotNetRDF",
        "ecosystem": "nuget",
        "canonical": "3.4.1",
        "canonical_source": "manifest",
        "divergences": [],
    },
]


def test_une_mention_de_version_perimee_dans_la_prose_est_relevee(tmp_path):
    """La prose qui annonce l'ancienne version est un constat, meme si l'epinglage est a jour."""
    manifest = _manifest_with(tmp_path, _LIB_PYTHONNET_AVEC_ECART)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code('#r "nuget: pythonnet, 3.1.0"'),
        _markdown("On utilise pythonnet 3.0.5 dans ce carnet."),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert any(
        f["kind"] == "mention_residuelle" and f["version"] == "3.0.5"
        for f in findings
    )


def test_la_ligne_depinglage_n_est_pas_une_mention(tmp_path):
    """La ligne qui porte l'epinglage n'est pas une mention : elle est l'epinglage."""
    manifest = _manifest_with(tmp_path, _LIB_PYTHONNET_AVEC_ECART)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([_code('#r "nuget: pythonnet, 3.0.5"')])
    assert clv.mention_findings("x.ipynb", payload, manifest, canonicals) == []


def test_les_lignes_depinglage_de_deux_bibliotheques_ne_sont_pas_des_mentions():
    """Point 1 (relecture #23079) : l'exclusion des lignes d'epinglage est
    library-agnostique.

    Deux epinglages voisins dans la meme cellule (`IKVM` et `IKVM.Image` en
    8.14.0, hors allowlist) faisaient deux constats `mention_residuelle` qui
    etaient precisement les deux lignes d'epinglage : le jeton de version de
    l'une etait attribue a l'autre.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code('#r "nuget: IKVM, 8.14.0"\n#r "nuget: IKVM.Image, 8.14.0"'),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert findings == [], findings


def test_une_mention_en_prose_reste_relevee_apres_le_correction_des_lignes_depinglage():
    """Controle positif : l'exclusion elargie ne doit pas eteindre la prose.

    La meme cellule epingle deux bibliotheques, et une cellule markdown
    annonce la version perimee : le constat de prose doit rester.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code('#r "nuget: IKVM, 8.14.0"\n#r "nuget: IKVM.Image, 8.14.0"'),
        _markdown("Note : l'artefact ombre est compile contre IKVM 8.14.0 (version figee)."),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert any(f["kind"] == "mention_residuelle" for f in findings), findings


def test_une_sortie_affichant_une_version_perimee_est_relevee(tmp_path):
    """Le bandeau « Installed Packages » affiche la version reellement chargee."""
    manifest = _manifest_with(tmp_path, _LIB_PYTHONNET_AVEC_ECART)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code(
            '#r "nuget: pythonnet, 3.1.0"',
            [{"output_type": "stream", "text": ["pythonnet 3.0.5" + chr(10)]}],
        ),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert any(f["kind"] == "mention_residuelle" for f in findings)


def test_une_mention_d_un_carnet_sans_epinglage_de_cette_bibliotheque_est_ignoree(
    tmp_path,
):
    """Le perimetre est borne : on ne parle que des bibliotheques que le carnet epingle."""
    manifest = _manifest_with(tmp_path, _LIB_PYTHONNET_AVEC_ECART)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code('#r "nuget: pythonnet, 3.1.0"'),
        _markdown("Un autre sujet : dotNetRDF 3.2.1 est cite ici."),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert all(f["library"] == "pythonnet" for f in findings)


def test_le_delta_ignore_une_mention_deja_presente(tmp_path):
    """Une mention deja presente et non touchee par la PR est une derive historique."""
    manifest = _manifest_with(tmp_path, _LIB_PYTHONNET_AVEC_ECART)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = _notebook_with([
        _code('#r "nuget: pythonnet, 3.1.0"'),
        _markdown("On utilise pythonnet 3.0.5 dans ce carnet."),
    ])
    head = _notebook_with([
        _code('#r "nuget: pythonnet, 3.1.0"'),
        _markdown("On utilise pythonnet 3.0.5 dans ce carnet."),
        _code('print("contenu sans rapport")'),
    ])
    assert clv.delta_mention_findings(
        "x.ipynb", base, head, manifest, canonicals
    ) == []


def test_le_delta_releve_une_mention_introduite_par_la_pr(tmp_path):
    manifest = _manifest_with(tmp_path, _LIB_PYTHONNET_AVEC_ECART)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = _notebook_with([_code('#r "nuget: pythonnet, 3.1.0"')])
    head = _notebook_with([
        _code('#r "nuget: pythonnet, 3.1.0"'),
        _markdown("On utilise pythonnet 3.0.5 dans ce carnet."),
    ])
    findings = clv.delta_mention_findings(
        "x.ipynb", base, head, manifest, canonicals
    )
    assert any(f["kind"] == "mention_residuelle" for f in findings)


def test_une_mention_autorisee_est_supprimee():
    """L'allowlist porte aussi les mentions : le motif vaut pour la prose."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code('#r "nuget: IKVM, 8.15.0"'),
        _markdown("Historique : ce carnet a utilise IKVM 8.14.0."),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert all(f["version"] != "8.14.0" for f in findings)


# --------------------------------------------------------------------------
# Relecture coordinateur #23079 -- points 1, 2 et 11
#
# Ces trois tests portent chacun leur controle positif : sans lui, ils
# passeraient aussi sur un organe qui refuse tout, ou sur un organe qui
# n'eteint jamais rien.
# --------------------------------------------------------------------------
_LIB_IKVM = [
    {
        "id": "IKVM",
        "ecosystem": "nuget",
        "canonical": "8.15.0",
        "canonical_source": "manifest",
    }
]


def test_allowlist_sans_motif_refuse_le_manifeste(tmp_path):
    """Point 1 -- une entree d'allowlist sans motif ecrit rend rc 2.

    Le test d'origine (``test_allowlist_entry_without_a_reason_is_refused``)
    parcourait le manifeste LIVRE ; il ne mordait pas tant que celui-ci
    portait ``"allowlist": []``. Celui-ci exerce le comportement sur une
    fixture, donc il mord quel que soit l'etat du manifeste livre.
    """
    sans_motif = _manifest_with(
        tmp_path,
        _LIB_IKVM,
        [{"library": "IKVM", "version": "8.14.0", "reason": "   "}],
    )
    erreurs = clv.allowlist_errors(sans_motif)
    assert erreurs, "une entree sans motif doit etre refusee"
    assert "motif absent ou vide" in erreurs[0]

    # Controle positif : le meme manifeste avec un motif ecrit passe.
    avec_motif = _manifest_with(
        tmp_path,
        _LIB_IKVM,
        [{"library": "IKVM", "version": "8.14.0", "reason": "DLL ombree liee a 8.14.0."}],
    )
    assert clv.allowlist_errors(avec_motif) == []

    # Et une allowlist vide reste valide (le cas du manifeste d'origine).
    assert clv.allowlist_errors(_manifest_with(tmp_path, _LIB_IKVM, [])) == []


def test_allowlist_sans_motif_n_eteint_pas_le_constat(tmp_path):
    """Point 1, seconde barriere -- meme sans la validation, le constat tient."""
    manifest = _manifest_with(
        tmp_path,
        _LIB_IKVM,
        [{"library": "IKVM", "version": "8.14.0", "reason": ""}],
    )
    assert clv._allowlisted(manifest, "IKVM", "8.14.0", "serie/x.ipynb") is None

    # Controle positif : avec un motif, la meme entree eteint bien le constat.
    manifest_ok = _manifest_with(
        tmp_path,
        _LIB_IKVM,
        [{"library": "IKVM", "version": "8.14.0", "reason": "motif ecrit"}],
    )
    assert clv._allowlisted(manifest_ok, "IKVM", "8.14.0", "serie/x.ipynb") == "motif ecrit"


def test_carnet_illisible_rend_rc_deux(tmp_path, capsys):
    """Point 2 -- un carnet illisible ne doit pas rendre du vert silencieux.

    Avant correctif, ``pins_from_file`` rendait ``[]`` sur ``JSONDecodeError``
    et le rapport annoncait « les carnets examines sont alignes ».
    """
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps({"schema_version": 1, "libraries": _LIB_IKVM, "allowlist": []}),
        encoding="utf-8",
    )
    casse = tmp_path / "casse.ipynb"
    casse.write_text("{ ceci n'est pas du JSON", encoding="utf-8")

    rc = clv.main([
        str(casse),
        "--repo-root", str(tmp_path),
        "--manifest", str(manifest_path),
    ])
    assert rc == 2
    assert "illisible" in capsys.readouterr().err

    # Controle positif : un carnet valide et aligne ne rend PAS 2.
    sain = _write_notebook(tmp_path, "sain.ipynb", ['#r "nuget:IKVM,8.15.0"'])
    rc_sain = clv.main([
        str(sain),
        "--repo-root", str(tmp_path),
        "--manifest", str(manifest_path),
    ])
    assert rc_sain == 0


def test_version_prefixe_v_et_composantes_manquantes():
    """Point 7 -- `v` decore l'ecriture, et une composante absente vaut zero."""
    # `v8.15.0` et `8.15.0` sont la meme version (avant : faux upgrade).
    assert clv.compare_versions("v8.15.0", "8.15.0") == 0
    # `8.15` et `8.15.0` sont la meme version (avant : faux downgrade).
    assert clv.compare_versions("8.15", "8.15.0") == 0
    # `1.0.0.0` et `1.0.0` sont la meme version (avant : faux upgrade).
    assert clv.compare_versions("1.0.0.0", "1.0.0") == 0

    # Controles positifs : l'ordre REEL reste tranche par les nombres.
    assert clv.compare_versions("8.14.0", "8.15.0") < 0
    assert clv.compare_versions("v8.16.0", "8.15.0") > 0
    assert clv.compare_versions("9.11.4210", "9.15.6755") < 0


def test_carnet_hors_depot_rend_rc_deux_nomme(tmp_path, capsys):
    """Point 11 -- un carnet hors de la racine est un rc 2 nomme, sans traceback.

    Le test exerce le CHEMIN D'APPEL (``main`` sur un chemin explicite), pas
    seulement l'utilitaire : c'est le site d'appel qui portait le defaut, et
    tester l'utilitaire seul aurait passe avant le correctif.
    """
    depot = tmp_path / "depot"
    depot.mkdir()
    manifest_path = depot / "manifest.json"
    manifest_path.write_text(
        json.dumps({"schema_version": 1, "libraries": _LIB_IKVM, "allowlist": []}),
        encoding="utf-8",
    )
    # Le carnet vit HORS de la racine passee a l'organe.
    hors = _write_notebook(tmp_path, "hors.ipynb", ['#r "nuget:IKVM,8.15.0"'])
    assert not str(hors).startswith(str(depot))

    rc = clv.main([
        str(hors),
        "--repo-root", str(depot),
        "--manifest", str(manifest_path),
    ])
    # Un carnet hors du depot n'est pas un carnet de la famille : la
    # relecture demande un rc 2 **nomme** (point 11), pas un rc 1 de
    # traceback. Le message doit dire ce qui ne va pas.
    assert rc == 2
    err = capsys.readouterr().err
    assert "hors du depot" in err
    assert "Traceback" not in err

    # Controle positif : l'utilitaire reste relatif dans le depot.
    dedans = depot / "serie" / "x.ipynb"
    assert clv._relative_to_repo(dedans, depot) == "serie/x.ipynb"


# --------------------------------------------------------------------------
# Points de revue traites par le troisieme commit (les points 1, 2, 7 et 11
# ont ete traites par le commit voisin b19f0ad68a8 -- voir le commentaire
# point par point de la PR).
# --------------------------------------------------------------------------
def test_un_manifeste_avec_allowlist_sans_motif_rend_rc_deux(tmp_path, capsys):
    """Point 1 : le refus se traduit par un rc 2 nomme, pas par un traceback."""
    path = tmp_path / "manifest.json"
    path.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "libraries": [],
                "allowlist": [{"library": "IKVM", "version": "8.14.0"}],
            }
        ),
        encoding="utf-8",
    )
    assert clv.main(["--manifest", str(path), "--repo-root", str(tmp_path)]) == 2
    assert "motif absent ou vide" in capsys.readouterr().err


def test_un_carnet_illisible_rend_rc_deux_et_non_un_vert(tmp_path, capsys):
    """Point 2 : un carnet illisible est un incident nomme (rc 2).

    Le rendre « aligne » produirait un vert silencieux sur un carnet que
    l'organe n'a pas reellement lu.
    """
    broken = tmp_path / "casse.ipynb"
    broken.write_text("{ ceci n'est pas du json", encoding="utf-8")
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "libraries": _LIB_IKVM,
                "allowlist": [],
            }
        ),
        encoding="utf-8",
    )
    assert (
        clv.main(
            [
                "--manifest",
                str(manifest_path),
                "--repo-root",
                str(tmp_path),
                str(broken),
            ]
        )
        == 2
    )
    assert "illisible" in capsys.readouterr().err


def test_le_manifeste_couvre_un_ecosysteme_pip():
    """Point 3 : pip est annonce dans la doc, donc il existe au manifeste."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    pip_libs = [
        lib for lib in manifest.libraries.values() if lib.ecosystem == "pip"
    ]
    assert pip_libs, "le manifeste doit porter au moins une bibliotheque pip"
    assert all(lib.canonical for lib in pip_libs)


def test_un_epinglage_pip_est_releve_et_compare_a_la_canonique():
    """Point 3 : le chemin pip n'est pas mort.

    La bibliotheque pip du manifeste est **exercee par le corpus** : ses
    declarations sont en cellules code, donc l'organe les voit.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    pip_lib = next(
        lib for lib in manifest.libraries.values() if lib.ecosystem == "pip"
    )
    payload = _notebook([f"pip install {pip_lib.id}=={pip_lib.canonical}"])
    pins = clv.pins_from_payload(payload, manifest)
    assert any(p.library == pip_lib.id and p.version == pip_lib.canonical for p in pins)
    findings = clv.state_findings("x.ipynb", pins, manifest, canonicals)
    assert findings == [], "le pin pip est a la version canonique"


def test_le_pin_pip_du_corpus_est_vraiment_relu():
    """Etat honnete du corpus pip apres #23104.

    Avant #23104 l'organe ne lisait que les cellules code : il rendait un
    corpus pip **vide**, alors que deux carnets declarent l'installation de
    mealpy dans une cellule markdown. Les deux declarations sont **non
    versionnees** (epinglage flottant) : aucune ne fixe 3.0.2. Le manifeste ne
    doit donc porter aucun epinglage versionne, et exactement ces deux
    declarations flottantes.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    report = clv.run_census(REPO_ROOT, manifest)
    pip_libs = [
        lib for lib in report["libraries"] if lib["ecosystem"] == "pip"
    ]
    assert pip_libs, "le manifeste doit porter une bibliotheque pip"
    for lib in pip_libs:
        assert lib["versions"] == [], (
            "aucun carnet ne doit epingler une version pip exacte : "
            f"{lib['library']} porte {lib['versions']}"
        )
        assert lib["floating_notebooks"] == [
            "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-11-Metaheuristics.ipynb",
            "MyIA.AI.Notebooks/Sudoku/Sudoku-05-PSO-Python.ipynb",
        ], (
            "les deux declarations markdown de mealpy doivent etre vues : "
            f"{lib['library']} porte {lib['floating_notebooks']}"
        )
        assert "hors perimetre de l'organe" not in (lib["note"] or ""), (
            "la note ne doit plus decrire le markdown comme hors perimetre"
        )


def test_les_quatre_formes_de_commande_pip_sont_reconnues():
    """#23104 : `pip`, `pip3`, `python -m pip` et `uv pip` sont des commandes.

    L'organe ne reconnaissait que la premiere : les six lignes
    `python -m pip install ...` du corpus (torch, transformers) n'etaient pas
    des declarations pour lui.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    for command in (
        "pip install mealpy==3.0.2",
        "pip3 install mealpy==3.0.2",
        "python -m pip install mealpy==3.0.2",
        "python3 -m pip install mealpy==3.0.2",
        "uv pip install mealpy==3.0.2",
        "!pip install mealpy==3.0.2",
        "%pip install mealpy==3.0.2",
    ):
        pins = clv.pins_from_payload(_notebook([command]), manifest)
        assert [p.version for p in pins] == ["3.0.2"], command


def test_une_declaration_markdown_est_lue_et_la_prose_ne_l_est_pas():
    """#23104 : le markdown est lu **sur ses lignes-commandes seulement**.

    Mesure du corpus : 36 lignes-commandes ancrees contre 114 mentions en
    prose. Une phrase qui cite la commande, ou un `print` qui l'imprime, n'est
    pas une declaration et ne doit pas etre relevee.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = {
        "cells": [
            {
                "cell_type": "markdown",
                "source": ["Installez avec `pip install mealpy==3.0.2` :\n"],
                "metadata": {},
            },
            {
                "cell_type": "markdown",
                "source": ["pip install mealpy==3.0.2\n"],
                "metadata": {},
            },
            {
                "cell_type": "code",
                "source": ["print('pip install mealpy==3.0.2')\n"],
                "metadata": {},
                "outputs": [],
            },
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    pins = clv.pins_from_payload(payload, manifest)
    assert len(pins) == 1, [(p.library, p.version, p.cell_type) for p in pins]
    pin = pins[0]
    assert (pin.library, pin.version, pin.cell) == ("mealpy", "3.0.2", 1)
    assert pin.cell_type == "markdown", "la provenance doit etre portee par le pin"


def test_une_version_pip_citee_en_prose_n_est_pas_un_epinglage():
    """Point 2 : une version citee dans un commentaire ou dans une chaine
    n'est pas une commande d'installation -- donc pas un epinglage.

    Cas mesure sur le corpus : `pip install mealpy==3.0.2` dans un commentaire
    C# et dans un `print` Python, alors que la commande reelle du corpus
    (`pip install mealpy numpy matplotlib`) ne fixe aucune version.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook([
        'print("mealpy non installe (pip install mealpy==3.0.2)")',
        '// installe qui importe mealpy (pip install mealpy==3.0.2)',
    ])
    pins = clv.pins_from_payload(payload, manifest)
    assert not [p for p in pins if p.library == "mealpy"], pins


def test_un_epinglage_pip_sans_version_produit_un_constat_nomme():
    """Point 2 : une installation pip sans version est un epinglage flottant.

    Le constat existe deja pour NuGet (#23086) ; il manquait pour pip, ou le
    corpus installait mealpy sans fixer la version.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook(["pip install mealpy numpy matplotlib"])
    pins = clv.pins_from_payload(payload, manifest)
    assert any(p.library == "mealpy" and p.version == "" for p in pins), pins
    findings = clv.state_findings("x.ipynb", pins, manifest, canonicals)
    assert any(f["kind"] == "pin_non_versionne" for f in findings), findings


def test_le_delta_compare_les_multiplicites_et_non_les_ensembles():
    """Point 5 : un carnet qui porte deux versions d'une bibliotheque ne
    produit pas de faux downgrade quand la PR n'y touche pas."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = clv.pins_from_payload(
        _notebook(['#r "nuget:IKVM,8.14.0"', '#r "nuget:IKVM,8.15.0"']), manifest
    )
    head = clv.pins_from_payload(
        _notebook(
            ['#r "nuget:IKVM,8.14.0"', '#r "nuget:IKVM,8.15.0"', 'print("x")']
        ),
        manifest,
    )
    assert clv.delta_findings("x.ipynb", base, head, manifest, canonicals) == []


def test_le_delta_signale_un_epinglage_supprime_et_remplace_par_un_autre():
    """Point 5 (contraire) : un deuxieme pin de la meme version est bien nouveau."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = clv.pins_from_payload(_notebook(['#r "nuget:pythonnet,3.1.0"']), manifest)
    head = clv.pins_from_payload(
        _notebook(['#r "nuget:pythonnet,3.1.0"', '#r "nuget:pythonnet,3.0.5"']),
        manifest,
    )
    findings = clv.delta_findings("x.ipynb", base, head, manifest, canonicals)
    assert any(f["kind"] == "downgrade" and f["version"] == "3.0.5" for f in findings)


def test_les_formes_de_pin_non_versionne_et_avec_prefixe_v_sont_lues():
    """Point 8 : prefixe `v`, forme a flux, et epinglage flottant."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook(
        [
            '#r "nuget: IKVM, v8.15.0"',
            '#r "nuget: IKVM.Image, 8.15.0, https://flux.example/ikvm"',
            '#r "nuget: SkiaSharp"',
        ]
    )
    pins = clv.pins_from_payload(payload, manifest)
    versions = {(p.library, p.version) for p in pins}
    assert ("IKVM", "8.15.0") in versions
    assert ("IKVM.Image", "8.15.0") in versions
    # Un pin flottant est conserve (version vide), pas jete.
    assert ("SkiaSharp", "") in versions


def test_un_epinglage_flottant_produit_un_constat_nomme():
    """Point 8 : le pin flottant est signale, avec le renvoi a #23086."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    pins = clv.pins_from_payload(_notebook(['#r "nuget: Google.OrTools"']), manifest)
    findings = clv.state_findings("x.ipynb", pins, manifest, canonicals)
    assert any(f["kind"] == "pin_non_versionne" for f in findings)
    assert any("#23086" in f["reason"] for f in findings)


def test_un_pin_flottant_deja_present_ne_rougit_pas_la_pr():
    """Point 8 : un pin flottant historique reste une derive, pas un rouge."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = clv.pins_from_payload(_notebook(['#r "nuget: Google.OrTools"']), manifest)
    head = clv.pins_from_payload(
        _notebook(['#r "nuget: Google.OrTools"', 'print("x")']), manifest
    )
    assert clv.delta_findings("x.ipynb", base, head, manifest, canonicals) == []


def test_le_provisionnement_etranger_est_cable_par_bibliotheque(tmp_path):
    """Point 10 : les motifs vivent au manifeste, pas sous un ecosysteme unique."""
    libraries = [
        {
            "id": "Contoso",
            "ecosystem": "nuget",
            "canonical": "1.0.0",
            "canonical_source": "manifest",
            "foreign_provisioning": [
                {
                    "pattern": "contoso\\.invalid/",
                    "reason": "Source hors de l'organe de serie.",
                }
            ],
        }
    ]
    manifest = _manifest_with(tmp_path, libraries)
    payload = _notebook(['BASE = "https://contoso.invalid/1.0.0/"'])
    pins = clv.pins_from_payload(payload, manifest)
    assert any(p.ecosystem == "provisioning" for p in pins)


def test_la_sortie_json_annonce_le_mode_etat_en_mode_chemins_explicites(
    tmp_path, capsys
):
    """Le mode « chemins explicites » est un mode d'etat : la sortie le dit."""
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "libraries": _LIB_IKVM,
                "allowlist": [],
            }
        ),
        encoding="utf-8",
    )
    notebook = tmp_path / "nb.ipynb"
    notebook.write_text(
        json.dumps(_notebook(['#r "nuget: IKVM, 8.15.0"'])), encoding="utf-8"
    )
    rc = clv.main(
        [
            "--json",
            "--manifest",
            str(manifest_path),
            "--repo-root",
            str(tmp_path),
            "nb.ipynb",
        ]
    )
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["state"] is True
    assert payload["checked"] == 1


def test_le_recensement_compte_les_epinglages_flottants():
    """Point 8 : le recensement expose les pins flottants (ils ne sont pas
    « aucune version pour cette bibliotheque »)."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    report = clv.run_census(REPO_ROOT, manifest)
    by_library = {lib["library"]: lib for lib in report["libraries"]}
    assert by_library["Google.OrTools"]["floating_notebooks"], (
        "le corpus contient des epinglages OrTools sans version"
    )


# --------------------------------------------------------------------------
# #23103 -- artefacts charges depuis un chemin (binaires et sources)
# --------------------------------------------------------------------------
def _git_repo(tmp_path: Path) -> Path:
    """Depot git minimal : `_tracked_paths` interroge git, pas le disque."""
    root = tmp_path.resolve() / "depot"
    root.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["git", "init", "-q"], cwd=root, check=True, capture_output=True
    )
    return root


def _repo_with(tmp_path: Path, cells: list[str], submodules: list[str] | None = None) -> Path:
    root = _git_repo(tmp_path)
    if submodules:
        root.joinpath(".gitmodules").write_text(
            "".join(
                f'[submodule "{path}"]\n\tpath = {path}\n\turl = https://exemple/{i}\n'
                for i, path in enumerate(submodules)
            ),
            encoding="utf-8",
        )
    return root


def _touch(root: Path, relative: str, track: bool) -> None:
    target = root / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(b"artefact")
    if track:
        subprocess.run(
            ["git", "add", "-f", "--", relative],
            cwd=root,
            check=True,
            capture_output=True,
        )


def test_binary_detector_distinguishes_path_from_assembly_name():
    """`#r "System.Text.Json"` n'est pas un chargement depuis un chemin."""
    assert not clv._looks_like_a_path("System.Text.Json")
    assert clv._looks_like_a_path("./libs/Tweety.jar")
    assert clv._looks_like_a_path("Tweety.dll")
    assert not clv._looks_like_a_path("")


def test_package_reference_is_not_a_binary_load(tmp_path):
    """`#r "nuget: X, v"` est un epinglage de paquet, pas un chemin."""
    payload = _notebook(['#r "nuget: IKVM, 8.15.0"'])
    root = _repo_with(tmp_path, [])
    assert clv.binary_loads("series/nb.ipynb", payload, root) == []


def test_binary_outside_the_repository_is_reported(tmp_path):
    """Chemin absolu hors depot : absent apres un clone (point 1)."""
    root = _repo_with(tmp_path, ['#r "/opt/ailleurs/Tweety.jar"'])
    found = clv.binary_findings("series/nb.ipynb", _notebook(['#r "/opt/ailleurs/Tweety.jar"']), root)
    assert [item["kind"] for item in found] == ["binary_hors_depot"]
    assert found[0]["library"] == "Tweety.jar"


def test_relative_path_escaping_the_repository_is_reported(tmp_path):
    """Un `../..` qui sort du depot est exactement le cas a voir (point 1)."""
    payload = _notebook(['#load "../../../evade/Tweety.jar"'])
    root = _repo_with(tmp_path, [])
    found = clv.binary_findings("series/sub/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_hors_depot"]


def test_binary_from_a_submodule_is_legitimate(tmp_path):
    """Cas legitime (a) : le binaire est produit par un sous-module du depot."""
    payload = _notebook(['#r "libs/MetaGeneticSharp.Domain.dll"'])
    root = _repo_with(tmp_path, [], submodules=["series/libs"])
    assert clv.binary_findings("series/nb.ipynb", payload, root) == []


def test_binary_versioned_in_the_repository_is_legitimate(tmp_path):
    """Cas legitime (b) : l'artefact est versionne, donc present apres un clone."""
    root = _repo_with(tmp_path, [])
    _touch(root, "series/libs/Tweety.dll", track=True)
    payload = _notebook(['#r "libs/Tweety.dll"'])
    assert clv.binary_findings("series/nb.ipynb", payload, root) == []


def test_binary_ignored_by_git_is_reported(tmp_path):
    """Dans le depot mais ignore par git : absent apres un clone (point 1)."""
    root = _repo_with(tmp_path, [])
    _touch(root, "series/libs/Tweety.dll", track=False)
    payload = _notebook(['#r "libs/Tweety.dll"'])
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_non_versionne"]


def test_declared_download_with_checksum_satisfies_the_reproduction_gate(tmp_path):
    """Point 3 : URL + empreinte declarees, le constat disparait."""
    root = _repo_with(tmp_path, [])
    _touch(root, "series/libs/Tweety.dll", track=False)
    payload = _notebook(
        [
            '#r "libs/Tweety.dll"',
            f'URL = "https://exemple/builds/Tweety.dll"\nSHA256 = "{SHA256_DIGEST}"',
        ]
    )
    assert clv.binary_findings("series/nb.ipynb", payload, root) == []


def test_declared_download_with_a_placeholder_checksum_is_still_reported(tmp_path):
    """Reserve NanoClaw (#24943) : `SHA256 = "abc123"` n'est pas une empreinte.

    La forme historique acceptait le seul marqueur `sha256`, si bien qu'une
    valeur bidon satisfaisait le contrat faible et court-circuitait la
    directive `archive`, qui exige un digest valide. Le marqueur doit
    desormais s'accompagner d'un digest de 64 hexadecimaux.
    """
    root = _repo_with(tmp_path, [])
    _touch(root, "series/libs/Tweety.dll", track=False)
    payload = _notebook(
        [
            '#r "libs/Tweety.dll"',
            'URL = "https://exemple/builds/Tweety.dll"\nSHA256 = "abc123"',
        ]
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]


def test_a_digest_without_a_checksum_marker_is_not_a_checksum(tmp_path):
    """Un digest seul ne declare pas un mecanisme de verification.

    Le contrat est la conjonction : marqueur de mecanisme (`sha256`,
    `Get-FileHash`, ...) **et** digest. Un identifiant de 64 hexadecimaux sans
    marqueur peut etre autre chose qu'une empreinte de fichier.
    """
    root = _repo_with(tmp_path, [])
    _touch(root, "series/libs/Tweety.dll", track=False)
    payload = _notebook(
        [
            '#r "libs/Tweety.dll"',
            f'URL = "https://exemple/builds/Tweety.dll"\nID = "{SHA256_DIGEST}"',
        ]
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]


def test_declared_download_without_checksum_is_still_reported(tmp_path):
    """Un telechargement sans empreinte ne rend pas la version reproductible."""
    root = _repo_with(tmp_path, [])
    _touch(root, "series/libs/Tweety.dll", track=False)
    payload = _notebook(
        ['#r "libs/Tweety.dll"', 'URL = "https://exemple/builds/Tweety.dll"']
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]


def test_checksum_declared_for_another_artifact_does_not_lift_the_finding(tmp_path):
    """Cas croise (reserve Hermes, #24520) : l'empreinte est par ARTEFACT.

    Deux artefacts sont declares, un seul porte une empreinte : le constat de
    l'autre doit rester. Avant le fix, `has_checksum` etait un booleen par
    carnet -- l'empreinte de Tweety.dll levait aussi le constat de Autre.dll.
    """
    root = _repo_with(tmp_path, [])
    _touch(root, "series/libs/Tweety.dll", track=False)
    _touch(root, "series/libs/Autre.dll", track=False)
    payload = _notebook(
        [
            '#r "libs/Tweety.dll"\n#r "libs/Autre.dll"',
            f'URL = "https://exemple/builds/Tweety.dll"\nSHA256 = "{SHA256_DIGEST}"',
            'URL = "https://exemple/builds/Autre.dll"',
        ]
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]
    assert found[0]["library"] == "Autre.dll"


def _archive_directive(
    *,
    artifact: str = "archive/QuikGraph.dll",
    entry: str = "lib/netstandard2.0/QuikGraph.dll",
    checksum: str = "2cde56fdd6e3b10eb89b2ee90a7c4cb39af446e6f0f6fee09268a48e9ea9731f",
) -> str:
    """Directive archive du témoin QuikGraph, sans télécharger le paquet."""
    return (
        "<!-- reproduction: "
        + json.dumps(
            {
                "kind": "archive",
                "artifact": artifact,
                "url": (
                    "https://api.nuget.org/v3-flatcontainer/quikgraph/2.5.0/"
                    "quikgraph.2.5.0.nupkg"
                ),
                "version": "2.5.0",
                "entry": entry,
                "sha256": checksum,
            },
            separators=(",", ":"),
        )
        + " -->"
    )


def _notebook_with_reproduction(load: str, directive: str) -> dict:
    payload = _notebook([load])
    payload["cells"].append(
        {"cell_type": "markdown", "source": [directive], "metadata": {}}
    )
    return payload


def test_archive_entry_and_checksum_satisfy_the_reproduction_gate(tmp_path):
    """Le nom du paquet ne se substitue pas à l'entrée DLL extraite (#24943)."""
    root = _repo_with(tmp_path, [])
    payload = _notebook_with_reproduction(
        '#r "./_deps/QuikGraph.dll"', _archive_directive()
    )
    assert clv.binary_findings("series/nb.ipynb", payload, root) == []


def test_archive_without_checksum_is_still_reported(tmp_path):
    root = _repo_with(tmp_path, [])
    payload = _notebook_with_reproduction(
        '#r "./_deps/QuikGraph.dll"', _archive_directive(checksum="")
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]
    assert "archive exige URL, version, entree et empreinte" in found[0]["reason"]


def test_archive_checksum_of_another_entry_does_not_lift_the_finding(tmp_path):
    """L'empreinte reste attachée à l'artefact ET au basename de l'entrée."""
    root = _repo_with(tmp_path, [])
    payload = _notebook_with_reproduction(
        '#r "./_deps/QuikGraph.dll"',
        _archive_directive(entry="lib/netstandard2.0/Autre.dll"),
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]


def test_archive_requires_a_valid_sha256(tmp_path):
    root = _repo_with(tmp_path, [])
    payload = _notebook_with_reproduction(
        '#r "./_deps/QuikGraph.dll"', _archive_directive(checksum="abc123")
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]


def _build_directive(project: str) -> str:
    return (
        "<!-- reproduction: "
        + json.dumps(
            {
                "kind": "build",
                "artifact": "build/MyIA.AI.Shared.dll",
                "command": f"dotnet build {project} -c Release",
                "project": project,
            },
            separators=(",", ":"),
        )
        + " -->"
    )


def test_build_recipe_with_tracked_project_satisfies_the_gate(tmp_path):
    """Le projet versionné atteste la présence de la recette après un clone."""
    root = _repo_with(tmp_path, [])
    project = "MyIA.AI.Shared/MyIA.AI.Shared.csproj"
    _touch(root, project, track=True)
    payload = _notebook_with_reproduction(
        '#r "../../../MyIA.AI.Shared/bin/Release/net9.0/MyIA.AI.Shared.dll"',
        _build_directive(project),
    )
    assert clv.binary_findings("series/sub/nb.ipynb", payload, root) == []


def test_build_recipe_with_untracked_project_is_still_reported(tmp_path):
    """Une commande qui nomme un fichier absent du clone n'est pas une preuve."""
    root = _repo_with(tmp_path, [])
    project = "MyIA.AI.Shared/MyIA.AI.Shared.csproj"
    _touch(root, project, track=False)
    payload = _notebook_with_reproduction(
        '#r "../../../MyIA.AI.Shared/bin/Release/net9.0/MyIA.AI.Shared.dll"',
        _build_directive(project),
    )
    found = clv.binary_findings("series/sub/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]
    assert "projet suivi par git" in found[0]["reason"]


def test_build_recipe_cannot_escape_the_repository(tmp_path):
    root = _repo_with(tmp_path, [])
    payload = _notebook_with_reproduction(
        '#r "./MyIA.AI.Shared.dll"',
        _build_directive("../ailleurs/MyIA.AI.Shared.csproj"),
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_sans_empreinte"]


def test_malformed_reproduction_directive_fails_closed(tmp_path):
    root = _repo_with(tmp_path, [])
    payload = _notebook_with_reproduction(
        '#r "./QuikGraph.dll"',
        '<!-- reproduction: {"kind":"archive","artifact":"archive/QuikGraph.dll" -->',
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_non_versionne"]


def test_archive_url_does_not_accidentally_match_the_legacy_url_form(tmp_path):
    """Un .nupkg n'est pas la DLL : sans empreinte, l'archive reste signalée."""
    root = _repo_with(tmp_path, [])
    payload = _notebook_with_reproduction(
        '#r "./_deps/QuikGraph.dll"', _archive_directive(checksum="")
    )
    found = clv.binary_findings("series/nb.ipynb", payload, root)
    assert found[0]["library"] == "QuikGraph.dll"


@pytest.mark.parametrize(
    "line, form",
    [
        ('#r "./libs/Tweety.dll"', "#r"),
        ('#load "./libs/Tweety.dll"', "#load"),
        ("%classpath add jar ./libs/Tweety.jar", "%classpath"),
        ("Add-Type -Path ./libs/Tweety.dll", "Add-Type"),
        ('clr.AddReference("./libs/Tweety.dll")', "clr.AddReference"),
        ('Assembly.LoadFrom("./libs/Tweety.dll")', "Assembly.Load"),
        ("pip install ./dist/Tweety-1.0.whl", "pip-fichier"),
    ],
)
def test_every_load_form_is_scanned(line: str, form: str):
    """Le balayage couvre toutes les formes, pas seulement `#r` (scope note)."""
    payload = _notebook([line])
    loads = clv.binary_loads("series/nb.ipynb", payload, Path.cwd())
    assert [load.form for load in loads] == [form]


def test_markdown_prose_citing_a_load_form_is_not_a_finding(tmp_path):
    """Une forme ecrite en markdown est de la prose, pas une ligne executee."""
    payload = {
        "cells": [
            {"cell_type": "markdown", "source": ['#r "/opt/ailleurs/Tweety.jar"']},
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    root = _repo_with(tmp_path, [])
    assert clv.binary_findings("series/nb.ipynb", payload, root) == []


def test_source_file_load_is_labelled_as_source_not_binary(tmp_path):
    """`#load "./Init.csx"` charge une source : le motif ne dit pas « binaire »."""
    root = _repo_with(tmp_path, [])
    payload = _notebook(['#load "../Init.csx"'])
    found = clv.binary_findings("series/sub/nb.ipynb", payload, root)
    assert [item["kind"] for item in found] == ["binary_non_versionne"]
    assert "le fichier source est dans le depot mais ignore par git" in found[0]["reason"]


def test_census_exposes_binary_findings(tmp_path):
    """Le recensement porte la section, avec la cellule et le chemin."""
    root = _repo_with(tmp_path, [])
    notebook = _write_notebook(root, "nb.ipynb", ['#r "/opt/ailleurs/Tweety.jar"'])
    subprocess.run(
        ["git", "add", "-f", "--", "nb.ipynb"], cwd=root, check=True, capture_output=True
    )
    assert notebook.exists()
    report = clv.run_census(root, _manifest_with(tmp_path, []))
    assert [item["kind"] for item in report["binary_findings"]] == ["binary_hors_depot"]


# --- Imputation du constat binaire au delta (#23103) ---------------------
#
# Un chargement hors depot deja present dans la base n'est pas impute a la PR :
# c'est l'etat du carnet, il se lit au recensement. Sans ce delta, toucher un
# carnet deja fautif rendrait la PR rouge pour un defaut qu'elle n'a pas cree.


def test_binary_finding_present_in_the_base_is_not_imputed_to_the_pr(tmp_path):
    """Meme chargement en base et a la tete : la PR ne porte pas le constat."""
    root = _repo_with(tmp_path, [])
    cell = '#r "/opt/ailleurs/Tweety.jar"'
    base_payload = _notebook([cell])
    head_payload = _notebook([cell, "print(1)"])
    assert (
        clv.delta_binary_findings("nb.ipynb", base_payload, head_payload, root) == []
    )


def test_binary_load_added_by_the_pr_is_imputed(tmp_path):
    """Chargement ajoute par la PR : le constat tombe sur la PR."""
    root = _repo_with(tmp_path, [])
    base_payload = _notebook(["print(1)"])
    head_payload = _notebook(["print(1)", '#r "/opt/ailleurs/Tweety.jar"'])
    found = clv.delta_binary_findings("nb.ipynb", base_payload, head_payload, root)
    assert [item["kind"] for item in found] == ["binary_hors_depot"]
    # `path` porte le chemin resolu, qui suit la racine du disque courant sous
    # Windows : on assertit sur le nom de l'artefact, pas sur le prefixe.
    assert found[0]["library"].endswith("Tweety.jar")


def test_new_notebook_reports_all_its_binary_findings(tmp_path):
    """Carnet neuf : il n'y a pas de base, donc tout constat lui est impute."""
    root = _repo_with(tmp_path, [])
    head_payload = _notebook(['#r "/opt/ailleurs/Tweety.jar"'])
    found = clv.delta_binary_findings("nb.ipynb", None, head_payload, root)
    assert [item["kind"] for item in found] == ["binary_hors_depot"]


# --------------------------------------------------------------------------
# Canonique par serie (torch, numpy) -- #23073
# --------------------------------------------------------------------------
def _notebook_with_outputs(outputs: list[str]) -> dict:
    """Carnet dont les cellules portent des sorties de type flux."""
    return {
        "cells": [
            {
                "cell_type": "code",
                "source": ["print(1)"],
                "metadata": {},
                "outputs": [
                    {"output_type": "stream", "name": "stdout", "text": [text]}
                ],
            }
            for text in outputs
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def test_series_prefix_covers_a_sub_series_but_not_a_sibling():
    """La frontiere d'un prefixe de serie est un SEGMENT, pas une chaine."""
    assert clv._series_covers(
        "RL", "MyIA.AI.Notebooks/RL/RL-06-DQN-Policy-Gradient-Python.ipynb"
    )
    assert clv._series_covers(
        "RL", "MyIA.AI.Notebooks/RL/PostTraining/RLPT-02-GRPO-Minimal-Python.ipynb"
    )
    assert not clv._series_covers("RL", "MyIA.AI.Notebooks/RLance/RL-01.ipynb")


def test_series_path_normalises_the_notebooks_root_prefix():
    """Ecrit avec ou sans la racine des series, c'est la meme serie."""
    assert clv.series_path("MyIA.AI.Notebooks/RL/RL-01.ipynb") == "RL/RL-01.ipynb"
    assert clv.series_path("RL/RL-01.ipynb") == "RL/RL-01.ipynb"


def test_la_canonique_par_serie_prime_sur_la_canonique_unique(tmp_path):
    manifest = _manifest_with(
        tmp_path,
        [
            {
                "id": "torch",
                "ecosystem": "observed",
                "observe_outputs": True,
                "canonical": "1.0.0",
                "canonical_by_series": [
                    {"series": "RL", "canonical": "2.13.0"},
                    {"series": "RL/PostTraining", "canonical": "2.14.0"},
                ],
            }
        ],
    )
    resolver = clv.CanonicalResolver(manifest, tmp_path)
    assert (
        resolver.for_notebook("torch", "MyIA.AI.Notebooks/RL/RL-06-DQN.ipynb")
        == "2.13.0"
    )
    # Le prefixe le plus long gagne : PostTraining decrit une sous-serie plus
    # fine que RL.
    assert (
        resolver.for_notebook(
            "torch", "MyIA.AI.Notebooks/RL/PostTraining/RLPT-02.ipynb"
        )
        == "2.14.0"
    )
    # Une serie non couverte retombe sur la canonique unique.
    assert (
        resolver.for_notebook("torch", "MyIA.AI.Notebooks/ML/ML-01.ipynb")
        == "1.0.0"
    )


def test_artifact_source_lit_le_pin_de_la_serie(tmp_path):
    """Le manifeste POINTE vers l'artefact : il ne recopie pas la valeur."""
    (tmp_path / "requirements.txt").write_text(
        "# un commentaire\ntorch==2.14.0\n", encoding="utf-8"
    )
    manifest = _manifest_with(
        tmp_path,
        [
            {
                "id": "torch",
                "ecosystem": "observed",
                "observe_outputs": True,
                "canonical_by_series": [
                    {
                        "series": "ML/04-Vision",
                        "canonical_source": "artifact",
                        "organ_path": "requirements.txt",
                    }
                ],
            }
        ],
    )
    resolver = clv.CanonicalResolver(manifest, tmp_path)
    assert (
        resolver.for_notebook("torch", "MyIA.AI.Notebooks/ML/04-Vision/4.5.ipynb")
        == "2.14.0"
    )
    assert resolver.errors == []


def test_artifact_source_accepte_un_plancher(tmp_path):
    """Un `>=` est un plancher : la contrainte dit ce qu'elle est."""
    (tmp_path / "requirements.txt").write_text(
        "torch>=2.0   # Reseaux de neurones\nnumpy>=1.24\n", encoding="utf-8"
    )
    manifest = _manifest_with(
        tmp_path,
        [
            {
                "id": "numpy",
                "ecosystem": "observed",
                "observe_outputs": True,
                "canonical_by_series": [
                    {
                        "series": "RL",
                        "canonical_source": "artifact",
                        "organ_path": "requirements.txt",
                    }
                ],
            }
        ],
    )
    resolver = clv.CanonicalResolver(manifest, tmp_path)
    assert (
        resolver.for_notebook("numpy", "MyIA.AI.Notebooks/RL/RL-06.ipynb")
        == "1.24"
    )


def test_artifact_source_absent_est_une_erreur_nommee(tmp_path):
    manifest = _manifest_with(
        tmp_path,
        [
            {
                "id": "torch",
                "ecosystem": "observed",
                "observe_outputs": True,
                "canonical_by_series": [
                    {
                        "series": "RL",
                        "canonical_source": "artifact",
                        "organ_path": "requirements.txt",
                    }
                ],
            }
        ],
    )
    resolver = clv.CanonicalResolver(manifest, tmp_path)
    assert resolver.errors, "un artefact absent doit etre signale"
    assert "introuvable" in resolver.errors[0]


def test_observed_versions_lit_les_formes_reelles_du_corpus(tmp_path):
    manifest = _manifest_with(
        tmp_path,
        [{"id": "torch", "ecosystem": "observed", "observe_outputs": True}],
    )
    payload = _notebook_with_outputs(
        [
            "torch 2.13.0+cu126\n",
            "torch=2.8.0+cu126\n",
            "torch        : 2.6.0+cu124 (cuda 12.4)\n",
            '"torch_version": "2.14.0+cu126",\n',
            "Imports OK : gymnasium 1.3.0, torch 2.11.0+cu126\n",
        ]
    )
    observed = clv.observed_versions_from_payload(payload, manifest)
    assert {version for _cell, _line, version in observed["torch"]} == {
        "2.13.0",
        "2.8.0",
        "2.6.0",
        "2.14.0",
        "2.11.0",
    }


def test_les_metriques_ne_sont_pas_des_versions(tmp_path):
    """`2.22e-16` et `0.4014` sont des mesures, pas des versions.

    Cas mesure : `3.2-Optimisateurs.ipynb` affiche « ecart max apres 1 pas
    NumPy vs torch = 2.22e-16 » et `3.3-Regularisation.ipynb` affiche
    « numpy=0.4014 | torch=0.4007 ». Un motif de version trop permissif les
    confondrait avec des versions chargees.
    """
    manifest = _manifest_with(
        tmp_path,
        [
            {"id": "torch", "ecosystem": "observed", "observe_outputs": True},
            {"id": "numpy", "ecosystem": "observed", "observe_outputs": True},
        ],
    )
    payload = _notebook_with_outputs(
        [
            "ecart max apres 1 pas NumPy vs torch = 2.22e-16\n",
            "numpy=0.4014 | torch=0.4007\n",
        ]
    )
    assert clv.observed_versions_from_payload(payload, manifest) == {}


def test_le_tag_de_construction_local_ne_compte_pas_comme_un_recul():
    """`2.14.0+cu126` est la MEME release que `2.14.0`.

    Le comparateur de versions traite un suffixe `+` comme un marqueur de
    pre-publication : sans normalisation, `2.14.0+cu126` serait classe en
    dessous de `2.14.0` -- un faux recul sur la quasi-totalite des carnets.
    """
    assert clv._base_version("2.14.0+cu126") == "2.14.0"
    assert clv.compare_versions("2.14.0+cu126", "2.14.0") < 0
    assert clv.compare_versions(clv._base_version("2.14.0+cu126"), "2.14.0") == 0


def _rl_resolver(tmp_path: Path, canonical: str = "2.13.0"):
    manifest = _manifest_with(
        tmp_path,
        [
            {
                "id": "torch",
                "ecosystem": "observed",
                "observe_outputs": True,
                "canonical_by_series": [
                    {"series": "RL", "canonical": canonical}
                ],
            }
        ],
    )
    return manifest, clv.CanonicalResolver(manifest, tmp_path)


def test_le_constat_signale_un_recul_de_charge(tmp_path):
    """Cas #23941 : le carnet est re-execute sous une version inferieure."""
    manifest, resolver = _rl_resolver(tmp_path)
    payload = _notebook_with_outputs(["torch 2.9.0+cu126\n"])
    findings = clv.observed_findings(
        "MyIA.AI.Notebooks/RL/RL-06-DQN-Policy-Gradient-Python.ipynb",
        payload,
        manifest,
        resolver,
    )
    assert len(findings) == 1
    assert findings[0]["kind"] == "downgrade"
    assert findings[0]["version"] == "2.9.0"
    assert findings[0]["canonical"] == "2.13.0"


def test_une_version_superieure_au_plancher_n_est_pas_un_defaut(tmp_path):
    """La serie converge vers le haut : 2.14 sur un plancher de 2.13 est sain."""
    manifest, resolver = _rl_resolver(tmp_path)
    payload = _notebook_with_outputs(["torch 2.14.0+cu126\n"])
    findings = clv.observed_findings(
        "MyIA.AI.Notebooks/RL/RL-06-DQN-Policy-Gradient-Python.ipynb",
        payload,
        manifest,
        resolver,
    )
    assert findings == []


def test_le_delta_ne_signale_pas_une_derive_historique(tmp_path):
    """La 2.6 etait deja la en base : elle ne pese pas sur la PR."""
    manifest, resolver = _rl_resolver(tmp_path)
    base = _notebook_with_outputs(["torch 2.6.0+cu124\n"])
    head = _notebook_with_outputs(["torch 2.6.0+cu124\n", "print(2)\n"])
    assert (
        clv.delta_observed_findings(
            "MyIA.AI.Notebooks/RL/RLPT-02-GRPO-Minimal-Python.ipynb",
            base,
            head,
            manifest,
            resolver,
        )
        == []
    )


def test_le_delta_signale_un_recul_introduit_par_la_pr(tmp_path):
    """La PR fait passer le carnet de 2.14.0 a 2.9.0 : le constat tombe."""
    manifest, resolver = _rl_resolver(tmp_path)
    base = _notebook_with_outputs(["torch 2.14.0+cu126\n"])
    head = _notebook_with_outputs(["torch 2.9.0+cu126\n"])
    findings = clv.delta_observed_findings(
        "MyIA.AI.Notebooks/RL/RL-06-DQN-Policy-Gradient-Python.ipynb",
        base,
        head,
        manifest,
        resolver,
    )
    assert [item["version"] for item in findings] == ["2.9.0"]


def test_le_recensement_liste_les_carnets_en_dessous_de_la_canonique(
    tmp_path, monkeypatch
):
    manifest = _manifest_with(
        tmp_path,
        [
            {
                "id": "torch",
                "ecosystem": "observed",
                "observe_outputs": True,
                "canonical_by_series": [
                    {"series": "RL", "canonical": "2.13.0"}
                ],
            }
        ],
    )
    folder = tmp_path / "MyIA.AI.Notebooks" / "RL"
    folder.mkdir(parents=True)
    notebook = folder / "RLPT-02-GRPO-Minimal-Python.ipynb"
    notebook.write_text(
        json.dumps(_notebook_with_outputs(["torch 2.6.0+cu124\n"])),
        encoding="utf-8",
    )
    monkeypatch.setattr(clv, "tracked_notebooks", lambda root: [notebook])
    report = clv.run_census(tmp_path, manifest)
    below = report["below_canonical"]
    assert len(below) == 1
    assert below[0]["version"] == "2.6.0"
    assert below[0]["canonical"] == "2.13.0"
    assert below[0]["series"] == "RL"
    rendered = clv.render_census(report)
    assert "Carnets en dessous de la canonique de leur serie" in rendered


def test_versioned_fallbacks_distinguish_code_from_prose():
    payload = _notebook([
        '''try:
    import example
except ImportError:
    print("Skipped: Example 1.28+ API change")
    print("Skipped: unavailable")
    print("Example version 1.28 available")
    # print("Skipped: Example 1.28")
    text = "Skipped: Example 1.28"
    def later():
        print("Skipped: Example 1.28")
''',
        '"""except ImportError: print("Skipped: Example 1.28")"""',
        'print("Skipped: Example 1.28")',
    ])
    payload["cells"].append({"cell_type": "markdown", "source": "Skipped 1.28"})
    found = clv.versioned_fallbacks("x.ipynb", payload)
    assert len(found) == 1
    assert found[0]["cell"] == 0 and found[0]["line"] == 4
    assert found[0]["message"] == "Skipped: Example 1.28+ API change"


def test_versioned_fallback_advisory_in_text_and_json(tmp_path, capsys):
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"schema_version": 1, "libraries": [], "allowlist": []}))
    _write_notebook(tmp_path, "nb.ipynb", [
        'try:\n    import example\nexcept ImportError:\n    print("Skipped: Example 1.28")\n'
    ])
    args = ["--manifest", str(manifest), "--repo-root", str(tmp_path), "nb.ipynb"]
    assert clv.main(args + ["--json"]) == 0
    report = json.loads(capsys.readouterr().out)
    assert report["findings"] == []
    assert report["advisories"][0]["kind"] == "repli_versionne"
    assert clv.main(args) == 0
    output = capsys.readouterr().out
    assert "Avis non bloquants" in output
    assert "Skipped: Example 1.28" in output


def test_versioned_fallback_is_advisory_in_changed_mode(tmp_path, capsys, monkeypatch):
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"schema_version": 1, "libraries": [], "allowlist": []}))
    notebook = _write_notebook(tmp_path, "nb.ipynb", [
        'try:\n    import example\nexcept ImportError:\n    print("Skipped: Example 1.28")\n'
    ])
    monkeypatch.setattr(clv, "changed_notebooks", lambda root, revision: ([notebook], "base"))
    monkeypatch.setattr(clv, "notebook_at", lambda root, revision, relative: _notebook([]))
    rc = clv.main(["--changed", "base...HEAD", "--json", "--manifest", str(manifest),
                   "--repo-root", str(tmp_path)])
    report = json.loads(capsys.readouterr().out)
    assert rc == 0 and report["findings"] == []
    assert report["advisories"][0]["notebook"] == "nb.ipynb"
