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
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
TOOLS_DIR = REPO_ROOT / "scripts" / "notebook_tools"
sys.path.insert(0, str(TOOLS_DIR))

import check_lib_versions as clv  # noqa: E402

MANIFEST_PATH = TOOLS_DIR / "lib_versions_manifest.json"


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
def test_positive_control_tweety_archive_is_red():
    """Le carnet archive de #23047 porte 1.28 et un chemin de provisionnement mort."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    assert not errors
    notebook = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "_archive" / "Tweety.ipynb"
    assert notebook.is_file(), "le carnet archive doit exister dans le depot"
    pins = clv.pins_from_file(notebook, manifest)
    findings = clv.state_findings(notebook.as_posix(), pins, manifest, canonicals)
    kinds = {f["kind"] for f in findings}
    assert "foreign_provisioning" in kinds
    assert "downgrade" in kinds
    versions = {f["version"] for f in findings if f["kind"] == "downgrade"}
    assert "1.28" in versions


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
    guards = {g.name: g for g in registry.TRANCHE29}
    guard = guards["Library versions guard (advisory, #23073)"]
    assert guard.blocking is False
    assert guard.needs_base is True
    assert "advisory" in guard.name.lower()
    assert "scripts/notebook_tools/check_lib_versions.py" in " ".join(guard.argv)


def test_guard_is_aggregated_by_the_fast_lane_engine():
    """Un groupe non cable n'est jamais execute : le geste doit etre dans l'engine."""
    engine = (REPO_ROOT / "scripts" / "ci" / "fast_lane.py").read_text(encoding="utf-8")
    assert "TRANCHE29" in engine, "le groupe TRANCHE29 n'est pas cable dans fast_lane.py"


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


def test_une_mention_de_version_perimee_dans_la_prose_est_relevee():
    """La prose qui annonce l'ancienne version est un constat, meme si l'epinglage est a jour."""
    manifest = clv.load_manifest(MANIFEST_PATH)
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


def test_la_ligne_depinglage_n_est_pas_une_mention():
    """La ligne qui porte l'epinglage n'est pas une mention : elle est l'epinglage."""
    manifest = clv.load_manifest(MANIFEST_PATH)
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


def test_une_sortie_affichant_une_version_perimee_est_relevee():
    """Le bandeau « Installed Packages » affiche la version reellement chargee."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code(
            '#r "nuget: pythonnet, 3.1.0"',
            [{"output_type": "stream", "text": ["pythonnet 3.0.5" + chr(10)]}],
        ),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert any(f["kind"] == "mention_residuelle" for f in findings)


def test_une_mention_d_un_carnet_sans_epinglage_de_cette_bibliotheque_est_ignoree():
    """Le perimetre est borne : on ne parle que des bibliotheques que le carnet epingle."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook_with([
        _code('#r "nuget: pythonnet, 3.1.0"'),
        _markdown("Un autre sujet : dotNetRDF 3.2.1 est cite ici."),
    ])
    findings = clv.mention_findings("x.ipynb", payload, manifest, canonicals)
    assert all(f["library"] == "pythonnet" for f in findings)


def test_le_delta_ignore_une_mention_deja_presente():
    """Une mention deja presente et non touchee par la PR est une derive historique."""
    manifest = clv.load_manifest(MANIFEST_PATH)
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


def test_le_delta_releve_une_mention_introduite_par_la_pr():
    manifest = clv.load_manifest(MANIFEST_PATH)
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
    """Point 2 (relecture #23079) : l'etat honnete du corpus pip.

    La mention 3.0.2 du paquet mealpy n'apparait que dans la **prose** (un
    commentaire C# et un `print` Python) ; sa seule commande d'installation
    est ecrite dans une cellule markdown, donc hors perimetre de l'organe.
    L'entree de manifeste ne doit donc pas pretendre que le corpus declare
    cette version : ni epinglage versionne, ni epinglage flottant.
    """
    manifest = clv.load_manifest(MANIFEST_PATH)
    report = clv.run_census(REPO_ROOT, manifest)
    pip_libs = [
        lib for lib in report["libraries"] if lib["ecosystem"] == "pip"
    ]
    assert pip_libs, "le manifeste doit porter une bibliotheque pip"
    for lib in pip_libs:
        assert lib["versions"] == [], (
            "aucun carnet ne doit epingler une version pip : "
            f"{lib['library']} porte {lib['versions']}"
        )
        assert lib["floating_notebooks"] == [], (
            "aucune commande d'installation pip en cellule code : "
            f"{lib['library']} porte {lib['floating_notebooks']}"
        )
        assert "s'accordent" not in (lib["note"] or ""), (
            "la note ne doit pas pretendre que le corpus declare la version"
        )


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
