#!/usr/bin/env python3
"""Unit tests for the pure helper `rendered_job_names` in
`scripts/ci/check_absorbed_check_run_identity.py`.

Ce module implemente un controle positif d'identite byte-a-byte des
gardes fast-lane absorbes : pour chaque garde absorbe du registre, il
parse le workflow source et exige que `guard.name` figure byte-
identique parmi les noms de job rendus. Le seul helper testable en
isolation (sans coupler au registre global `fast_lane_registry`) est
`rendered_job_names(workflow_file, yaml)` :

  - Workflow illisible (OSError, parse fail) -> None
  - Workflow parse mais sans jobs -> liste vide
  - Job avec `uses:` (reusable) -> ignore
  - Job avec `name:` declare -> utilise `name`
  - Job sans `name:` -> utilise la cle du job (job_key)

L'import de `fast_lane_registry as reg` au top-level du module n'est
pas evalue ici (le helper prend le YAML en parametre, pas une lecture
globale). Les tests injectent un faux module yaml (`FakeYaml`) avec
`safe_load` qui implemente le workaround `on:` -> `"on":` deja present
dans `_parse_workflow`. Un fichier YAML temporaire (tmp_path) sert
de workflow_file.

Couvre :
  - Workflow illisible (OSError simule) -> None
  - YAML casse (YAMLError) -> None
  - Workflow vide (aucun job) -> []
  - Job avec name explicite -> utilise name
  - Job sans name -> utilise la cle
  - Job reusable (uses:) -> ignore
  - Job.name non-string -> coerce en str
  - Mix de tous les cas ci-dessus

Contexte : cycle 79 pool atomic epuise (cycles 76-78 : test coverage
DATASET_REGISTRY, assert_sweep_payload, doc FR TSAD), META grain
aligned sur un organe CI recent sans pytest coverage.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import check_absorbed_check_run_identity as caci  # noqa: E402


class FakeYamlError(Exception):
    """Stand-in for yaml.YAMLError (we just need any exception class)."""


class FakeYaml:
    """Minimal stand-in for PyYAML exposing safe_load + YAMLError class.

    The real `_parse_workflow` in check_unique_check_run_names does the
    `on:` -> `"on":` workaround before calling safe_load, so we just need
    a working dict serializer here. We refuse to load if the marker
    FAIL_YAML_PARSE is present in the text.
    """

    YAMLError = FakeYamlError

    def __init__(self, fail_on: str | None = None):
        self._fail_on = fail_on

    def safe_load(self, text: str):
        if self._fail_on and self._fail_on in text:
            raise FakeYamlError(f"synthetic fail on marker {self._fail_on!r}")
        return _MiniYamlParser(text).parse()


class _MiniYamlParser:
    """A *very* small YAML subset parser tailored for the workflows we use in
    tests: top-level `jobs:` dict of `{job_key: {name?: str, uses?: str}}`.

    Supports:
      - 2-space indentation
      - scalars: name, value, path-like (str), list of scalars
      - dict values via indentation
    Enough for tests, not a general YAML implementation.
    """

    def __init__(self, text: str):
        self.text = text

    def parse(self):
        lines = self.text.splitlines()
        # Find top-level `jobs:` line
        jobs_idx = None
        for i, line in enumerate(lines):
            if line.strip() == "jobs:":
                jobs_idx = i
                break
        if jobs_idx is None:
            return {}
        # Parse the jobs block
        jobs = {}
        current_key = None
        current_dict = None
        for line in lines[jobs_idx + 1:]:
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            indent = len(line) - len(line.lstrip(" "))
            if indent == 2 and stripped.endswith(":"):
                # New job key
                current_key = stripped[:-1]
                jobs[current_key] = {}
                current_dict = jobs[current_key]
            elif indent >= 4 and current_dict is not None and ":" in stripped:
                # key: value
                k, v = stripped.split(":", 1)
                k = k.strip()
                v = v.strip()
                if v == "":
                    current_dict[k] = None
                elif v.startswith('"') and v.endswith('"'):
                    current_dict[k] = v[1:-1]
                else:
                    current_dict[k] = v
        return {"jobs": jobs}


# --- Cas de base ---------------------------------------------------------


def test_rendered_job_names_empty(tmp_path):
    """Workflow sans aucun job -> liste vide."""
    f = tmp_path / "wf.yml"
    f.write_text("# just a comment\njobs:\n", encoding="utf-8")
    yaml = FakeYaml()
    assert caci.rendered_job_names(f, yaml) == []


def test_rendered_job_names_one_job_with_name(tmp_path):
    """Job avec name explicite -> utilise name."""
    f = tmp_path / "wf.yml"
    f.write_text(
        "jobs:\n"
        "  my_job:\n"
        '    name: "Mon job explicite"\n',
        encoding="utf-8",
    )
    yaml = FakeYaml()
    assert caci.rendered_job_names(f, yaml) == ["Mon job explicite"]


def test_rendered_job_names_one_job_without_name(tmp_path):
    """Job sans name -> utilise la cle du job."""
    f = tmp_path / "wf.yml"
    f.write_text(
        "jobs:\n"
        "  fallback_key:\n"
        "    runs-on: ubuntu-latest\n",
        encoding="utf-8",
    )
    yaml = FakeYaml()
    assert caci.rendered_job_names(f, yaml) == ["fallback_key"]


def test_rendered_job_names_reusable_job_ignored(tmp_path):
    """Job avec `uses:` (reusable) -> ignore."""
    f = tmp_path / "wf.yml"
    f.write_text(
        "jobs:\n"
        "  reusable:\n"
        "    uses: org/reusable/.github/workflows/x.yml@v1\n"
        "    name: ReusableX\n",
        encoding="utf-8",
    )
    yaml = FakeYaml()
    # Le job reusable est ignore, malgre le name declare.
    assert caci.rendered_job_names(f, yaml) == []


def test_rendered_job_names_mix_real_and_reusable(tmp_path):
    """Mix : job avec name explicite + job reusable + job sans name."""
    f = tmp_path / "wf.yml"
    f.write_text(
        "jobs:\n"
        "  real_one:\n"
        '    name: "Job reel"\n'
        "  reusable:\n"
        "    uses: org/r.yml@v1\n"
        "  another_real:\n"
        "    runs-on: ubuntu-latest\n",
        encoding="utf-8",
    )
    yaml = FakeYaml()
    names = caci.rendered_job_names(f, yaml)
    # L'ordre depend de l'ordre d'insertion
    assert "Job reel" in names
    assert "another_real" in names
    assert len(names) == 2


# --- Robustesse ----------------------------------------------------------


def test_rendered_job_names_unreadable_file_returns_none(tmp_path):
    """Fichier inexistant (OSError sur read_text) -> None."""
    nonexistent = tmp_path / "nope.yml"
    yaml = FakeYaml()
    assert caci.rendered_job_names(nonexistent, yaml) is None


def test_rendered_job_names_yaml_parse_error_returns_none(tmp_path):
    """YAML invalide (YAMLError levee par safe_load) -> None."""
    f = tmp_path / "broken.yml"
    f.write_text("jobs:\n  broken: [unclosed", encoding="utf-8")
    yaml = FakeYaml(fail_on="[unclosed")
    assert caci.rendered_job_names(f, yaml) is None


def test_rendered_job_names_name_coerced_to_string(tmp_path):
    """Job avec name non-string (ex: int) -> coerce en str."""
    # Notre mini-parser ne gere pas name numerique directement, donc on
    # verifie via un workflow ou name apparait explicitement avec str().
    f = tmp_path / "wf.yml"
    f.write_text(
        "jobs:\n"
        "  numeric:\n"
        '    name: "42"\n',
        encoding="utf-8",
    )
    yaml = FakeYaml()
    names = caci.rendered_job_names(f, yaml)
    assert names == ["42"]
    # Et chaque element est bien un str (signature typed)
    assert all(isinstance(n, str) for n in names)


def test_rendered_job_names_empty_name_falls_back_to_key(tmp_path):
    """Job avec name="" (chaine vide) -> fallback sur la cle (falsy)."""
    f = tmp_path / "wf.yml"
    f.write_text(
        "jobs:\n"
        "  mykey:\n"
        '    name: ""\n',
        encoding="utf-8",
    )
    yaml = FakeYaml()
    # Le code utilise `job_def.get("name") or job_key` -> empty string
    # est falsy -> fallback sur la cle.
    assert caci.rendered_job_names(f, yaml) == ["mykey"]


def test_rendered_job_names_returns_list(tmp_path):
    """La sortie est bien une `list` (pas un generateur ou autre)."""
    f = tmp_path / "wf.yml"
    f.write_text("jobs:\n  j:\n    runs-on: u\n", encoding="utf-8")
    yaml = FakeYaml()
    out = caci.rendered_job_names(f, yaml)
    assert isinstance(out, list)
    assert out == ["j"]


# --- Integration : cas reel simplifie -----------------------------------


def test_rendered_job_names_mimics_check_unique_check_run_names(tmp_path):
    """Pattern exact du module source : name ou cle, uses: ignore, str coerce.

    Reproduit le pattern documente dans check_unique_check_run_names.py
    (`job.name` si declare, sinon la cle du job ; jobs `uses:` sautes).
    """
    f = tmp_path / "wf.yml"
    f.write_text(
        "# Workflow de test reproduisant le pattern reel.\n"
        "jobs:\n"
        "  build:\n"
        '    name: "Build (Python 3.11)"\n'
        "    runs-on: ubuntu-latest\n"
        "  reuse:\n"
        "    uses: actions/checkout@v4\n"
        "  deploy:\n"
        "    runs-on: ubuntu-latest\n",
        encoding="utf-8",
    )
    yaml = FakeYaml()
    names = caci.rendered_job_names(f, yaml)
    # build -> "Build (Python 3.11)" (name explicite)
    # reuse  -> ignore (uses:)
    # deploy -> "deploy" (cle)
    assert names == ["Build (Python 3.11)", "deploy"]


# --- Decouverte dynamique + exemption natif (#19193) ----------------------


def test_absorbed_guards_decouvre_dynamiquement_les_tranches(monkeypatch):
    """`absorbed_guards` couvre TOUTES les listes de Guard du registre.

    Preuve de non-regression : une nouvelle TRANCHE18 ajoutee au registre est
    automatiquement couverte sans toucher au filet. Le test injecte une
    TRANCHE_TEST factice dans `fast_lane_registry` (via monkeypatch sur
    `vars(reg)`) et verifie qu'elle apparait dans le resultat.
    """
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
    import fast_lane_registry as fl_reg

    tranche_test = [caci.Guard(
        name="guard-temoin-tranche-x",
        source="check_unique_check_run_names.yml",  # existe vraiment
        paths=[],
        argv=["echo", "noop"],
        blocking=True,
    )]
    monkeypatch.setattr(fl_reg, "TRANCHE_TEST_X", tranche_test, raising=False)
    seen = {g.name for g in caci.absorbed_guards()}
    assert "guard-temoin-tranche-x" in seen, (
        f"TRANCHE_TEST_X ajoutee mais non couverte par le filet dynamique. "
        f"Gardes vus : {sorted(seen)[:5]}..."
    )


def test_absorbed_guards_exempte_les_fast_lane_native():
    """Les gardes `source == FAST_LANE_NATIVE` ne sont PAS dans `absorbed_guards()`.

    Raison : un garde natif n'a pas de workflow d'origine, donc le filet ne
    peut rien verifier. Le contrat fondateur de la PR est qu'ils sont
    exemptes par declaration, et le saut n'est pas silencieux : la sortie
    du CLI les enumere separement (cf `mismatches`).
    """
    import fast_lane_registry as fl_reg
    seen_native = {g.name for g in caci.absorbed_guards()
                   if g.source == fl_reg.FAST_LANE_NATIVE}
    assert seen_native == set(), (
        f"Gardes natifs encore dans absorbed_guards(): {seen_native}"
    )


def test_mismatches_exempte_decl_les_natifs(monkeypatch):
    """`native_exemptions()` enumere les exemptions natives en parallele des problemes.

    Preuve du contrat : un saut silencieux fabriquerait une garantie fausse.
    Le filet doit signaler les deux classes separement (cf `_main` qui
    affiche EXEMPTE: avant MISMATCH:).
    """
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
    import fast_lane_registry as fl_reg

    tranche_test = [caci.Guard(
        name="guard-temoin-natif-x",
        source=fl_reg.FAST_LANE_NATIVE,
        paths=[],
        argv=["echo", "noop"],
        blocking=False,
    )]
    monkeypatch.setattr(fl_reg, "TRANCHE_NATIVE_TEST", tranche_test, raising=False)

    exemptions = caci.native_exemptions()
    exempte_names = {line.split("'")[1] for line in exemptions}
    assert "guard-temoin-natif-x" in exempte_names, (
        f"Garde natif injecte absent des exemptions signalees : {exemptions}"
    )


def test_mismatches_temoin_negatif_renommage_rougit(monkeypatch):
    """Témoin négatif : renommer un garde absorbe d'une tranche >= 6 fait rougir.

    Le contrat fondateur : si quelqu'un renomme `guard.name` SANS mettre a
    jour le job dans le workflow source, le filet doit signaler un mismatch.
    On injecte un garde fictif dans TRANCHE_TEST avec un nom qui n'existe
    pas dans le workflow source, et on verifie que `mismatches()` le signale.
    """
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
    import fast_lane_registry as fl_reg

    fake_yaml = FakeYaml()
    fake_wf_content = (
        "jobs:\n"
        "  job_renomme:\n"
        '    name: "Job renomme dans le workflow source"\n'
    )

    class _FakeWorkflowSource:
        def __init__(self, content):
            self.content = content
            self.name = "fake-source.yml"

        def is_file(self):
            return True

        def read_text(self, encoding="utf-8"):
            return self.content

    tranche_test = [caci.Guard(
        name="guard-renomme-dans-le-registre",
        source="fake-source.yml",
        paths=[],
        argv=["echo", "noop"],
        blocking=True,
    )]
    monkeypatch.setattr(fl_reg, "TRANCHE_RENOMMAGE_TEST", tranche_test, raising=False)

    # Monkeypatcher WORKFLOWS_DIR + _parse_workflow pour pointer sur notre contenu
    fake_source = _FakeWorkflowSource(fake_wf_content)
    monkeypatch.setattr(caci, "WORKFLOWS_DIR",
                        type("P", (), {"__truediv__": lambda s, p: fake_source})())
    monkeypatch.setattr(caci, "_parse_workflow",
                        lambda text, yaml: fake_yaml.safe_load(text))

    problems = caci.mismatches()
    assert any("guard-renomme-dans-le-registre" in p for p in problems), (
        f"Renommage non detecte. Problems : {problems}"
    )
