#!/usr/bin/env python3
"""Tests de la FILIATION par renommage pour l'organe axiom-gate (#26056, #26381).

Le module scinde le fichier `test_check_axiom_gate_coverage.py` : la
COUVERTURE (qui appelle la garde, quels lakes sont matrises) reste dans le
module d'origine, la FILIATION (le lake bouge parce que son repertoire PARENT
a ete renomme, ou qu'il a change de nom deux fois de suite) est ici.

Le cliquet de taille des scripts neufs (`scripts/tests/test_script_size_ratchet.py`)
plafonne a 800 lignes : reunir les deux sujets dans un seul module le
depassait. Aucun test n'est perdu par ce decoupage -- ils sont deplaces, pas
supprimes.

Dual-mode: runnable directement (``python scripts/lean/tests/test_check_axiom_gate_filiation.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_axiom_gate_coverage import classify_deleted  # noqa: E402


class TestRenamedParentFiliation:
    """Le repertoire PARENT renomme : la forme du chemin ne prouve rien."""

    def _d(self, paths):
        return {"dispatcher": "lean-x.yml", "deleted_by": "0123456789",
                "had_gate": True, "gated_paths": paths}


    # -- le repertoire PARENT renomme (#26056) ---------------------------
    # Le lake bouge parce que son repertoire PARENT a ete renomme
    # (`Lean/GALOIS` -> `Lean/Galois`). Le successeur n'est alors plus sous
    # l'ancien parent : la filiation ne se lit plus sur la chaine, et seule
    # la detection de renommage de git peut la prouver.

    def test_a_renamed_parent_directory_is_relocation_not_loss(self):
        """Preuve de renommage presente : le deplacement est reconnu."""
        d = self._d(["A/Lean/Galois/galois_lean"])
        gated = {"A/Lean/Galois2/galois_lean"}
        r = classify_deleted([d], gated, exists_at=lambda p: p in gated,
                             rename_proof=lambda old, new: True)
        assert r["lost"] == []
        [entry] = r["relocated"]
        assert entry["moved_to"] == "A/Lean/Galois2/galois_lean"

    def test_an_unproven_renamed_parent_stays_lost(self):
        """Controle negatif : sans preuve, la forme du chemin ne suffit pas."""
        d = self._d(["A/Lean/Galois/galois_lean"])
        gated = {"A/Lean/Galois2/galois_lean"}
        r = classify_deleted([d], gated, exists_at=lambda p: p in gated,
                             rename_proof=lambda old, new: False)
        assert r["relocated"] == []
        assert [e["dispatcher"] for e in r["lost"]] == ["lean-x.yml"]

    def test_a_renamed_parent_without_proof_stays_lost(self):
        """Pas de sonde de renommage = pas de preuve : fail-closed."""
        d = self._d(["A/Lean/Galois/galois_lean"])
        gated = {"A/Lean/Galois2/galois_lean"}
        r = classify_deleted([d], gated, exists_at=lambda p: p in gated)
        assert r["relocated"] == []
        assert [e["dispatcher"] for e in r["lost"]] == ["lean-x.yml"]

    def test_the_same_lake_listed_twice_is_one_lake(self):
        """Deux jobs de gate qui passent le MEME lake : c'est un lake, pas deux.

        Mesure 2026-11-15 : `lean-conway.yml` listait
        `.../Lean/GOL/conway_lean` deux fois (repertoire renomme `JeuDeLaVie`
        le 2026-11-22, #26056). Compter les LIGNES rendait le
        deplacement inprouvable, et la couverture d'un lake couvert etait
        declaree PERDUE. Le compte se fait sur les chemins DISTINCTS.
        """
        d = self._d(["A/Lean/Galois/galois_lean", "A/Lean/Galois/galois_lean"])
        gated = {"A/Lean/Galois2/galois_lean"}
        r = classify_deleted([d], gated, exists_at=lambda p: p in gated,
                             rename_proof=lambda old, new: True)
        assert r["lost"] == []
        [entry] = r["relocated"]
        assert entry["moved_to"] == "A/Lean/Galois2/galois_lean"

    def test_two_proven_renamed_successors_stay_lost(self):
        """Deux successeurs prouves : le deplacement reste inprouvable."""
        d = self._d(["A/Lean/Galois/galois_lean"])
        gated = {"A/Lean/Galois2/galois_lean", "B/Lean/Galois3/galois_lean"}
        r = classify_deleted([d], gated, exists_at=lambda p: p in gated,
                             rename_proof=lambda old, new: True)
        assert r["relocated"] == []
        assert [e["dispatcher"] for e in r["lost"]] == ["lean-x.yml"]


class TestRenameProof:
    """La filiation quand le repertoire PARENT du lake est renomme.

    L'organe lit la filiation sur la chaine du chemin ; quand le repertoire
    parent bouge, cette lecture devient impossible. Ce que git sait reste
    vrai : les fichiers du lake ont bouge avec lui. Ces tests verifient la
    lecture git sur un depot jetable, pas sur le depot mesure.
    """

    def _init(self, tmp_path):
        env = {**os.environ, "MSYS_NO_PATHCONV": "1"}

        def run(*args):
            proc = subprocess.run(["git", "-C", str(tmp_path), *args],
                                  capture_output=True, env=env)
            assert proc.returncode == 0, proc.stderr.decode("utf-8", "replace")
            return proc.stdout.decode("utf-8", "replace")

        run("init", "-q")
        run("config", "user.email", "test@example.invalid")
        run("config", "user.name", "test")
        return run

    def _lake(self, tmp_path, where="Lean/GALOIS2/galois2_lean"):
        lake = tmp_path / where
        lake.mkdir(parents=True)
        (lake / "lakefile.toml").write_text("name = \"galois\"\n", encoding="utf-8")
        return lake

    def test_a_renamed_parent_directory_is_proven(self, tmp_path, monkeypatch):
        """Le renommage du repertoire PARENT est vu par git comme un R."""
        from check_axiom_gate_coverage import rename_proven
        run = self._init(tmp_path)
        self._lake(tmp_path)
        run("add", "-A")
        run("commit", "-q", "-m", "init")
        run("mv", "Lean/GALOIS2", "Lean/GaloisRenamed2")
        run("commit", "-q", "-m", "rename parent")
        monkeypatch.chdir(tmp_path)
        assert rename_proven("HEAD", "Lean/GALOIS2/galois2_lean",
                              "Lean/GaloisRenamed2/galois2_lean") is True

    def test_a_chained_rename_is_proven(self, tmp_path, monkeypatch):
        """Deux renommages successifs : la filiation reste prouvable.

        Cas mesure le 2026-11-15 : le repertoire parent a ete renomme deux
        fois (``Lean/GOL`` -> ``Lean/GameOfLife`` puis ``Lean/JeuDeLaVie``).
        La preuve ne peut pas s'arreter au premier hop -- sinon la garde
        declare PERDU un lake dont la couverture n'a pas bouge.
        """
        from check_axiom_gate_coverage import rename_proven
        run = self._init(tmp_path)
        self._lake(tmp_path, where="Lean/GALOIS4/galois4_lean")
        run("add", "-A")
        run("commit", "-q", "-m", "init")
        # noms differents au-dela de la casse : sur Windows, un renommage
        # qui ne change que la casse echoue ("Invalid argument")
        run("mv", "Lean/GALOIS4", "Lean/Galois4Hop")
        run("commit", "-q", "-m", "rename 1")
        run("mv", "Lean/Galois4Hop", "Lean/Galois4Final")
        run("commit", "-q", "-m", "rename 2")
        monkeypatch.chdir(tmp_path)
        assert rename_proven("HEAD", "Lean/GALOIS4/galois4_lean",
                              "Lean/Galois4Final/galois4_lean") is True

    def test_a_chained_rename_is_proven_on_a_merge_ref(self, tmp_path, monkeypatch):
        """Le `ref` de FUSION ne doit pas perdre la filiation (mesure 2026-11-15).

        La CI checkout le `ref` de fusion (``refs/pull/N/merge``), pas la tete
        de branche. Les deux ne se comportent pas de meme facon : au `ref` de
        fusion, l'historique limite au chemin est simplifie par TREESAME, et
        le chemin INTERMEDIAIRE du renommage en deux temps n'a jamais existe
        sur le premier parent -- git ne suit donc que ce parent, et le commit
        du second hop disparait de la reponse. La filiation devenait alors
        INPROUVABLE et la garde declarait PERDU un lake dont la couverture
        n'a pas bouge. Mesure : PR #26381, `conway_lean` et `knot_lean`
        PERDUS en CI, 0 PERDU sur la tete de branche.
        """
        from check_axiom_gate_coverage import rename_proven
        run = self._init(tmp_path)
        self._lake(tmp_path, where="Lean/GOL5/conway5_lean")
        run("add", "-A")
        run("commit", "-q", "-m", "init")
        base_branch = run("rev-parse", "--abbrev-ref", "HEAD").strip()
        run("checkout", "-q", "-b", "branche")
        run("mv", "Lean/GOL5", "Lean/GameOfLife5")
        run("commit", "-q", "-m", "rename 1")
        run("mv", "Lean/GameOfLife5", "Lean/JeuDeLaVie5")
        run("commit", "-q", "-m", "rename 2")
        # Fusion de la branche dans la base : parents (base, branche) et
        # arbre = celui de la branche -- la forme du `ref` de la CI.
        run("checkout", "-q", base_branch)
        run("merge", "--no-ff", "-q", "-m", "merge", "branche")
        monkeypatch.chdir(tmp_path)
        assert rename_proven("HEAD", "Lean/GOL5/conway5_lean",
                              "Lean/JeuDeLaVie5/conway5_lean") is True

    def test_a_copied_lake_is_not_a_rename(self, tmp_path, monkeypatch):
        """Une copie n'est pas un deplacement : l'ancien chemin existe encore."""
        import shutil
        from check_axiom_gate_coverage import rename_proven
        run = self._init(tmp_path)
        self._lake(tmp_path, where="Lean/GALOIS3/galois3_lean")
        run("add", "-A")
        run("commit", "-q", "-m", "init")
        (tmp_path / "Lean" / "GaloisRenamed3").mkdir(parents=True)
        shutil.copytree(tmp_path / "Lean" / "GALOIS3" / "galois3_lean",
                        tmp_path / "Lean" / "GaloisRenamed3" / "galois3_lean")
        run("add", "-A")
        run("commit", "-q", "-m", "copy")
        monkeypatch.chdir(tmp_path)
        assert rename_proven("HEAD", "Lean/GALOIS3/galois3_lean",
                              "Lean/GaloisRenamed3/galois3_lean") is False

    def test_an_unknown_old_path_is_not_proven(self, tmp_path, monkeypatch):
        """Un ancien chemin qui n'a jamais existe n'a rien a prouver."""
        from check_axiom_gate_coverage import rename_proven
        run = self._init(tmp_path)
        self._lake(tmp_path)
        run("add", "-A")
        run("commit", "-q", "-m", "init")
        monkeypatch.chdir(tmp_path)
        assert rename_proven("HEAD", "Lean/NOPE/galois4_lean",
                              "Lean/GaloisRenamed4/galois4_lean") is False
