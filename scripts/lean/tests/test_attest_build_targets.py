"""Tests for scripts/lean/attest_build_targets.py — resolution des cibles de `lake build`.

Couvre la resolution pure (aucun `lake`, aucun reseau, aucune machine) :
- lecture du lakefile par l'organe canonique `lake_selectors` (selecteurs
  `one` / `sub` / `all`, sucre `` `X.*`` / `` `X.+``, TOML, commentaires) ;
- enumeration des modules **du lac** (les selecteurs font foi, pas la
  presence du fichier) ;
- resolution d'un fichier touche -> module Lean ;
- jumeau `_en` (deux fichiers, deux modules) ;
- dependants **transitifs** ;
- agregateur ecarte **et nomme** (une borne invisible surdeclare la portee) ;
- agregateur **strict** : un fichier qui porte une commande n'en est pas un (#26966) ;
- repli explicite **et nomme** quand un fichier `.lean` touche n'est pas un
  module du lac (#26812 : le repli doit dire QUEL fichier, pas « rien ») ;
- repli explicite quand un fichier **non `.lean`** du lake est touche (#26966) ;
- **document** vs **entree de build** : un `README` du lac est prouve
  documentaire et ne force pas le repli ; un `lake-manifest.json` reste
  une entree de build et le force.

Fixtures synthetiques sous ``tmp_path``. Zero dependance externe.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from attest_build_targets import (  # noqa: E402
    dependents_of,
    enumerate_modules,
    est_documentaire,
    import_graph,
    is_aggregator,
    module_name_of,
    resolve_targets,
    selectors,
    sibling_en_module,
    source_root,
)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

LAKEFILE = """import Lake
open Lake DSL

package «demo» where
  require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target]
lean_lib «Demo» where
  globs := #[.submodules `Demo, `Demo_en]
"""


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _make_lake(root: Path) -> Path:
    """Un lake de demonstration : un agregateur racine, un module de contenu,
    son jumeau `_en`, un dependant, un agregateur intermediaire et un
    dependant de cet aggregateur."""
    lake = root / "demo"
    _write(lake / "lakefile.lean", LAKEFILE)
    _write(lake / "lean-toolchain", "leanprover/lean4:v4.33.0\n")
    # Agregateur racine : des imports, aucune declaration.
    _write(lake / "Demo.lean", "import Demo.Alpha\nimport Demo.Beta\n")
    # Agregateur racine `_en` (deux declarations : ce n'est PAS un agregateur).
    _write(lake / "Demo_en.lean", "import Demo.Alpha_en\n\ndef demoHelper : Nat := 0\n")
    # Module de contenu, avec son jumeau `_en`.
    _write(lake / "Demo" / "Alpha.lean", "import Demo.Beta\n\ntheorem alpha_ok : True := trivial\n")
    _write(lake / "Demo" / "Alpha_en.lean", "import Demo.Beta_en\n\ntheorem alpha_ok : True := trivial\n")
    _write(lake / "Demo" / "Beta.lean", "theorem beta_ok : True := trivial\n")
    _write(lake / "Demo" / "Beta_en.lean", "theorem beta_ok : True := trivial\n")
    # Agregateur intermediaire : il importe Alpha, sans declarer.
    _write(lake / "Demo" / "Gamma.lean", "import Demo.Alpha\n")
    # Dependant NON-agregateur de l'agregateur : il doit etre construit.
    _write(lake / "Demo" / "Delta.lean", "import Demo.Gamma\n\ntheorem delta_ok : True := trivial\n")
    return lake


# ---------------------------------------------------------------------------
# lakefile
# ---------------------------------------------------------------------------

def test_le_globs_sont_lus(tmp_path):
    lake = _make_lake(tmp_path)
    assert selectors(lake) == [("sub", "Demo"), ("one", "Demo_en")]


def test_une_lib_sans_globs_constructit_seulement_son_module_racine(tmp_path):
    lake = tmp_path / "plain"
    _write(lake / "lakefile.lean", "import Lake\n@[default_target]\nlean_lib «Plain» where\n")
    _write(lake / "Plain.lean", "theorem ok : True := trivial\n")
    _write(lake / "Plain" / "Sub.lean", "theorem sub : True := trivial\n")
    assert selectors(lake) == [("one", "Plain")]
    modules = enumerate_modules(lake)
    # `Plain.Sub` n'est pas dans les globs : il n'est pas constructible.
    assert set(modules) == {"Plain"}


def test_le_srcdir_est_honore(tmp_path):
    lake = tmp_path / "s"
    _write(lake / "lakefile.lean", "import Lake\n@[default_target]\nlean_lib «S» where\n  srcDir := \"src\"\n  globs := #[.andSubmodules `S]\n")
    _write(lake / "src" / "S.lean", "theorem ok : True := trivial\n")
    _write(lake / "src" / "S" / "Sub.lean", "theorem sub : True := trivial\n")
    assert source_root(lake) == (lake / "src").resolve()
    assert set(enumerate_modules(lake)) == {"S", "S.Sub"}


def test_un_lakefile_illisible_ne_devine_pas(tmp_path):
    lake = tmp_path / "vide"
    lake.mkdir()
    assert selectors(lake) == []
    assert enumerate_modules(lake) == {}


# ---------------------------------------------------------------------------
# formes de glob reellement employees par les lakes du manifeste (#26812)
# ---------------------------------------------------------------------------

def test_le_glob_andsubmodules_couvre_le_prefixe_et_ses_sous_modules(tmp_path):
    """`.andSubmodules `X` -- la forme du lac `knot` (#26812)."""
    lake = tmp_path / "knot"
    _write(lake / "lakefile.lean", "import Lake\n@[default_target]\nlean_lib «Knots» where\n  globs := #[.andSubmodules `Knots, `Knots_en]\n")
    _write(lake / "Knots.lean", "import Knots.Alpha\n")
    _write(lake / "Knots" / "Alpha.lean", "theorem a : True := trivial\n")
    _write(lake / "Knots" / "Alpha_en.lean", "theorem a : True := trivial\n")
    _write(lake / "Knots_en.lean", "import Knots.Alpha_en\n")
    assert selectors(lake) == [("all", "Knots"), ("one", "Knots_en")]
    # Le prefixe ET ses sous-modules : sans cela, le lac entier etait construit.
    assert set(enumerate_modules(lake)) == {
        "Knots", "Knots_en", "Knots.Alpha", "Knots.Alpha_en",
    }


def test_le_sucre_etoile_desugare_en_prefixe_et_sous_modules(tmp_path):
    """`` `X.*`` -- la forme des lakes `galois`, `grothendieck`, `gametheory`."""
    lake = tmp_path / "g"
    _write(lake / "lakefile.lean", "import Lake\n@[default_target]\nlean_lib «G» where\n  globs := #[`G.*]\n")
    _write(lake / "G.lean", "import G.Sub\n")
    _write(lake / "G" / "Sub.lean", "theorem s : True := trivial\n")
    assert selectors(lake) == [("all", "G")]
    assert set(enumerate_modules(lake)) == {"G", "G.Sub"}


def test_un_glob_commente_ne_compte_pas(tmp_path):
    """Un `globs :=` cite dans un commentaire n'est PAS une declaration."""
    lake = tmp_path / "c"
    _write(lake / "lakefile.lean", "import Lake\n-- globs := #[`Fake, `Fake_en]\n@[default_target]\nlean_lib «Real» where\n  globs := #[`Real]\n")
    _write(lake / "Real.lean", "theorem r : True := trivial\n")
    assert selectors(lake) == [("one", "Real")]


def test_un_lakefile_toml_est_lu(tmp_path):
    lake = tmp_path / "t"
    _write(lake / "lakefile.toml", 'name = "t"\n\n[[lean_lib]]\nname = "T"\nglobs = ["T", "T_en"]\n')
    _write(lake / "T.lean", "theorem t : True := trivial\n")
    _write(lake / "T_en.lean", "theorem t : True := trivial\n")
    assert selectors(lake) == [("one", "T"), ("one", "T_en")]
    assert set(enumerate_modules(lake)) == {"T", "T_en"}


# ---------------------------------------------------------------------------
# resolution
# ---------------------------------------------------------------------------

def test_un_fichier_lean_hors_module_est_nomme_meme_sans_une_seule_racine(tmp_path):
    """#26812 : le repli doit nommer le fichier, pas dire « aucun module »."""
    lake = tmp_path / "plain"
    _write(lake / "lakefile.lean", "import Lake\n@[default_target]\nlean_lib «Plain» where\n")
    _write(lake / "Plain.lean", "theorem ok : True := trivial\n")
    verdict = resolve_targets(lake, ["plain/Note.lean"], lake_prefix="plain/")
    assert not verdict["ok"]
    assert verdict["targets"] == []
    assert "Note.lean" in verdict["reason"]
    assert verdict["unresolved"] == ["plain/Note.lean"]


# ---------------------------------------------------------------------------
# modules
# ---------------------------------------------------------------------------

def test_les_modules_suivent_les_globs(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    # `.submodules `Demo` ne couvre PAS le module racine `Demo` : la
    # semantique Lake est `Glob.submodules` (strictement sous le prefixe).
    # C'est ce qui vaut pour `lake build` -- nommer `Demo` serait un
    # module inconnu. Les lakes qui veulent le prefixe disent
    # `.andSubmodules` (cf. `knot`).
    assert set(modules) == {
        "Demo_en",
        "Demo.Alpha",
        "Demo.Alpha_en",
        "Demo.Beta",
        "Demo.Beta_en",
        "Demo.Gamma",
        "Demo.Delta",
    }


def test_module_name_of():
    assert module_name_of("Demo/Life/JumpCapture.lean") == "Demo.Life.JumpCapture"
    assert module_name_of("Demo.lean") == "Demo"
    assert module_name_of("Demo.lean.bak") is None


def test_le_graphe_ne_garde_que_les_imports_internes(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    graph = import_graph(lake, modules)
    assert graph["Demo.Alpha"] == {"Demo.Beta"}
    assert graph["Demo.Gamma"] == {"Demo.Alpha"}
    assert graph["Demo.Beta"] == set()


def test_dependants_transitifs(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    graph = import_graph(lake, modules)
    dependents = dependents_of(graph, {"Demo.Alpha"})
    # Gamma importe Alpha ; Delta importe Gamma (fermeture, pas voisinage).
    assert {"Demo.Gamma", "Demo.Delta"} <= dependents


# ---------------------------------------------------------------------------
# agregateurs
# ---------------------------------------------------------------------------

def test_un_fichier_sans_declaration_est_un_agregateur():
    assert is_aggregator("import Demo.Alpha\n")
    assert is_aggregator("/-- un commentaire --/\nimport Demo.Alpha\n")
    assert not is_aggregator("theorem ok : True := trivial\n")
    assert not is_aggregator("def helper : Nat := 0\n")


# ---------------------------------------------------------------------------
# agregateurs -- definition stricte (#26966)
# ---------------------------------------------------------------------------

def test_un_agregateur_ne_porte_aucune_commande():
    """Un agregateur n'importe que des modules : ni commande, ni declaration.

    Un fichier qui porte une **commande** (`attribute`, `notation`, `macro`,
    `syntax`, `elab`, `deriving instance`, `#check`, `#eval`, `open ... in`)
    casse des que l'import qu'il cite est renomme ou retire : le construire
    est donc obligatoire.
    """
    # Agregateurs : des imports, et rien qui agisse sur la suite.
    assert is_aggregator("import Demo.Alpha\n")
    assert is_aggregator("namespace Demo\nimport Demo.Alpha\nend Demo\n")
    assert is_aggregator("open Demo\nimport Demo.Alpha\n")
    # Commentaires et lignes vides ne sont pas du contenu.
    assert is_aggregator("-- un commentaire\n\nimport Demo.Alpha\n")
    # Contenu : une commande suffit a disqualifier l'agregateur.
    assert not is_aggregator("import Demo.Alpha\nattribute [simp] Demo.alpha_ok\n")
    assert not is_aggregator("import Demo.Alpha\nnotation `x` := 0\n")
    assert not is_aggregator("import Demo.Alpha\nmacro `x` : Term := `0\n")
    assert not is_aggregator("import Demo.Alpha\nsyntax `x` : term\n")
    assert not is_aggregator("import Demo.Alpha\nopen Demo in\n")
    assert not is_aggregator("import Demo.Alpha\n#check Demo.alpha_ok\n")
    assert not is_aggregator("import Demo.Alpha\n#eval Demo.alpha_ok\n")


def test_un_fichier_qui_porte_une_commande_est_construit_et_non_ecarte(tmp_path):
    """Le cas（B.lean = `import A` + `attribute [simp] A.foo`) est construit.

    Avant #26966, ce fichier passait pour un agregateur : il etait ecarte des
    dependants, donc jamais construit -- alors que la commande qu'il porte
    peut casser quand l'import cite bouge.
    """
    lake = _make_lake(tmp_path)
    _write(
        lake / "Demo" / "Epsilon.lean",
        "import Demo.Alpha\n\nattribute [simp] Demo.alpha_ok\n",
    )
    verdict = resolve_targets(lake, ["demo/Demo/Alpha.lean"], lake_prefix="demo/")
    assert verdict["ok"], verdict["reason"]
    assert "Demo.Epsilon" in verdict["targets"]
    assert "Demo.Epsilon" not in verdict["skipped_aggregators"]


def test_un_lakefile_touche_force_le_repli_sur_le_lac_entier(tmp_path):
    """Un `lakefile.toml` touche change la compilation du lac entier.

    Un build cible n'atteste que les modules cites : il n'attesterait donc
    rien des modules que les options du lakefile peuvent casser. Le repli est
    obligatoire, et sa raison est nommee.

    Le cas `lakefile.lean` releve au meme titre est couvert par la regle des
    fichiers `.lean` hors module (repli avec la raison nommee) ; il est
    verifie ici pour qu'aucune des deux formes ne se glisse dans une
    construction ciblee.
    """
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(
        lake,
        ["demo/lakefile.toml", "demo/Demo/Alpha.lean"],
        lake_prefix="demo/",
    )
    assert not verdict["ok"]
    assert "lakefile.toml" in verdict["reason"]
    assert verdict["targets"] == []
    assert verdict["non_lean_touched"] == ["demo/lakefile.toml"]


def test_un_lakefile_lean_touche_force_le_repli_sur_le_lac_entier(tmp_path):
    """`lakefile.lean` n'est pas un module du lac : le repli reste obligatoire."""
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(
        lake,
        ["demo/lakefile.lean", "demo/Demo/Alpha.lean"],
        lake_prefix="demo/",
    )
    assert not verdict["ok"]
    assert "lakefile.lean" in verdict["reason"]
    assert verdict["targets"] == []


def test_un_fichier_non_lean_hors_du_lake_ne_touche_pas_la_resolution(tmp_path):
    """Le perimetre est le prefixe du lake : un `.md` d'ailleurs ne force rien."""
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(
        lake,
        ["docs/Note.md", "demo/Demo/Alpha.lean"],
        lake_prefix="demo/",
    )
    assert verdict["ok"], verdict["reason"]
    assert verdict["non_lean_touched"] == []


# ---------------------------------------------------------------------------
# documentation vs entree de build (#26976)
# ---------------------------------------------------------------------------

def test_un_readme_du_lac_est_prouve_documentaire_et_ne_force_pas_le_repli(tmp_path):
    """Un `README.md` DANS le lac ne change pas la compilation.

    Le repli sur le lac entier etait declenche par TOUT fichier non
    `.lean` du lake. Un document n'est pas une entree de build : il force
    le repli sans raison, et le repli coute une heure de compilation.

    T witness : le `README.md` du lac, avec un module touche a cote.
    """
    lake = _make_lake(tmp_path)
    _write(lake / "README.md", "# Demo\n\nUn lac de demonstration.\n")
    verdict = resolve_targets(
        lake,
        ["demo/README.md", "demo/Demo/Alpha.lean"],
        lake_prefix="demo/",
    )
    assert verdict["ok"], verdict["reason"]
    assert verdict["documentaire_touched"] == ["demo/README.md"]
    assert verdict["non_lean_touched"] == []
    assert "Demo.Alpha" in verdict["targets"]


def test_un_manifeste_du_lac_reste_une_entree_de_build(tmp_path):
    """Le temoin jumeau : `lake-manifest.json` n'est PAS un document.

    Meme extension « de configuration », meme emplacement : c'est une entree
    de build. La preuve est le NOM, pas l'extension : un `.json` de manifeste
    change les dependances du lac, donc force le repli.
    """
    lake = _make_lake(tmp_path)
    _write(lake / "lake-manifest.json", '{"version": "1.0.0"}\n')
    verdict = resolve_targets(
        lake,
        ["demo/lake-manifest.json", "demo/Demo/Alpha.lean"],
        lake_prefix="demo/",
    )
    assert not verdict["ok"]
    assert "lake-manifest.json" in verdict["reason"]
    assert verdict["non_lean_touched"] == ["demo/lake-manifest.json"]
    assert verdict["documentaire_touched"] == []


def test_un_lean_toolchain_reste_une_entree_de_build(tmp_path):
    """Un `lean-toolchain` n'a pas d'extension : ce n'est pas un document."""
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(
        lake,
        ["demo/lean-toolchain", "demo/Demo/Alpha.lean"],
        lake_prefix="demo/",
    )
    assert not verdict["ok"]
    assert verdict["non_lean_touched"] == ["demo/lean-toolchain"]


def test_la_preuve_documentaire_est_stricte():
    """Ce qui est documentaire, ce qui ne l'est pas.

    La liste est close : un nom de document connu **et** une extension de
    document. Tout le reste est une entree de build (fail-CLOSED : le repli
    est sur, donc sur).
    """
    for rel in ("README.md", "readme.markdown", "README.en.md",
                "LICENSE", "LICENSE-Apache-2.0", "CHANGELOG.md",
                "Demo/README.md", "contributing.rst"):
        assert est_documentaire(rel), rel
    for rel in ("lean-toolchain", "lake-manifest.json", "lakefile.toml",
                "Notes.md", "Toolchain.md", "Demo/Notes.md", "Main.lean"):
        assert not est_documentaire(rel), rel


# ---------------------------------------------------------------------------
# resolution
# ---------------------------------------------------------------------------

def test_la_resolution_nomme_les_cibles_les_dependants_et_les_agregateurs_ecartes(tmp_path):
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(lake, ["demo/Demo/Alpha.lean"], lake_prefix="demo/")
    assert verdict["ok"], verdict["reason"]
    # La racine : le module touche + son jumeau `_en`.
    assert set(verdict["roots"]) == {"Demo.Alpha", "Demo.Alpha_en"}
    # Le dependent non-agregateur (Delta) est construit ; l'agregateur
    # (Gamma) ne l'est pas -- et il est NOMME.
    assert "Demo.Delta" in verdict["targets"]
    assert "Demo.Gamma" not in verdict["targets"]
    assert "Demo.Gamma" in verdict["skipped_aggregators"]
    # La racine elle-meme n'est jamais un "dependant" d'elle-meme.
    assert "Demo.Alpha" not in verdict["dependents"]


def test_un_fichier_lean_touche_hors_module_force_le_repli(tmp_path):
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(lake, ["demo/Demo/Alpha.lean", "demo/Note.lean"], lake_prefix="demo/")
    assert not verdict["ok"]
    assert "Note.lean" in verdict["reason"]
    assert verdict["targets"] == []


def test_un_diff_sans_lean_ne_resout_rien(tmp_path):
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(lake, ["demo/README.md"], lake_prefix="demo/")
    assert not verdict["ok"]
    assert verdict["targets"] == []


def test_le_prefixe_du_lake_est_deduit_du_depot(tmp_path):
    repo = tmp_path / "repo"
    lake = _make_lake(repo)
    # Les chemins du diff sont relatifs au depot : `demo/...`, pas `repo/...`.
    verdict = resolve_targets(
        lake, ["demo/Demo/Beta.lean"], repo_root=repo
    )
    assert verdict["ok"], verdict["reason"]
    # Le module touche et son jumeau `_en` (deux fichiers, deux modules).
    assert verdict["roots"] == ["Demo.Beta", "Demo.Beta_en"]


def test_le_jumeau_en_est_resolu_dans_les_deux_sens(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    assert sibling_en_module(modules, "Demo.Alpha") == "Demo.Alpha_en"
    assert sibling_en_module(modules, "Demo.Alpha_en") == "Demo.Alpha"
    # `Demo.Beta` a un jumeau `_en` ; `Demo.Delta` n'en a pas.
    assert sibling_en_module(modules, "Demo.Beta") == "Demo.Beta_en"
    assert sibling_en_module(modules, "Demo.Delta") is None


# ---------------------------------------------------------------------------
# manifeste reel (#26812)
# ---------------------------------------------------------------------------

def test_aucun_lake_du_manifeste_ne_tombe_a_zero_module():
    """Aucun lake du manifeste ne doit s'enumerer a zero module.

    Zero module = repli sur le build du lac ENTIER : c'est ce que le
    parseur local provoquait sur 6 lakes (galois, grothendieck, gamedefs,
    gamedefsext, asymmetricinformation, conwaycgt) et ce qui rendait
    l'attestation de #26812 equivalente a un build complet.
    """
    here = Path(__file__).resolve()
    manifest = here.parents[1] / "ci_lakes.json"
    if not manifest.is_file():
        pytest.skip("manifeste des lakes absent")
    repo_root = here.parents[3]
    lakes = json.loads(manifest.read_text(encoding="utf-8")).get("lakes") or []
    vides = []
    visites = 0
    for entry in lakes:
        root = repo_root / entry["project-path"]
        if not root.is_dir():
            continue
        visites += 1
        if not enumerate_modules(root):
            vides.append(entry["lake"])
    assert visites > 0, "aucun lake du manifeste present dans ce checkout"
    assert not vides, "lakes sans module enumeré : {}".format(", ".join(vides))


# ---------------------------------------------------------------------------
# payload
# ---------------------------------------------------------------------------
# Le payload de build n'est PAS construit ici : ce module est pur, et une
# liste de commande posee hors de la main de l'organe est une voie directe
# (refusee par `scripts/lean/check_lake_direct_invocation.py`). Le contrat
# du payload est verifie la ou il est remis a l'organe :
# `tests/test_attest_local_build_payload.py`.


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
