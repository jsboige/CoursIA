"""Tests de `check_quarto_listings` (#25680, fille de l'EPIC #10921).

Contrat verifie ici, dans cet ordre :

1. **controle positif** : un listing dont le motif resout au moins un fichier
   ne signale rien, ET le depot reel ne contient aucun listing vide -- un
   garde qui ne declenche jamais ne prouve rien ;
2. **la classe de defaut** : un motif `contents:` qui ne correspond a aucun
   fichier est signale avec un motif nomme (fichier source, id du listing,
   motif lui-meme) ;
3. **les formes de `contents:`** que Quarto accepte et que le depot porte :
   chaine, liste de chaines, liste de dictionnaires (`{id:, contents:}` et
   `{path:}`), dictionnaire imbrique ;
4. **les URLs** ne se resolvent pas sur disque : elles ne doivent jamais
   compter comme un listing vide ;
5. **fail-closed sur l'instrument** : un front matter illisible qui annonce
   un listing est une PANNE (exit 2), pas un verdict ;
6. **CLI** : rc 0 / 1 / 2 selon l'etat, et sortie JSON exploitable.
"""
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "check_quarto_listings",
    Path(__file__).resolve().parents[1] / "check_quarto_listings.py",
)
mod = importlib.util.module_from_spec(_SPEC)
# Le module doit etre enregistre dans sys.modules AVANT son execution : les
# dataclasses y resolvent leur module par `sys.modules[cls.__module__]`, et
# un module jamais enregistre y vaut None -> AttributeError au decorateur.
sys.modules[_SPEC.name] = mod
_SPEC.loader.exec_module(mod)

REPO_ROOT = Path(__file__).resolve().parents[3]


def _write_index(directory: Path, body: str) -> Path:
    """Ecrit un `index.qmd` minimal portant le front matter donne."""
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "index.qmd"
    path.write_text(f"---\n{body}\n---\n\nTexte.\n", encoding="utf-8")
    return path


def _write_notebook(directory: Path, name: str) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / name
    path.write_text("{}\n", encoding="utf-8")
    return path


class TestControlePositif:
    def test_un_listing_resolu_ne_signale_rien(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "Serie-01-Setup.ipynb")
        _write_index(
            serie,
            'listing:\n  - id: phase1\n    contents: "Serie-01-Setup.ipynb"\n    type: grid',
        )
        broken, instrument_errors, checked = mod.scan(tmp_path)
        assert broken == []
        assert instrument_errors == []
        assert checked == 1

    def test_un_motif_glob_resout_plusieurs_fichiers(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "Serie-02-A.ipynb")
        _write_notebook(serie, "Serie-03-B.ipynb")
        _write_index(
            serie,
            'listing:\n  - id: phase2\n    contents: "Serie-0[2-9]-*.ipynb"',
        )
        broken, _errors, checked = mod.scan(tmp_path)
        assert broken == []
        assert checked == 1

    def test_le_depot_reel_n_a_aucun_listing_vide(self):
        """Controle positif du garde : sur `main`, 0 listing vide.

        Sans cette mesure, un garde qui ne declenche jamais serait
        indiscernable d'un garde qui ne fonctionne pas.
        """
        broken, instrument_errors, checked = mod.scan(REPO_ROOT)
        assert checked >= 30, f"le depots reel ne devrait porter que {checked} listings"
        assert broken == [], f"listings vides sur le depot reel : {[b.to_dict() for b in broken]}"
        assert instrument_errors == []


class TestClasseDeDefaut:
    def test_un_motif_sans_correspondance_est_nomme(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "Serie-01-Setup-Python.ipynb")
        _write_index(
            serie,
            'listing:\n  - id: phase1\n    contents: "Serie-01-Setup.ipynb"',
        )
        broken, _errors, checked = mod.scan(tmp_path)
        assert checked == 1
        assert len(broken) == 1
        finding = broken[0]
        assert finding.source == "Serie/index.qmd"
        assert finding.listing_id == "phase1"
        assert finding.motif == "Serie-01-Setup.ipynb"
        assert finding.reason == "listing-empty:phase1"

    def test_un_glob_sans_correspondance_est_nomme(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "Serie-01-Setup.ipynb")
        _write_index(serie, 'listing:\n  - id: phase2\n    contents: "Serie-0[5-9]-*.ipynb"')
        broken, _errors, _checked = mod.scan(tmp_path)
        assert len(broken) == 1
        assert broken[0].motif == "Serie-0[5-9]-*.ipynb"

    def test_plusieurs_listings_vides_sont_tous_signales(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_index(
            serie,
            'listing:\n'
            '  - id: a\n    contents: "absent-a.ipynb"\n'
            '  - id: b\n    contents: "absent-b.ipynb"\n',
        )
        broken, _errors, _checked = mod.scan(tmp_path)
        assert [item.listing_id for item in broken] == ["a", "b"]


class TestFormesDeContents:
    def test_une_liste_de_chaines(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "A.ipynb")
        _write_notebook(serie, "B.ipynb")
        _write_index(
            serie,
            'listing:\n  - id: setup\n    contents:\n      - "A.ipynb"\n      - "B.ipynb"',
        )
        broken, _errors, checked = mod.scan(tmp_path)
        assert broken == []
        assert checked == 2

    def test_une_liste_de_dictionnaires_avec_contents(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "A.ipynb")
        _write_index(
            serie,
            'listing:\n  - id: grp\n    contents:\n      - id: un\n        contents: "A.ipynb"',
        )
        broken, _errors, checked = mod.scan(tmp_path)
        assert broken == []
        assert checked == 1

    def test_une_entree_avec_path(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "A.ipynb")
        _write_index(
            serie,
            'listing:\n  - id: un\n    contents:\n      - path: "A.ipynb"',
        )
        broken, _errors, checked = mod.scan(tmp_path)
        assert broken == []
        assert checked == 1

    def test_une_url_de_contents_n_est_pas_une_panne(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_index(
            serie,
            'listing:\n  - id: distant\n    contents: "https://example.invalid/x.ipynb"',
        )
        broken, instrument_errors, _checked = mod.scan(tmp_path)
        assert broken == []
        assert instrument_errors == []

    def test_un_fichier_sans_front_matter_est_ignore(self, tmp_path):
        serie = tmp_path / "Serie"
        serie.mkdir(parents=True, exist_ok=True)
        (serie / "index.qmd").write_text("Texte sans front matter.\n", encoding="utf-8")
        broken, instrument_errors, checked = mod.scan(tmp_path)
        assert broken == []
        assert instrument_errors == []
        assert checked == 0

    def test_une_racine_sous_un_repertoire_ignore_est_bien_scanee(self, tmp_path):
        """Regression du 2026-11-12 : le filtre portait sur les composants
        ABSOLUS du chemin, si bien qu'un arbre place sous un repertoire de
        `SKIP_DIRS` (`.tmp/`) rendait `listings verifies : 0` et un rc 0 --
        un vert qui ne mesurait rien. Le filtre porte desormais sur le
        chemin RELATIF a la racine."""
        root = tmp_path / ".tmp" / "arbre"
        serie = root / "Serie"
        _write_notebook(serie, "A.ipynb")
        _write_index(serie, 'listing:\n  - id: a\n    contents: "absent.ipynb"')
        broken, _errors, checked = mod.scan(root)
        assert checked == 1
        assert len(broken) == 1
        assert broken[0].motif == "absent.ipynb"


class TestFailClosed:
    def test_un_front_matter_illisible_qui_annonce_un_listing_est_une_panne(self, tmp_path):
        serie = tmp_path / "Serie"
        serie.mkdir(parents=True, exist_ok=True)
        (serie / "index.qmd").write_text(
            "---\nlisting:\n  - id: a\n   contents: [malformé\n---\n",
            encoding="utf-8",
        )
        broken, instrument_errors, _checked = mod.scan(tmp_path)
        assert broken == []
        assert len(instrument_errors) == 1
        assert "front-matter-unreadable" in instrument_errors[0].reason

    def test_un_front_matter_illisible_sans_listing_est_ignore(self, tmp_path):
        serie = tmp_path / "Serie"
        serie.mkdir(parents=True, exist_ok=True)
        (serie / "index.qmd").write_text("---\ntitre: [malformé\n---\n", encoding="utf-8")
        broken, instrument_errors, _checked = mod.scan(tmp_path)
        assert broken == []
        assert instrument_errors == []


class TestCli:
    def _run(self, root, *args):
        return subprocess.run(
            [sys.executable, str(REPO_ROOT / "scripts/ci/check_quarto_listings.py"),
             "--root", str(root), *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )

    def test_rc_0_sans_defaut(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_notebook(serie, "A.ipynb")
        _write_index(serie, 'listing:\n  - id: a\n    contents: "A.ipynb"')
        result = self._run(tmp_path)
        assert result.returncode == 0, result.stdout + result.stderr
        assert "listings SANS correspondance sur disque : 0" in result.stdout

    def test_rc_1_avec_defaut(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_index(serie, 'listing:\n  - id: a\n    contents: "absent.ipynb"')
        result = self._run(tmp_path)
        assert result.returncode == 1, result.stdout + result.stderr
        assert "Serie/index.qmd" in result.stdout
        assert "absent.ipynb" in result.stdout

    def test_rc_2_quand_la_racine_est_introuvable(self, tmp_path):
        result = self._run(tmp_path / "absent-pas")
        assert result.returncode == 2

    def test_la_sortie_json_expose_la_cause(self, tmp_path):
        serie = tmp_path / "Serie"
        _write_index(serie, 'listing:\n  - id: a\n    contents: "absent.ipynb"')
        result = self._run(tmp_path, "--json")
        assert result.returncode == 1
        report = json.loads(result.stdout)
        assert report["broken_count"] == 1
        assert report["broken"][0]["reason"] == "listing-empty:a"
        assert report["broken"][0]["motif"] == "absent.ipynb"
        assert report["checked"] == 1

    def test_le_racine_par_defaut_est_le_depot(self):
        result = subprocess.run(
            [sys.executable, str(REPO_ROOT / "scripts/ci/check_quarto_listings.py"), "--json"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        report = json.loads(result.stdout)
        assert report["broken_count"] == 0
        assert report["checked"] >= 30
