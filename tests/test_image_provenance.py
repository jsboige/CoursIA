"""Tests de ``slides/_tools/image_provenance.py`` -- census de provenance des images des decks.

Deux familles : un arbre fictif sous ``tmp_path``, ou chaque regle est isolement fautive ;
puis l'arbre reel du depot, ou l'organe doit tourner sans reference cassee, ou sa decoupe doit
rester identique a celle de ``slide_tools.count_slidev_slides``, et ou le temoin a reponse
connue de la reconstitution PPTX doit tenir.

Usage : pytest tests/test_image_provenance.py -v
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]


def _charger(nom: str):
    spec = importlib.util.spec_from_file_location(nom, REPO / "slides" / "_tools" / f"{nom}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[nom] = module
    spec.loader.exec_module(module)
    return module


ip = _charger("image_provenance")

SOURCE = """---
theme: default
title: Demo
---

# Titre

<img src="./images/img_001.png" alt="Schema AIMA du reseau">

---

```python
print("---")
```

![Schema](./images/img_002.png)

---
layout: center
---

<img src="./images/logo.png" alt="logo">

---
layout: two-cols
---

<img src="./images/img_003.png" alt="img_003.png">

<div style="background: url(/pptx-reference/slide-01.png)"></div>

<img src="https://exemple.org/distant.png" alt="distante">

<img src="./images/absente.png" alt="absente">
"""

INVENTAIRE = {
    "filename": "demo.pptx",
    "slide_count": 3,
    "total_images": 3,
    "slides": [
        {"number": 1, "image_count": 1, "text_content": "reseau de neurones"},
        {"number": 2, "image_count": 2, "text_content": "carte de la Roumanie"},
        {"number": 3, "image_count": 0, "text_content": "fin"},
    ],
}

SANS_DECLARATIONS = Path("aucune-declaration.tsv")


def _ecrire(chemin: Path, texte: str) -> None:
    chemin.parent.mkdir(parents=True, exist_ok=True)
    chemin.write_text(texte, encoding="utf-8", newline="\n")


def _image(chemin: Path) -> None:
    chemin.parent.mkdir(parents=True, exist_ok=True)
    chemin.write_bytes(b"\x89PNG\r\n\x1a\n" + bytes(16))


def _arbre(racine: Path) -> Path:
    """Un deck fictif complet : medias, generateur, rendu, capture, inventaire."""
    deck = racine / "slides" / "demo"
    _ecrire(deck / "slides.md", SOURCE)
    for rang in (1, 2, 3):
        _image(deck / "images" / f"img_{rang:03d}.png")
    _image(deck / "images" / "logo.png")
    _ecrire(deck / "images" / "gen_logo.py", "print('logo')\n")
    _image(deck / "public" / "pptx-reference" / "slide-01.png")
    _image(deck / "screenshots" / "shot_01.png")
    _ecrire(deck / "extracted" / "inventory.json", json.dumps(INVENTAIRE))
    return racine / "slides"


def _par_image(census: dict) -> dict[str, object]:
    return {l.image: l for l in census["lignes"]}  # type: ignore[attr-defined]


# ---------------------------------------------------------------------------
# Arbre fictif -- une regle par test
# ---------------------------------------------------------------------------


def test_decoupe_suivant_la_regle_slidev() -> None:
    """Frontmatter globale et par diapositive, ``---`` en bloc de code : quatre diapositives."""
    corps = ip.split_slides(SOURCE)
    assert len(corps) == 4
    assert "img_001" in corps[0]
    assert 'print("---")' in corps[1]
    assert "logo.png" in corps[2]
    assert "img_003" in corps[3]


def test_porteurs_et_diapositive_pptx(tmp_path: Path) -> None:
    racine = _arbre(tmp_path)
    census = ip.recenser(racine, tmp_path / SANS_DECLARATIONS)
    par_image = _par_image(census)

    assert set(par_image) == {
        "images/img_001.png",
        "images/img_002.png",
        "images/img_003.png",
        "images/logo.png",
        "public/pptx-reference/slide-01.png",
    }
    assert par_image["images/img_001.png"].porteur == ip.PORTEUR_MEDIA
    assert par_image["images/img_001.png"].pptx == 1
    assert par_image["images/img_002.png"].pptx == 2
    assert par_image["images/img_003.png"].pptx == 2
    # Le generateur voisin se lit avant le nom : un fichier genere n'est pas un media PPTX.
    assert par_image["images/logo.png"].porteur == ip.PORTEUR_GENERE
    assert par_image["public/pptx-reference/slide-01.png"].porteur == ip.PORTEUR_RENDU
    assert par_image["images/img_001.png"].diapositives == [1]
    assert par_image["images/logo.png"].diapositives == [3]

    assert census["non_resolues"] == [("demo", 4, "./images/absente.png")]
    assert census["distantes"] == [("demo", 4, "https://exemple.org/distant.png")]
    assert census["par_deck"]["demo"]["non_referencees"] == 1  # screenshots/shot_01.png
    assert census["par_deck"]["demo"]["pptx_certifie"] is True


def test_un_rang_manquant_arrete_la_reconstitution(tmp_path: Path) -> None:
    """Un fichier retire decale tous les rangs suivants : l'organe ne dit rien plutot que deplacer."""
    racine = _arbre(tmp_path)
    (racine / "demo" / "images" / "img_002.png").unlink()
    census = ip.recenser(racine, tmp_path / SANS_DECLARATIONS)
    par_image = _par_image(census)

    assert "images/img_002.png" not in par_image
    assert par_image["images/img_001.png"].pptx == 1
    assert par_image["images/img_003.png"].pptx is None
    assert "reconstitution arretee au rang 2" in str(par_image["images/img_003.png"].preuve)
    assert census["par_deck"]["demo"]["pptx_certifie"] is False


def test_media_du_pptx_que_le_deck_ne_montre_pas(tmp_path: Path) -> None:
    """Un rang present sur le disque et montre par aucun deck se compte, sans devenir une ligne."""
    racine = _arbre(tmp_path)
    _image(racine / "demo" / "images" / "img_004.png")
    census = ip.recenser(racine, tmp_path / SANS_DECLARATIONS)

    assert "images/img_004.png" not in _par_image(census)
    assert census["par_deck"]["demo"]["pptx_non_montres"] == 1
    # Un rang de plus que l'inventaire : le deck n'est plus certifie, et le compte le dit.
    assert census["par_deck"]["demo"]["pptx_certifie"] is False


def test_source_secondaire_comptee_hors_census(tmp_path: Path) -> None:
    """Un ``deck-*.md`` qu'aucun ``src:`` n'inclut : ses images sont comptees, pas listees."""
    racine = _arbre(tmp_path)
    _image(racine / "demo" / "images" / "img_004.png")
    _ecrire(racine / "demo" / "deck-annexe.md", "---\n# Annexe\n\n![A](./images/img_004.png)\n")
    census = ip.recenser(racine, tmp_path / SANS_DECLARATIONS)
    source = {s["fichier"]: s for s in census["sources_secondaires"]}["demo/deck-annexe.md"]

    assert source == {
        "fichier": "demo/deck-annexe.md",
        "images": 1,
        "vues": ["images/img_004.png"],
        "sans_ligne": 1,
        "incluse": False,
    }
    assert "images/img_004.png" not in _par_image(census)

    # Incluse par un ``src:`` d'un ``slides.md``, elle est montree au lecteur -- et toujours sans ligne.
    _ecrire(racine / "demo" / "slides.md", "---\ntheme: default\n---\n\n# Titre\n\n---\nsrc: ./deck-annexe.md\n---\n")
    census = ip.recenser(racine, tmp_path / SANS_DECLARATIONS)
    source = {s["fichier"]: s for s in census["sources_secondaires"]}["demo/deck-annexe.md"]
    assert source["incluse"] is True

    # Montree aussi par le ``slides.md`` de son deck : ce n'est plus une image sans ligne.
    _ecrire(racine / "demo" / "slides.md", SOURCE + "\n---\n\n![A](./images/img_004.png)\n")
    census = ip.recenser(racine, tmp_path / SANS_DECLARATIONS)
    source = {s["fichier"]: s for s in census["sources_secondaires"]}["demo/deck-annexe.md"]
    assert source["sans_ligne"] == 0
    assert source["incluse"] is False


def test_alt_qui_nomme_une_source(tmp_path: Path) -> None:
    racine = _arbre(tmp_path)
    census = ip.recenser(racine, tmp_path / SANS_DECLARATIONS)
    par_image = _par_image(census)

    assert par_image["images/img_001.png"].statut == ip.STATUT_DECLAREE
    assert "AIMA" in str(par_image["images/img_001.png"].origine)
    assert par_image["images/img_001.png"].licence == "non"
    assert par_image["images/img_003.png"].statut == ip.STATUT_NON_ETABLIE


def test_une_declaration_fait_sortir_ou_nomme(tmp_path: Path) -> None:
    racine = _arbre(tmp_path)
    declarations = tmp_path / "declarations.tsv"
    _ecrire(
        declarations,
        "deck\timage\torigine\tlicence\tremplacable\tpreuve\n"
        "demo\timages/img_002.png\tAIMA figure 3.1\tnon\tnon\tpage 70\n"
        "demo\timages/logo.png\tfigure maison\toui\tnc\t#1\n",
    )
    census = ip.recenser(racine, declarations)
    par_image = _par_image(census)

    declaree = par_image["images/img_002.png"]
    assert declaree.statut == ip.STATUT_DECLAREE
    assert declaree.origine == "AIMA figure 3.1"
    assert declaree.remplacable == "non"
    assert "declaration : page 70" in str(declaree.preuve)

    hors = par_image["images/logo.png"]
    assert hors.statut == ip.STATUT_HORS
    assert hors.licence == "oui"
    assert hors.remplacable == "nc"
    assert census["declarations"] == 2


@pytest.mark.parametrize(
    "ligne",
    [
        "demo\timages/inconnue.png\tx\toi\tnc\t-",  # image non referencee
        "demo\timages/img_002.png\tx\tpeut-etre\tnc\t-",  # licence hors bareme
        "demo\timages/img_002.png\tx\toui\tbientot\t-",  # remplacable hors bareme
        "demo\timages/img_002.png\t\toi\tnc\t-",  # origine vide
        "demo\timages/img_002.png\tx\toui",  # champ manquant
    ],
)
def test_declaration_refusee(tmp_path: Path, ligne: str) -> None:
    racine = _arbre(tmp_path)
    declarations = tmp_path / "declarations.tsv"
    _ecrire(declarations, "\t".join(ip.DECL_COLUMNS) + "\n" + ligne + "\n")
    with pytest.raises(ip.ErreurDeclarations):
        ip.recenser(racine, declarations)


def test_declaration_en_double_refusee(tmp_path: Path) -> None:
    racine = _arbre(tmp_path)
    declarations = tmp_path / "declarations.tsv"
    _ecrire(
        declarations,
        "\t".join(ip.DECL_COLUMNS) + "\n"
        "demo\timages/img_002.png\ta\tnon\tnon\t-\n"
        "demo\timages/img_002.png\tb\tnon\tnon\t-\n",
    )
    with pytest.raises(ip.ErreurDeclarations, match="deux fois"):
        ip.recenser(racine, declarations)


def test_declaration_invalide_fait_sortir_l_organe_en_2(tmp_path: Path, capsys) -> None:
    racine = _arbre(tmp_path)
    declarations = tmp_path / "declarations.tsv"
    _ecrire(declarations, "\t".join(ip.DECL_COLUMNS) + "\ndemo\timages/rien.png\tx\toi\tnc\t-\n")
    assert ip.main(["--repo-root", str(tmp_path), "--declarations", str(declarations)]) == 2
    assert "DECLARATIONS-INVALIDES" in capsys.readouterr().err
    assert not (tmp_path / ip.PAGE_MD).exists()


def test_check_propre_puis_derive(tmp_path: Path) -> None:
    racine = _arbre(tmp_path)
    assert ip.main(["--repo-root", str(tmp_path)]) == 0
    page = tmp_path / ip.PAGE_MD
    table = tmp_path / ip.PAGE_TSV
    assert page.is_file() and table.is_file()
    assert ip.main(["--repo-root", str(tmp_path), "--check"]) == 0

    page.write_text(page.read_text(encoding="utf-8") + "retouche a la main\n", encoding="utf-8")
    assert ip.main(["--repo-root", str(tmp_path), "--check"]) == 1

    assert ip.main(["--repo-root", str(tmp_path)]) == 0
    assert "retouche a la main" not in page.read_text(encoding="utf-8")


def test_page_et_table_portent_les_listes_attendues(tmp_path: Path) -> None:
    racine = _arbre(tmp_path)
    assert ip.main(["--repo-root", str(tmp_path)]) == 0
    page = (tmp_path / ip.PAGE_MD).read_text(encoding="utf-8")
    table = (tmp_path / ip.PAGE_TSV).read_text(encoding="utf-8")

    for titre in (
        "## La liste — images dont l'origine n'est pas établie",
        "## Origine déclarée, licence non établie",
        "## Hors EPIC — origine et licence établies",
        "## Références qui ne résolvent pas",
        "## Images distantes",
    ):
        assert titre in page
    assert "https://exemple.org/distant.png" in page
    assert "\t" in table and table.count("\n") == 6  # en-tete + 5 images
    assert not any(ch in page for ch in ("\x00",))


# ---------------------------------------------------------------------------
# Arbre reel du depot
# ---------------------------------------------------------------------------


def _sources_reelles() -> list[Path]:
    return sorted(p for p in (REPO / "slides").rglob("slides.md") if "node_modules" not in p.parts)


@pytest.mark.skipif(not _sources_reelles(), reason="arbre du depot absent")
def test_decoupe_identique_a_count_slidev_slides() -> None:
    """L'indice de diapositive publie doit etre celui que compte l'organe de structure."""
    slide_tools = _charger("slide_tools")
    sources = _sources_reelles()
    assert len(sources) >= 12
    for source in sources:
        texte = source.read_text(encoding="utf-8")
        assert len(ip.split_slides(texte)) == slide_tools.count_slidev_slides(texte), source


@pytest.mark.skipif(not _sources_reelles(), reason="arbre du depot absent")
def test_arbre_reel_sans_reference_cassee() -> None:
    census = ip.recenser(REPO / "slides", REPO / ip.DECLARATIONS)
    lignes = census["lignes"]
    assert len(lignes) > 600
    assert census["non_resolues"] == []
    assert census["distantes"] == []
    assert not any(l.porteur == ip.PORTEUR_INCONNU for l in lignes)
    certifies = [d for d, v in census["par_deck"].items() if v["pptx_certifie"]]
    assert len(certifies) >= 5
    for l in lignes:
        if l.porteur == ip.PORTEUR_MEDIA and ip.NOM_MEDIA.match(Path(l.image).stem):
            assert l.pptx is not None or "reconstitution arretee" in l.preuve or "inventaire" in l.preuve


@pytest.mark.skipif(not _sources_reelles(), reason="arbre du depot absent")
def test_page_et_table_commitees_sont_a_jour() -> None:
    """La page et la table commitees sont ce que l'organe produit : un drift se voit ici."""
    assert ip.main(["--repo-root", str(REPO), "--check"]) == 0


@pytest.mark.skipif(not _sources_reelles(), reason="arbre du depot absent")
def test_temoin_sur_arbre_reel(capsys) -> None:
    """Reponse connue : sur un deck certifie, un mot de contenu de l'alt se retrouve dans le texte
    de la diapositive PPTX reconstituee bien plus souvent que dans celle d'une diapositive tiree
    au hasard. Sans cet ecart, deux erreurs de cumul pourraient se compenser.

    Le temoin est calcule par l'organe (``temoin_par_deck``), pas par ce test : la page publie le
    meme compte par deck, et un deck n'y est dit soutenu que si sa probabilite sous le hasard passe
    sous le seuil. Le test controle l'agregat et exige qu'au moins trois decks soient soutenus --
    sans quoi la reconstitution ne serait plus prouvee par le temoin.
    """
    census = ip.recenser(REPO / "slides", REPO / ip.DECLARATIONS)
    temoins = census["temoin"]
    essais = sum(t.essais for t in temoins)
    touches = sum(t.touches for t in temoins)
    hasard = sum(t.hasard_tire for t in temoins)
    with capsys.disabled():
        print(f"\ntemoin : {touches} touches sur {essais} essais ; au hasard {hasard}")
        for t in temoins:
            verdict = "soutient" if t.mord else "non concluant"
            print(
                f"  {t.deck:34s} {t.touches:3d}/{t.essais:3d}  hasard tire {t.hasard_tire:2d}"
                f"  attendu {t.hasard_attendu:5.1f}  p={t.valeur_p:.2e}  {verdict}"
            )
    assert essais >= 100
    assert touches >= 2 * max(hasard, 1)
    assert sum(t.mord for t in temoins) >= 3
