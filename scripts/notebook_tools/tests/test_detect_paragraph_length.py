"""Tests for detect_paragraph_length.py -- paragraphes markdown trop longs.

Le contrat epingle : (1) un paragraphe > 2000 c est flagge avec son
emplacement ; (2) un paragraphe de longueur frontiere (pile 2000 ou
pile 2001) tranche exactement ; (3) fences code, titres, lignes de
tableau, commentaires HTML (CATALOG-STATUS) sont ignores ; (4) un
paragraphe post-fix du meme contenu segmente en 6 est silencieux ;
(5) la fixture externe demontre chaque cas sur un fichier reel.

Pas de reseau, pas de kernel.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from detect_paragraph_length import (
    FOUNDING_PARAGRAPH,
    MAX_PARAGRAPH_LEN,
    detect,
    iter_paragraphs,
)

FIXTURE = Path(__file__).parent / "fixtures" / "paragraph_wall_md.md"


def _read_section(start_marker: str) -> str:
    """Lit le contenu entre `## {start_marker}` et le prochain `## `."""
    text = FIXTURE.read_text(encoding="utf-8")
    s = text.split(f"## {start_marker}", 1)[1]
    return s.split("\n## ", 1)[0]


def test_founding_paragraph_fires():
    """Le paragraphe fondateur (PR #15405, 3336 c reellement sur main) tire."""
    got = detect(FOUNDING_PARAGRAPH + "\n")
    walls = [f for f in got if f["type"] == "oversized_paragraph"]
    assert walls, "temoin fondateur muet -- detecteur debranche"
    assert walls[0]["chars"] >= 3000, f"longueur sous-estimee : {walls[0]['chars']}"
    assert walls[0]["chars"] <= 3500, f"longueur surestimee : {walls[0]['chars']}"


def test_threshold_exact():
    """2000 c pile = OK ; 2001 c = finding (frontiere > stricte)."""
    assert not detect("a" * 2000 + "\n"), "2000 c devrait etre muet"
    over = detect("a" * 2001 + "\n")
    assert over, "2001 c devrait declencher"
    assert over[0]["chars"] == 2001


def test_fixture_section_1_fires():
    """La section 1 de la fixture (paragraphe-mur fondateur) tire."""
    section = _read_section("Section 1")
    got = detect(section)
    walls = [f for f in got if f["type"] == "oversized_paragraph"]
    assert walls, f"section 1 muette : devrait tirer (mur fondateur). got={got}"


def test_fixture_section_2_silent():
    """6 paragraphes aeres (post-fix PR A) -- muets."""
    section = _read_section("Section 2")
    got = detect(section)
    assert not got, f"section 2 (6 paragraphes aeres) devrait etre muette : {got}"


def test_fixture_section_3_silent():
    """Fence code de 5000 chars ne declenche pas."""
    section = _read_section("Section 3")
    got = detect(section)
    assert not got, f"section 3 (fence code longue) ne devrait pas tirer : {got}"


def test_fixture_section_4_silent():
    """Bloc CATALOG-STATUS (commentaire HTML) ignore."""
    section = _read_section("Section 4")
    got = detect(section)
    assert not got, f"section 4 (CATALOG-STATUS + paragraphe court) muette : {got}"


def test_fixture_section_5_silent():
    """Titre H1 + ligne de tableau de 5000 chars ignores."""
    section = _read_section("Section 5")
    got = detect(section)
    assert not got, f"section 5 (titre + tableau long) ne devrait pas tirer : {got}"


def test_iter_paragraphs_ignores_fences():
    """Le decoder ne voit PAS les 5000 chars du code dans une fence."""
    text = (
        "Avant la fence.\n\n"
        "```python\n"
        "# code de 3000 chars dans la fence\n"
        + ("x" * 3000) + "\n"
        "```\n\n"
        "Apres la fence.\n"
    )
    paras = iter_paragraphs(text)
    bodies = [body for _, _, body in paras]
    joined = " ".join(bodies)
    assert "x" * 3000 not in joined, "le code de la fence a fuit dans un paragraphe"


def test_iter_paragraphs_keeps_list_with_long_item():
    """Une liste avec un item de 2500 chars doit etre signalee (meme si
    c'est une liste -- c'est de la prose continue, pas de la structure)."""
    text = "- item tres long : " + ("bla " * 500) + "\n- item court.\n"
    got = detect(text)
    walls = [f for f in got if f["type"] == "oversized_paragraph"]
    assert walls, "item de liste > 2000 c devrait etre signale"


def _bullet_run(n_items: int, per_item: int) -> str:
    """Un run de `n_items` items de liste contigus, chacun de `per_item` c."""
    return "".join(f"- **Champ{i}** : " + ("mesure " * (per_item // 7)) + "\n"
                   for i in range(n_items))


def test_bullet_run_of_short_items_is_silent():
    """Controle de NON-REGRESSION #15512 : un run d'items courts n'est pas
    un mur.

    La preuve d'appartenance au motif est verifiee d'abord (le run depasse
    le seuil *en somme* et chaque item reste dessous) : sans elle, le test
    serait vacuement vert -- il passerait aussi sur un texte anodin.
    """
    run = _bullet_run(n_items=6, per_item=580)
    items = [ln for ln in run.splitlines() if ln.strip()]
    assert len(items) == 6
    assert sum(len(ln) for ln in items) > MAX_PARAGRAPH_LEN, (
        "controle vacue : le run ne depasse pas le seuil en somme")
    assert max(len(ln) for ln in items) <= MAX_PARAGRAPH_LEN, (
        "controle vacue : un item depasse deja le seuil tout seul")
    assert detect(run) == [], (
        "un run de 6 items courts (chacun <= seuil) ne doit pas tirer -- "
        "c'est la classe de faux positifs #15512 (MANIFEST)")


def test_single_long_bullet_still_fires():
    """Controle POSITIF de la segmentation : **un** item long tire toujours.

    Borne le fix precedent -- la segmentation par-item ne doit pas eteindre
    l'intention documentee du module (« un item de liste de 10k caracteres
    est un mur aussi »).
    """
    run = _bullet_run(n_items=1, per_item=2400)
    got = detect(run)
    assert got, "un item de liste unique > seuil doit tirer"
    assert got[0]["chars"] > MAX_PARAGRAPH_LEN


def test_bullet_run_splits_each_item_as_its_own_block():
    """`iter_paragraphs` rend un bloc par item (pas la somme du run)."""
    run = _bullet_run(n_items=4, per_item=700)
    blocks = iter_paragraphs(run)
    bodies = [b for _, _, b in blocks if b.strip()]
    assert len(bodies) == 4, f"attendu 4 blocs, obtenu {len(bodies)}"
    assert all("\n" not in b for b in bodies), (
        "chaque item doit etre son propre bloc")


def test_bullet_run_then_prose_is_not_merged_into_an_item():
    """La prose qui suit un item lui reste attachee (continuation
    paresseuse markdown) : elle n'ouvre pas un bloc separe."""
    text = "- item.\nprose collee a l'item.\n"
    blocks = [b for _, _, b in iter_paragraphs(text) if b.strip()]
    assert len(blocks) == 1
    assert "prose collee" in blocks[0]


def test_detect_returns_sorted_findings():
    """Les findings sont tries par longueur decroissante (les murs
    d'abord), puis par start_line croissant."""
    text = (
        "court.\n\n"
        + ("a" * 2500) + "\n\n"
        + ("b" * 2100) + "\n\n"
        "encore court.\n"
    )
    got = detect(text)
    assert len(got) == 2
    assert got[0]["chars"] == 2500
    assert got[1]["chars"] == 2100


def test_max_paragraph_len_locked():
    """Le seuil est un module constant, PAS un argument CLI."""
    assert MAX_PARAGRAPH_LEN == 2000


def test_self_test_runs_clean():
    """Le --self-test ne fait pas d'I/O, son resultat est l'assertion."""
    from detect_paragraph_length import self_test
    assert self_test() == 0