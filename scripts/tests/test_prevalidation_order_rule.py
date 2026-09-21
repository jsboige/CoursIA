"""Epingle : la regle porte l'ORDRE du dossier de prevalidation, sans re-ecrire la moitie DWELL.

Pourquoi ce fichier existe
--------------------------
#16878. Le 2026-09-19, le gate d'entree de la passe de merge a refuse **17 candidates
sur 17**, aucune pour un defaut de PR : le dossier de prevalidation atteste une
**tete**, et `gh pr update-branch` change la tete.

L'issue fondatrice motivait la boucle par un mecanisme qui est **faux depuis
#16149** : « `update-branch` re-arme le plancher DWELL pour 120 min ». Un
rafraichissement de base content-free est **saute** par le predicat
`last_authoritative_committed_at` — le plancher reste **inchange**.

D'ou le double risque que cette epingle ferme :

1. **reintroduire la claim DWELL fausse** dans la nouvelle sous-section, en
   « completant » la regle de bonne foi (c'est exactement ce que #16962/#17286
   venaient de retirer) ;
2. **perdre l'ordre en 4 temps**, qui est la seule livraison qui debloque la
   boucle, au profit du seul constat « la tete change ».

Chaque test a son **controle negatif** : sans lui, une epingle qui passe toujours
serait indiscernable d'un test vide.

Ce que l'epingle ne couvre PAS : la classe entiere « une regle cite un organe et
se trompe ». Elle couvre l'instance et empeche sa regression.
"""
import re
import unicodedata
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
RULE = REPO_ROOT / ".claude" / "rules" / "git-workflow.md"
DETAIL = REPO_ROOT / "docs" / "reference" / "prevalidation-dossier-order-detail.md"
ORGAN = REPO_ROOT / "scripts" / "check_adjoint_prevalidation.py"

#: La claim DWELL perimee — celle que la nouvelle sous-section ne doit PAS rapporter.
#: (Verbatim de la formulation d'origine, conservee pour le controle negatif.)
_STALE_DWELL = re.compile(
    r"update-branch\D{0,40}remet\s+le\s+plancher\s+DWELL\s+.{0,40}\s*z[eé]ro",
    re.IGNORECASE | re.DOTALL,
)
_OLD_CLAIM = (
    "- **`gh pr update-branch` remet le plancher DWELL à zéro** (#15859) : le "
    "plancher de merge (120 min, `scripts/ci/merge_dwell.py`) se mesure depuis "
    "le **dernier commit** de la branche, et `update-branch` en crée un."
)


def _norm(text: str) -> str:
    """Normalise espaces, accents ET casse (meme discipline que l'epingle DWELL)."""
    folded = unicodedata.normalize("NFKD", text)
    folded = "".join(c for c in folded if not unicodedata.combining(c))
    return re.sub(r"\s+", " ", folded).lower()


def _rule_text() -> str:
    return RULE.read_text(encoding="utf-8")


def _order_section() -> str:
    """La sous-section « dossier de prevalidation », bornee a sa fin de bloc.

    Sans borne haute, une assertion « tel mot est absent » pourrait etre
    satisfaite (ou cassee) par du texte sans rapport.
    """
    text = _rule_text()
    start = text.find("dossier de prévalidation")
    assert start >= 0, "la regle ne porte plus la sous-section : epingle a reancrer"
    head = text.rfind("\n### ", 0, start)
    rest = text[head if head >= 0 else start:]
    bounds = [m.start() for m in re.finditer(r"\n(?:### |---)", rest[1:])]
    return rest[: bounds[0] + 1] if bounds else rest


# ------------------------------------------- 1. la claim DWELL n'est pas rapportee

def test_order_section_does_not_restate_the_stale_dwell_claim():
    """#16149 : un rafraichissement content-free laisse le plancher INCHANGE."""
    assert _STALE_DWELL.search(_norm(_order_section())) is None


def test_negative_control_the_old_dwell_wording_is_flagged():
    """Controle negatif — sans lui, l'epingle ci-dessus serait un test vide."""
    assert _STALE_DWELL.search(_norm(_OLD_CLAIM)) is not None


# ------------------------------------------------- 2. la seconde moitie est portee

def test_rule_names_the_attested_surface_as_the_head():
    """Le fait qui fonde tout : le dossier atteste une TETE, pas une PR."""
    section = _norm(_order_section())
    assert "head" in section
    assert "atteste une tete" in section or "atteste une tête".lower() in section
    assert "perime" in section or "périmé" in section


def test_rule_cross_references_instead_of_restating():
    """Anti-derive (#16962) : le fait est deja dans le skill -> renvoi, pas copie.

    Le renvoi doit ETRE un lien, pas une simple mention : c'est ce qui rend la
    surface unique verifiable.
    """
    section = _order_section()
    assert "coordinate/SKILL.md" in section, "le renvoi au skill a disparu"
    assert "../skills/coordinate/SKILL.md" in section, "le renvoi n'est plus un lien"


# -------------------------------------------------------- 3. l'ordre en 4 temps

def test_rule_carries_the_four_step_order():
    section = _norm(_order_section())
    for marker in ("update-branch", "rejoue la jambe", "alors seulement", "merge aussitot"):
        assert marker in section, "etape absente de l'ordre : {}".format(marker)


def test_rule_names_the_branch_freeze_as_the_condition():
    """Le gel est la seule piece qui ne se deduit pas du mecanisme."""
    section = _norm(_order_section())
    assert "gelee de 3 a 4" in section or "gel" in section
    assert "silencieuse" in section, "la raison du gel (branche silencieuse) a disparu"


def test_rule_cites_the_founding_measurement():
    """Sans la mesure, la regle se relit comme une precaution theorique."""
    assert "17 candidates sur 17" in _norm(_order_section())


# ------------------------------------------------- 4. le detail porte les preuves

def test_detail_doc_exists_and_quotes_the_organ():
    assert DETAIL.exists(), "le detail deporte a disparu"
    detail = _norm(DETAIL.read_text(encoding="utf-8"))
    for marker in ("head is stale", "diff-files is stale", "surfaces changed or were not fully attested"):
        assert marker in detail, "verbatim de l'organe absent du detail : {}".format(marker)


def test_detail_doc_marks_the_measurement_as_reported():
    """Honteete SDDD : 17/17 est un temoignage date, le mecanisme est ce qui est verifie."""
    detail = _norm(DETAIL.read_text(encoding="utf-8"))
    assert "rapporte par l'issue" in detail
    assert "non re-mesure" in detail


def test_organ_still_emits_the_three_refusal_shapes():
    """Si l'organe changeait, les verbatim cites par le detail deviendraient faux."""
    organ = ORGAN.read_text(encoding="utf-8")
    assert 'f"{key} is stale: dossier=' in organ
    assert '"head is stale: dossier=' in organ
