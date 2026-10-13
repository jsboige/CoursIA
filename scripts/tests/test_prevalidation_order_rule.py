"""Epingle : la regle porte l'ORDRE du dossier de prevalidation une seule fois, et juste.

Pourquoi ce fichier existe
--------------------------
#16878. Le 2026-09-19, le gate d'entree de la passe de merge a refuse **17 candidates
sur 17**, aucune pour un defaut de PR : le dossier de prevalidation atteste une
**tete**, et `gh pr update-branch` change la tete.

L'issue fondatrice motivait la boucle par un mecanisme qui est **faux depuis
#16149** : « `update-branch` re-arme le plancher DWELL pour 120 min ». Un
rafraichissement de base content-free est **saute** par le predicat
`last_authoritative_committed_at` — le plancher reste **inchange**.

Apres la reduction du 2026-09-23 (reserve #17289), la livraison de cette branche
est **l'epingle elle-meme**, plus une seconde redaction : #16879 puis #16963
avaient deja mis sur `main` — dans la puce « `update-branch` tue AUSSI le dossier
de prevalidation » — l'ordre en 4 temps, le gel, la mesure fondatrice ET la
correction #16962 du claim DWELL.

Les trois risques que cette epingle ferme :

1. **reintroduire la claim DWELL fausse** en « completant » la regle de bonne foi
   (c'est ce que #16962/#17286 venaient de retirer — et ce que l'etape 2 de la
   section ajoutee par cette branche avait fait) ;
2. **perdre l'ordre en 4 temps**, seule livraison qui debloque la boucle, au
   profit du seul constat « la tete change » ;
3. **ouvrir une seconde surface** qui redit la meme regle : deux redactions
   divergent, c'est le defaut de #16962 sur ce meme fichier.

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

#: La puce qui porte la seconde moitie du mecanisme — surface UNIQUE depuis #17289.
_BULLET = "\n- **`update-branch` tue AUSSI le dossier de prévalidation"
#: Un titre de sous-section qui redirait la meme regle (#17289 : a ne pas rouvrir).
_SECOND_SURFACE = re.compile(r"\n### [^\n]*dossier de prévalidation")

#: La claim DWELL perimee — celle que la puce ne doit PAS rapporter.
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
    """Normalise espaces, accents, casse ET balisage (meme discipline que l'epingle DWELL).

    Le balisage (`*`, backticks) est retire parce que les epingles ci-dessous
    visent le CONTENU des claims, pas leur mise en forme : un marqueur qui
    casserait sur un `**gras**` ajoute plus tard mesurerait la typographie au
    lieu de la regle.
    """
    folded = unicodedata.normalize("NFKD", text)
    folded = "".join(c for c in folded if not unicodedata.combining(c))
    folded = folded.replace("*", "").replace("`", "")
    return re.sub(r"\s+", " ", folded).lower()


def _rule_text() -> str:
    return RULE.read_text(encoding="utf-8")


def _order_section() -> str:
    """La PUCE « update-branch tue AUSSI le dossier », bornee a la puce suivante.

    L'ancrage est le debut de la puce, pas la phrase nue : un `find` sur
    « dossier de prévalidation » attraperait la premiere occurrence du texte, et
    une mention de la phrase ailleurs dans le fichier ferait deriver la borne --
    l'epingle testerait alors un voisinage sans rapport en le declarant vert.

    Sans borne haute, une assertion « tel mot est absent » pourrait de meme etre
    satisfaite (ou cassee) par du texte sans rapport.
    """
    text = _rule_text()
    start = text.find(_BULLET)
    assert start >= 0, "la puce « update-branch tue AUSSI le dossier » a disparu"
    rest = text[start + 1:]
    following = re.search(r"\n- \*\*", rest)
    return rest[: following.start()] if following else rest


# ------------------------------- 1. la puce ne rapporte pas la claim DWELL perimee

def test_bullet_does_not_restate_the_stale_dwell_claim():
    """#16149 : un rafraichissement content-free laisse le plancher INCHANGE."""
    assert _STALE_DWELL.search(_norm(_order_section())) is None


def test_negative_control_the_old_dwell_wording_is_flagged():
    """Controle negatif — sans lui, l'epingle ci-dessus serait un test vide."""
    assert _STALE_DWELL.search(_norm(_OLD_CLAIM)) is not None


# ------------------------------------- 2. une seule surface porte la regle (#17289)

def test_rule_does_not_open_a_second_surface_for_the_same_rule():
    """#17289 : la branche ajoutait une sous-section qui redit l'ordre de la puce.

    Mesure firsthand de la reserve : la section `### update-branch et le dossier
    de prevalidation` (l.51-70 de la branche) reprenait l'ordre en 4 temps, le
    gel ET la mesure fondatrice deja portes par la puce l.43-52 -- et son etape 2
    redisait la claim DWELL que #16962 venait de corriger. La duplication n'est
    pas seulement du poids : elle **re-derive**.
    """
    text = _rule_text()
    assert _SECOND_SURFACE.search(text) is None, (
        "une seconde surface redit la regle : la puce est la surface unique"
    )
    assert text.count(_BULLET) == 1, "la puce est dupliquee dans la regle"


def test_negative_control_a_synthetic_second_section_is_flagged():
    """Controle negatif : le detecteur mord sur la forme qu'il pretend interdire."""
    synthetic = "\n### update-branch et le dossier de prévalidation — l'ordre\n\ntexte\n"
    assert _SECOND_SURFACE.search(synthetic) is not None


# ------------------------------------------------- 3. la seconde moitie est portee

def test_bullet_names_the_attested_surface_as_the_head():
    """Le fait qui fonde tout : le dossier atteste une TETE, pas une PR."""
    bullet = _norm(_order_section())
    assert "exact-head" in bullet
    assert "perime" in bullet
    assert "head is stale" in bullet


def test_bullet_cross_references_instead_of_restating():
    """Anti-derive (#16962) : le fait est deja dans le skill -> renvoi, pas copie.

    Le renvoi doit ETRE un lien, pas une simple mention : c'est ce qui rend la
    surface unique verifiable.
    """
    bullet = _order_section()
    assert "coordinate/SKILL.md" in bullet, "le renvoi au skill a disparu"
    assert "../skills/coordinate/SKILL.md" in bullet, "le renvoi n'est plus un lien"


# -------------------------------------------------------- 4. l'ordre en 4 temps

def test_bullet_carries_the_four_step_order():
    bullet = _norm(_order_section())
    for marker in ("si elle doit recuperer main", "on rejoue",
                   "alors l'adjoint ecrit le dossier", "merge immediatement"):
        assert marker in bullet, "etape absente de l'ordre : {}".format(marker)
    assert "personne ne re-pousse" in bullet, "le garde anti-push a disparu"


def test_bullet_names_the_branch_freeze_as_the_condition():
    """Le gel est la seule piece qui ne se deduit pas du mecanisme."""
    bullet = _norm(_order_section())
    assert "gelee entre 3 et 4" in bullet
    assert "silencieuse" in bullet, "la raison du gel (branche silencieuse) a disparu"


def test_bullet_cites_the_founding_measurement():
    """Sans la mesure, la regle se relit comme une precaution theorique."""
    assert "17 candidates sur 17" in _norm(_order_section())


# ------------------------------------------------- 5. le detail porte les preuves

def test_detail_doc_exists_and_quotes_the_organ():
    assert DETAIL.exists(), "le detail deporte a disparu"
    detail = _norm(DETAIL.read_text(encoding="utf-8"))
    for marker in ("head is stale", "diff-files is stale",
                   "surfaces changed or were not fully attested"):
        assert marker in detail, "verbatim de l'organe absent du detail : {}".format(marker)


def test_detail_doc_marks_the_measurement_as_reported():
    """Honteete SDDD : 17/17 est un temoignage date, le mecanisme est ce qui est verifie."""
    detail = _norm(DETAIL.read_text(encoding="utf-8"))
    assert "rapporte par l'issue" in detail
    assert "non re-mesure" in detail


def test_detail_doc_defers_to_the_rule_for_the_order():
    """#17289 : le detail explique le POURQUOI, il ne rejoue pas l'ordre."""
    detail = _norm(DETAIL.read_text(encoding="utf-8"))
    assert "la regle fait foi" in detail
    assert "il n'est pas recopie ici" in detail or "pas recopie ici" in detail


def test_organ_still_emits_the_three_refusal_shapes():
    """Si l'organe changeait, les verbatim cites par le detail deviendraient faux."""
    organ = ORGAN.read_text(encoding="utf-8")
    assert 'f"{key} is stale: dossier=' in organ
    assert '"head is stale: dossier=' in organ