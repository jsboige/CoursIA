"""Epingle : la regle DWELL ne doit pas contredire l'organe qui l'implemente.

Pourquoi ce fichier existe
--------------------------
#16962. La ligne `.claude/rules/git-workflow.md` affirmait, jusqu'au
2026-09-21, que « `gh pr update-branch` remet le plancher DWELL a zero
(#15859) ». C'etait **vrai avant #16149** et **faux depuis** : `scripts/ci/
merge_dwell.py` mesure desormais le plancher par
`last_authoritative_committed_at`, qui saute les fusions de rafraichissement
de base **prouvees content-free**.

La meme ligne portait un SECOND ecart, trouve par la meme passe : elle appelait
le balayage « horaire » alors que le message du gate ecrit par l'organe dit
l'inverse (« cadence MESUREE 2 h 33 - 5 h 18 entre tirs, **pas horaire** »).

Le defaut a vecu ~5 jours sans etre vu parce que **rien ne comparait les deux
surfaces**. C'est ce que ce fichier fait.

Ce que l'epingle couvre, et ce qu'elle ne couvre PAS (honnetete)
---------------------------------------------------------------
Elle couvre des **invariants inter-surface** : deux surfaces qui doivent dire
la meme chose sont comparees, et la claim fausse est interdite de retour.
Elle ne couvre **pas** la classe entiere « une regle cite un organe et se
trompe » — un test ne peut pas verifier une affirmation en langue naturelle
contre un comportement arbitraire. Elle attrape l'**instance** et empeche sa
**regression**, ce qui est la portee reelle d'une epingle.

Chaque test a son **controle negatif** : le texte d'AVANT le correctif doit
etre signale par le meme predicat. Sans ce controle, une epingle qui passe
toujours serait indiscernable d'un test vide.
"""
import re
import unicodedata
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
RULE = REPO_ROOT / ".claude" / "rules" / "git-workflow.md"
ORGAN = REPO_ROOT / "scripts" / "ci" / "merge_dwell.py"

#: La phrase d'AVANT correctif, verbatim (pour les controles negatifs).
OLD_LINE = (
    "- **`gh pr update-branch` remet le plancher DWELL à zéro** (#15859) : le "
    "plancher de merge (120 min, `scripts/ci/merge_dwell.py`) se mesure depuis "
    "le **dernier commit** de la branche, et `update-branch` en crée un (merge "
    "commit). Rafraîchir sa branche pour récupérer un fix de `main` repousse "
    "donc le merge de 120 min — et tout plancher déjà noté dans un rapport est "
    "périmé. Ce rouge n'est **pas un défaut de la PR** : le gate le nomme "
    "`DWELL -- ... leve au premier balayage suivant <ts>` et le balayage "
    "horaire (`pr-gate-stale-sweep.yml`) lève seul. Ne pas re-pusher pour "
    "« réparer » : chaque push re-arme le plancher depuis la nouvelle tête."
)

#: « update-branch remet le plancher a zero » — la claim perimee par #16149.
_STALE_FLOOR_RESET = re.compile(
    r"update-branch`?\s+remet\s+le\s+plancher\s+DWELL", re.IGNORECASE
)

#: Le balayage decrit comme horaire — l'organe dit « pas horaire ».
_HOURLY_SWEEP = re.compile(r"balayage\s+horaire", re.IGNORECASE)


def _norm(text: str) -> str:
    """Normalise espaces, accents ET casse.

    Les trois servent la meme fin : une epingle ne doit pas dependre d'un
    detail de frappe (un paragraphe replie, un accent pose ou non, une
    capitale) — sans quoi elle signale une reformulation au lieu d'une
    regression. Les marqueurs compares a `_norm(...)` s'ecrivent donc en
    minuscules SANS accent.
    """
    folded = unicodedata.normalize("NFKD", text)
    folded = "".join(c for c in folded if not unicodedata.combining(c))
    return re.sub(r"\s+", " ", folded).lower()


def stale_floor_reset_claims(text: str):
    """Claims « update-branch remet le plancher a zero » presentes dans `text`."""
    return _STALE_FLOOR_RESET.findall(_norm(text))


def hourly_sweep_claims(text: str):
    """Descriptions du balayage comme « horaire » presentes dans `text`."""
    return _HOURLY_SWEEP.findall(_norm(text))


def _rule_text() -> str:
    return RULE.read_text(encoding="utf-8")


def _dwell_section() -> str:
    """Le voisinage DWELL de la regle, borne a la fin de son bloc.

    Borne haute = la prochaine frontiere de section (`### ` ou `---`) : sans
    elle, une assertion « tel mot est absent » pourrait etre satisfaite (ou
    cassee) par du texte sans rapport, ce qui rendrait l'epingle muette sur ce
    qu'elle pretend mesurer.
    """
    text = _rule_text()
    start = text.find("DWELL")
    assert start >= 0, "la regle ne mentionne plus DWELL : epingle a reancrer"
    rest = text[start:]
    bounds = [m.start() for m in re.finditer(r"\n(?:### |---)", rest)]
    return rest[:bounds[0]] if bounds else rest


# ------------------------------------------------------- 1. la claim perimee

def test_rule_does_not_claim_update_branch_resets_the_floor():
    """#16149 : une fusion de base content-free NE re-arme PAS le plancher."""
    assert stale_floor_reset_claims(_dwell_section()) == []


def test_negative_control_the_old_wording_is_flagged():
    """Controle negatif — sans lui, l'epingle ci-dessus serait un test vide."""
    assert stale_floor_reset_claims(OLD_LINE) != []


# --------------------------------------------------- 2. le predicat est nomme

def test_rule_names_the_real_predicate():
    """La regle doit nommer l'organe par ce qui le definit, pas par « dernier commit ».

    Nuance qui compte : « le dernier commit de la branche » et « le dernier
    commit qui MODIFIE le cote PR » different exactement sur le cas
    update-branch — c'est l'erreur d'origine.
    """
    section = _norm(_dwell_section())
    assert "last_authoritative_committed_at" in section
    assert "dernier commit" not in section or "modifie le cote pr" in section


def test_rule_states_the_three_conjunctive_conditions():
    """Les trois conditions sont conjonctives : en oublier une rend le predicat faux."""
    section = _norm(_dwell_section())
    for marker in ("deux parents", "ancetre de la base", "auto-merge"):
        assert marker in section, "condition absente de la regle : {}".format(marker)


def test_rule_carries_the_gesture_matrix():
    """La matrice geste -> effet : c'est elle qui rend la regle operatoire."""
    section = _norm(_dwell_section())
    for gesture in ("sans conflit", "avec resolution de conflit", "rebase"):
        assert gesture in section, "geste absent de la matrice : {}".format(gesture)


# ------------------------------------- 3. #15859 conserve comme historique

def test_15859_kept_as_corrected_history():
    """Acceptance #16962 : le defaut a existe, on le date, on ne l'efface pas."""
    section = _dwell_section()
    assert "#15859" in section, "le defaut d'origine doit rester date (#15859)"
    assert "#16149" in section, "le correctif d'origine doit rester date (#16149)"


# ------------------------------- 4. l'invariant de cadence, organe <-> regle

def test_organ_still_declares_the_sweep_not_hourly():
    """Si l'organe changeait d'avis, l'invariant ci-dessous deviendrait faux."""
    organ = ORGAN.read_text(encoding="utf-8")
    assert "pas horaire" in _norm(organ)
    assert "2 h 33 - 5 h 18" in _norm(organ)


def test_rule_does_not_call_the_sweep_hourly():
    """L'organe dit « pas horaire » : la regle ne peut pas dire « horaire »."""
    assert hourly_sweep_claims(_dwell_section()) == []


def test_negative_control_the_old_hourly_claim_is_flagged():
    assert hourly_sweep_claims(OLD_LINE) != []
