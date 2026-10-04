"""Régression #18336 : « relevée », « soulevée », « enlevée » ne sont pas des levées.

`_live_lift_positions` cherchait `levee` / `levée` par sous-chaîne sans
frontière de mot à GAUCHE : le mot à l'intérieur de « relevée »,
« soulevée » ou « enlevée » matchait, la review porteuse d'un VERDICT
CONCERNS était classée `None` (annonce de levée), et sa réserve
disparaissait du gate. Instance mesurée : review NanoClaw du 28/09 sur
#18314 — « dérive de body relevée sur #18269 » à la position 2498
éteignait deux réserves de précision, B.0 rendait rc=0.

Remède : rejeter un hit dont le caractère précédent est une lettre
(garde 3bis, même rang que la garde underscore). La tolérance préfixe
ne vit qu'à DROITE — aucune forme fléchie française ne préfixe
« levée », donc « est levée », « sont levés », « Mergée » lèvent
toujours (critère 3, contrôles positifs ci-dessous).
"""
import importlib.util
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

BOT = "clusterManager-Myia"


# --- Critère 1 : les trois cas minimaux rendent BOT-CONCERN ---

def test_relevee_dans_concern_ne_leve_pas():
    body = ("**VERDICT: CONCERNS** — deux réserves de précision : "
            "la dérive relevée sur #18269 et le compte de cellules.")
    assert mod.classify(BOT, body) == "BOT-CONCERN"


def test_soulevee_dans_concern_ne_leve_pas():
    body = ("**VERDICT: CONCERNS** — la question soulevée par la review "
            "précédente n'est pas traitée.")
    assert mod.classify(BOT, body) == "BOT-CONCERN"


def test_enlevee_dans_concern_ne_leve_pas():
    body = ("**VERDICT: CONCERNS** — la cellule enlevée laisse une "
            "sortie orpheline, à corriger avant merge.")
    assert mod.classify(BOT, body) == "BOT-CONCERN"


# --- Contrôle instance fondatrice #18314 ---

def test_position_fondatrice_18314_plus_eteinte():
    # Avant le fix : le hit tombait sur « relevée » à ~2498 et classify
    # rendait None. Le remplacement par « notée » est le contrôle croisé
    # de l'issue — les deux corps doivent maintenant classe à l'identique.
    avec = ("**VERDICT: CONCERNS** — réserve 1 : la dérive de body relevée "
            "sur #18269. Réserve 2 : compte de cellules erroné.")
    sans = ("**VERDICT: CONCERNS** — réserve 1 : la dérive de body notée "
            "sur #18269. Réserve 2 : compte de cellules erroné.")
    assert mod.classify(BOT, avec) == mod.classify(BOT, sans) == "BOT-CONCERN"


# --- Critère 2 : une vraie levée rend toujours None ---

def test_vraie_levee_reste_none():
    body = "Réserve levée : corrigé au commit abc1234."
    assert mod.classify(BOT, body) is None


def test_vraie_levee_apres_concern_reste_none():
    # Le chemin complet de `_live_lift_positions` dans le comparateur
    # d'ordre : une levée VIVE après un verdict doit éteindre la réserve.
    body = ("**VERDICT: CONCERNS** — point de précision. "
            "Réserve levée : corrigé au commit abc1234.")
    assert mod.classify(BOT, body) is None


# --- Critère 3 : formes fléchies à droite lèvent toujours ---

def test_est_levee_leve_toujours():
    body = "**VERDICT: CONCERNS** — point mineur. La réserve est levée au commit abc1234."
    assert mod.classify(BOT, body) is None


def test_sont_leves_leve_toujours():
    body = "**VERDICT: CONCERNS** — points mineurs. Les deux réserves sont levées au commit abc1234."
    assert mod.classify(BOT, body) is None


def _positions(texte: str):
    # `_live_lift_positions` attend une entrée déjà unaccentée — tous
    # ses appelants réels passent `_unaccent(body)` d'abord.
    return mod._live_lift_positions(mod._unaccent(texte))


def test_mergee_leve_toujours():
    # « Mergé » dans « Mergée » : match préfixe à droite assumé (#16103),
    # casse préservée. (Sans astérisques : une plage **...** est
    # neutralisée par _QUOTED_RANGES avant la garde — préexistant.)
    assert _positions("corrigé puis Mergée au commit abc1234")


# --- Frontière : la garde ne touche que la gauche ---

def test_hit_en_debut_de_phrase_non_precede_de_lettre_leve():
    # « levée » en tête après ponctuation : émission valide
    assert _positions("point traité. levée du blocage : commit abc1234")


def test_hit_precede_d_underscore_deja_filtre():
    # Garde (3) d'origine : identifiant snake_case, pas une émission
    assert not _positions("py::test_15837_candidat_refuse_levee_devant_le_marqueur")


def test_relevee_seul_sans_concern():
    # Sans verdict ni glyphe, « relevée » n'était de toute façon pas un
    # concern — le classement reste None, mais pour la bonne raison
    # (aucune émission), pas parce qu'une levée fantôme a tout éteint.
    assert not _positions("constat : dérive de body relevée sur #18269")
