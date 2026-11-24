"""#24141 — « APPROVE avec 1 réserve » : la réserve sur approbation doit
survivre au COMPTE qui la precede.

Cas fondateur : la review Hermes de #24117 (2026-11-02T03:44:09Z, state
APPROVED) s'ouvre par « **Verdict : APPROVE avec 1 réserve 🟡 (arithmétique du
corps).** » — la réserve est posee dans le meme corps que l'approbation.
L'alternative « avec <réserve> » de `_APPROVE_RESERVATION_RE` ne matchait que
« avec réserve(s) » : le « 1 » entre les deux cassait le motif, la branche
APPROVED rendait `kind = None` (l'etat natif decide), et B.0 rendait rc=0.
La PR est partie en merge le 02/11 05:07Z avec la réserve en suspens.

Le correctif elargit l'alternative au compte, a l'article et au determinant
places ENTRE « avec » et « réserve ». « 0 réserve » reste exclue (zero
reserve = aucune reserve, meme logique que les CITERS).

Controles negatifs tires de #13559 (les deux corps REELS mesures le 30/08) :
une review APPROVED qui NOMME la reserve qu'elle leve, ou qui CONVERTIT un
verdict, ne doit toujours pas bloquer. Ils sont charges depuis le module de
reference plutot que recopies, pour ne pas diverger.

Aucun appel reseau : `analyse` est pur sur un PR de synthese.
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"
MENTION_PATH = HERE / "test_check_unaddressed_nits_mention.py"


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


mod = _load("check_unaddressed_nits", CHECK_PATH)
mention = _load("check_unaddressed_nits_mention", MENTION_PATH)

# ---------------------------------------------------------------------------
# Controle POSITIF — le corps REEL de la review Hermes de #24117, verbatim
# (API reviews, 2026-11-02T03:44:09Z, state APPROVED).
# ---------------------------------------------------------------------------
FIXTURE_24117_HERMES = (
    "[Hermes] Review #24117 — re-cléfrage 23 chemins déplacés "
    "(iit.csv, ml-datascience.csv)\n"
    "\n"
    "**Verdict : APPROVE avec 1 réserve 🟡 (arithmétique du corps).** Toutes les "
    "assertions mécaniques du corps ont été rejetouées sur les blobs base/head et "
    "l'arbre main — elles tiennent toutes.\n"
    "\n"
    "**Rejoué et confirmé (blobs git extraits aux deux refs, tailles vérifiées) :**\n"
    "- **Diff exact** : 515 lignes `iit.csv` + 69 `ml-datascience.csv` = 584 "
    "inscriptions modifiées, **colonne `notebook` (0) seule touchée** sur 100 % des "
    "lignes divergentes — `cell_id`, `text_fr`, `text_en`, `txt_es`, `src_hash` "
    "intacts.\n"
    "\n"
    "**Réserve 🟡 — arithmétique interne du corps :** la table « résidu re-mesuré » "
    "liste `ml-datascience.csv | 2` alors que cette table compte **3** clés stales au "
    "moment de la mesure ; la somme des lignes 12+21+2+1 = 36 ≠ total annoncé 37. "
    "Corriger la ligne en « 3 » rend la table auto-cohérente ; n'affecte ni le diff "
    "ni le critère de mort.\n"
)


def _pr_with_review(body, state="APPROVED", login="jsboige"):
    return {
        "author": {"login": "myia-ai-01"},
        "commits": [{"committedDate": "2026-11-02T05:00:00Z"}],
        "comments": [],
        "reviews": [{"author": {"login": login}, "state": state,
                     "submittedAt": "2026-11-02T05:44:09Z", "body": body}],
    }


def _blocking(body, state="APPROVED"):
    res = mod.analyse(_pr_with_review(body, state), [],
                      datetime(2026, 11, 2, 6, tzinfo=timezone.utc))
    return res.get("blocking", res) if isinstance(res, dict) else res


def test_24141_le_verdict_avec_compte_est_classe_concern():
    """Le glyphe 🟡 du corps reel fait bien un constat : le probleme n'est pas
    la detection de la reserve, c'est la REINITIALISATION par la branche
    APPROVED quand le motif « avec <reserve> » ne matchait pas."""
    assert mod.classify("jsboige", FIXTURE_24117_HERMES) == "BOT-CONCERN"


def test_24141_approve_avec_1_reserve_bloque():
    """Controle positif : le corps reel de #24117 doit bloquer (1 bloquant)."""
    assert len(_blocking(FIXTURE_24117_HERMES)) == 1


def test_24141_les_quantites_de_reserve_bloquent():
    """Le compte, l'article et le determinant entre « avec » et « reserve »
    ouvrent la meme famille de trou — ils sont tous pris."""
    for corps in (
        "**[Hermes]** APPROVE avec 1 réserve 🟡 : l'arithmétique du corps est à revoir.",
        "**[Hermes]** APPROVE avec une réserve 🟡 : le point 2 reste ouvert.",
        "**[Hermes]** APPROVE avec 2 réserves 🟡 : les deux points sont ouverts.",
        "**[Hermes]** APPROVE avec deux réserves 🟡 : les deux points sont ouverts.",
        "**[Hermes]** APPROVE avec la réserve 🟡 : le point 2 reste ouvert.",
        "**[Hermes]** APPROVE avec ma réserve 🟡 : le point 2 reste ouvert.",
    ):
        assert len(_blocking(corps)) == 1, corps


def test_24141_zero_reserve_ne_bloque_pas():
    """« 0 réserve » n'est pas une réserve : zero reserve = aucune reserve
    (meme logique que les CITERS, qui excluent « zero » et « 0 »)."""
    corps = ("**[Hermes]** APPROVE avec 0 réserve : le point d'arithmétique du "
             "corps a été corrigé dans le head.")
    assert _blocking(corps) == []


def test_24141_controles_negatifs_13559_intacts():
    """Les deux corps REELS de #13559 (charges depuis le module de reference)
    doivent continuer de ne PAS bloquer : une review APPROVED qui nomme la
    reserve qu'elle leve, ou qui convertit un verdict, n'en pose aucune."""
    assert _blocking(mention.FIXTURE_13496_APPROVE) == []
    assert _blocking(mention.FIXTURE_13027_APPROVE) == []


def test_24141_les_autres_formes_de_reserve_bloquent_toujours():
    """Non-regression : les alternatives deja couvertes (#13559) le restent.

    Le glyphe 🟡 est present comme dans les fixtures de reference : sans un
    constat emis dans le corps, la branche APPROVED n'a rien a reinitialiser
    (l'etat natif decide) et il n'y a rien a bloquer — c'est le cas normal,
    pas une regression."""
    for corps in (
        "**[Hermes]** APPROVE sous reserve 🟡 de la correction du chemin relatif.",
        "**[Hermes]** APPROVE partiel 🟡. Je maintiens ma CHANGES_REQUESTED sur le module B.",
        "**[Hermes]** APPROVE 🟡. Le typo du docstring est a corriger avant merge.",
    ):
        assert len(_blocking(corps)) == 1, corps
