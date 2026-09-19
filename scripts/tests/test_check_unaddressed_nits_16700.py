"""Tests for #16700 — la levée EN OUVERTURE n'est pas une émission de réserve.

Défaut fondateur (#16381, 2026-09-18T13:47:46Z sous `jsboige`) : la levée
ouvrait sur un heading (« ## Levée de la réserve NanoClaw ») mais portait un
glyphe cité (🔴) et un résidu mineur — l'étage lift complet de `classify` ne
l'absorbait pas (glyphe vif), la prose sans CRLF tombait dans BOT-CONCERN.
Le geste qui DÉBLOQUAIT la PR créait un nit de plus à son propre nom, régime
absorbant : chaque nouvelle tentative de levée sous le même login aggravait le
compte. Mesure dans l'issue : `rc=1`, le nit n°1 = la levée elle-même.

Double peine mesurée au passage : `explicit_lifts` exige `classify(...) is
None` — le commentaire compté comme nit ne pouvait PAS non plus lever la
réserve qu'il annonçait lever. Le fix au niveau `classify` guérit les deux.

Discriminant retenu (piste 1 de l'issue) : la POSITION. Ouvrir son corps sur
« Réserve levée » / « Levée de la réserve » / « Je lève la réserve » est un
geste de résolution par construction, quel que soit l'auteur — l'identité est
le mauvais discriminant quand le trousseau gh bascule sans geste délibéré.
Le vocabulaire est volontairement ÉTROIT : le mot RESERVE fait partie du
discriminant. Mesure avant/après (audit 25 PRs mergées 2026-09-18, fenêtre
00:41→15:09) : 4 PRs flaggées avant, les MÊMES 4 après, nits identiques —
0 VP / 0 FP sur le corpus réel, dont :
  - #16619 « ## Je leve ma propre reserve 🟡, et je retiens celle d'Hermes »
    reste BOT-CONCERN (CORRECT : l'auteur déclare RETENIR une réserve —
    commentaire mixte à résidu vivant, pinné ci-dessous) ;
  - #16617 « ## Levée des deux réserves, par leur auteur ou par issue
    nommée » reste BOT-CONCERN (plural hors vocabulaire, near-miss documenté
    dans le body de la PR) ;
  - #16656 nit HUMAN jsboige (vrai nit user CRLF) reste HUMAN — contrôle
    positif : l'assouplissement ne touche pas les nits user sans ouverture
    de levée.

Aucun appel réseau : `classify` est pure, on lui passe le corps.
"""
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

# VERBATIM — commentaire 5730922323 de #16381 (jsboige, 2026-09-18T13:47:46Z).
# Le corps complet est la loi de la famille de tests : les glyphes cités, le
# résidu « Mineur 2 » et la table de vérification sont précisément CE qui
# faisait échouer l'étage lift complet — tronquer le corps ferait mesurer
# un autre commentaire que celui de l'incident.
FOUNDING_16381 = """## Levée de la réserve NanoClaw — vérifiée moi-même au head `da003d54a`, et un mot résiduel

La review porte sur le head `9d1807f9`. Le head courant est `da003d54a`. **Un commit poussé ne lève rien par lui-même** (B.0 : ce qui lève est une phrase, pas un SHA) — voici donc la phrase, avec ce que j'ai mesuré en ouvrant le notebook au head de la PR, pas en lisant le body.

### 🔴 Le concern bloquant est traité

NanoClaw relevait que la cellule « Lecture des statistiques » enseignait `1 722 s` / `4,8 km` là où le `describe` committé dit `1433.571429` / `4.412500`. Au head courant, la cellule dit :

> moyennes **1 434 s** et **4,4 km**

`1433.571429 → 1 434` et `4.4125 → 4,4`. Les deux valeurs sont désormais ancrées sur la sortie que la cellule commente. Le défaut était réel et sérieux — c'est *la* cellule qui apprend à lire un `describe` — et il est corrigé au bon endroit : dans la prose, pas dans la sortie.

### Mineur 1 : traité, et mieux que demandé

« écart-type ~ 1 000 s » (réel 957,98) est devenu :

> écart-type ~ **958 s** *(cellule describe plus haut)*

La valeur est juste **et** la parenthèse dit désormais au lecteur **où** la vérifier. C'est la bonne forme.

### Mineur 2 : non traité — un mot

La cellule écrit encore :

> `vendor_id` et `payment_type` sont de type `object` (chaînes)

La sortie committée juste au-dessus affiche :

```
vendor_id                str
payment_type             str
dtype: object
```

Sous pandas 2.x les colonnes sortent en `str`. Le seul `object` visible est le `dtype:` de pied — celui de la **Series des dtypes**, pas celui des colonnes. Dans n'importe quelle autre cellule je laisserais passer : le raisonnement (non-numérique → one-hot) est juste. Ici non — c'est la cellule dont le sujet est *lire la sortie*, et confondre le dtype d'une colonne avec le `dtype:` de pied de Series est précisément l'erreur de lecture qu'un étudiant commet à cet endroit. La prose la renforcerait.

**Un mot suffit**, par exemple : *« sont de type texte (`str` dans la sortie ci-dessus, `object` dans l'ancienne nomenclature pandas) »*. Je ne demande rien d'autre.

### Ce que j'ai vérifié par ailleurs

| Contrôle | Mesure au head `da003d54a` |
|---|---|
| Lignes du diff touchant `execution_count` / `outputs` / `cell_type: code` | **0** |
| Cellules ajoutées | markdown uniquement (corrobore le comptage cell-by-cell de NanoClaw) |
| Exception C.2 « markdown seul » | **applicable**, littéralement |
| Fichiers `twin_pairs.d/` | 4 fichiers d'accrétion, +6 lignes chacun — forme attendue |

Je **ne** revérifie pas l'ancrage des ~28 autres nombres : NanoClaw les a confrontés un à un aux sorties committées et son échantillon est cité. Rejouer ce travail serait le payer deux fois.

### Suite

Je merge dès que le mot de ML-2 est poussé — le gate et le `DWELL` courent de toute façon. Pas d'autre demande, pas de re-review nécessaire : poussez, dites-le ici, je prends.
"""


def test_fondateur_16381_levee_sous_jsboige_nest_plus_un_nit():
    """Avant : BOT-CONCERN (mesuré dans l'issue, nit n°1). Apres : None."""
    assert mod.classify("jsboige", FOUNDING_16381) is None


def test_fondateur_16381_devient_eligible_comme_levee():
    """Double peine guerie : explicit_lifts exige classify(...) is None ET
    has_live_lift. Le fondateur satisfait les deux apres le fix."""
    assert mod.has_live_lift(mod._strip_adjoint_dossier(FOUNDING_16381))
    assert mod.classify("jsboige", FOUNDING_16381) is None


def test_reserve_levee_en_gras():
    """La seconde levée de #16381 (myia-ai-01, 14:39:41Z) : deja None par
    l'etage lift complet, l'ouverture la couvre aussi."""
    body = ("**Réserve levée.** Le résidu que j'avais signalé est traité, "
            "et mieux que demandé.")
    assert mod.classify("myia-ai-01", body) is None
    assert mod._opens_on_lift(body)


def test_variantes_douverture():
    for body in (
        "## Levee de la reserve NanoClaw — sans accents",  # unaccented
        "## **Réserve levée** — heading et gras cumules",
        "Je lève la réserve NanoClaw ici même.",
        "Réserve dissipée : le run 123 est vert et lu.",
    ):
        assert mod._opens_on_lift(body), body


def test_negatifs_douverture():
    for body in (
        "Levée des alertes CI : le run 123 est vert, reste le 456.",  # rapport
        "Réserve : le describe contredit 1 722 s.",  # reservation, pas levee
        "D'abord le contexte, la réserve levée vient plus bas.",  # pas en tete
        "",
    ):
        assert not mod._opens_on_lift(body), body


def test_controle_positif_vrai_nit_user_crlf():
    """Un vrai nit user (CRLF, pas d'ouverture de levee) reste HUMAN."""
    body = ("Il reste un souci :\r\nla cellule dit 1 722 s mais le describe "
            "dit 1433.57.")
    assert mod.classify("jsboige", body) == "HUMAN"


def test_controle_positif_verdict_reviewer():
    """Un verdict de reviewer reste BOT-CONCERN meme sous le meme login."""
    body = ("VERDICT: CONCERNS **[NanoClaw]** review structurelle (PR +15/-1, "
            "1 fichier) — ancrage non verifie.")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_mixte_16619_reserve_retenue_survit():
    """#16619 (corpus de mesure) : « ## Je leve ma propre reserve 🟡, et je
    retiens celle d'Hermes » — l'auteur DECLARE RETENIR une reserve. Hors
    vocabulaire d'ouverture (« ma propre »), et c'est CORRECT : le residu
    est vivant par propre declaration de l'auteur."""
    body = ("## Je leve ma propre reserve 🟡, et je retiens celle d'Hermes\n\n"
            "### 1. Mon nit `Grain:` — LEVE\nMa remarque du 2026 reste "
            "valable pour Hermes.")
    assert not mod._opens_on_lift(body)
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN"


def test_blocage_precede_ouverture_de_levee():
    """Fail-closed : un blocage coordinateur EMIS dans le corps reste BLOCK
    meme si le corps ouvre sur une levee. Le glyphe 🟡 neutralise l'etage
    lift complet (cas fondateur) — c'est alors `_block_emitted`, place AVANT
    l'ouverture-de-levee, qui decide ; le marqueur de protocole `[BLOCAGE]
    lane` pose en tete de ligne est la forme ABSOLUE (a). Comportement
    preexistant signale au passage : SANS glyphe, l'etage lift complet du
    dessus absorbe deja un « levee + BLOCAGE » (le lift vif l'emporte sur
    le bloc) — hors scope de ce fix, inchange ici."""
    body = ("Réserve levée sur le volet densité, verdict vérifié au head. 🟡\n"
            "[BLOCAGE] lane myia-ai-01:CoursIA — path defect, must be fixed "
            "before any merge.")
    assert mod._opens_on_lift(body)
    assert mod.classify("myia-ai-01", body) == "BLOCK"
