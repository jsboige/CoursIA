"""Position J (D)+(E) — le glyphe de severite cite dans une REPONSE ne doit plus
compter comme reserve neuve (#22911).

Le defaut mesure : une lane qui repond a une reserve en la nommant voit sa
reponse classee `[BOT-CONCERN]` — l'acte de documenter la levee cree le blocage
qu'il documente, et la PR ne peut plus atteindre `rc=0` tant que la lane
continue d'ecrire.

Les trois corps ci-dessous sont les commentaires MESURES cites par l'issue,
recuperes verbatim (aucune reecriture) :

- `c.6432162050` (#22529) — « **Reponse a la reserve 🟡 de la review ... ** » :
  le prefixe porte `reserve`, pas `marqueur` ; rien de ce que neutralisait les
  positions A-C ne s'appliquait. Regle (D).
- `c.6430493444` (#22708) — « **Live-read freshness (🟡)** : ... » : un
  libelle en gras ouvre la ligne et referme son glyphe entre parentheses.
  Regle (E).
- `c.6423062492` (#22708) — controle negatif : reponse sans glyphe, elle
  reste propre.

Controles positifs obligatoires (l'issue, critere 2) : un corps qui EMET un
glyphe en tete de ligne reste classe `BOT-CONCERN` — un correctif qui rend le
glyphe muet partout est un echec, pas un progres.

Aucun appel reseau : les corps sont figes dans le fichier.
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


def live_markers(body: str) -> list[str]:
    """Meme pipeline que l'issue : nettoyage complet, puis marqueurs vivants."""
    surface = mod._strip_mentioned_verdicts(mod._strip_quoted(body))
    return [m for m in mod.CONCERN_MARKERS if mod.has_live_marker(surface, (m,))]

# #22529 — instance 1 : le glyphe est nomme par le mot « reserve » (c.6432162050)
REPLY_RESERVE = "**Réponse à la réserve 🟡 de la review `clusterManager-Myia` du 2026-10-25T16:47:21Z** — celle qui note, pour la traçabilité, que la cellule PT_01 `a053d4e0` porte une figure régénérée sur kernel local « sans témoin papermill (cellule unique re-exécutée, pas le carnet) ».\n\nLa réserve est fondée : au commit `dadf1204` la figure venait d'une exécution réelle mais d'une cellule seule, et rien dans le carnet ne datait cette exécution. Elle se ferme en faisant la chose réelle plutôt qu'en l'argumentant — PT_01 est entièrement exécutable localement (8 cellules, matplotlib/numpy/pandas, ni modèle ni GPU), donc rien n'obligeait à s'en tenir à une cellule.\n\n## Ce qui a été fait — commit `dd34b1ddf1`\n\nExécution **complète** du carnet au kernel `python3` (papermill 2.7.0, Python 3.13.14 ; base exécutée en 3.13.3, même `major.minor`) :\n\n```\n[PT_01_intro_post_training.ipynb] (kernel: python3)\n  [+] SUCCESS\n```\n\nLe carnet porte désormais un bloc `metadata.papermill` de tête (`duration`, `start_time`, `end_time`, `version`, `parameters`) et un bloc par cellule : c'est le témoin qui manquait.\n\n## Ce que l'exécution change — et ce qu'elle ne change pas\n\n| Mesure | Base `dadf1204`/`ec665e8b` → tête `dd34b1ddf1` |\n|---|---|\n| Cellules de code | 8 → 8 (aucune ajoutée, aucune perdue) |\n| Séquence `execution_count` | `1,2,3,4,5,6,7,8` → `1,2,3,4,5,6,7,8` (inchangée) |\n| Sources de cellule | **aucune modification** (comparaison cellule par cellule des `source`) |\n| Sorties texte | byte-identiques sur les 6 cellules qui en portent |\n| Figure `a053d4e0` (celle de la réserve) | **58 186 → 58 186 octets — identique** |\n| Figure `3e6d375d` | 41 790 → 41 690 octets (−0,2 %) |\n| Figure `c1f5cde9` | 44 104 → 44 152 octets (+0,1 %) |\n| Erreurs | 0 |\n\nLe point qui vaut d'être relevé : la figure de `a053d4e0` régénérée par une exécution complète est **byte-identique** à celle du transplant manuel qu'elle remplace. Le rendu n'était donc pas un artefact du kernel local, et l'exécution d'ensemble le confirme au lieu de le supposer.\n\n## Organes, relancés à la tête\n\n| Organe | Verdict |\n|---|---|\n| `check_papermill_ratchet.py origin/main` | 4 carnets changés, **0 régression** — PT_01 `BLOCK_MOVED` (le bloc bouge parce que la preuve d'exécution change : c'est le comportement attendu quand on exécute) |\n| `check_exec_ratchet.py origin/main` | 4 carnets, **0 régression**, `CLEAN→CLEAN` sur les quatre |\n| `check_output_collapse.py origin/main` | **0 flagged** |\n| `check_source_collapse.py origin/main` | **0 flagged** |\n| `check_output_failure_text.py origin/main` | **0 regressed** |\n| `validate_pr_notebooks.py origin/main` | **1/1 PASS** (8 cellules) |\n| `check_prose_quantitative_claims.py --diff` | **OK** |\n\nRéserve annexe de la même review, « organes CI : 21 encore `queued` — à relire à la tête finale avant merge » : les jambes sont relancées par ce push ; le diff se limite à PT_01, donc les trois autres carnets ne sont pas re-exécutés (C.3).\n\n## Portée\n\nLe diff de ce commit est **métadonnée et figures uniquement** : horodatages papermill par cellule, bloc de tête, deux figures à quelques dizaines d'octets près. `metadata.papermill.input_path`/`output_path` sont ramenés aux basenames et l'identifiant de la cellule de paramètres est laissé tel quel — deux normalisations de métadonnée, pas de sortie, faites avant le hook `scrub-papermill-paths` qui les applique de toute façon.\n\nJe ne lève pas cette réserve moi-même : elle a été posée par `clusterManager-Myia`, et sous le login partagé `jsboige` une phrase de ma part n'est pas une levée (B.0). Ce commentaire en apporte la matière — l'appréciation reste à son auteur ou à `myia-ai-01`.\n\n"

# #22708 — instance 2 : le glyphe referme un libelle en gras (c.6430493444)
REPLY_LABEL = "Réponse à la review Hermes 16:02Z — le point bloquant et les deux jaunes de fond sont traités en `63d809e97f` (markdown + docstring uniquement, aucune cellule code touchée, donc pas de re-exec due ; vérifié : la docstring n'apparaît dans aucun output committé).\n\n**1. nav-chain orphan_entry (bloquant) — corrigé.** Bloc ajouté dans la cellule d'en-tête de TV-00b, exactement le remède mesuré : `**Navigation** : [TV-00d — Encodeurs (suite)](TV-00d-Encodeurs-from-scratch.ipynb)`. Rejoué firsthand à la tête actuelle (`5ba96f8e`) : `check_notebook_nav_chain.py TV-00d… --diff-base origin/main` rend `OK: chaque notebook est atteignable dans sa serie (1652 notebook(s) au graphe)` — les deux findings (TV-00d et l'effet de seuil TV-04) tombent.\n\n**2. Docstring `selfcheck_encodeurs` sur-prometteuse — reformulée.** Votre mesure (écart 5.96e-08 en permutant la mémoire = invariante aussi) était exacte : `attn_pleine` ne code aucune position sur les clés. La docstring dit maintenant que la seconde invariance est une **propriété de l'implémentation** (aucun encodage positionnel sur la mémoire), pas une hypothèse testée ; le selfcheck ancre la première (permutation des requêtes du décodeur).\n\n**3. « Deux exécutions identiques » — périmètre écrit.** La conclusion du carnet (cell. 35) porte désormais : les valeurs numériques sont propres au couple torch épinglé (2.13.0+cu126) et à la graine — vos conclusions directionnelles reproductibles, le chiffre-pour-chiffre non portable, dit tel quel.\n\n**Live-read freshness (🟡)** : hérité de `main` comme vous l'avez établi (GOL-01 → Pillars.lean, hors diff de cette PR) — réparation portée par #22717, rien ici.\n\n`PR gate` CANCELLED hier soir = famine de runners self-hosted (queue partagée), non lié au contenu.\n\n"

# #22708 — controle negatif : reponse sans glyphe (c.6423062492)
REPLY_CLEAN = "Réponse à la review Hermes — les trois points imputables sont traités en `63d809e97f` (3 fichiers, +9/-5).\n\n**1. `check-nav-chain` (le point bloquant) — corrigé.** TV-00d n'avait aucune arête entrante : la cellule de conclusion de TV-00b porte désormais la ligne `**Navigation** : [TV-00d — Encodeurs (suite)](TV-00d-Encodeurs-from-scratch.ipynb)` — le geste que #22693 avait fait pour son renommage. Garde rejouée sur l'arbre modifié (`python scripts/notebook_tools/check_notebook_nav_chain.py MyIA.AI.Notebooks/GenAI/Texte/TransformerVariants/TV-00d-Encodeurs-from-scratch.ipynb`) : `OK: chaque notebook est atteignable dans sa serie`, rc=0 — les deux findings tombent d'un coup, TV-04 compris (effet de seuil), exactement comme le replay labo de la review le mesurait.\n\n**2. Docstring `selfcheck_encodeurs` (b) — corrigée dans `tv/model.py`.** La permutation de la mémoire est elle aussi invariante (écart 5.96e-08 mesuré par la review ; `attn_pleine` ne code aucune position sur les clés, la sortie est une somme pondérée sur le multiensemble des jetons sources — l'ordre de la mémoire n'entre pas dans le calcul). La docstring énonce maintenant : le selfcheck ancre l'invariance aux positions du décodeur ; l'invariance mémoire est une propriété de l'implémentation (aucun encodage positionnel), pas une hypothèse testée. Les lectures du carnet (§2 et §2.1) n'énonçaient que l'invariance aux requêtes et restaient justes — inchangées.\n\n**3. Périmètre torch — phrase ajoutée en §6** (« Ce que ce carnet ne mesure pas ») : les valeurs numériques sont de plus propres au couple torch épinglé (2.13.0+cu126) et à la graine ; rejoué sous un autre bâtiment de torch, des cellules individuelles bougent — jusqu'à plusieurs points sur les colonnes fines, notamment le témoin causal ré-entraîné — alors que les classements directionnels tiennent.\n\n**4. Live-read freshness — constat partagé, rien à faire ici** : le finding cite `GOL-01-Reges-Vie-Lean.ipynb`, hors diff de cette PR (hérité de `main`) ; la réparation est déjà ouverte en #22717.\n\n"



# --- Instance 1 : le glyphe est nomme par le mot de reprise (regle D) ---


def test_22911_reponse_a_la_reserve_ne_compte_plus_comme_reserve():
    assert live_markers(REPLY_RESERVE) == []
    assert mod.classify("jsboige", REPLY_RESERVE) is None


# --- Instance 2 : le glyphe referme un libelle en gras (regle E) ---


def test_22911_libelle_en_gras_ne_compte_plus_comme_reserve():
    assert live_markers(REPLY_LABEL) == []
    assert mod.classify("jsboige", REPLY_LABEL) is None


# --- Controle negatif : reponse sans glyphe, rien ne change ---


def test_22911_controle_negatif_reponse_sans_glyphe_reste_propre():
    assert live_markers(REPLY_CLEAN) == []
    assert mod.classify("jsboige", REPLY_CLEAN) is None


# --- Variantes de vocabulaire (regle D) : les mots de reprise nomment le glyphe ---


def test_22911_variantes_remarque_observation_point_item():
    for nom in ("remarque", "observation", "point", "item", "reponse", "reserve"):
        body = ("**Reponse a la %s 🟡 de la review Hermes** — traitee, "
                "rien ne reste." % nom)
        assert live_markers(body) == [], nom
        assert mod.classify("jsboige", body) is None, nom


def test_22911_variante_anglais_neutralisee():
    body = ("**Response to the concern 🟡 raised by the review** — handled, "
            "nothing left.")
    assert live_markers(body) == []
    assert mod.classify("jsboige", body) is None
    # `concern` est dans le set de noms de reprise de la regle (D) : la
    # variante anglaise passe par la REGLE, et non par le chemin
    # d'attribution preexistant (« the » ∈ CITERS, citer + un mot). Sans ce
    # token, « **Response to my concern 🟡 ...** » resterait vivant — « my »
    # est hors CITERS par construction (« my CONCERN is... » est une emission
    # reelle).
    assert mod._GLYPH_RESPONSE_NOUN_RE.search(
        "**Response to the concern "), "« concern » absent du set de (D)"
    assert mod._GLYPH_RESPONSE_NOUN_RE.search(
        "**Response to my concern "), "« my concern » absent du set de (D)"


# --- Surface CONNUE, verrouillee (review du 2026-11-02, point 2) ---
#
# La regle (D) neutralise un glyphe adjacent a un nom de reprise des lors que
# la ligne porte un marqueur de reponse. Une reserve NEUVE emise DANS une
# reponse partage cette forme et disparait donc de l'analyse -- faux vert
# ASSUME et documente : l'organe ne peut pas distinguer une levee d'une
# reserve neuve sans lire la queue semantique de la ligne, ce qu'il refuse de
# faire. Parade : une reserve neuve s'emet dans un commentaire distinct, sans
# marqueur de reponse sur la ligne.
#
# Ce test verrouille l'etat courant pour qu'un changement soit visible.


def test_22911_surface_connue_reserve_neuve_dans_reponse():
    prefix = "Réponse au point "
    assert mod._GLYPH_REPLY_MARKER_RE.search(prefix), "marqueur de reponse absent"
    assert mod._GLYPH_RESPONSE_NOUN_RE.search(prefix), "nom de reprise absent"
    # Surface residuelle : le glyphe disparait, et aucun autre marqueur ne
    # rattrape la reserve.
    body = "Réponse au point 🟡 : ce point n’est pas traité."
    assert live_markers(body) == []
    assert mod.classify("clusterManager-Myia", body) is None


def test_22911_surface_connue_le_marqueur_cotier_rattrape_la_reserve():
    # L'exemple cite par la review (« a corriger avant merge ») n'est PAS un
    # faux vert : « avant merge » est lui-meme un marqueur de reserve
    # (`CONCERN_MARKERS`), donc la reserve reste bloquee meme glyphe
    # neutralise. C'est le cas general sans marqueur cotier qui reste le
    # residuel documente ci-dessus.
    body = "Réponse au point 🟡 : à corriger avant merge."
    assert "avant merge" in mod.CONCERN_MARKERS
    assert live_markers(body) == ["avant merge"]
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_22911_variantes_accentu_neutralisees():
    # Le corps mesure (`c.6432162050`) porte « reserve » ACCENTUE : un set
    # ASCII seul laissait la reserve vivante. Les formes accentuees sont donc
    # verrouillees explicitement.
    for nom in ("réponse", "réserve", "Réserve", "réponses", "réserves"):
        body = ("**Réponse à la %s 🟡 de la review Hermes** — traitée, "
                "rien ne reste." % nom)
        assert live_markers(body) == [], nom
        assert mod.classify("jsboige", body) is None, nom


# --- Controls positifs : une EMISSION reste vivante ---


def test_22911_vp_emission_tete_de_ligne_reste_bloquante():
    body = "🟡 FINDING — les 5 hyperparametres contredisent le run mesure."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_22911_vp_emission_en_tete_de_ligne_avec_verdict_entre_parentheses():
    # Le libelle en gras n'ouvre PAS la ligne : l'echappement (E) ne s'applique
    # pas, le glyphe reste une emission.
    body = "Verdict (**🟡**) — la cellule 19 casse C.2, a corriger avant merge."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_22911_vp_mot_de_reprise_loin_du_glyphe_neutralise_pas():
    # L'ancre de (D) est ADJACENTE : un mot de reprise qui precede le glyphe
    # sans lien immediat avec lui ne neutralise rien.
    body = "Le point est clair : 🟡 bloquant, la cellule 19 casse C.2."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_22911_vp_libelle_gras_avec_mot_de_reprise_reste_bloquant():
    # (E) exige que le glyphe FERME la parenthese du libelle ; un glyphe
    # place apres le libelle n'est pas un referent de libelle.
    body = "**Live-read freshness** 🟡 : le run date de la base, pas de la tete."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


# --- Controls positifs : une reserves REELLE emise par un reviewer reste vivante ---


def test_22911_vp_reserve_emise_par_un_reviewer_reste_bloquante():
    # Le mot `reserve` colle au glyphe est aussi la forme d'EMISSION de
    # Hermes (« APPROVE avec 1 reserve 🟡 », « **Reserve 🟡 — ...** ») : sans
    # marqueur de reponse sur la ligne, la reserve reste vivante. Ce controle
    # verrouille les fixtures de la suite de l'organe.
    for body in (
        "**[Hermes]** APPROVE avec 1 reserve 🟡 : le point 2 reste ouvert.",
        "**Reserve 🟡 — arithmetique interne du corps :** la table est fausse.",
        "## Je leve ma propre reserve 🟡, et je retiens celle d'Hermes",
    ):
        assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN", body
