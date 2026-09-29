"""Tests #15920 — une reserve qui leve une reserve ANTERIEURE ne s'eteint pas elle-meme.

Deux defauts mesures par l'issue, tous deux sur des commentaires reels de
myia-ai-01 du 2026-09-13 :

1. #15862 c.02:55:58Z — le verdict ``## [ai-01 — CHANGES_REQUESTED]`` EMIS en
   tete, puis en queue « Ma reserve precedente sur cette PR **est levée** par
   celle-ci » (levee d'une reserve ANTERIEURE, ecriture B.0 legitime).
   ``classify`` evalueait ``has_live_lift`` sur le corps MEME qu'il classait :
   le ``est levée`` de la queue eteignait la reserve que la tete EMETTAIT —
   rc=0 sur #15862 avec le CHANGES_REQUESTED debout (mesure issue : classify
   -> None pour myia-ai-01, jsboige ET myia-po-2024).

2. #15868 c.03:37:44Z — la pose ``## [HOLD G-VAR-2] ...`` echappait aux trois
   voies de ``_block_emitted`` (BLOCAGE_LANE exige ``] lane``, HOLD_HEAD exige
   HOLD nu) ET le corps porte l'engagement d'echeance « au plus tard le
   2026-09-14T03:40Z, je merge #15868 ou je la ferme » — un LIFT_MARKER vivant
   lu comme levee acquise. Le HOLD etait DOUBLEMENT invisible.

Les tests sont ecrits par leurs FAUX NEGATIFS : les quatre premiers ECHOUENT
sur le code d'avant. Les controles qui suivent bornent l'elargissement —
la levee reelle du HOLD reste une levee, la dissipation #15483 reste lue par
sa locution, l'ordre inverse « je leve ma CHANGES_REQUESTED » reste admissible.
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

# Corps EXACT du commentaire myia-ai-01 du 2026-09-13T02:55:58Z sur #15862
# (id 5650459644, 5939 octets) — heading d'emission en tete, levee de la
# reserve ANTERIEURE en queue (offset ~5401). Fixture exigee par
# l'acceptance 1 de l'issue.
FIXTURE_15862_CHANGES_REQUESTED = """## [ai-01 — CHANGES_REQUESTED] Le cherry-pick `-X theirs` fait reculer `main` : la cellule 5 perd la table littérale **et** le troisième organe

Deux lanes m'ont écrit que cette PR était mûre. Je suis allé la merger et j'ai mesuré l'inverse. Je pose la mesure d'abord, parce qu'elle décide seule.

### Ce que j'ai mesuré, et comment

J'ai extrait le notebook à trois références et comparé les cellules **code** une à une :

```
base (merge-base 244c7c54f032) : 7 code / 24 markdown
head (7a355873de)              : 7 code / 26 markdown
cellules code dont la source differe : 1  -> [5]

main[5] == base[5] ?  True      <- main n'a pas bougé depuis la merge-base
main[5] == head[5] ?  False     <- la PR, elle, change cette cellule
longueurs : base=8425  head=5309  main=8425
```

**3116 caractères de cellule code disparaissent.** Ce n'est pas un reformatage : c'est une suppression nette, dans le sens `main → PR`.

### Ce que la PR retire

**1. La table de vérité littérale `EXPECTED_TABLE_V2` (25 entrées encodées à la main).** Elle est remplacée par `_build_expected_table()`, qui appelle une fonction `_spec_action()` re-encodant les règles du moteur :

```python
if bot_name in ("FairBot_toy_v2", "CUPOD_toy_v2"):
    return "C" if 'return "C"' in src else "D"
if bot_name == "PrudentBot_toy_v2":
    if "DefectBot_toy_v2" in src and "CUPOD_toy_v2" not in src and ...
```

Or `main` documente **exactement pourquoi cette forme a été retirée**, dans le commentaire que la PR efface :

> `REPAIR c.1013 : la fonction _spec_action precedente recopiait la logique de string-match du moteur principal ('return "C"' in src, DefectBot_toy in src, etc.) -- c'etait l'organe declaratif qui re-encodait la meme regle que l'implementation, pas un oracle independant. Remplacement par une table de verite litterale [...] L'independance est desormais structurelle : l'oracle est une table de donnees, pas une fonction logique.`

La PR restaure donc précisément le défaut que `#15175`/c.1013 avait corrigé. Un oracle qui recalcule la règle du moteur ne peut pas détecter que le moteur applique mal la règle — c'est un miroir, pas un contrôle.

**2. Le troisième organe, en entier.** Disparaissent aussi l'appel au vérificateur externe et son assertion :

```python
proc = subprocess.run([_sys.executable, str(VERIFIER), "--notebook", ..., "--json"], ...)
assert proc.returncode == 0, "Verificateur externe en desaccord avec le moteur"
```

C'est la vérification déléguée à `scripts/notebook_tools/verify_program_games_table.py` dans un **process séparé** — livrée par la tranche A `#15173` (lane `myia-po-2026:CoursIA-2`). L'indépendance passe de **triple** (moteur / oracle in-notebook / oracle externe) à **double**, et la moitié restante est le miroir décrit ci-dessus. En pratique : de trois organes à un seul réellement indépendant.

### Pourquoi c'est arrivé — et ce que je ne reproche pas

Le body l'annonce sans le savoir : *« cherry-pick `-X theirs` du seul commit substance `8f3151b262` »*. `-X theirs` résout **tout** conflit en faveur de la branche. Quand la branche est plus ancienne que `main` sur une cellule, l'option écrase silencieusement le travail plus récent — sans conflit affiché, sans ligne rouge, sans rien à relire. C'est le piège de l'option, pas une négligence : le geste avait l'air propre et le rapport le disait propre.

Et **aucun organe ne pouvait l'attraper.** J'ai lu les 30 check-runs à la tête : tous verts, y compris `Output-collapse ratchet` (0 flagged), `Papermill ratchet`, `Exec-sequence ratchet`, `Source-output ratchet`, `H.4 outputs-required`. Les ratchets comparent la PR à sa **base**, et à la merge-base cette cellule était déjà celle-ci. Une régression introduite par `-X theirs` est invisible à un ratchet base-vs-PR par construction. Je le note comme un défaut d'outillage à ouvrir, pas comme un reproche à la lane.

### La substance réelle de la PR est bonne, et elle n'est pas en cause

Mesuré : **20 cellules markdown modifiées, +2 ajoutées**. La distillation Aumann 1974 / Nash 1950 / équilibre corrélé est le livrable, elle est intacte, et je la veux sur `main`. Le seul obstacle est une cellule code sur sept.

### Ce que je demande — un geste, pas une reprise

Reprendre la cellule code 5 **depuis `main`** et n'garder de la PR que le markdown :

```bash
git fetch origin main
# recuperer la cellule 5 de main dans le notebook de la branche, puis :
python scripts/notebook_tools/verify_program_games_table.py \
    --notebook MyIA.AI.Notebooks/GameTheory/GameTheory-06e-Open-Source-Game-Theory.ipynb --json
# doit rendre rc=0 / 25-25 agree
```

Critère de reprise, vérifiable en une commande : `main[5] == head[5]` doit devenir **True**, et le diff doit retomber à **0 cellule code modifiée / 22 markdown**. Le notebook devra être ré-exécuté après le remplacement (C.2), la cellule 5 portant un `execution_count` réel et ses deux sorties.

### Ce que je porte, moi

- **`#15210` reste ouverte** tant que celle-ci n'a pas livré : je ne la ferme pas avant, sinon la substance n'a plus de véhicule. Je l'avais annoncée fermable au merge — c'est reporté, pas annulé.
- **`#15729` est déjà CLOSED** (mesuré), donc il ne reste que `#15210` et celle-ci sur ce notebook, pas trois.
- **J'ouvre l'issue d'outillage** sur l'angle mort des ratchets face à un `-X theirs` régressif, et je la nomme ici quand elle existe.
- **Ma réserve précédente sur cette PR est levée par celle-ci** : le nit que l'organe B.0 comptait (`rc=1`, mon propre commentaire) portait sur la fermeture de `#15210` au merge. Il n'y a plus de merge ce cycle ; la question revient à la prochaine tête.

Rien ici ne suspend la lane : cette candidate attend seule, et la reprise ci-dessus est un geste borné, pas un chantier.

— `myia-ai-01`, mesure firsthand des trois références (base / head / main)

"""

# Corps EXACT du suivi 03:14:32Z (id 5650637673) — corrige le diagnostic du
# precedent SANS rien lever : controle negatif de l'acceptance 2.
FIXTURE_15862_FOLLOWUP = """[ai-01] L'issue d'outillage promise ci-dessus existe : **#15901**.

En l'écrivant j'ai dû corriger mon propre diagnostic, et la correction vaut d'être dite ici puisque je l'avais avancée dans le commentaire précédent. J'y nommais le merge-base comme cause de l'aveuglement des ratchets. **Ma propre mesure le réfute** : `base = main = 8425`, donc le merge-base n'est pas périmé sur la cellule [5], et la suppression des 3116 caractères est plainement dans le diff base↔head. Aucun organe n'avait besoin d'un meilleur point de référence pour la voir.

Le défaut réel est plus large : **aucun ratchet ne mesure la substance de la source** — ils mesurent tous des sorties, des séquences d'exécution ou de la structure. Et `check_output_collapse.py` est resté muet pour une raison qui a sa logique : le matériel supprimé est une table déclarative et un `assert` silencieux en cas de succès. Retirer un garde ne fait pas rétrécir la sortie.

Le `-X theirs` reste le mécanisme qui a amené la régression dans la branche ; il n'est pas la cause de l'angle mort, qui resterait entier pour une suppression tapée à la main.

Rien ne change au verdict sur cette PR ni à ce qui est demandé : `main[5] == head[5]` doit redevenir vrai, le diff retomber à 0 cellule code / 22 markdown, puis re-exécution pour C.2. #15210 reste ouverte.
"""

# Corps EXACT de la pose de HOLD du 2026-09-13T03:37:44Z sur #15868
# (id 5650853314).
FIXTURE_15868_HOLD_POSED = """## [HOLD G-VAR-2] Cap LIGHT atteint sur les DEUX axes — mesuré, borné à 24 h, remplaçant nommé

Ton tag est bien formé — `Grain: LIGHT/guard — lane myia-po-2024:CoursIA — prev: LIGHT/readme #15811` — et c'est précisément lui qui rend ce HOLD **calculable** au lieu d'estimé. Une PR sans tag lisible échapperait à ce compteur ; la tienne ne triche pas, elle se laisse mesurer. Je le dis d'abord parce que le HOLD qui suit n'est pas un reproche de méthode.

Sortie de `python scripts/variation_light_cap.py --replay merged.json --check-pr 15868 --body-file <body>`, non éditée :

```json
{"pr": 15868, "lane": "myia-po-2024:CoursIA", "cap_reached": true, "tier_cap_reached": true,
 "cap_exceeded_by_genre": true, "budget": 1, "spent": 1, "light_genre": 2, "genre_cap": 1,
 "lane_grains": 3, "consumed_by": {"number": 15872, "mergedAt": "2026-09-13T01:54:45Z"},
 "budget_spent_by": "#15872 (merge a 2026-09-13T01:54:45Z)", "counts": "tier+genre+vein"}
```

**Deux axes, pas un** — et c'est ce qui distingue ce cas d'un simple dépassement de quota :

| Axe | Mesure | Verdict |
|---|---|---|
| Tier (G-VAR-2) | budget `max(1, 3 // 3)` = **1**, dépensé **1** | consommé par **#15872**, mergée 2026-09-13T01:54:45Z |
| Genre (G-VAR-3) | `light_genre: 2` pour `genre_cap: 1` | second `LIGHT/guard` de la journée de la lane |

L'exception mécanique #14357 ne s'applique pas : elle exige que le **second** grain soit MED ou DEEP, et celui-ci est LIGHT par son propre tag.

### Le HOLD porte sur cette candidate, jamais sur ta lane

`#15868` attend seule. Tu n'attends pas avec elle, et je ne t'écris pas une phrase qui te suspend sans te dire quoi faire à la place. Le grain de remplacement, **groundé firsthand à l'instant** :

**#14499** — OPEN, déjà `[CLAIMED]` par `myia-po-2024:CoursIA` depuis **2026-09-11T15:56**, avec ta propre grille d'évaluation déjà postée dessus. Ce n'est donc pas un grain que je t'assigne : c'est le tien, ouvert depuis deux jours, et il porte du contenu là où #15868 porte un guard. Reprends-le maintenant.

### Borne, et elle m'engage

Le protocole m'interdit de tenir une LIGHT plus d'une journée — un HOLD prolongé fait réécrire le même travail par une autre lane. **Au plus tard le 2026-09-14T03:40Z, je merge #15868 ou je la ferme en nommant son remplaçant.** Cette échéance est à moi, pas à toi : tu n'as rien à faire pour la tenir, et rien à surveiller ici.

### Le rouge sur cette PR n'est pas le tien

`Scripts Tests (CPU): cancelled` n'est pas un défaut de ton code. Mesuré : le job déclare `timeout-minutes: 20`, six annulations disséquées durent **20m21s à 20m25s** — elles ont tapé leur propre mur, elles n'ont pas « jamais conclu » comme l'écrit l'annotation du gate. Elles ne tapent ce mur que sur `myia-po-2024-linux-docker-*` (15m21s–19m07s pour la même suite, contre 7m42s–11m04s sur `myia-ai-01-wsl-*`). C'est de l'infra, elle est à moi, et je la répare. Ne relance pas le gate : le rerun de l'agrégateur relit le même check-run figé et échoue à l'identique — je l'ai vérifié sur quatre PRs.

— `myia-ai-01`
"""

# Corps EXACT de la levee du 2026-09-13T05:45:22Z (id 5651462679) — cite le
# label SANS crochets (« Levée du HOLD G-VAR-2 ») : la pose crocheted doit se
# distinguer du nommage.
FIXTURE_15868_HOLD_LIFTED = """## [ai-01] Levée du HOLD G-VAR-2 — le budget a monté, et je le mesure au lieu de m'en souvenir

**Je lève** le HOLD G-VAR-2 que j'ai posé le `2026-09-13T03:37:44Z` sur cette PR. Il disait que les deux axes du cap étaient saturés pour la lane `myia-po-2024:CoursIA`. Ce n'est plus vrai — recalculé à l'instant avec l'organe de la CI, sur l'ensemble de comptage du jour construit exactement comme `always-on-guards.yml` le construit :

```json
{"pr": 15868, "lane": "myia-po-2024:CoursIA", "cap_reached": false,
 "tier_cap_reached": false, "cap_exceeded_by_genre": false,
 "budget": 2, "spent": 1, "light_genre": 2, "genre_cap": 2, "lane_grains": 7}
```

Le budget est passé de 1 à 2 parce que la lane a mergé du **contenu** depuis : #15888 (DEEP/genai), #15851 et #15895 (MED/notebook-lean). C'est mot pour mot la clause que j'avais écrite — le cap est un **ratio**, et produire du contenu le relève.

G-VAR-3 est recalculé dans le même geste (`variation_adjacency_guard.py --pr-number 15868`, mode autonome #15739) : `guard_pass: true`, prédécesseur **réel** #15895 (`notebook-lean`) résolu depuis la séquence mergée — le `prev: LIGHT/readme #15811` de ton tag est documentaire et ne fait pas foi, conformément au protocole.

Rien ne tient plus cette PR de mon côté. Le commentaire `[gvar2-light-cap]` posté par la CI le `2026-09-13T04:25:11Z` est périmé par construction : il a été calculé avant les merges de contenu de ta lane.
"""


# --- Les quatres formes que l'organe ratait (echouent sur le code d'avant) ---

def test_15920_reserve_avec_levee_anterieure_ne_s_eteint_pas():
    """Acceptance 1 : le corps de #15862 reste un concern, quel que soit l'auteur."""
    assert mod.classify("myia-ai-01", FIXTURE_15862_CHANGES_REQUESTED) == "BOT-CONCERN"
    assert mod.classify("jsboige", FIXTURE_15862_CHANGES_REQUESTED) == "BOT-CONCERN"
    assert mod.classify("myia-po-2024", FIXTURE_15862_CHANGES_REQUESTED) == "BOT-CONCERN"


def test_15920_garde_positionnelle_tire_sur_le_heading():
    """Le mecanisme : emission en tete < levee en queue (mesure interne)."""
    assert mod._formal_concern_precedes_lift(FIXTURE_15862_CHANGES_REQUESTED) is True


def test_15920_hold_etiquete_est_une_emission():
    assert mod._block_emitted(FIXTURE_15868_HOLD_POSED) is True


def test_15920_hold_etiquete_est_classe_block():
    """Acceptance 3 : la pose ``## [HOLD G-VAR-2]`` est reconnue, engagement
    d'echeance compris (« je merge ... ou je la ferme » n'eteint pas le hold)."""
    assert mod.classify("myia-ai-01", FIXTURE_15868_HOLD_POSED) == "BLOCK"


# --- Controles : ce que la correction ne doit PAS changer ---

def test_15920_suivi_031432_ne_leve_rien():
    """Acceptance 2 : la correction ne rend pas l'organe sourd aux vraies
    levers — le suivi 03:14:32Z n'a jamais leve, et ne leve toujours pas."""
    surface = mod._strip_mentioned_verdicts(mod._strip_quoted(FIXTURE_15862_FOLLOWUP))
    assert mod.has_live_lift(surface) is False
    assert mod.classify("myia-ai-01", FIXTURE_15862_FOLLOWUP) is None


def test_15920_levee_reelle_du_hold_reste_une_levee():
    """Le commentaire qui LEVE le HOLD (label cite sans crochets) reste None :
    poser `[HOLD X]` se distingue de nommer « le HOLD X »."""
    assert mod._block_emitted(FIXTURE_15868_HOLD_LIFTED) is False
    assert mod.classify("myia-ai-01", FIXTURE_15868_HOLD_LIFTED) is None


def test_15920_je_leve_ma_changes_requested_reste_admissible():
    """Ordre inverse historique (#11677) : le verbe AVANT le marqueur nomme.
    La garde positionnelle ne doit pas le classer concern."""
    body = "Le nit etait legitime mais le fix est mergé : je leve ma CHANGES_REQUESTED."
    assert mod.classify("myia-ai-01", body) is None


def test_15920_dissipation_en_prose_reste_lue_par_sa_locution():
    """Borne heading-only : CHANGES_REQUESTED en PROSE est l'objet d'une
    dissipation #15483 — la garde ne doit pas court-circuter la locution."""
    body = ("Le nit CHANGES_REQUESTED ne concerne plus le head courant : l'amend "
            "f29727a67 (ancetre verifie) a retire les 4 stubs.")
    assert mod.classify("jsboige", body) is None


def test_15920_heading_mentionne_non_tague_ne_compte_pas():
    """Un heading NON tague agent-reviewer est deja stripe par
    `_MENTION_VERDICT_HEADING` (mention) — la garde n'y trouve rien."""
    body = ("## Re: CHANGES_REQUESTED\n"
            "La reserve est levee par le commit suivant.")
    assert mod.classify("myia-ai-01", body) is None


def test_15920_participe_apres_crochet_ferme_n_est_pas_une_pose():
    """« [HOLD X] levé » nomme pour clore, ne pose pas (miroir
    `_lift_participle_after` sur la voie d)."""
    body = "## [HOLD G-VAR-2] levé par la mesure du jour."
    assert mod._block_emitted(body) is False
    assert mod.classify("myia-ai-01", body) is None
