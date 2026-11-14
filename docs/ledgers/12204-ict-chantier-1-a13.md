# A13 — Re-mesure du témoin `Argumentation-06c` : la limite (i) tient

**Lane** : `myia-po-2024:CoursIA` · **Tranche** : A13 (dispatch coordinateur c2811-C) · **Date de mesure** : 2026-11-11
**Grain** : DEEP/notebook-python · **Parent** : EPIC #12204 (Chantier 1 — la table ICT)
**Témoin mesuré** : `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-06c-Revision-Croyances-Python.ipynb` (carnet Python, non Lean), introduit par `e66153de9e5` (PR #23173), renommé dans le renommage `62c512ad3e3` (#25195).

## La question posée

Le §4octies du body de #12204 (édition du 2026-11-09) consigne la limite (i) — phrase exacte :

> (i) littérature — **partagé sur le canon AGM**, distinct sur les branches. Consigné comme limite explicite : la paire établit l'opération sur deux **substrats** et deux **problèmes**, pas sur deux théories étrangères.

L'hypothèse d'une **troisième lignée** ne vient pas du body de #12204 (le mot « Dalal » n'y apparaît ni dans le body, ni dans ses éditions, ni dans ses commentaires) mais du **ledger A12** (l. 27-29, PR #25453), formulée pour ce carnet avant sa mise sur `main` : « Quand il atterrira, ce sera un **troisième** témoin — d'une troisième lignée d'implémentation. »

La tranche A12 n'avait pas compté l'usage d'`Argumentation-06c` : « non committé, organe `argumentation_lib` absent de main, à re-mesurer au merge ». L'organe et le carnet sont désormais sur `main` : A13 fait cette re-mesure **à la source**, et tranche la limite.

## Verdict : la limite (i) n'est PAS levée

**`method='dalal'` est un alias documenté du chemin Levi**, et non une troisième lignée. La troisième lignée reste une lacune du recouvrement. **Ce verdict contredit l'anticipation du ledger A12 citée ci-dessus** — la « troisième lignée d'implémentation » attendue de ce carnet n'existe pas : la re-mesure à la source établit l'alias Levi, et c'est précisément ce qui fait de la troisième lignée une **lacune** plutôt qu'une attestation manquée.

### 1. Ce que le code fait — pas ce qu'il déclare

L'organe `argumentation_lib/_belief_revision_handler.py` est une copie **verbatim** EPITA (`NOTICE-EPITA`) ; il le dit lui-même, noir sur blanc :

- `__init__`, l. 76-90 : « a prior revision referenced a fabricated `org.tweetyproject.beliefdynamics.revops.DalalRevision` class here — that class does NOT exist in Tweety 1.28 (there is no `revops` package at all). [...] Tweety exposes no distance-based `DalalRevision` operator class; the `dalal` method maps to the same Levi pattern as `levi`. »
- `revise()`, l. 131-136 : « Both `dalal` and `levi` methods use the Levi pattern (contraction + expansion) — the only AGM revision operator family Tweety 1.28 exposes. [...] We do NOT fabricate a DalalRevision class. »

Le code d'exécution est identique quelle que soit la valeur de `method` (l. 137-141) :

```python
contraction = self.KernelContraction()   # RandomKernelContractionOperator (no-arg)
expansion = self.DefaultExpansion()      # DefaultMultipleBaseExpansionOperator
operator = self.LeviRevision(contraction, expansion)  # LeviMultipleBaseRevisionOperator
revised = operator.revise(bs, new_formula)
```

Le paramètre `method` n'intervient **nulle part** dans le calcul : il est recopié tel quel dans la clé `method` du résultat (l. 146). La docstring du module (l. 41) annonce « Dalal revision (distance-based) » — **annonce seulement** : aucune classe de distance n'est construite.

### 2. Ce que la mesure in-repo confirme

Le carnet 06c ne se contente pas de rapporter l'écart : il le **mesure** (cellule [7], sortie committée) :

```
dalal -> ['p', 'q', 'r']
levi  -> ['p', 'q', 'r']
resultats identiques : True
```

Et sa conclusion (md 17) : « La distinction nominale ne correspond donc à aucune différence de comportement dans cette version de Tweety — c'est exactement ce que dit l'en-tête du port, et la mesure le confirme plutôt que de le présumer. »

### 3. Conséquence sur la table

- **Substrat identique** à l'attestation 1 (`Tweety-04-Belief-Revision-Python`) : même bibliothèque Java **Tweety/JVM via JPype**, même paquet `org.tweetyproject.beliefdynamics`.
- **Algorithme identique** : contraction par noyaux aléatoire (`RandomKernelContractionOperator`) + expansion, assemblés par l'opérateur de Levi — exactement la **deuxième** famille nommée par la limite (i) (« la contraction par noyaux »), **pas** une troisième.
- Comme le jumeau C# via IKVM écarté en A12 (« variante de substrat et non algorithme distinct »), le présent témoin serait **double comptage** : il ne constitue ni une troisième lignée, ni une seconde attestation indépendante de `réviser une croyance`.
- La table après A12 est donc **inchangée** ; la file d'attente (`institutionnaliser`, `inhiber`) est inchangée. La limite (i) reste consignée telle quelle, désormais **vérifiée** plutôt que supposée.

## Défaut d'organe — `method='inconnu'` accepté en silence (constat 2026-11-11, corrigé par #25745)

Constat mesuré à la source (cellule [7], sortie committée) et lu dans le code, **le 2026-11-11**, sur la copie alors verbatim :

- `REVISION_METHODS = {"dalal", "levi"}` (l. 59) n'était **jamais** lu dans `revise()` : aucune validation.
- `handler.revise(["p"], "q", method="inconnu")` aboutissait, prenait le chemin Levi, et recopiait `'inconnu'` dans la clé `method` du résultat.
- Le carnet le qualifiait justement : « L'énumération `REVISION_METHODS` est donc une **documentation**, pas un **garde-fou** » (md 17) — un appelant qui passe une méthode mal orthographiée ne le saura pas.
- Signalé le jour même dans l'issue de série #23163 ; la réparation envisagée d'abord était la ré-écriture amont puis re-port, hors du scope verbatim.

**Résolu le même jour par #25745, comme adaptation locale déclarée** (issue #23163, signal c.6784603097) : plutôt que d'attendre l'amont, la copie porte un écart **déclaré** (`DECLARED LOCAL DEVIATION, NOT-VERBATIM` en tête de module + `NOTICE-EPITA` « Adaptations locales déclarées », même mécanisme que `_adf_handler.py` 2026-10-29). `revise()` valide `method` contre `REVISION_METHODS` **avant** le bloc `try` : un hors-ensemble lève `ValueError` en nommant les méthodes acceptées, sans toucher la JVM ; un test de contrat JVM-free l'épingle (`tests/test_belief_revision_handler.py`) ; le carnet re-exécuté mesure le refus (`Unknown revision method 'inconnu': expected one of ['dalal', 'levi']`, cellule [7]) et re-qualifie l'énumération en **garde-fou**.

**Le verdict de ce ledger ne change pas.** La validation rend le refus bruyant, elle ne donne pas à `dalal` un calcul propre : les deux valeurs acceptées prennent toujours le même chemin Levi (le code d'exécution l. 137-141 est inchangé par l'écart déclaré). L'alias documenté et la non-levée de la limite (i) restent le verdict ; le garde-fou rend simplement l'API honnête avec sa propre énumération.

## Méthode et limites de la mesure

- **Lu à la source** : le handler et les cellules du carnet, prose et sorties committées — aucune re-copie de résumé.
- **Exécution locale non rejouée** : les actifs JVM (`Tweety/libs/*.jar`, `jdk-17-portable/`) sont gitignorés et **absents de cette machine** (répertoires présents, vides — mesuré le 2026-11-11) ; une re-exécution Papermill échoue à l'initialisation du handler (`raise RuntimeError("BeliefRevisionHandler instantiated before JVM is ready.")`, `argumentation_lib/_belief_revision_handler.py` l. 63-64). La série interdit le mode dégradé. Le verdict repose donc sur (a) le code lu et (b) les **sorties réelles committées** du carnet (écrites sur une machine JVM-outillée), non sur une nouvelle exécution — ce qui suffit : la question porte sur l'**identité d'algorithme**, établie par le code lui-même (le paramètre `method` n'entre pas dans le calcul).
- **Portée** : la convergence `dalal ≡ levi` vaut pour le jeu de JARs présent à l'exécution committée (Tweety 1.28, version non figée dans le dépôt). Le code documente l'absence de classe Dalal dans cette version ; il ne prétend rien sur une version future.
