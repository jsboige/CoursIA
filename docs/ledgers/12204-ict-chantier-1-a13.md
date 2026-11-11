# A13 — Re-mesure du témoin `Argumentation-06c` : la limite (i) tient

**Lane** : `myia-po-2024:CoursIA` · **Tranche** : A13 (dispatch coordinateur c2811-C) · **Date de mesure** : 2026-11-11
**Grain** : DEEP/notebook-python · **Parent** : EPIC #12204 (Chantier 1 — la table ICT)
**Témoin mesuré** : `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-06c-Revision-Croyances-Python.ipynb` (carnet Python, non Lean), introduit par `e66153de9e5` (PR #23173), renommé dans le renommage `62c512ad3e3` (#25195).

## La question posée

Le §4octies du body de #12204 consigne une limite d'attestation au mot près :

> (i) la littérature est partagée sur le canon AGM, pas deux théories étrangères — une **troisième lignée** (révision de Dalal par modèles, distincte de CrMas et de la contraction par noyaux) resterait **à vérifier, pas à supposer**.

La tranche A12 n'avait pas compté l'usage d'`Argumentation-06c` : « non committé, organe `argumentation_lib` absent de main, à re-mesurer au merge ». L'organe et le carnet sont désormais sur `main` : A13 fait cette re-mesure **à la source**, et tranche la limite.

## Verdict : la limite (i) n'est PAS levée

**`method='dalal'` est un alias documenté du chemin Levi**, et non une troisième lignée. La troisième lignée reste une lacune du recouvrement.

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

## Défaut d'organe — `method='inconnu'` accepté en silence

Constat mesuré à la source (cellule [7], sortie committée) et lu dans le code :

- `REVISION_METHODS = {"dalal", "levi"}` (l. 59) n'est **jamais** lu dans `revise()` : aucune validation.
- `handler.revise(["p"], "q", method="inconnu")` aboutit, prend le chemin Levi, et recopie `'inconnu'` dans la clé `method` du résultat.
- Le carnet le qualifie justement : « L'énumération `REVISION_METHODS` est donc une **documentation**, pas un **garde-fou** » (md 17) — un appelant qui passe une méthode mal orthographiée ne le saura pas.
- Le défaut n'est **pas corrigé ici** : le fichier est une copie verbatim, et modifier une copie verbatim casse son contrat de provenance (`NOTICE-EPITA`). Signalé dans l'issue de série #23163 (réparation par ré-écriture amont puis re-port, hors du scope verbatim).

## Méthode et limites de la mesure

- **Lu à la source** : le handler et les cellules du carnet, prose et sorties committées — aucune re-copie de résumé.
- **Exécution locale non rejouée** : les actifs JVM (`Tweety/libs/*.jar`, `jdk-17-portable/`) sont gitignorés et **absents de cette machine** (répertoires présents, vides — mesuré le 2026-11-11) ; une re-exécution Papermill échoue à l'initialisation (`RuntimeError: JVM/Tweety non demarree via la shim`). La série interdit le mode dégradé. Le verdict repose donc sur (a) le code lu et (b) les **sorties réelles committées** du carnet (écrites sur une machine JVM-outillée), non sur une nouvelle exécution — ce qui suffit : la question porte sur l'**identité d'algorithme**, établie par le code lui-même (le paramètre `method` n'entre pas dans le calcul).
- **Portée** : la convergence `dalal ≡ levi` vaut pour le jeu de JARs présent à l'exécution committée (Tweety 1.28, version non figée dans le dépôt). Le code documente l'absence de classe Dalal dans cette version ; il ne prétend rien sur une version future.
