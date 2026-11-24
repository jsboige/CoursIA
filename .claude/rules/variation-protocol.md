# Protocole de variation — anti-monoculture, tag déclaré + merge-gate coordinateur

S'applique à **tous les workers** (`po-*`) **et au coordinateur `ai-01`**. Source : mandat user 2026-07-21. Les concepts (tiers DEEP/MED/LIGHT, rotation des genres, never-idle) vivent dans [proactive-coordination.md](proactive-coordination.md) R6/R7 ; ce fichier ajoute la mécanique qui les fait mordre : **tag auditable**, **merge-gate**, **obligation de provisionnement** (pourquoi la prose seule n'a pas tenu : [détail §1](../../docs/reference/variation-protocol-detail.md)).

**Détail** (justifications mesurées, incidents fondateurs, verbatims ; provenance : fragments déportés des lignes de la base `7a558e4d7ce8`) : [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md).

## 1. Le tag de grain (HARD)

Tout `[CLAIMED]` **et** tout body de PR portent en **première ligne** :

```
Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>
```

Exemple : [détail §Levier B, L15](../../docs/reference/variation-protocol-detail.md).

`prev:` documente le grain précédent de la lane (adjacence G-VAR-3) et le lie à une PR relisable ; les deux sont obligatoires. **Le genre déclaré dans `prev:` n'est PAS la clé d'adjacence** : l'organe [`scripts/ci/variation_adjacency_guard.py`](../../scripts/ci/variation_adjacency_guard.py) lit la **séquence mergée** de la lane — ne pas dériver l'adjacence à la main depuis les `prev:` déclarés (mécanisme + incident : [détail §2.1](../../docs/reference/variation-protocol-detail.md)).

Le guard ([`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml)) vérifie la **substance** seule (TIER, GENRE, `lane`), pas la ponctuation ([détail §3](../../docs/reference/variation-protocol-detail.md)) — pas de churn cosmétique sur un tag valide en substance.

### TIER — test objectif, pas auto-évaluation

| TIER | Litmus décisif |
|---|---|
| **DEEP** | `main` contient-il désormais un **résultat/capacité qui n'existait pas**, dont la production a demandé du **raisonnement de domaine** ? |
| **MED** | Étend de la substance existante **avec ré-exécution/vérification**, et **change quelque chose** (pas « 0 trouvé ») |
| **LIGHT** | **« Pourrais-je en générer une douzaine en scannant l'instance suivante ? »** → si oui : LIGHT, quel que soit le label |

Exemples par tier : [détail §Levier B, L23](../../docs/reference/variation-protocol-detail.md).

Le litmus LIGHT est le **cœur anti-gaming** ([détail §7](../../docs/reference/variation-protocol-detail.md)).

### GENRE — énumération CLOSE

`lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `notebook-lean` · `slides` · `docs` · `guard` · `refactor` · `ledger` · `readme` · `test` · `tooling` · `research-code`.

**L'énumération se partitionne en deux, et la frontière porte G-VAR-1 :**

| Classe | Genres | Ce qu'un grain y produit |
|---|---|---|
| **CONTENU** | `lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `notebook-lean` · `slides` · `research-code` | une capacité, une preuve, un résultat, du matériel pédagogique — ce que le dépôt existe pour offrir |
| **META** | `guard` · `tooling` · `ledger` · `docs` · `readme` · `test` · `refactor` | l'outillage, les garde-fous et la prose *autour* du contenu — nécessaire, jamais suffisant |

Un genre META n'est pas inférieur, mais une flotte qui ne produit que du META construit un atelier sans rien y fabriquer ([détail §11](../../docs/reference/variation-protocol-detail.md)).

**`slides`** : CONTENU si le grain écrit ou enrichit le deck ; sinon le genre du type de travail (gate CI de build → `guard`, script → `refactor`, convertisseur → `tooling`) — [détail §Levier B, L44](../../docs/reference/variation-protocol-detail.md).

Un genre hors liste est un **alias** que le merge-gate normalise : pas une violation, le worker n'est ni repris ni HOLD. **Le GENRE est le TYPE DE TRAVAIL, jamais la famille où vivent les fichiers** : le composé `<famille>-<genre>` **se réduit toujours à sa tête** ; les synonymes se normalisent (table complète : [détail §Alias](../../docs/reference/variation-protocol-detail.md)).

**`guard` vs `tooling` — le discriminant est « est-ce que ça peut rougir ».** Un check susceptible de passer au rouge est `guard` ; un script/helper/convertisseur sans statut d'échec propre est `tooling`.

**Entrer dans la liste LIGHT de G-VAR-3 se mesure, jamais s'intuitionne** : un genre y entre dès **≥ 2 grains LIGHT mergés**.

### Grain REPAIR — hérite du genre de la PR qu'il répare

| PR réparée | Tag REPAIR | Genre | Plancher G-VAR-1 |
|---|---|---|---|
| `notebook-python` | `MED/notebook-python` | **CONTENU** | grain de contenu **au-delà** du plancher |
| `lean` | `MED/notebook-lean` | **CONTENU** | grain de contenu **au-delà** du plancher |
| `guard` | `MED/guard` | **META** | ne tient **pas** le plancher, comme toute PR META |

**Prescriptions** : genre hérité déclaré **directement**, sans annotation (le REPAIR se lit au titre `fix(`) ; tier au litmus habituel (ré-exécution complète + diagnostic de ratchet = `MED` ; ligne de body = `LIGHT`, budget G-VAR-2) ; un REPAIR de PR **META** reste **META**, jamais le plancher. Exemples et arbitrage : [détail §13](../../docs/reference/variation-protocol-detail.md), [§Levier B, L52](../../docs/reference/variation-protocol-detail.md).

## 2. Les trois gates durs

- **G-VAR-1 — Plat principal DEEP, dans un genre de CONTENU.** La PR-plancher du cycle (R1 de proactive-coordination) **DOIT** être DEEP **et** porter un genre de la classe CONTENU. **Une LIGHT ne satisfait JAMAIS le plancher ; un genre META non plus, quel que soit son tier ; un MED non plus.** Le MED et le META restent **bienvenus au-delà** du plancher (sous budget G-VAR-2 pour leurs composantes LIGHT) : ce qui est exigé, c'est qu'**au moins un** grain DEEP de contenu porte le cycle ([détail §12.3](../../docs/reference/variation-protocol-detail.md)).

  **Consolider est du DEEP, et la priorité se règle au tapis (mandat user 2026-10-25).** Une consolidation de série déclare le genre des carnets qu'elle réorganise, comme un REPAIR hérite du genre de la PR réparée. Un carnet neuf reste DEEP, mais son tier ne le rend pas prioritaire : les issues de consolidation reviennent en tête du tapis, un EPIC qui étend une série au plus une fois ([détail §14](../../docs/reference/variation-protocol-detail.md)).

  **#15793** : le plancher est **DEEP**, pas « DEEP ou MED » — motif et contre-poids anti-inflation (`TIER-INFLATION`) : [détail §12](../../docs/reference/variation-protocol-detail.md).

  **La sécheresse se mesure — [`scripts/pick_idle_grain.py`](../../scripts/pick_idle_grain.py) — elle ne s'auto-évalue pas (#13086).** Au seuil de merges consécutifs sans genre CONTENU, le picker **restreint le tirage aux genres CONTENU** (le grain reçu tient le plancher). L'échappatoire `--ignore-drought` **se justifie par écrit** ; une capability **se mesure sur les lanes sœurs du même modèle**, elle ne se déclare pas (mécanisme : [détail §12.3](../../docs/reference/variation-protocol-detail.md)).

- **G-VAR-2 — Budget LIGHT proportionnel : `max(1, grains_mergés_du_jour // 3)`**, par lane et par jour, **toutes catégories LIGHT confondues** ; au-delà du budget, la LIGHT attend demain ou cède la place à du DEEP/MED. Le budget se **calcule** — [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) — il ne se déclare pas ([détail §4](../../docs/reference/variation-protocol-detail.md)).

  Note d'arbitrage (#11154) : les PRs `DEFECT-ALIVE` (dette #11044) **consomment le budget LIGHT**, avec exception écrite + mesure de la dette résiduelle à chaque merge au cap.

- **G-VAR-3 — Pas deux fois le même GENRE LIGHT consécutif.** Sur les genres LIGHT (`guard` · `ledger` · `docs` · `readme` · `test`) : bloqué dès 2 grains consécutifs de même genre, **sauf** exception mécanique. Les genres de CONTENU ne relèvent pas de G-VAR-3 ([détail §7](../../docs/reference/variation-protocol-detail.md)).

  **Exception MED/DEEP mesurable (#14357)** : deux grains consécutifs d'un même genre LIGHT sont autorisés **ssi** (i) le **second** est MED ou DEEP et (ii) les deux PRs ne partagent **aucun fichier**. Le critère est **mécanique, jamais jugé à la main, fail-CLOSED** (rendu par `variation_light_cap.py`, consommé par `variation_adjacency_guard.py`) — un run de ≥3 s'exempte seulement si **chaque paire adjacente** satisfait (i) et (ii). Le « Tell décisif » (litmus LIGHT bloquant **même sous une étiquette DEEP**) : [détail §Levier B, L78](../../docs/reference/variation-protocol-detail.md).

  **Exemption de lane (#26988, décision user Q194 a du 16/11/2026)** : la lane désignée pour les organes de CI est **exempte de G-VAR-3** (liste unique : `G_VAR3_EXEMPT_LANES` dans l'organe) ; **G-VAR-1 et G-VAR-2 restent appliqués** ([détail §15](../../docs/reference/variation-protocol-detail.md)).

## 3. Merge-gate coordinateur (ai-01) — les dents (HARD)

À chaque passe, pour chaque PR, **lire le tag** et croiser avec les grains récents de la lane ([détail §1](../../docs/reference/variation-protocol-detail.md)) :

| Constat | Action |
|---|---|
| LIGHT d'une lane à budget épuisé (G-VAR-2) | **HOLD** : citer la sortie de `variation_light_cap.py` (`N` LIGHT pour `M` grains), pas une estimation |
| 2ᵉ même-GENRE consécutif (G-VAR-3) | **HOLD**, sauf exception mécanique #14357 rendue par l'organe (`exempt_runs`) |
| Plancher tenu par une LIGHT (G-VAR-1) | steer vers un grain **DEEP de contenu** du pool, **nommé** |
| Plancher tenu par un **MED** ou un genre **META**, même tagué DEEP (G-VAR-1) | le cycle n'a pas de plancher : merger la PR si elle est bonne, **et** nommer dans le même geste le grain DEEP de contenu qui portera le cycle suivant. Ne **pas** HOLD une PR META saine — c'est le **provisionnement** qui a manqué (§4) |
| Tag mal dérivé (tier sur-coté, genre pris sur la famille, alias/composé) | **re-qualifier le tag soi-même**, puis traiter selon le tag corrigé |
| `lane` absente | **HOLD** jusqu'à déclaration — un grain sans lane est **structurellement incomptable** |

**Le tag déclaré n'est pas auto-exécutoire** : il rend le grain auditable, il ne le définit pas. Merger sans lire le tag laisse le protocole s'auto-certifier.

**Ne jamais tenir une LIGHT plus d'une journée** : un hold prolongé fait réécrire le même travail par une autre lane. Passé 24 h : merger, ou fermer **en nommant le remplaçant**.

Le HOLD est **attaché à la candidate**, jamais à la cadence de sa lane. Il ne sanctionne jamais l'idle ([coordinator-discipline.md](coordinator-discipline.md) R0/R4) et ne bloque jamais un nouveau grain **DEEP de contenu** : toujours accompagné d'un grain nommé du pool, en **double canal** (DM inbox + `[DISPATCH→inbox]` dashboard). HOLD sans remplacement, ou HOLD pour réduire les dispatchs, = échec coordinateur.

## 4. Provisionnement d'exception — ce qui lie ai-01 (HARD)

Le provisionnement est une **exception nommée** : le coordinateur provisionne **quand il a une raison nommée** (sécheresse mesurée, dette de batch-close, veine à équilibrer), pas par quota de lane ni à chaque cycle (cause racine et corollaires mesurés : [détail §9](../../docs/reference/variation-protocol-detail.md)). Quand il provisionne, `ai-01` :

0. **Le tirage est la voie par défaut** : une lane sans steering **tire** et n'attend rien. Un steering nommé s'ajoute au tirage quand il est déjà là (mécanisme never-empty, règle 7) — et doit être le plus équilibré possible : un steering qui répète le genre du cycle précédent fait pire que le tirage.
1. **Provisionne sur sa raison nommée**, **groundé firsthand** (`gh issue view`), varié en genre d'une lane à l'autre.
2. **Agrège les GENRES des merges récents avant de provisionner**, pas seulement leurs tiers — le tirage ne voit pas l'historique de genres de la flotte ([détail §9](../../docs/reference/variation-protocol-detail.md)).
3. **Un batch-close de famille crée une dette de provisionnement**, à honorer dans le même cycle.
4. **Varie la loterie** — le coordinateur applique G-VAR-3 à son propre dispatch.
5. **Dissocie admission et production** : les candidates en HOLD, `DWELL`, review ou attente de merge ne diminuent jamais le provisionnement dû. La queue d'admission se résorbe par une piste de digestion parallèle ; elle n'applique aucune backpressure globale aux producteurs.

Sous-provisionner puis merger la monoculture = **le** manquement corrigé ; ralentir la production pour la digestion = l'autre ([détail §9](../../docs/reference/variation-protocol-detail.md)).

## 5. Auto-détection

Avant de claim / de merger : **« ce grain est-il générable-en-série (LIGHT) ET (budget épuisé OU même-genre-que-le-précédent) ? »** Si oui, c'est la monoculture — le worker pioche un **DEEP de contenu**, le coordinateur HOLD+redirige.

Et la question que le tier seul ne posait pas, en fin de cycle : **« qu'est-ce que ce cycle a ajouté au dépôt qu'un lecteur ou un étudiant puisse utiliser ? »** Si la seule réponse honnête est « un détecteur de plus, un guard de plus, une doc de plus », le plancher n'est pas tenu — quel que soit le nombre de PR mergées. Côté worker : piocher un grain de contenu. Côté coordinateur : c'est un défaut de provisionnement (§4), pas une faute de lane.

## Voir aussi

- [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md) — justifications mesurées, incidents #8056 / #8961, historique des applications
- [proactive-coordination.md](proactive-coordination.md) — R1, R5 (pool global), R6/R7 (variété, never-idle)
- [coordinator-discipline.md](coordinator-discipline.md) — R4 (jamais sanctionner l'idle), R5 (steer qui ATTEINT/VRAI/DÉCIDE)
