# Double-clé de resynchronisation (`translation-override`) — voie normale d'une lane

> **Statut** : référence opérationnelle. Ce document transpose dans le dépôt l'arbitrage
> ai-01 du dispatch `c2760` (commentaire sur #20232, 2026-11-03), qui ne vivait jusqu'ici
> que dans un fil d'issue. Les organes cités sont lus à la source et les chiffres de la
> section 7 sont mesurés ; la décision, elle, appartient au coordinateur.

## 1. La boucle que ce document dénoue

Deux organes, tous deux sains, se contredisent sur les mêmes fichiers.

| Organe | Ce qu'il exige | Où il parle |
|---|---|---|
| Cliquet hot-subset (#13551) | Une cellule FR modifiée qui portait déjà une traduction doit voir sa ligne CSV resynchronisée **par cellule**. Jamais de ré-extraction globale, qui orpheline les traductions déposées | `scripts/translation/tests/test_hot_subset_ratchet.py`, docstring et message d'assertion |
| Garde de traduction (#10332) | Les fichiers dérivés sous `translations/` ne se modifient pas à la main ; une PR qui les touche rougit | `.github/workflows/translation-guard.yml` |

La resynchronisation exigée par le premier **est** une modification des fichiers que le
second protège. Une lane qui obéit à l'un rougit sur l'autre, revient en arrière, et
laisse des `_en` orphelins — c'est l'occurrence fondatrice décrite dans #20232.

Les deux organes se nomment désormais mutuellement : le message du cliquet nomme le garde
et son double-clé, et le résumé d'étape du garde nomme le cliquet
(`.github/workflows/translation-guard.yml`, étape de détection et commentaire d'en-tête).
Cette partie a été livrée par la PR #21395 (mergée le 2026-10-24, `c0c5f369390`). Ce qui
manquait n'était donc pas la nomenclature, mais **la règle** : quand le double-clé est-il
la bonne voie, et avec quel motif.

## 2. La décision

Arbitrage ai-01 (dispatch `c2760`, #20232, 2026-11-03). Le cliquet traite deux tailles de
dérive avec le même organe ; on les sépare.

| Cas | Règle |
|---|---|
| Dérive **cosmétique** ou de faible valeur (exemple : un lien de version dans une ligne de navigation) | On ne la poursuit pas. Aucun gate n'est conditionné dessus, donc le double-clé ne se paie pas pour elle : le jumeau `_en` reste au niveau de référence de la chaîne de navigation. |
| Dérive **substantielle** (la source FR diverge réellement du CSV — cas des 36 CSV de #21490) | On resynchronise par `T1 --update`, qui est une opération **par cellule et préservante**, sous le double-clé mainteneur. |

Le point qui dénoue le conflit est le second : `T1 --update` **est** la resynchronisation
par cellule que le cliquet prescrit, et ce n'est **pas** la ré-extraction globale qu'il
interdit.

Cette distinction est une **règle de conduite, pas un contrôle automatique** : le helper
vérifie la présence des deux clés et un motif non vide, mais aucun organe ne lit le motif
pour distinguer le substantiel du cosmétique. Une lane qui poserait le double-clé sur une
dérive cosmétique passerait le garde sans un rouge — c'est le motif journalisé qui permet
de le lui reprocher après coup.

## 3. La voie normale (quand, à qui, quel motif)

### Quand

La source FR d'un carnet traduit a réellement dérivé du CSV — une dérive de **contenu**,
pas cosmétique — **et** le remède est une resynchronisation, pas un abandon du carnet.

### À qui

Le mainteneur. Le geste est le double-clé mécanique de #10332, posé sur la PR :

- l'étiquette **`translation-override`** ;
- **et** un commentaire de PR dont la **première ligne** est `[TRANSLATION-OVERRIDE] <motif>`.

Les deux sont requis. Le helper `scripts/ci/translation_override_required.py` est
l'organe testable qui rend le verdict ; le garde journalise le motif accepté
(`::notice ... OVERRIDE accepted -- motif: ...`) et un motif absent laisse la PR rouge.
Dans la pratique mesurée (section 7), l'étiquette est posée sur la PR par la lane qui
porte la resynchronisation, et c'est le **motif** qui rend le geste auditable.
« Mainteneur » s'entend ici comme **la personne qui assume la responsabilité du geste** :
ni le helper ni le garde ne vérifient qui a posé l'étiquette — le double-clé rend le
geste visible, il ne l'autorise pas.

### Motif type

> resync T1 `--update` du CSV `<chemin>` : dérive substantielle (`<cause>` : source FR
> modifiée / corpus périmé / N cellules nouvelles) ; traductions déposées préservées
> verbatim ; cliquet hot-subset satisfait (SRC_DRIFT ramené à 0).

Le motif dit trois choses : **ce qui a dérivé**, **pourquoi la modification d'un fichier
dérivé est légitime**, et **le verdict de l'autre organe**. Un motif qui ne dit que
« resync » ne permet pas de distinguer le cas substantiel du cas cosmétique que la
section 2 refuse.

## 4. Pourquoi `T1 --update` satisfait le cliquet

`scripts/translation/extract_cells_to_csv.py` documente le mode `--update` en tête de
fichier : il met à jour un CSV **existant** sans écraser les autres entrées ni perdre les
colonnes remplies par T3, et « les colonnes cibles non-pivot sont préservées verbatim si
la ligne (notebook, cell_id) existe déjà ». Quand `--update` change `src_hash` (le pivot),
les colonnes `text_<lang>`, `hash_<lang>` et `src_hash_<lang>` survivent verbatim.

Conséquence : la resynchronisation déplace le `src_hash` de la ligne — ce qui ramène
`SRC_DRIFT` à zéro — **sans** perdre la traduction déposée. Une ligne dont la cellule a
disparu est conservée, pas effacée. C'est exactement l'inverse de la ré-extraction
globale que le cliquet interdit.

Deux précisions que le lecteur du rapport de cliquet croisera immédiatement :

- La préservation de `src_hash_<lang>` (#20836) est **voulue** : c'est elle qui garde le
  verdict `STALE_TRAD` capable de signaler une traduction déposée sur une source
  antérieure. « Corriger » un `STALE_TRAD` en remettant `src_hash_<lang>` à jour
  détruirait le signal — la traduction périmée paraîtrait fraîche. (Sur le chemin
  « append » — cellule nouvelle sans ligne préexistante — la ligne fraîche ne porte que
  les colonnes pivot : il n'y a rien à préserver.)
- **L'ordre des gestes fait la différence** (#21490) : `src_hash` est calculé sur le
  texte **courant** du carnet au moment du `--update`. On édite la source, **puis** on
  resynchronise — jamais l'inverse : resynchroniser un carnet dont la source va encore
  bouger laisse un `SRC_DRIFT` à zéro pour un texte intermédiaire.

## 5. Contexte : le moteur est en attente mainteneur

`translation-sync.yml` est en attente mainteneur depuis le 2026-08-12 (#15198, #10038) :
il ne tourne plus à chaque PR, donc **éditer la source FR ne rafraîchit plus le fichier
dérivé**. Tant que cette attente dure, le double-clé est la seule sortie auditables pour
une modification légitime d'un fichier dérivé ; une modification silencieuse à la main
reste interdite. L'attente est antérieure à l'arbitrage et le double-clé avait été conçu
pour elle (#10332) avant que le conflit avec le cliquet ne soit identifié (#20232).

## 6. Ce que le double-clé ne couvre pas

- **Une modification à la main d'un fichier dérivé** sans resynchronisation par l'organe :
  c'est ce que le garde existe pour empêcher, et le motif ne le couvre pas.
- **Une ré-extraction globale** : elle satisfait le garde mais casse le cliquet en
  orphelinant les traductions. Le motif ne la rend pas acceptable.
- **Une dérive cosmétique** : le double-clé n'est pas un péage à payer pour la propreté
  d'une ligne de navigation (section 2).

## 7. Mesures

Relevés sur `main` le 2026-11-13 (`myia-po-2024:CoursIA`) :

| Mesure | Valeur | Commande |
|---|---|---|
| PR portant l'étiquette `translation-override` | **244** (231 mergées, 9 fermées, 4 ouvertes) | `gh pr list --label translation-override --state all --limit 1000 --json number,state` |
| Cliquet hot-subset | **vert** — 2 tests passés, `hot == []` | `python -m pytest scripts/translation/tests/test_hot_subset_ratchet.py` |

Le blocage décrit dans #20232 est donc **latent**, pas actif : il ne mord qu'une lane qui
touche une source traduite dont la ligne CSV porte une traduction déposée. Les 244 PRs de
la première ligne montrent que la voie est déjà empruntée en pratique ; ce document en
écrit les bornes.

## 8. Voir aussi

- #20232 — le conflit cliquet / garde, et l'arbitrage transposé ici
- #10332 — la mécanique du double-clé (étiquette + marqueur de commentaire)
- #13551 — le cliquet hot-subset
- #15198 et #10038 — l'attente mainteneur du moteur de synchronisation
- #21490 — le rejeu `T1 --update` des 36 CSV, autorisé par la voie du double-clé
- #20836 — la colonne `src_hash_<lang>` et le verdict `STALE_TRAD`, que la préservation
  du `--update` garde vivants
- `scripts/ci/translation_override_required.py` — le helper testable du verdict
- `.claude/rules/secrets-hygiene.md` règle 6 — une sortie de cellule ne s'édite jamais à
  la main ; la modification d'un fichier dérivé passe par son organe
- `docs/i18n/CSV-by-series-design.md` — le design de l'infrastructure CSV par série
- `docs/translation/translations-root-diagnostic.md` — l'état des lieux du répertoire
  `translations/`

***

*Rédigé le 2026-11-13 par `myia-po-2024:CoursIA` (c477), à partir de l'arbitrage ai-01 du
dispatch `c2760`. Doc-only : aucune modification de code, de workflow ni de fichier
traduit.*
