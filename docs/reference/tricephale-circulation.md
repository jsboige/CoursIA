# Tricéphalie — coordinateur, titulaire, secrétaire

La coordination CoursIA a **trois têtes**, chacune avec sa lane, sa skill et son artefact. Ce document dit **qui est qui** et **comment l'information circule** entre elles. La règle de lecture elle-même (inbox d'abord, puis énumération des dashboards) est portée par `CLAUDE.md` §A et par la skill `coordinate-adjoint` ; elle n'est pas redéfinie ici.

| Tête | Lane | Skill | Rôle | Artefact |
|---|---|---|---|---|
| **Coordinateur** | `myia-ai-01:CoursIA` | `coordinate` | merge, clôture, arbitrage, politique de flotte | `workspace-CoursIA` (+ `global`) |
| **Titulaire** | `myia-po-2025:CoursIA-2` | `coordinate-adjoint` | émet les dossiers `[ADJOINT PREFLIGHT]` exact-head que `merge_ready` et le coordinateur consomment | `workspace-CoursIA-2` |
| **Secrétaire** | `myia-po-2026:CoursIA-3` | `adjoint-secretary` | attestation tierce du plus ancien au plus récent (dossiers qu'ai-01 lit et approuve, puis que `merge_ready` merge), puis circulation : DMs nominatifs, alertes conflits / quota / runners | `workspace-CoursIA-3` |

« Le secrétariat », « le secrétaire » et « le troisième dashboard » désignent `myia-po-2026:CoursIA-3` et son artefact `workspace-CoursIA-3`.

Ces clés sont des **identités**, pas une liste de lecture : le tableau dit qui est qui, jamais quoi lire.

## Pourquoi le tour énumère les dashboards au lieu de les nommer

Une liste codée en dur rend **structurellement aveugle** à toute clé qu'elle n'anticipe pas. Mesure fondatrice (#17197) : `workspace-CoursIA (2)`, clé forkée par collision de noms Google Drive, a porté **23 messages vivants** de deux lanes, dont deux PRs débloquées en attente du merge-gate, pendant plusieurs jours sans qu'aucun cycle la voie. L'indice de suffixe tourne d'un fork à l'autre : une règle qui aurait nommé `(2)` aurait été périmée au fork suivant.

Une clé à suffixe ` (N)` dont le `workspace` déclaré **ne porte pas** ce suffixe est une **moitié de la même lane**, pas une lane voisine : la lire, et escalader la réparation (`action:"merge"`).

Pourquoi l'inbox passe avant : elle porte souvent le DM nominatif qui change la priorité du cycle. Mesure : un lot nominatif du coordinateur et deux corrections de doctrine ont dormi non lus pendant que deux cycles consécutifs du titulaire produisaient selon une doctrine périmée.

**Articulation avec la R3 de [coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md)** (« deux dashboards workspace co-égaux ») : la R3 fixe un **plancher**, les deux lanes sur lesquelles le coordinateur lit et poste un contenu propre à chacune. L'énumération le couvre, puisque ces deux clés figurent dans le résultat de `list`, et l'étend au secrétariat et aux moitiés forkées. Les deux textes ne se contredisent pas.

## Le format se rend nominatif — mesuré

| Format rendu au coordinateur | Conversion en merge |
|---|---|
| liste **nominative** (numéros en clair) | 10/10 — 100 % |
| **cumul** non nommé (« 56 OK B.0 frais ») | 15/53 — 28 % |
| auto-tirage aveugle par le coordinateur | 2/54 — 4 % |

Un compte dit que du travail existe ; **une liste dit lequel merger**. La re-découverte à l'aveugle périme en outre les dossiers qu'elle traverse.

## Rôle du secrétaire

Le constat qui a fondé le rôle, le 22/09 : 158 PRs attestées pour 10 mergées, soit **6 %** de conversion. Un dossier attendait alors le cycle du coordinateur et périssait en attendant ; la doctrine a donc réservé les dossiers aux dispatchs nominatifs.

Depuis le 23/09, l'organe `scripts/coordination/merge_ready.py` merge toutes les 20 minutes les PRs hors harnais et hors DEEP qui portent un dossier tiers READY ; depuis le 28/09 (#18257), il exige en plus une approbation d'ai-01 qui couvre le contenu de la tête, et ne sert qu'à éviter qu'un dossier se périme entre cette lecture et le merge. Le constat s'est inversé : le 28/09, 98 des 103 PRs ouvertes attendaient un dossier valide, et huit cycles consécutifs du secrétaire n'en avaient émis aucun. La doctrine a été corrigée le 28/09 :

- **Niveau 1** (mode normal) : attestation tierce, à l'initiative du secrétaire, de toute PR sans dossier vivant, du plus ancien au plus récent, sans attendre de dispatch. Le crible de fond reste obligatoire : ai-01 lit les réserves, le delta et la preuve centrale, et s'appuie sur le dossier pour le reste.
- **Niveau 2** : circulation. Liste nominative au coordinateur de tous les READY, qui déclenche sa lecture ; alertes aux porteurs des PRs `CONFLICTING` ou en `CHANGES_REQUESTED` ; quota et runners quand la mesure le justifie.

Critère de succès d'un cycle du secrétaire : des PRs sortent de la file grâce à lui. Une surveillance sans dossier, alors que le pool en attend, n'est pas un cycle. Détail et garde-fous : skill `adjoint-secretary`.

## Les skills du trio sont sous contrôle de source

`coordinate`, `coordinate-adjoint` et `adjoint-secretary` se relisent et se corrigent régulièrement, comme du code, pas seulement quand elles cassent (`coordinate` §« Amelioration continue des skills »). Trois défauts muets à y chercher en priorité :

1. une **liste codée en dur** de ce qu'il faut lire (dashboards, lanes, organes) — elle ne voit pas ce qu'elle n'anticipe pas ;
2. une **référence vers une branche** plutôt que `main` — elle pointe un état périmé, et devient muette si la branche disparaît ;
3. un **geste réimplémenté à la main** alors que `scripts/` porte l'organe.

## Rappels d'émission

- Poster le dossier **en dernier** : toute écriture tierce postérieure le périme (`discussion changed after dossier` = 12 des 32 refus d'un cycle mesuré).
- Un `BLOCKED` attesté vaut mieux qu'un `READY` forcé : `exit 3` laisse dispatcher depuis le motif.
- Sur un rouge `Scripts Tests (CPU)` imputable au runner, attester `BLOCKED` **en nommant la cause runner** plutôt que de renvoyer la PR à son auteur, qui n'a rien à réparer.

## Voir aussi

- [coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) — autorité et cadence du coordinateur
- [proactive-coordination.md](../../.claude/rules/proactive-coordination.md) — pool global, plancher de production
- [lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md) — le claim vit sur l'issue
- [variation-protocol.md](../../.claude/rules/variation-protocol.md) — tag `Grain:` et merge-gate
