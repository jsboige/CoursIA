# Picker delaisse — verifier FIRSTHAND avant de conclure "pool sature"

Source : issue **#11900** « [variation] Le tirage remonte du delaisse — et le delaisse est presque toujours une EPIC dont le body est faux (2/2 mesures) ». Mesure du 2026-08-20 par ai-01 sur la lane `myia-ai-01:CoursIA` : deux EPICs remontées par le picker (`inact` = 68 j et 31 j), leurs bodies étaient devenus **faux** post-resolution, et le paragraphe bloquant avait survécu à sa propre resolution.

| EPIC | inactive | ce que son body réclamait | ce qui était vrai |
|---|---|---|---|
| **#2874** knot Lean | **68 j** | « PR #2875 en review, attente review ai-01 » + un chemin de lake | PR **mergee le 13/06** ; chemin **inexistant** (lake déplacé vers `SymbolicAI/Lean/`) |
| **#7357** Backtester E2 | **31 j** | « j'ai besoin d'un `/coordinate` avec l'option choisie **AVANT** d'engager » | décision prise **par le user lui-même, le jour même**, 1er commentaire : « le gate est leve » |

Mécanisme identique : une lane tire l'EPIC, lit une demande adressée à **quelqu'un d'autre**, conclut « bloquée sur autrui », la repose. **Le paragraphe bloquant a survécu à sa propre resolution.**

## Regle HARD

**Avant de conclure qu'un grain issu du picker est « bloqué sur autrui », « saturated », « done elsewhere », ou « narrow structural » — vérifier FIRSTHAND que la situation décrite dans son body est toujours vraie.** Un body d'issue/PR est daté de **sa rédaction**, pas de sa lecture ; `gh issue view N` est un status condensé de plus dès qu'un merge, une décision user, ou une PR résolue est passée après.

L'organe de vérification est :

1. **L'artefact** sur `main` courant — `git log -- <fichier>` + lecture du fichier (`Read` direct, pas un résumé).
2. **Le plateau** — `gh pr list --state all --search "head:<branch>"` + `gh pr list --state open --json files` sur le **chemin** visé.
3. **Le commentaire de fermeture / décision** — `gh issue view N --comments` pour les commentaires après le dernier commit de référence du body.

Tant qu'un seul de ces trois montre que la situation a changé, le grain n'est PAS ce que son body dit ; il faut soit le clôturer (acceptance livrée), soit en extraire un sous-grain effectivement vivant.

## Anti-patterns interdits

| Anti-pattern | Pourquoi c'est un piège | Alternative |
|---|---|---|
| **Conclure "pool narrow saturé"** parce que tous les top picks du picker sont sous PR d'autres lanes ou `candidate-delivered` | Les PRs d'autres lanes peuvent être **OPEN BLOCKED** en attente drainage `#11860` — le picker ne les voit pas comme deliverable. Le narrow peut être **structurel** (saturation file CI), pas une absence réelle de grain. | Vérifier `gh issue list --state open --limit 300` filtré non-EPIC/non-candidate-delivered ; vérifier que la PR sous-jacente a des **checks réels** (pas tous PENDING depuis 24 h). Si narrow structurel confirmé → geste META productif (escalade DM ai-01 ou règle du harnais), **pas** un état terminal-idle. |
| **Conclure "EPIC bloquée sur autrui"** parce que le 1er paragraphe du body dit « attente review/de décision » | Le paragraphe bloquant peut avoir été **résolu** postérieurement — un merge, une décision user dans un commentaire, un déplacement de fichier. | `gh issue view N --comments` pour le **commentaire le plus récent** + `git log --all --oneline -- <chemin>` pour vérifier la subsistance. Si la situation a changé → clôturer ou sous-grainer. |
| **Re-piocher** une issue `candidate-delivered` sans vérifier qu'elle est bien livrée | Le label est posé par advisory, **pas** une vérité — il a ~60 % de faux positifs (mesuré #11900 + audits antérieurs). | `gh pr list --state all --search "<issue-id>"` + lire la PR référencée, vérifier qu'elle satisfait **toute** l'acceptance du body, **et** qu'aucun commentaire ne la contredit. |
| **Citer le `mergeStateStatus: BLOCKED`** comme « le grain est rouge » | BLOCKED ≠ rouge. BLOCKED = soit en attente review, soit en attente de re-rollup (file CI saturée). Aucun des deux ne dit « la lane doit réparer ». | Croiser BLOCKED avec le contenu de `statusCheckRollup` : si tous PENDING depuis >N h sans failed → narrow structurel, escalader ai-01 ; si un `conclusion: FAIL` existe → vérifier si la lane peut le lever (sinon `--ignore-red`). |
| **Sauter la vérification FIRSTHAND** parce que le picker a déjà filtré | Le picker **remonte** des grains pondérés par délaissement — il ne lit **pas** les bodies, il ne valide **pas** la situation. C'est l'opérateur qui porte cette charge. | `gh issue view N --json title,body,comments` (10 s) **avant** de claimer. Si le body dit « attente X » → vérifier que X est toujours en attente. |

## Verdict pour un grain delaisse remonte

Apres verification FIRSTHAND (3 etapes de la regle HARD), le grain tombe dans exactement **une** de ces 4 cases :

1. **Situation inchangée** → grain **vivant** : claimer, livrer (ou sous-grainer si EPIC).
2. **Situation resolue** mais issue non fermée → grain **delivered** : fermer avec preuve (cf pattern `candidate-delivered` proactive-coordination.md) ou **retirer le label** en disant pourquoi.
3. **Situation resolue et acceptee par toutes les parties** mais issue oubliée → grain **clos-substantive** : poster un rapport de cloture avec preuves (cf pattern po-2027 c.504-L1 delivered) + recommander `option 1 : cloture par ai-01`.
4. **Situation resolue MAIS corps devenu périmé** (le 1er paragraphe dit « attente X » mais X est passé) → grain **misleading** : corriger le body avec un edit honest (`gh issue edit N` ou commentaire en tete), **puis** appliquer la case 1/2/3 appropriée.

L'erreur systémique qui produit le narrow structurel persistant = **sauter la verification FIRSTHAND et appliquer la case 1 (vivant)** alors que la case 2/3/4 etait la bonne. La flotte conclut à tort que le pool est sature — l'inverse exact de l'intention du tirage.

## Detection systematique — un test par cycle

A chaque cycle `/continue` ou `/coordinate`, **avant de conclure quoi que ce soit** :

```bash
# 1. Verifier qu'un top pick du picker n'est pas un delivered fantome
gh issue view <N> --json title,body,comments --jq '.comments[-1] | {body: .body[0:200], createdAt: .createdAt}'
git log --all --oneline -- <chemin du body> 2>&1 | head -5

# 2. Verifier qu'une PR d'une autre lane n'est pas un OPEN BLOCKED structurel
gh pr list --state open --search "<issue-id>" --json number,state,mergeStateStatus,statusCheckRollup --jq '.[] | "\(.number) \(.state) \(.mergeStateStatus)"'

# 3. Confirmer que le narrow est reel, pas une错觉 de picker
gh issue list --limit 200 --state open --json number,title | jq 'length'
```

Si l'etape 3 retourne 0 alors que le picker a rendu des candidats → **le picker lit un cache ou un filtre étriqué**, escalader ai-01.
Si l'etape 1 montre un commentaire récent qui résout la situation → case 2/3/4, pas case 1.

## Lien avec les autres regles

- [proactive-coordination.md](proactive-coordination.md) R5 — le picker systématique remonte ce pool ; sans cette règle, le régime produit des rerolls en boucle.
- [proactive-coordination.md](proactive-coordination.md) règle `candidate-delivered` — pattern de vérif qui a inspiré cette règle (vérifier FIRSTHAND avant de re-piocher).
- [coordinator-discipline.md](coordinator-discipline.md) R5 — le coordinateur **doit** grounder firsthand AVANT de dispatcher (analogie côté supply).
- [verify-before-claiming.md](verify-before-claiming.md) — règle générale G.1 (vérifier avant de clamer « X est bloqué »).
- [audit-reassessment.md](audit-reassessment.md) — pattern de ré-assessment 4 étapes applicable ici (vérification mécanique + pédagogique + dashboard + fix).

## Origine et leçons ancrees

Issue **#11900** — pools narrow structurels documentés par ai-01 c.1331p477 et suivants (mesures 2/2 delaisse body faux). Reproduit par ma lane `myia-po-2023:CoursIA-2` pendant 9 cycles consecutifs (c.503 → c.522) avant la consignation ; la cause directe était l'absence de **regle explicite** imposant la verification FIRSTHAND a chaque grain picker.

Leçon durable : **un picker pondéré n'est pas un picker qui sait lire**. La vérification de l'opérateur reste le remède ; cette règle la rend explicite et reproductible.