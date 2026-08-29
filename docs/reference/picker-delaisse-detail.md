# Picker delaisse — verification FIRSTHAND (detail)

> **Source :** [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md) regle 5. Cette page est le detail ; la regle auto-chargee pose le geste obligatoire.

## Origine : issue #11900

Mesure du 2026-08-20 par ai-01 sur la lane `myia-ai-01:CoursIA` : deux EPICs remontees par le picker (`inact` = 68 j et 31 j), leurs bodies etaient devenus **faux** post-resolution, et le paragraphe bloquant avait survécu a sa propre resolution.

| EPIC | inactive | ce que son body réclamait | ce qui etait vrai |
|---|---|---|---|
| **#2874** knot Lean | **68 j** | « PR #2875 en review, attente review ai-01 » + un chemin de lake | PR **mergee le 13/06** ; chemin **inexistant** (lake deplacé vers `SymbolicAI/Lean/`) |
| **#7357** Backtester E2 | **31 j** | « j'ai besoin d'un `/coordinate` avec l'option choisie **AVANT** d'engager » | decision prise **par le user lui-meme, le jour meme**, 1er commentaire : « le gate est leve » |

Mecanisme identique : une lane tire l'EPIC, lit une demande adressée a **quelqu'un d'autre**, conclut « bloquée sur autrui », la repose. **Le paragraphe bloquant a survécu a sa propre resolution.**

## Verdict pour un grain delaisse remonte

Apres verification FIRSTHAND (3 etapes de la regle 5), le grain tombe dans exactement **une** de ces 4 cases :

1. **Situation inchangee** → grain **vivant** : claimer, livrer (ou sous-grainer si EPIC).
2. **Situation resolue** mais issue non fermee → grain **delivered** : fermer avec preuve (cf pattern `candidate-delivered` proactive-coordination.md) ou **retirer le label** en disant pourquoi.
3. **Situation resolue et acceptee par toutes les parties** mais issue oubliee → grain **clos-substantive** : poster un rapport de cloture avec preuves (cf pattern po-2027 c.504-L1 delivered) + recommander `option 1 : cloture par ai-01`.
4. **Situation resolue MAIS corps devenu perime** (le 1er paragraphe dit « attente X » mais X est passé) → grain **misleading** : corriger le body avec un edit honest (`gh issue edit N` ou commentaire en tete), **puis** appliquer la case 1/2/3 appropriee.

L'erreur systemique qui produit le narrow structurel persistant = **sauter la verification FIRSTHAND et appliquer la case 1 (vivant)** alors que la case 2/3/4 etait la bonne. La flotte conclut a tort que le pool est sature — l'inverse exact de l'intention du tirage.

## Anti-patterns interdits

| Anti-pattern | Pourquoi c'est un piege | Alternative |
|---|---|---|
| **Conclure "pool narrow sature"** parce que tous les top picks du picker sont sous PR d'autres lanes ou `candidate-delivered` | Les PRs d'autres lanes peuvent etre **OPEN BLOCKED** en attente drainage `#11860` — le picker ne les voit pas comme deliverable. Le narrow peut etre **structurel** (saturation file CI), pas une absence reelle de grain. | Verifier `gh issue list --state open --limit 300` filtre non-EPIC/non-candidate-delivered ; verifier que la PR sous-jacente a des **checks reels** (pas tous PENDING depuis 24 h). Si narrow structurel confirme → geste META productif (escalade DM ai-01 ou regle du harnais), **pas** un etat terminal-idle. |
| **Conclure "EPIC bloquée sur autrui"** parce que le 1er paragraphe du body dit « attente review/de decision » | Le paragraphe bloquant peut avoir ete **resolu** postérieurement — un merge, une decision user dans un commentaire, un deplacement de fichier. | `gh issue view N --comments` pour le **commentaire le plus recent** + `git log --all --oneline -- <chemin>` pour verifier la subsistance. Si la situation a change → clôturer ou sous-grainer. |
| **Re-piocher** une issue `candidate-delivered` sans verifier qu'elle est bien livree | Le label est pose par advisory, **pas** une verite — il a ~60 % de faux positifs (mesure #11900 + audits anterieurs). | `gh pr list --state all --search "<issue-id>"` + lire la PR referencee, verifier qu'elle satisfait **toute** l'acceptance du body, **et** qu'aucun commentaire ne la contredit. |
| **Citer le `mergeStateStatus: BLOCKED`** comme « le grain est rouge » | BLOCKED ≠ rouge. BLOCKED = soit en attente review, soit en attente de re-rollup (file CI saturee). Aucun des deux ne dit « la lane doit reparer ». | Croiser BLOCKED avec le contenu de `statusCheckRollup` : si tous PENDING depuis >N h sans failed → narrow structurel, escalader ai-01 ; si un `conclusion: FAIL` existe → verifier si la lane peut le lever (sinon `--ignore-red`). |
| **Sauter la verification FIRSTHAND** parce que le picker a deja filtre | Le picker **remonte** des grains ponderes par delaissement — il ne lit **pas** les bodies, il ne valide **pas** la situation. C'est l'operateur qui porte cette charge. | `gh issue view N --json title,body,comments` (10 s) **avant** de claimer. Si le body dit « attente X » → verifier que X est toujours en attente. |

## Detection systematique — un test par cycle

A chaque cycle `/continue` ou `/coordinate`, **avant de conclure quoi que ce soit** :

```bash
# 1. Verifier qu'un top pick du picker n'est pas un delivered fantome
gh issue view <N> --json title,body,comments --jq '.comments[-1] | {body: .body[0:200], createdAt: .createdAt}'
git log --all --oneline -- <chemin du body> 2>&1 | head -5

# 2. Verifier qu'une PR d'une autre lane n'est pas un OPEN BLOCKED structurel
gh pr list --state open --search "<issue-id>" --json number,state,mergeStateStatus,statusCheckRollup --jq '.[] | "\(.number) \(.state) \(.mergeStateStatus)"'

# 3. Confirmer que le narrow est reel, pas une illusion de picker
gh issue list --limit 200 --state open --json number,title | jq 'length'
```

Si l'etape 3 retourne 0 alors que le picker a rendu des candidats → **le picker lit un cache ou un filtre etrique**, escalader ai-01.
Si l'etape 1 montre un commentaire recent qui resout la situation → case 2/3/4, pas case 1.

## Origine et lecons ancrees

Issue **#11900** — pools narrow structurels documentes par ai-01 c.1331p477 et suivants (mesures 2/2 delaisse body faux). Reproduit par la lane `myia-po-2023:CoursIA-2` pendant 9 cycles consecutifs (c.503 → c.522) avant la consignation ; la cause directe etait l'absence de **regle explicite** imposant la verification FIRSTHAND a chaque grain picker.

Lecon durable : **un picker pondere n'est pas un picker qui sait lire**. La verification de l'operateur reste le remede ; la regle 5 de `verify-before-claiming.md` la rend explicite et reproductible, cette page detaille son application.

## Liens

- [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md) — regle 5 (auto-chargee)
- [proactive-coordination.md](../../.claude/rules/proactive-coordination.md) R5 — picker systematique + `candidate-delivered`
- [coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) R5 — coordinateur **doit** grounder firsthand
- [audit-reassessment.md](../../.claude/rules/audit-reassessment.md) — pattern de re-assessment 4 etapes
