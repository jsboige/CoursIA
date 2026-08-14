# Valeurs quantitatives en prose de notebook — détail de la règle C.5

Détail déporté de [`.claude/rules/notebook-conventions.md`](../../.claude/rules/notebook-conventions.md) §C.5, qui garde la règle et la table de classification. Ce fichier porte les arbitrages et les cas-limites — utiles quand on tranche une PR, inutiles à charger à chaque session.

Source : mandat user **#9377** — « les données quantitatives doivent être tenues par le CI, pas dans la prose manuelle ». Appliqué aux README (comptes de notebooks #9377, tailles #9425, comptes de cellules #9432), il vaut **à l'intérieur des notebooks**, où la même pathologie rouvre un ticket #8052 à chaque re-exécution.

## La frontière est la machine-dépendance, pas « nombre + unité »

Arbitrage **#9434** (2026-08-06). Une valeur en `ms`/`sec`/`min` n'est pas toujours un runtime à retirer : la classe **donnée en unité de temps** regroupe les valeurs qui portent une unité de temps mais restent **déterministes** — moyenne statistique de données (postérieur bayésien, moyenne de trajets Infer-101 `15.33 min`), longueur d'un contenu (durée d'un clip `30 sec`), estimation pédagogique humaine (`Durée : ~2 h`). Elles ne dérivent ni avec la machine ni au re-run ; les retirer détruit du contenu pédagogique réel.

Critère discriminateur : *« cette valeur changerait-elle si je ré-exécutais le notebook sur une autre machine ? »* — non pour un data-unit, oui pour un runtime.

C'est cette frontière (et non la présence d'une unité de temps) qu'instrumentent [`scan_quant_classify.py`](../../scripts/notebook_tools/scan_quant_classify.py) + son [golden set](../../scripts/tests/golden_quantitative_claims.json).

## L'arbitrage §D.5 ↔ #9377 : retirer gagne

Les deux règles se croisent sur toute PR « alignement doc-honesty » et semblent se contredire :

- **§D.5** ([pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md)) gouverne le **ré-épinglage** : si l'on remplace un nombre volatil par un autre nombre, celui-ci doit venir d'une **re-exécution fraîche**, jamais d'un alignement à la main sur une vieille sortie.
- **#9377** dit de **préférer retirer** l'épingle.

**Quand les deux s'appliquent, retirer gagne** — parce que retirer sort définitivement la valeur du domaine de §D.5. Une prose qui ne cite plus de nombre volatil ne peut plus dériver, donc ne peut plus déclencher un #8052 au prochain passage kernel. C'est la seule des deux issues qui **ferme** la boucle au lieu de la déplacer d'un cran.

## Le coût relatif se garde, le coût absolu se retire

C'est la classe la plus fournie en pratique (temps de calcul comparant deux approches), et « retirer » y perd parfois du contenu réel : quand le propos **est** que telle approche coûte plus cher que telle autre, effacer les chiffres efface la leçon.

La sortie est de passer de l'absolu au **rapport**. `0.2 s contre 0.1 s` devient `~2x le coût du filtrage` : les deux mesures viennent de la même exécution sur la même machine, donc leur rapport est **invariant** là où chacune dérive. Le lecteur garde l'information qui compte (l'ordre de grandeur relatif) et la prose sort du domaine de §D.5.

Deux réserves : le rapport n'est valable que si les deux termes sont **mesurés dans la même cellule** (comparer un timing d'aujourd'hui à un timing d'une ancienne exécution ne vaut rien), et il ne remplace pas une complexité — `$O(n^2)$` reste la bonne façon de dire un coût asymptotique.

## Reformuler ne doit pas maquiller la contradiction

Retirer la valeur ne veut pas dire écrire une affirmation théorique qui *a l'air* fausse à côté d'un output qui la contredit. Si la sortie committée affiche `-0.033` et que la prose devient « converge vers `-1/18` », le lecteur voit toujours l'écart.

La prose honnête dit ce qui est réellement vrai : la valeur théorique **et** le fait que l'instance affichée s'en écarte, avec la raison (« une exécution unique de CFR fluctue ; la convergence est en espérance sur les itérations »). Le contenu pédagogique, c'est la loi **plus** l'écart, pas la loi seule.

## Critère de relecture

Une seule question sur la prose modifiée : **cite-t-elle encore un nombre qui rebougera au prochain passage kernel ?** Si oui, la PR ré-épingle et §D.5 s'applique dans toute sa rigueur (re-exécution fraîche exigée). Si non, la boucle est fermée.

## Diagnostic de dérive (C.4) — les trois verdicts

Rappel du contexte dans lequel C.5 est le plus sollicitée. Une contradiction prose↔output signale que le notebook a dérivé (env défectueux, claim antérieure fabriquée, moteur qui change, stochasticité non-seedée). Verdict obligatoire dans le body de PR :

| Verdict | Critère | Action |
|---------|---------|--------|
| `CAUSE_FIXED` | Cause racine corrigée (env réparé règle F, claim antérieure revertée, seed ajouté) | Merge OK |
| `CAUSE_DOCUMENTED_ONLY` | Cause identifiée, non traitée (ré-alignement cosmétique = « jambe de bois repeinte ») | Issue fille ouverte + `See #N` |
| `CAUSE_INTRINSIC` | Cause structurelle non corrigeable (moteur upstream cassé sans alternative) | Bandeau honnête + issue engine-fix |

Ré-aligner sans diagnostic = consacrer la dégénérescence : le notebook re-dérive au cycle suivant. Vague de référence SW-13 : #7751 → #7872 → #7944 → #8343, quatre PRs pour colmater des claims fabriquées en série.

See #9377, #8052, #9434, #8364.
