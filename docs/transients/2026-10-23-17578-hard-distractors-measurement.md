# 17578 — Mesure deux-taux du contrôle aller-retour (distracteurs difficiles)

**Date** : 2026-10-23 · **Lane** : `myia-po-2024:CoursIA` · **Grain** : `DEEP/research-code`
**Référence** : point 2 de la revue amont du 2026-10-21 ([c.6327388489](https://github.com/jsboige/CoursIA/issues/17578#issuecomment-6327388489)) — PR #22220, claim c.6369139377.

## Question

La revue amont a établi (DÉRIVÉ) que `pick_distractors` à 5 distracteurs aléatoires parmi ~1 400 sophismes / ~220 vertus attrape un nœud difficile (frère, homonyme) avec ~2,8 % de chances par paire : le taux d'aller-retour de 86,8 % mesuré jusque-là dit « plus proche que 5 pris au hasard », pas la discrimination fine de la taxonomie. Cette mesure confronte les **mêmes textes** à deux contrôles : l'aléatoire **propre** (0 nœud difficile, exclus du tirage) et le **difficile** (pairs tirés d'abord).

## Paramètres

- `--split val --limit 40 --votes 3 --hard-distractors --seed 7` (échantillon stratifié round-robin par famille)
- Modèle `qwen3.6-35b-a3b` sur le hub vLLM (`192.168.0.47:5002`), température 0 pour les votes, 0,8 pour la génération
- `build_hard_peers` sur les deux taxonomies vendorées : 1 629 nœuds, médiane 5 pairs (max 16), 0 nœud sans pair, construction 0,1 s
- Durée : 481,7 s (280 complétions : 40 générations + 2×40×3 questions) ; 0 texte vide, 0 sous plancher, 0 recouvrement d'exemple
- Corpus et rapport du run : hors dépôt (scratchpad de session), seuls les agrégats ci-dessous sont durable.

## Résultats

| Contrôle | Taux | IC 95 % (binomial) |
|---|---:|---|
| Aléatoire propre (0 nœud difficile) | **87,5 %** (35/40) | [73,2 % ; 95,8 %] |
| Difficile (frères/parent/enfants/homonymes d'abord) | **47,5 %** (19/40) | [31,5 % ; 63,9 %] |

Concordance par paire : **18** réussissent les deux contrôles, **17** réussissent l'aléatoire seul, **1** le difficile seul, **4** échouent aux deux. Le déséquilibre discordant (17 contre 1) rend la chute significative malgré n = 40 (McNemar exact, p ≈ 1,4 × 10⁻⁴).

Le taux aléatoire propre (87,5 %) recouvre la baseline de 86,8 % de la revue (280 paires, tirage aléatoire non exclu) : exclure les rares nœuds difficiles du tirage aléatoire ne change pas le niveau — c'est la présence de pairs difficiles qui fait tout l'écart.

## Lecture

- Le 86,8 % historique et le 87,5 % propre mesurent la même chose : le texte est plus proche de son nœud que de 5 pris au hasard.
- Face aux pairs difficiles, le maître ne reconnaît son propre texte qu'une fois sur deux. La discrimination fine demandée par la taxonomie (un enfant variation subtile de son parent, un frère du même argument) **n'est pas acquise** au niveau de granularité visé — c'est le plafond que la revue pronostiquait et que l'ancien contrôle ne pouvait pas voir.
- Per-family (top familles, n = 3 chacune) : l'écart aléatoire→difficile est systématique (ex. `Honnêteté intellectuelle` 3→1, `Erreur de raisonnement` 3→1, `Inférence maîtrisée` 2→0) — aucune famille ne l'absorbe.

## Ce que cette mesure n'établit pas

- n = 40 en un seul seed de génération : la grandeur de l'écart (40 points) est robuste au seuil de signification ci-dessus, mais le taux difficile exact (47,5 %) mérite un run plus large (280 paires, comme la baseline) avant d'être cité comme référence.
- Le verdict difficile dépend des définitions tronquées à 140 caractères dans la question de vote : une partie de l'échec peut venir de la troncature, pas de la génération. La question difficile utilise exactement le même format que l'aléatoire — l'écart mesure donc bien l'effet des pairs, pas un artefact de format.
- Le flip du défaut (durcir le contrôle pour tout le corpus) est un arbitrage coordinateur : cette mesure fournit l'organe et les nombres, pas la décision.

## Reproduire

```bash
export VLLM_API_KEY_MEDIUM=<cle du hub>   # .secrets/master.env, VLLM_API_KEY
python -m fallacy_detection.generate_teacher_corpus --out <dossier> \
    --split val --limit 40 --votes 3 --hard-distractors --seed 7
```
