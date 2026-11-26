# Évaluer avant de livrer

**Projet cross-séries.** Ce projet livre un **protocole d'évaluation
reproductible** et son premier carnet transverse : la mesure d'un modèle sur une
référence que le dépôt publie lui-même.

## Carnets

| Carnet | Ce qu'on y apprend | Séries mobilisées |
|---|---|---|
| [`Evaluation-Livraison-01-Protocole-Python.ipynb`](Evaluation-Livraison-01-Protocole-Python.ipynb) | Jouer un protocole d'évaluation complet : route déclarée, référence, juge, seuils, mesures, verdict | GenAI (appel de modèle local), cross-séries (banque de questions) |

## La thèse transversale

Évaluer un système que l'on livre soi-même n'a rien d'un exercice : la
référence existe déjà, la banque de questions est publiée, et le juge peut être
déterministe. Un protocole d'évaluation cesse alors d'être une intention : il
devient un enchaînement vérifiable, dont chaque maillon est nommé avant la
mesure.

Le carnet livré ici joue cet enchaînement sur un cas réel du dépôt :

- **la route** — le modèle local du siège, joint par une adresse déclarée dans
  la première cellule, et une clé lue dans le trousseau local, jamais écrite
  dans le carnet ;
- **la référence** — la banque de questions publiée, lue et jamais modifiée ;
- **le juge** — déterministe, vérifié par auto-tests avant la première question ;
- **les seuils** — écrits avant la mesure, jamais réécrits après ;
- **le verdict** — la comparaison aux seuils, seuil par seuil, avec la liste de
  ceux qui sont franchis et de ceux qui ne le sont pas.

## La branche livrée

Le manifeste [`evaluation-livraison.json`](evaluation-livraison.json) reprend ce
protocole sous la forme des parcours verticaux : une branche, son carnet, sa
référence, son juge, ses seuils et son verdict.

C'est la **première branche** du parcours vertical d'évaluation ; les suivantes
ont vocation à y ajouter le juge probabiliste avec garde-fou anti-bias, qui
n'est pas écrit ici.

## Exécution

Le carnet s'exécute avec le noyau Python du dépôt. Il lit la clé du service
local dans le trousseau du dépôt — jamais dans le carnet — et interroge le
service local :

```bash
python -m papermill MyIA.AI.Notebooks/cross-series/Evaluation-Livraison/Evaluation-Livraison-01-Protocole-Python.ipynb .tmp/evaluation-livraison-exec.ipynb
```

Les sorties committées dans le carnet sont celles d'une exécution réelle sur le
siège : route déclarée, mesure, verdict.
