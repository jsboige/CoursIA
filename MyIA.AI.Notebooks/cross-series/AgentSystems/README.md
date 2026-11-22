# AgentSystems — systèmes d'agents composables

**Projet cross-séries.** La boucle d'un agent — *percevoir → décider → agir* — est
une **méthode d'orchestration** qui mobilise à la fois la perception (GenAI/ML),
le raisonnement symbolique (une spine composable, la valeur d'information comme
critère de décision), la recherche (la boucle de décision) et la compression (le
rejeu d'une politique amortie). Ce projet la démontre sur une ou plusieurs
carnets, chacun isolant une capacité de la boucle.

## Carnets

| Carnet | Capacité isolée | Séries mobilisées |
|--------|-----------------|-------------------|
| [AgentSystems-01 — Perception → Action](AgentSystems-01-Perception-Vers-Action-Python.ipynb) | La **spine composable** : la boucle *percevoir → représenter → inférer → décider → vérifier → exécuter → observer* comme *squelette réutilisable*, l'inférence (déterministe **ou** LLM) comme *point de composition*. | Search, SymbolicAI, Compression, GenAI |
| [AgentSystems-02 — Perception active et valeur d'information](AgentSystems-02-Perception-Active-Valeur-Information-Python.ipynb) · [jumeau C#](AgentSystems-02-Perception-Active-Valeur-Information-CSharp.ipynb) | La **perception active** : ne lire que les capteurs dont la **valeur d'information** (EVOI) justifie le coût, avec sondage Monte-Carlo du postérieur et politique d'arrêt. | GameTheory, GenAI |

Le deuxième angle du projet — la **perception active** (ne lire que les capteurs
dont la **valeur d'information** justifie le coût) — fait l'objet d'un carnet
compagnon.

## La thèse transversale

Un **agent composable** n'est ni un LLM ni un classifieur : c'est un **squelette**
qu'on assemble avec des *pièces* interchangeables derrière des interfaces. La même
boucle tourne avec un cerveau déterministe ou un LLM ; la vérification et la
safety bound ne changent pas, seul le **coût d'inférence** change. Et comme tout
actif amorti (cf. [`Compression-07b`](../../InformationCalcul/Compression/Compression-07b-Triage-LLM-Semantic-Kernel-Python.ipynb)),
la politique découverte une fois se **rejoue à coût nul**.

> **Position du projet.** C'est une **méthode transversale**, pas une application
> de domaine : elle ne résout pas un problème métier, elle montre comment
> **combiner** des concepts déjà vus dans plusieurs séries pour construire un
> système d'agents. C'est ce qui le distingue des [case studies](../../CaseStudies/)
> (domaine-ancrées) et des projets [`matching-cv`](../matching-cv/) /
> [`socle-metadata-driven`](../socle-metadata-driven/) de ce répertoire.
