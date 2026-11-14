# Série Oversight — mesurer la surveillance d'un agent

Cette série produit des **mesures** autour d'une question : que peut-on savoir,
chiffrer, et anticiper de la capacité d'un système à superviser un agent ?
Les carnets s'appuient sur le jeu de Nim modifié et les scénarios de R12
(Engels et al., NeurIPS 2025, arXiv:2504.18530) tels qu'ils y sont définis ;
chaque carnet porte sa propre méthodologie et ses propres sorties.

## Ordre de lecture

| Étape | Carnet | Rôle |
|---|---|---|
| 1 | [Oversight-Scaling-Laws-Nim](Oversight-Scaling-Laws-Nim.ipynb) | Le carnet de tête : mesure empirique sur le jeu de Nim modifié, stratégie résolue par force brute, win rates contre un joueur parfait, fit des lois d'échelle. |
| 2 | [Oversight-Scaling-Laws-Analytics](Oversight-Scaling-Laws-Analytics.ipynb) | Étend le premier carnet en appliquant les formules analytiques de R12 sur un balayage paramétrique exhaustif. |
| 3 | [Oversight-Scaling-Laws-Statistics](Oversight-Scaling-Laws-Statistics.ipynb) | Le module statistique consolidé : validation de l'inversion Elo sur données contrôlées et consolidation des carnets antérieurs du parcours. |
| 4 | [Oversight-Scaling-Laws-Wargames](Oversight-Scaling-Laws-Wargames.ipynb) | Le scénario Wargames de R12, section 5, en simulation stochastique pure, sans LLM externe. |
| 5 | [Backdoor-Code-From-Scratch](Backdoor-Code-From-Scratch.ipynb) | L'autre face de la série : un pipeline de backdoor construit et mesuré de bout en bout. |
| 6 | [Backdoor-Dormant-Neurons](Backdoor-Dormant-Neurons.ipynb) | La porte dérobée par les poids : la réprogrammation d'un neurone dormant, mesurée de bout en bout (ASR, fuite, dérive bénigne). |

Chaque carnet porte, en fin de corps, sa ligne de navigation vers le précédent,
cet index et le suivant.

## Fichiers annexes

Le dossier contient les caches d'exécution (`*.json`, `llm_cache/`) et les
générateurs (`oversight_*_cachegen.py`) produits par les carnets : ils ne font
pas partie de la lecture.
