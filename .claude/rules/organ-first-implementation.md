# Organ-first implementation — nommer l'organe natif avant de réimplémenter

S'applique à toute PR qui ajoute ou modifie une implémentation de sémantique dans une série de notebooks, quand une **autre série du dépôt possède déjà l'organe** correspondant (librairie, lake, module, service). Source : proposition #13564 (sign-off user requis à l'ajout — voir l'issue pour le constat et les trois occurrences fondatrices).

## Règle

**Avant d'implémenter une opération qu'une autre série pourrait posséder, répondre par écrit dans le body de la PR aux 5 questions :**

1. Quelle série possède déjà la sémantique de cette opération ?
2. Peut-on invoquer son module / librairie / service réel ?
3. Sinon, que faut-il exporter ou refactorer **dans la série source** pour la rendre consommable ?
4. Quel témoin négatif l'organe natif fournit-il ?
5. Quelle autre série assure la vérification indépendante du résultat ?

Une réimplémentation locale sans ces cinq réponses = `CHANGES_REQUESTED` (reviewers humains et bots).

C'est le geste de la checklist 6 axes d'`INTRINSIC` ([sota-not-workaround.md](sota-not-workaround.md)) transposé : on n'interdit pas la réimplémentation, on interdit de la faire **sans avoir nommé l'organe qu'on contourne**.

## Périmètre

Toute série, pas seulement `IIT/` — le défaut existe partout (« un notebook Search qui refait du SMT plutôt que d'appeler Z3 »). La forme visée, validée par #13568/#13569 : **la série demandeuse pose le problème, l'organe natif calcule**, et l'écart entre organes est rapporté plutôt que moyenné.

## Porte de sortie (faux positif assumé)

Une **copie pédagogique déclarée** (montrer comment marche Dung en 30 lignes) est légitime : elle se déclare par **une phrase dans le body** (« copie pédagogique déclarée, motif : … ») et satisfait alors les questions 1-2 par construction. Jamais de skip silencieux ; une copie déclarée qui **dure** (plusieurs notebooks consommateurs) devient une extraction à demander à la série source (question 3) — cf. le cas Greffe2/STRIPS, contrôle positif de l'audit 2026-09-10.

## Organe

La règle ne vit que par son détecteur ([[rule-needs-an-organ-not-more-vigilance]]) : `scripts/audit/detect_organ_duplication.py` (spec, contrôles et acceptance : **#16776**) — repère dans un diff les symboles qui collisionnent avec l'API publique des organes de séries (`grounded_extension`, `sparql_update`, `plan`, `posterior`, …), avec contrôle positif sur le cas Greffe2 et exemption des copies déclarées. Jusqu'à son merge, les reviewers appliquent les 5 questions à la main.

## Voir aussi

- #13564 — constat, occurrences, arbitrages, sign-off
- #16776 — l'organe (détecteur) : spec, contrôles, acceptance
- [sota-not-workaround.md](sota-not-workaround.md) — checklist 6 axes `INTRINSIC`, dont ce geste est le transposé
