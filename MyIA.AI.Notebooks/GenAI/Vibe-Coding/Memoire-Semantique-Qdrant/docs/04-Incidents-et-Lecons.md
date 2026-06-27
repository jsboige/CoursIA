# 04 - Incidents et leçons

[← 03 Utilisation](03-Utilisation-MCP-Indexation.md) | [Mémoire Sémantique Qdrant](../README.md)

Ce document est le plus utile de la section, parce qu'il est le plus honnête. Une infrastructure ne s'apprend pas dans son état idéal mais dans ses pannes : ce qui a cassé, pourquoi, et ce qu'on a changé pour que cela ne recommence pas. Chaque incident ci-dessous est réel (les dates sont conservées pour l'authenticité) ; tout identifiant sensible est généralisé.

## 1. La perte de données par dérive de montage

**Ce qui s'est passé (mi-mai 2026).** Le disque virtuel (VHDX) hébergeant les données de production s'est retrouvé **non monté**. Le point de montage Docker s'est alors résolu vers un répertoire **vide** de la distribution Linux par défaut. Qdrant a démarré sur ce magasin vide, sans erreur apparente — et la collection principale a été **recréée à vide**. La mémoire conversationnelle, patiemment accumulée, n'était plus servie.

**L'aggravation.** Au moment précis de l'incident, **il n'existait aucune sauvegarde**. Un script de sauvegarde *existait* pourtant sur le disque — mais il n'avait **jamais été planifié** : ses derniers logs dataient de plusieurs mois. Le filet de sécurité était à moitié construit (voir section 3).

**La récupération.** Une copie périmée du système de fichiers a permis, via `rsync`, de récupérer une partie des points (de l'ordre de quelques centaines de milliers). Mais une partie de l'historique a été définitivement perdue.

**Les leçons.**

- **Une sauvegarde n'existe que si elle s'est exécutée récemment.** La présence d'un script ne prouve rien ; seule la présence de **sauvegardes datées et vérifiées** compte.
- **Un service en apparence sain peut corrompre silencieusement.** Démarrer à vide sans erreur est pire qu'un crash : la panne est invisible jusqu'à ce qu'on cherche une donnée disparue.
- C'est cet incident qui a fait naître la **sentinelle anti-split-brain** (document 02) : « on ne réindexe pas dans le vide ».

## 2. La dérive de montage, mécanique et remédiation

L'incident de la section 1 n'était pas un accident isolé : la dérive de montage s'est reproduite. En la diagnostiquant à répétition, on a appris sa mécanique exacte.

**Pourquoi elle survient.** Le montage du VHDX dans WSL2 peut être perdu **en cours de fonctionnement** (pas seulement au démarrage), par exemple si une opération WSL retire le disque. Docker continue alors de servir l'ancien point de montage, désormais cassé.

**Les pièges du diagnostic.**

- **Les lettres de périphérique sont instables.** Le même disque peut apparaître `/dev/sde`, puis `/dev/sdg`, puis `/dev/sdf` à travers les redémarrages. Résoudre par la lettre conduit tôt ou tard à monter le mauvais disque. **Toujours résoudre par le *label*** (`qdrant-e`).
- **Compter les collections ne suffit pas à valider un montage.** Le répertoire vide « leftover » peut contenir des restes trompeurs et passer un test naïf « nombre de collections > 0 ». La vérification correcte porte sur le **label du périphérique** réellement monté.
- **Un simple `restart` ne suffit pas.** Seul un **`compose down` puis `up`** (recréation du conteneur) force une **nouvelle résolution** des points de montage. Un `restart` réutilise le montage figé au moment de la création.
- **L'espace de noms compte.** Docker résout les montages depuis l'espace de noms du processus d'init de la distribution. Monter depuis une session WSL fraîche ne suffit pas ; il faut entrer dans le bon espace de noms.

**La remédiation, maintenant automatisée.** Une tâche planifiée (watchdog) vérifie le label toutes les deux minutes et, en cas de dérive, remonte le disque puis recrée le conteneur. Détail défensif appris à la dure : cette remédiation a un **auto-délai** (*self-timeout*), car un appel WSL ou Docker bloqué pouvait autrefois figer toute la chaîne pendant des heures.

**Le verdict positif.** La sentinelle (document 02) a été **prouvée en production** lors d'une vraie dérive : le conteneur a refusé de démarrer, panne franche et visible, **zéro perte de données**. Le garde-fou a fonctionné exactement comme prévu.

## 3. La sauvegarde à moitié câblée : « consolider n'est pas archiver »

**Le piège.** Un script de sauvegarde consolidé existait, fonctionnel, testé… mais sans **tâche planifiée** pour le déclencher. Sur le disque, tout avait l'air en ordre. Dans les faits, plus aucune sauvegarde ne tournait depuis des mois. Le symptôme révélateur : des logs de sauvegarde abondants jusqu'à une date, puis **plus rien**.

**La leçon générale.** Pour toute opération de sûreté, vérifier **deux choses indépendantes** :

1. le **script** existe et fonctionne ;
2. un **ordonnanceur** le déclenche réellement (et ses exécutions récentes ont réussi).

Un script sans planification est un filet de sécurité à moitié construit — il donne l'illusion de la protection sans la fournir.

**Ce qui a été durci ensuite.** La sauvegarde canonique a reçu deux garde-fous :

- **Garde anti-poison** : si la collection contient moins d'un seuil de points (signe d'un état vide ou corrompu), la sauvegarde **avorte** et **ne fait pas tourner la rotation** — pour ne pas écraser de bonnes sauvegardes avec une mauvaise.
- **Garde de taille** : si la nouvelle sauvegarde est anormalement plus petite que la plus grosse existante, la rétention est **suspendue** par précaution.

Les sauvegardes sont écrites en **deux endroits** (un stockage hors-site et un disque local), avec une rétention quotidienne et hebdomadaire **par destination**. La restauration, elle, est **sûre par défaut** : elle téléverse dans une collection nommée sans jamais toucher aux volumes ; l'option destructive (recréer la collection) est explicite et séparée.

## 4. La résurrection de la VM WSL

**Ce qui s'est passé (début juin 2026).** Lors d'une opération de maintenance, l'intégration Docker/WSL s'est cassée. Les remèdes habituels (`wsl --shutdown`, quitter/relancer Docker) **échouaient tous** — la machine virtuelle WSL2 refusait de mourir.

**La cause.** Le **watchdog de montage** (section 2), qui s'exécute toutes les deux minutes, **ressuscitait la VM** à chaque tentative d'arrêt : à peine arrêtée, il la relançait pour vérifier le montage. Course infernale entre l'opérateur qui éteint et le watchdog qui rallume.

**La leçon, devenue procédure.**

- **Désactiver le watchdog *d'abord***, avant toute opération sur WSL.
- **Quitter complètement Docker Desktop avant** tout `wsl --shutdown` / `--mount` / `--unmount`, et le relancer après.
- **Vérifier que la VM est réellement éteinte** (aucun processus `vmmem`/`vmmemWSL`) avant de relancer.
- Puis seulement : remonter le disque, et **ré-armer le watchdog**.

Un mécanisme d'auto-réparation est précieux, mais il faut savoir le **mettre en pause** pendant qu'on opère manuellement la ressource qu'il surveille — sinon il combat l'opérateur.

## 5. Une opération réussie, par contraste : la migration TurboQuant

Toutes les interventions ne sont pas des désastres. La migration de la collection principale vers la quantization **TurboQuant 4 bits** (document 02) illustre la **bonne** manière de toucher à une ressource précieuse :

1. **Sauvegarde vérifiée d'abord.** Un instantané a été pris **avant** de toucher au moteur, et validé octet par octet sur les deux destinations.
2. **Montée de moteur explicite.** Le moteur est passé à une version épinglée (TurboQuant exige le moteur ≥ 1.18.0), via recréation propre du conteneur. La sentinelle a confirmé le bon montage, l'intégralité des points était intacte.
3. **Test sur cobaye.** La syntaxe du `PATCH` a été dé-risquée sur une **collection jetable** avant de toucher la vraie.
4. **Migration et mesure.** Le `PATCH` appliqué, l'optimiseur a re-quantizé les segments en arrière-plan. Un **banc de rappel** a confirmé `recall@10 = 1.0` : zéro perte de qualité.

Le contraste avec les sections 1 à 4 est la leçon : **sauvegarde préalable + test sur cobaye + mesure de validation** transforment une opération risquée en routine sereine.

## 6. La montée de version, explicite et réversible

La montée d'une version mineure du moteur (un correctif de sécurité, sans changement cassant ni migration) a suivi le même esprit : épingler la nouvelle version précise plutôt qu'un tag mouvant, recréer proprement, valider en direct (nombre de collections, points de la collection principale, quantization intacte, sentinelle OK). Parce que la version est épinglée, la manœuvre est **réversible** : revenir en arrière, c'est ré-épingler l'ancienne version. C'est tout l'intérêt de bannir `:latest` en production.

## 7. La compaction du disque virtuel (dette différée, assumée)

Tous les chantiers ne sont pas urgents. Un VHDX **ne se réduit pas tout seul** quand on supprime des données : le fichier conserve sa taille maximale historique. Sur notre hôte, le disque virtuel occupait plusieurs centaines de Go de plus que les données réelles. La compaction (hors-ligne) récupérerait cet espace — mais elle exige d'arrêter proprement Qdrant et de manipuler WSL.

La décision a été de **différer** cette opération à une fenêtre calme et surveillée, plutôt que de la lancer sous pression. C'est aussi une leçon d'ops : **une dette connue, bornée et planifiée n'est pas une urgence** ; la traiter au mauvais moment crée plus de risque qu'elle n'en résout (voir section 4 sur les opérations WSL).

## 8. Méta-leçons

En filigrane de tous ces incidents, quelques principes transversaux :

- **L'échec visible vaut mieux que la corruption silencieuse.** Tous les garde-fous (sentinelle, gardes de sauvegarde, healthcheck) sont construits pour **s'arrêter bruyamment** plutôt que continuer dans le doute.
- **Vérifier deux faits indépendants.** Un script *et* sa planification. Un montage *et* son label. Une sauvegarde *et* sa date.
- **Sauvegarder avant, mesurer après.** Aucune opération sur une ressource irremplaçable sans instantané préalable vérifié et validation postérieure.
- **Connaître l'interaction entre couches.** Beaucoup de pannes venaient de l'interface Windows / WSL2 / Docker, pas de Qdrant lui-même. Un automatisme (watchdog) peut entrer en conflit avec une opération manuelle.
- **L'honnêteté est un outil.** Documenter les pertes réelles, pas seulement les succès, est ce qui a permis de construire les garde-fous. Ce document en est l'application.

---

[← Retour au README de la section](../README.md) · [↑ Vibe-Coding](../../README.md)
