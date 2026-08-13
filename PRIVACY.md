# Confidentialité — CoursIA

> Posture PII **du dépôt public** `jsboige/CoursIA`. Ce document décrit ce qui n'y figure
> jamais, où vivent les données sensibles, et ce qui est publiquement exposé — pour qu'un
> lecteur externe n'ait pas à le deviner.
>
> Il complète la notice RGPD du moteur de notation, [`GradeBookApp/PRIVACY.md`](GradeBookApp/PRIVACY.md),
> qui détaille le traitement des données étudiantes par l'application elle-même.

## 1. Ce qui n'est jamais dans ce dépôt

Le dépôt est **public** et ne contient, par construction, **aucune donnée étudiante** :

- **Copies et rendus** : jamais de travaux, de fichiers soumis, de notebooks d'étudiant.
- **Notes et appréciations** : aucun relevé, aucune moyenne, aucun commentaire d'évaluation.
- **Identités** : aucun nom, prénom, adresse e-mail, numéro étudiant, identifiant.
- **Captures et artifacts nominatifs** : aucune capture d'écran, aucun log, aucune sortie
  nommant une personne.

Cette règle est vérifiée automatiquement : des gates CI refusent les commits introduisant
des données étudiantes (`pii_no_output`) et le dépôt est audité pour les secrets en clair
(`gitleaks`). L'historique public reste consultable.

## 2. Où vivent les données sensibles

Les pipelines de notation et les **données par cohorte** vivent sur un **stockage privé,
hors dépôt**, accessible aux seuls enseignants concernés. Le chemin est résolu localement
par le moteur via la variable `COURSIA_ROOT` (voir
[`GradeBookApp/configs/README.md`](GradeBookApp/configs/README.md)). **Ce fichier ne cite
ni le chemin exact, ni les noms de cohortes** : la posture se décrit sans exposer la
topologie de stockage.

## 3. Ce qui est public, et pourquoi

Est publiquement exposé **uniquement le moteur générique** de notation
([`GradeBookApp/`](GradeBookApp/)) : configuration, barèmes-types, code de calcul. Il est
vide de données — utile pédagogiquement (reproductibilité, transparence de la méthode),
sans risque pour les personnes. La notice de traitement de ce moteur est documentée
séparément dans [`GradeBookApp/PRIVACY.md`](GradeBookApp/PRIVACY.md).

Tout le reste du dépôt (notebooks, scripts, documentation) est du matériel **pédagogique
sans données personnelles**.

## 4. Finalité et durée

- **Finalité unique** : évaluation et pilotage pédagogique des cours concernés. Aucune
  finalité commerciale, de profilage ou de publicité.
- **Conservation** : limitée au cycle de la promotion concernée. Les données privées hors
  dépôt ne sont pas conservées au-delà de leur utilité pédagogique.

## 5. Contact

Pour une demande d'accès, de rectification ou d'effacement relative à des données traitées
dans le cadre d'un cours, contacter l'enseignant responsable du dépôt (le propriétaire du
compte `jsboige` sur GitHub). Le moteur étant exécuté localement par l'enseignant sur ses
propres données, c'est ce dernier qui est responsable du traitement
(cf. [`GradeBookApp/PRIVACY.md`](GradeBookApp/PRIVACY.md) §2).

---

Ce document décrit des **faits vérifiables** sur la structure du dépôt ; il ne constitue
pas une attestation de conformité à un cadre normatif particulier. La responsabilité du
traitement des données étudiantes revient à l'enseignant qui exécute le moteur, non au
dépôt.
