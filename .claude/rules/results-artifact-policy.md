---
paths: "scripts/results/**"
---

# Artefacts de resultats — barre de poids et convention hors-depot

**Source** : issue #15890 (2026-09-13) — `scripts/results/m16_har_asymmetric_debiased_7asset.json` entre sur main a 7 800 634 o, 40x le plus gros artefact precedent du repertoire (193 333 o), ~37x les quatre suivants reunis. Depot public forke par ~95 projets etudiants qui clonent l'historique entier : le poids des resultats ne doit pas depasser le poids du cours.

## Regle HARD 1 — barre : 512 000 octets par artefact NOUVEAU dans `scripts/results/`

Tout **nouveau** fichier sous `scripts/results/` de plus de **512 000 octets** est refuse par la garde `check_results_artifact_weight.py` (organe bloquant d'`always-on-guards.yml`). Le bar est **ancre**, pas rond : 2,6x le plus gros artefact legitime de main au moment de la politique. Le changer exige de re-ancrer publiquement (mesure fresh du plus gros legitime), pas d'editer le litteral.

La falsifiabilite d'un verdict ML (biais signes, p-values Diebold-Mariano par configuration, preuves de folds) tient en quelques milliers de lignes. Ce sont les series de previsions/cibles point par point qui font le volume.

## Regle HARD 2 — au-dela de la barre : agrege commite, series completes hors depot

Au-dela de la barre, l'artefact commite porte les champs qui portent la falsifiabilite (verdicts, metriques par configuration, tailles d'echantillons, chemins de folds). Les series completes vont **hors depot** (GDrive, comme la bibliotheque et les pipelines de notation), et le body de la PR **cite le chemin** des series completes. Un tiers doit pouvoir re-jouer le verdict depuis l'agrege ; personne ne doit cloner 7 Mo de JSON pour lire un verdict.

## Regle 3 — les artefacts deja entres restent (grandfathering, aucune reecriture d'historique)

Les artefacts au-dela de la barre deja presents sur main **restent**. Aucune reecriture d'historique, aucune migration forcee. Une PR qui **modifie** un artefact grandfathered declenche une advisory visible (::warning), jamais un bloc — la sortie de l'etat grandfathered se decide separemment.

## Enforcement

- Organe bloquant : `scripts/ci/check_results_artifact_weight.py` (step "Results artifact weight" d'`always-on-guards.yml`). Verdict `over_bar` sur un fichier AJOUTANT du volume au-dela du bar = exit 1. Verdict `unknown` (pas de merge-base, panne git) = exit 0 + warning — jamais de rouge fabrique sur l'infrastructure (#14849).
- Tests : `scripts/tests/test_check_results_artifact_weight.py` (7 tests, dont l'ancrage du bar et le fail-open sur base inconnue).

## Voir aussi

- [catalog-pr-hygiene.md](catalog-pr-hygiene.md) — les artefacts generes appartiennent a l'automatisation (meme principe de propriete)
- CLAUDE.md section B — preuves verifiables : l'agrege commite EST la preuve, la series-complete hors depot en est l'annexe
