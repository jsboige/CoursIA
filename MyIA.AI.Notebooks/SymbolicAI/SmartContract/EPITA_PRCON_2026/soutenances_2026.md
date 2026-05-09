# EPITA PrCon 2026 — Soutenances Logistics

**Course**: SCIA Programmation par Contraintes
**Repo**: `jsboigeEpita/2026-Epita-Programmation-par-Contraintes`
**Evaluation**: collegiale (pairs + enseignants), 4 criteres x 0-10, somme/2 = /20

---

## Planning

### Session 1 — Lundi 18 mai 2026

| Heure | Groupe | Sujet | Membres | Size Bonus |
|-------|--------|-------|---------|------------|
| 14h00 | **E4** | Allocation de validateurs PoS (Bin Packing) | Evariste BALVAY | +3 (solo) |
| 15h00 | **H1** | Composition Musicale Assistee par Contraintes | Louis Parmentier, Marianne Proux, Ethan Girard | 0 (trio) |

**Salle**: _a confirmer_
**Jury**: _a confirmer_

### Session 2 — Vendredi 22 mai 2026

| Heure | Groupe | Sujet | Membres | Size Bonus |
|-------|--------|-------|---------|------------|
| 14h00 | **H2** | Procedural Generation (WFC + CP-SAT) | Martin Couturier | +3 (solo) |
| 15h00 | **J1** | Allocation multicritere de candidats | Alexandre Bodin, Mark Delaloy (+?) | 0 (duo/trio) |
| 16h00 | **I2** | Angles/Geometrie (CSP notebooks) | ANGLES, DEGUEST, HIEGEL | 0 (trio) |

**Salle**: _a confirmer_
**Jury**: _a confirmer_

---

## Grille d'evaluation (rappel)

| Dimension | Poids | Indicateurs |
|-----------|-------|-------------|
| **Presentation** | 0-10 | Clarte, structure, demonstration live, reponses aux questions |
| **Qualite theorique** | 0-10 | Formulation CP, modele (variables/constraints/objectif), baselines, metriques |
| **Qualite technique** | 0-10 | Code CP-SAT, notebook, solver usage, volume et qualite du code |
| **Organisation** | 0-10 | Commits, contributeurs, PRs, README, fichier completeness |

**Note finale** = (somme 4 dimensions + size_bonus) / 2, plafonnee a 20/20

---

## Points d'attention par groupe (pre-soutenance)

### E4 — ZERO code (solo +3)

README excellent (formulation complete, baselines, metriques) mais **aucun fichier de code** dans le depot. Verifier pendant la soutenance :
- Le code existe-t-il en local non pousse ?
- Y a-t-il un blocage technique (installation OR-Tools, environnement) ?
- Le README decrit-il un plan realiste ou une surpromesse ?

### H1 — ZERO code (trio)

Architecture detaillee (core/, constraints/, export/) mais **rien d'implemente**. Verifier :
- Y a-t-il du code sur les machines des etudiants ?
- Le trio a-t-il reparti le travail (chacun un module) ?
- Quel est l'etat d'avancement reel vs le README ?

### H2 — Frontrunner (solo +3)

Seul groupe avec un CP-SAT fonctionnel (WFC + adjacency + connectivity). Verifier :
- Le notebook presente-t-il une analyse comparative (CP-SAT vs WFC pure vs random) ?
- La complexite du modele est-elle comprise (nombre de variables, temps de resolution) ?
- Les extensions (cave tileset, global constraints) sont-elles solides ?

### J1 — CRITICAL: pas de solveur CP

Projet complet (FastAPI, embeddings, UI) mais **aucun solveur de contraintes**. C'est un systeme de scoring ML, pas un probleme de satisfaction de contraintes. Points a verifier :
- L'etudiant comprend-il la difference entre optimisation par scoring et CSP ?
- Y a-t-il une tentative d'integration CP-SAT (meme partielle) ?
- Le sujet "Allocation multicritere" aurait du se preter naturellement a CP-SAT

**Note**: En cas de confirmation de l'absence totale de CP, la dimension "Qualite technique" sera impactee.

### I2 — Scaffolding uniquement (trio)

4 notebooks listes mais contenu potentiellement copie du cours sans contribution originale. Verifier :
- Les notebooks contiennent-ils du code original ou sont-ils des copies ?
- Le trio a-t-il compris les concepts CP (questionner sur propagation, backtrack, arc consistency) ?
- Les demo/slides/resources sont-ils prevus ?

---

## Auto-grade results (epita_prcon_autograde.py)

Generated: 2026-05-09 from repository analysis

| Group | Theory | Tech | Org | Presentation | Size | Min/20 | Max/20 |
|-------|--------|------|-----|--------------|------|--------|--------|
| E4 | 9 | 0 | 2 | PENDING | +3 | 7.0 | 12.0 |
| H1 | 8 | 0 | 2 | PENDING | +0 | 5.0 | 10.0 |
| H2 | 6 | 9 | 5 | PENDING | +3 | 11.5 | 16.5 |
| J1 | 4 | 6 | 5 | PENDING | +0 | 7.5 | 12.5 |
| I2 | 3 | 3 | 2 | PENDING | +0 | 4.0 | 9.0 |

**Note**: These are auto-graded (excl. presentation). Final score requires soutenance evaluation.

---

## Checklist pre-soutenance

- [ ] Confirmer salles pour 18/05 et 22/05
- [ ] Confirmer jurys (pairs + enseignants)
- [ ] Imprimer grilles d'evaluation (4 dimensions x 0-10)
- [ ] Verifier acces au repo GitHub (credentials)
- [ ] Installer OR-Tools sur machine demo si necessaire
- [ ] Preparer questions specifiques par groupe (cf. points d'attention ci-dessus)
