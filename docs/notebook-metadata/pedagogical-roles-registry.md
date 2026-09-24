# Registre des rôles pédagogiques — `pedagogical_role`

**Issue parente** : [#15080](https://github.com/jsboige/CoursIA/issues/15080) — critère 4 (le compteur d'exercices s'inverse)
**Pattern de** : `scientific-review-registry.md` (c.997, axe 3) — whitelist curée, même mécanique de chargement
**Auteur du registre** : myia-po-2027 / lane `myia-po-2027:CoursIA`
**Date de fondation** : 2026-09-23
**Base SHA** : `d762eb527a14` (origin/main)

---

## 1. Purpose

Aucun champ du catalogue ne dit **à quoi sert le notebook pour un étudiant**. `status: READY` signifie « s'exécute proprement » et se lit à tort « prêt à être confié à un étudiant » : un corrigé entièrement résolu est parfaitement `READY` et parfaitement inutilisable comme sujet ; réciproquement, un énoncé sans support de code peut porter `forensic_category: NO_CODE` et être un vrai sujet ouvert (mesures #15080 §1-§3).

Le rôle pédagogique est un **jugement éditorial** — il n'est pas dérivable du fichier (un `# TODO etudiant` survit dans une solution complète). Il vit donc dans ce registre whitelist curé, lu par `generate_catalog.py` (`_load_pedagogical_roles_registry`), fail-OPEN : une entrée absente ou invalide laisse le champ `""`, elle ne devine jamais.

**Pourquoi un registre et pas une heuristique** : même raison que le registre axe 3 — l'instrument lit la présence d'un marqueur, jamais l'état du travail. Seule une décision de lecture humaine distingue « trois sujets sans endroit pour écrire » de « pas d'exercice du tout », qui rendaient le même couple `(0, false)` à la sortie de `count_exercises.py` avant #15092.

## 2. Format YAML — schéma

```yaml
- notebook_path: <chemin relatif depuis MyIA.AI.Notebooks/>
  role: <open_subject|worked_solution|method_demo>
  justification: <preuve de lecture, mesurée firsthand>
```

### Vocabulaire fermé (3 valeurs)

| Token | Sens (issue #15080 : « a minima ») | Contre-exemple qui le distingue |
|---|---|---|
| `open_subject` | sujet ouvert — l'étudiant a un travail à produire | un énoncé **sans** cellule où écrire reste un sujet ouvert (le défaut est l'absence de support, pas l'absence de sujet) |
| `worked_solution` | corrigé — solution complète, référence à lire | les marqueurs `# TODO` y survivent alors que le corps répond à l'énoncé |
| `method_demo` | démonstration de méthode — grain de cours, pas un exercice | mérite son `0` au compteur d'exercices ; c'est lui qui rend le `0` des autres diagnostiquable |

Une valeur hors vocabulaire est écartée avec avertissement à la génération (jamais silencieusement acceptée).

## 3. Entrées (les cinq notebooks lus firsthand dans #15080)

```yaml
- notebook_path: GenAI/RAG-et-Memoire-Semantique/05-Stockage-Vectoriel.ipynb
  role: worked_solution
  justification: "3 exercices entièrement résolus et exécutés (ec 12/13/14, sorties présentes) ; mur_latence_exo/prix_du_rappel/filtre_multiple répondent à leur énoncé (mesuré #15080 §1)"

- notebook_path: GenAI/Integrations-DotNet/CopilotSDK/01-GitHub-Copilot-SDK-Binding.ipynb
  role: open_subject
  justification: "3 sujets réellement ouverts, aucune cellule où écrire — le défaut est l'absence de support, pas l'absence de sujet (mesuré #15080 §1)"

- notebook_path: GenAI/RAG-et-Memoire-Semantique/05b-Stockage-Vectoriel-Serveur.ipynb
  role: method_demo
  justification: "0 occurrence exercice/exercise/TODO/challenge/a vous sur 23 cellules ; se déclare « Grain #13021 » avec critères d'acceptation — son 0 est légitime (mesuré #15080 §5)"

- notebook_path: GenAI/Video/01-Foundation/01-1b-Video-Slideshow-Bonus.ipynb
  role: open_subject
  justification: "énoncé de challenge (5 images nommées, OUTPUT_DIR, 0.5 pts, soumission par PR) ; a reçu depuis 5 cellules de code exécutées avec stubs C.1 (3 exercices « a completer », OUTPUT_DIR défini cells 4/7/12) — le livrable reste le travail étudiant. NB : chemin déplacé depuis GenAI/Texte/ (le catalogue référence déjà Video/01-Foundation/)"
  # role note: challenge enoncé + 3 exercices stubbés a completer -> le sujet est le livrable etudiant

- notebook_path: GenAI/Texte/10e_LLamaSharp_DotNet_BakeOff.ipynb
  role: method_demo
  justification: "bake-off de méthode (benchmarks multi-configs), pas un exercice ; projet csproj reconstruit in-notebook (cell 3, #15570), modèle résolu relatif au harnais TOOLS — 0 chemin _scratch en code"
```

## 4. Extension du registre

Le registre démarre aux cinq notebooks cités par #15080 (« je n'extrapole pas au reste du corpus »). Une nouvelle entrée exige :
1. une **lecture firsthand** du notebook (rôle par contenu, cf `exercise-example-labeling`) ;
2. une **justification mesurée** citée (compteur, cellules, ec) ;
3. un des trois tokens du vocabulaire — au-delà, proposer l'élargissement du vocabulaire dans l'issue parente.

909 entrées sur 1124 n'ont jamais été auditées sous cet angle : le champ vide est l'état honnête par défaut, pas un manque à combler en masse.

## 5. Voir aussi

- [#15080](https://github.com/jsboige/CoursIA/issues/15080) — audit fondateur (fiche D01, re-mesuré firsthand)
- `scripts/notebook_tools/generate_catalog.py` — loader `_load_pedagogical_roles_registry` + champ `pedagogical_role`
- `scientific-review-registry.md` — pattern whitelist curé (axe 3)
- `editorial-review-registry.md` — pattern whitelist curé (axe 1)
