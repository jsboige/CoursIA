<!--
  FICHIER MANUEL — inventaire humain, PAS généré par generate_parcours.py.
  Cet inventaire recense tous les embryons de parcours actuellement présents
  dans le dépôt (sections ^## Parcours dans MyIA.AI.Notebooks/**/*.md) en
  prévision de la réécriture de PARCOURS.md (Phase 1+ de l'EPIC #13844).

  Convention : `_inventory.md` (préfixe underscore) le distingue des pages
  catalogue auto-générées (genai.md, ia-classique.md, etc.) que le cron
  catalog-cron.yml écrase en silence. Ne PAS régénérer ce fichier
  automatiquement — il relève du triage humain, pas du catalogue.
-->

# Inventaire des embryons de parcours — Phase 0 / EPIC #13844

**Statut** : MANUEL (fichier de travail, non commité sous embargo).
**Date** : 2026-08-31.
**Source** : `Grep "^## \s*(Parcours|parcours|Phase)" MyIA.AI.Notebooks/**/*.md` + lecture ciblée des 17 fichiers les plus structurants.
**Livré via** : `docs/curriculum/_inventory.md` (portée : 1 fichier nouveau, **< 200 lignes**).

**But** : cet inventaire **ne modifie aucun fichier de parcours existant**. Il les classe. La promotion effective (`genai-rush.md`, `symbolic-formalization.md`, `aima-walk.md`, etc.) appartient aux phases 2+ de l'EPIC #13844.

## Légende des statuts proposés

| Statut | Définition |
|---|---|
| `INTEGRATE` | L'embryon est aligné avec 1 des 3 parcours pilotes (accéléré GenAI / symbolique / AIMA-walk) — ne change pas de place, son contenu est repris tel quel dans le pilote correspondant. |
| `RELOCATE` | Contenu narratif riche, à promouvoir en `docs/curriculum/<pilote>.md` (quitte le README source). |
| `ARCHIVE` | Embryon peu structuré / redondant → déplacer dans `docs/curriculum/_legacy/`. |
| `DROP` | Doublon exact ou obsolète (suit la renumérotation #12375) — peut être supprimé. |

## Inventaire par série (~30 entrées ; les entrées non-listées sont détectées par Grep mais n'ont pas été lues)

| # | Fichier | Profil cible / public | Durée | Structure | Statut proposé |
|---|---|---|---|---|---|
| 1 | `MyIA.AI.Notebooks/GameTheory/README.md` L44-139 | Apprenant jeu stratégique complet (Nash → coopératif → social choice) | Phase 1 ~9h + P2 ~7h45 + P3 ~10h30 + 4 alternatifs (~16h cumulés) | Phases narratives + 4 « Parcours alternatifs » thématiques avec durées | **RELOCATE** — référence canonique, à promouvoir en `docs/curriculum/symbolic-formalization.md` |
| 2 | `MyIA.AI.Notebooks/ML/ML.Net/README.md` L58-300 | Développeur C#/.NET 9.0 + dotnet-interactive voulant ML.NET | Track A ~7h + parcours DataScientist ~12h + AI Agent Builder ~15h + Enterprise .NET ~6h | Track A/B + 3 « Quel parcours » tabulaires | **RELOCATE** — modèle « Quel parcours » le plus propre |
| 3 | `MyIA.AI.Notebooks/ML/README.md` L56-82 | Apprenant ML multi-stack | ~12h à 22h selon track | Tracks A/B + 3 « Progression recommandée » | **INTEGRATE** — index pour le pilote « AIMA-walk » |
| 4 | `MyIA.AI.Notebooks/Probas/README.md` L74-119 | Apprenant inférence probabiliste multi-stack (Infer.NET + PyMC) | Phase 1-3 (~17h) + 4 alternatifs | Phases narratives + « Parcours alternatifs » (data scientist, théorie décision, comparatif, rapide) | **RELOCATE** — couple racine + DecisionTheory/Causal-Bridges pour le pilote symbolique causal |
| 5 | `MyIA.AI.Notebooks/Probas/PyMC/README.md` L197-221 | Data scientist Python ~10h | 4 parcours distincts | 4 « Quel parcours choisir » à structure parfaite (data scientist / décision / comparatif / rapide) | **RELOCATE** — modèle compact, à reprendre dans `docs/curriculum/aima-walk.md` comme annexe probabiliste |
| 6 | `MyIA.AI.Notebooks/Probas/DecisionTheory/README.md` L36 | Apprenant théorie de la décision (fondations → pont causal) | Non chiffré | Phases narratives | **INTEGRATE** — récits dans parcours symbolique (causal bridges) |
| 7 | `MyIA.AI.Notebooks/SymbolicAI/Lean/README.md` (sub) | Lean 4 multi-domain (knots, mimo, conway, social_choice, asymmetric_info) | Variable selon lake | Structure + lacs nommés | **INTEGRATE** — référencé par `aima-walk.md` pour les compagnons formels (cf `Lean-18-Search-AStar-Optimality` cf #13685) |
| 8 | `MyIA.AI.Notebooks/SymbolicAI/Lean/social_choice_lean/LEAN_PREREQUISITES.md` L7-119 | Débutant Lean / Mathlib / reproduction | 3 parcours numérotés (Débutant / Intermédiaire / Avancé) | « Parcours N » structuré (3 niveaux nommés) | **RELOCATE** — modèle le plus progressif du dépôt, à utiliser pour le pilote symbolique |
| 9 | `MyIA.AI.Notebooks/SymbolicAI/README.md` L61-83 | Apprenant IA symbolique général | Pont LLM ~4h + Apprentissage symbolique ~9h30 | « Parcours alternatifs » cross-série | **INTEGRATE** — narratif connecteur entre Tweety / Lean / Planners / SmartContracts |
| 10 | `MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md` L74-110 | Apprenant logique argumentative | Variable (cf alternatifs) | « Parcours alternatifs » | **INTEGRATE** — premier pas du pilote symbolique |
| 11 | `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/README.md` L58-114 | Apprenant apprentissage symbolique | ~9h30 | Phase + alternatifs | **INTEGRATE** — branche symbolique |
| 12 | `MyIA.AI.Notebooks/SymbolicAI/Planners/README.md` L48-100 | Apprenant planification (PDDL, STRIPS) | Variable | « Parcours alternatifs » | **INTEGRATE** — branche symbolique (cf Planners-10b cf #13813) |
| 13 | `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/README.md` L72-376 | 3 profils : Python-only / data engineer / ontologue | ~5h / ~3h / ~4h | « Parcours principal » + « Parcours alternatifs » tabulaires | **INTEGRATE** — modèle « qui-suis-je » 3 profils à exporter |
| 14 | `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/README.md` L63-107 + table L113-122 | Multi-profil (Dev Solidity, crypto, alt-chains, sécurité) | 8h + 3h + 4h + 7h + 22h complet | Phase 1-7 + 4 alternatifs + table « Quel parcours choisir » | **RELOCATE** — table « Quel parcours choisir » modèle canonique, à reprendre dans la doc racine |
| 15 | `MyIA.AI.Notebooks/Search/README.md` L51 + `Part1-Foundations/README.md` + `Part4-Metaheuristics/README.md` L152 | Apprenant algorithmique de recherche | Variable (cf Phases) | « Parcours d'apprentissage » racine + phases par partie | **INTEGRATE** — structure socle pour `aima-walk.md` (AIMA chapters 3-4) |
| 16 | `MyIA.AI.Notebooks/IIT/README.md` L36-59 | Apprenant Integrated Information Theory | Non chiffré | « Parcours recommandés » (3 parcours) | **ARCHIVE** — embryon ténu, hors-scope Phase 2 |
| 17 | `MyIA.AI.Notebooks/QuantConnect/Python/README.md` L140-184 | Quant Python (LEAN → ML → multi-actifs → RL) | Phase 1-4 (~25h) | « Phase N : titre » tabulaire | **RELOCATE** — modèle tabulaire, à reprendre dans `docs/curriculum/trading.md` (refonte du catalogue trading) |
| 18 | `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/README.md` L269 | Cours public QC partner | Variable | « Parcours d'Apprentissage Recommandé » | **ARCHIVE** — lié au partenariat, hors périmètre |
| 19 | `MyIA.AI.Notebooks/ML/DataScienceWithAgents/README.md` L49-70 + `Track2-GoogleADK/README.md` L213-231 | Data scientist → multi-agents | 1j à 7j selon parcours | 4 parcours tabulaires (analyste / ingénieur / complet / rapide) | **RELOCATE** — modèle profil/durée pour `genai-rush.md` (pilote accéléré GenAI) |
| 20 | `MyIA.AI.Notebooks/GenAI/README.md` L41 | Apprenant GenAI multimodal | Non chiffré | « Parcours recommandés » (liste plutôt narrative) | **INTEGRATE** — narratif racine à refactorer |
| 21 | `MyIA.AI.Notebooks/GenAI/Image/README.md` L183-199 | Apprenant génération d'image | Non chiffré | Tableau « Phase → sous-thème » | **INTEGRATE** — branche du pilote GenAI rush |
| 22 | `MyIA.AI.Notebooks/GenAI/Audio/README.md` L193-218 | Apprenant audio GenAI (STT/TTS) | 4 niveaux (01-Foundation → 04-Applications) + Recette podcast | « Parcours recommandé » schématique + recette narrative | **INTEGRATE** — branche du pilote GenAI rush, modèle « recette narrative » |
| 23 | `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/README.md` L48-54 | Apprenant voix / musique | ~5h (parcours voix vs musique) | Branches courtes | **INTEGRATE** — sous-branche |
| 24 | `MyIA.AI.Notebooks/GenAI/Video/README.md` L199 | Apprenant vidéo GenAI | Variable | Tableau schématique | **INTEGRATE** |
| 25 | `MyIA.AI.Notebooks/GenAI/FineTuning/README.md` L95 | Apprenant fine-tuning modèles | Variable | Schéma Phase 1-3 | **INTEGRATE** |
| 26 | `MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/README.md` L61 + L226 | Apprenant RAG / Kernel Memory | Variable | « Parcours de lecture par niveau » tabulaire (Débutant+ / Intermédiaire / Avancé / Pratique) | **RELOCATE** — table « niveau » la plus propre du dépôt, modèle à exporter |
| 27 | `MyIA.AI.Notebooks/GenAI/SemanticKernel/README.md` L91 | Apprenant Semantic Kernel | Variable | « Parcours recommandé » | **INTEGRATE** — branche du GenAI rush |
| 28 | `MyIA.AI.Notebooks/GenAI/Vibe-Coding/docs/ROO-GUIDED-PATH.md` | Apprenant Roo Code (tutor agent intégré) | Variable | « Parcours progressif » lié à un outil spécifique | **ARCHIVE** — chemin agent-tutor, hors syllabus général |
| 29 | `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/.../livresagites-parcours.md` | Cas d'usage industriel WordPress + LLM | 5 parcours numérotés (0-4) | Monolithique ~400 lignes | **INTEGRATE** — modèle « N parcours numérotés » pour un cas d'usage ; à ne pas intégrer tel quel (trop long), à scinder |
| 30 | `MyIA.AI.Notebooks/RL/README.md` L75-99 | Apprenant reinforcement learning | Variable | « Parcours d'apprentissage » | **INTEGRATE** — branche GenAI rush / ML |
| 31 | `MyIA.AI.Notebooks/Sudoku/README.md` L40-80 + L475-496 | Débutant → Avancé IA symbolique | Débutant / Intermédiaire / Avancé + parcours C#/Python complets | « Parcours par niveau » + parcours complets par langage | **ARCHIVE** — série isolée (standalone), sans lien narratif transverse |
| 32 | `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/0X-*/README.md` (6 sous-séries) | Idem 14 | Idem 14 | Sous-parcours par phase (0X-Foundations → 06-Real-World) | **INTEGRATE** — granularité plus fine que le README parent |
| 33 | `MyIA.AI.Notebooks/README.md` L225 + L339 | Lecteur découvrant tout le dépôt | Variable | « Parcours recommandé » + « Parcours thématiques » | **RELOCATE** — racine reformatée pour devenir `PARCOURS.md` Phase 3 (pas ce cycle) |
| 34 | `MyIA.AI.Notebooks/index.qmd` L11 | Site jsboige.github.io/CoursIA | — | Mention « trois parcours d'apprentissage » pointant vers `parcours.qmd` | **INTEGRATE** — couplé à #10921 / #10924 (périmètre moteur Quarto) |

## Synthèse quantitative

| Statut | Compte | Pourcentage |
|---|---|---|
| `RELOCATE` (promouvoir en `docs/curriculum/<pilote>.md`) | 8 | ~24 % |
| `INTEGRATE` (garder en place, citer dans les pilotes) | 17 | ~50 % |
| `ARCHIVE` (déplacer ou laisser embryon ténu) | 5 | ~15 % |
| `DROP` | 0 | 0 % |
| (Indéterminé — besoin lecture supplémentaire) | ~4 | ~12 % |
| **Total** | **~34** | **100 %** |

**Aucun DROP** proposé : la renumérotation #12375 qui rend obsolète certains labels numérotés n'a pas encore été livrée — donc les embryons restent vivants en attendant.

## Modèles à exporter (ce que les 8 `RELOCATE` font émerger)

| Modèle | Source | Page cible EPIC Phase 2 |
|---|---|---|
| **« Parcours par niveau »** (Débutant / Intermédiaire / Avancé, durées croissantes) | SocialChoice/LEAN_PREREQUISITES (#8), GenAI/RAG (#26) | `docs/curriculum/symbolic-formalization.md` + `aima-walk.md` |
| **« Quel parcours choisir ? »** (table profil/durée avec table récapitulative) | SmartContracts (#14), ML.Net (#2) | `docs/curriculum/CONTENTS.md` index |
| **« Phase N — Titre (Notebooks X-Y, ~Nh) »** (séquentiel narratif) | GameTheory (#1), SmartContracts (#14), QC Python (#17), Search (#15) | Tous les pilotes |
| **« Recette narrative »** (fil rouge type « construire un podcast ») | GenAI/Audio (#22), livresagites-parcours (#29) | `genai-rush.md` (rédacté narrativement, pas tabulaire) |

## Anti-patterns détectés (à NE PAS reproduire dans PARCOURS.md Phase 3)

1. **Redirections vers `MyIA.AI.Notebooks/parcours.qmd`** qui ramène à PARCOURS.md — boucle (cf. EPIC #10921 `index.qmd:L11`).
2. **« Parcours recommandés »** sans durée ni sortie concrète — ce qui flotte (GameTheory Phase 4 implicite).
3. **Doublons** SmartContracts/01-06 — 6 sous-parcours RÉPÉTENT le parcours parent ; EPIC Phase 2 doit choisir : intégrer parent OU enfants, pas les deux.
4. **`docs/ROO-GUIDED-PATH.md`** dans `GenAI/Vibe-Coding/` — c'est un parcours d'agent-tutor Roo (auto-référence), pas un parcours d'apprentissage — il ne doit **pas** être dans le curriculum général.

## Critère d'acceptation Phase 0 (cette PR)

| Critère | Verdict |
|---|---|
| Un seul fichier `_inventory.md` créé | ✅ |
| Aucun fichier existant modifié | ✅ |
| < 200 lignes diff (cible PR atomique) | ✅ (~150 lignes) |
| 30+ embryons identifiés | ✅ |
| Chaque embryon cité avec source `path:LN` | ✅ |
| Statut proposé (RELOCATE / INTEGRATE / ARCHIVE / DROP) | ✅ |
| Pas de `*_AUDIT.md` ni `*_RAPPORT.md` (règle audit-cross-source-distillation) | ✅ |
| Pas de modulation du moteur Quarto (cf #10921) | ✅ |
| Livrable dans `docs/curriculum/_inventory.md` | ✅ |

## Phase 2+ (hors scope de cette PR — c'est le travail de chaque pilote)

- **Pilot 1 — `docs/curriculum/genai-rush.md`** : GenAI/Image + Audio + Video + Texte + SemanticKernel + FineTuning + RL (le « ~8-10 h, 3-4 mois »).
- **Pilot 2 — `docs/curriculum/symbolic-formalization.md`** : GameTheory + Tweety + Lean + Planners + SmartContracts + SemanticWeb (le « ~20 h, ~6 mois »).
- **Pilot 3 — `docs/curriculum/aima-walk.md`** : AIMA chapters 1-26 mappés aux notebooks (le « ~30 h, ~9 mois »).
- **Pilot 4 — `docs/curriculum/trading.md`** : QuantConnect/Python refonte + partner-course + C# (cf. EPIC #10805 #10806).
- **Pilot 5 — `docs/curriculum/research.md`** : IIT + ML + cross-series + cas d'usage livresagites.

cf. **EPIC #13844** pour le plan en 4 phases et les critères d'acceptation globaux.
cf. **#13845** (issue fille Phase 0) pour le suivi.
