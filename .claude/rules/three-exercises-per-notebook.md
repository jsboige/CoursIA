# Convention : 3 exercices par notebook pedagogique

**Source** : mandat user 2026-06-02. Issue #2161.
**Scope** : tout notebook pedagogique (`MyIA.AI.Notebooks/**/*.ipynb`) sauf setup/environment (0-1 ex OK).

## Regle HARD

Chaque notebook pedagogique vise **>= 3 exercices** (cellules code stub). Les exercices **cohabitent** avec les exemples guids (cf [exercise-example-labeling.md](exercise-example-labeling.md)).

### Classification et stubs

- **Exercice** = cellule code avec stub (`pass` / `return None` / `print("Exercice a completer")` / `result = None  # TODO`). Jamais `raise NotImplementedError` / `assert False` / `1/0` (regle C.1).
- **Exemple** = cellule code avec solution complete fonctionnelle. Ne JAMAIS stubber.
- Classification **par contenu**, pas par titre (cf [exercise-example-labeling.md](exercise-example-labeling.md) section "Classification PAR CONTENU").

### Exceptions

| Type de notebook | Minimum exercices | Justification |
|------------------|-------------------|---------------|
| Setup / Environment (ex: `*-Setup*`, `*-0-Environment*`) | 0-1 | Configuration seul, pas de concept a exercer |
| Notebook purement Lean (ex: `*-Lean-*`) | 0-2 | Preuves formelles = paradigme different |
| Archive / Legacy | 0 | Pas maintenir |

### Placement pedagogique

- Exercices **repartis** dans le notebook (pas tous en fin).
- Chaque exercice **precede d'un markdown** : contexte + objectif + indices (`# Indice`, `# Etape N`).
- Exercice **suit un exemple guide** demonstrant le meme concept quand possible.

### Application progressive (rollout)

1. **Notebooks nouvellement cre**s : 3 exercices obligatoires des la creation.
2. **Notebooks modifies** (enrichissement, fix) : profiter de l'edition pour ajouter des exercices si sous le seuil.
3. **Rollout systematique** : tracker par famille via issues filles (ne PAS tout faire d'un coup).

## Liens

- [exercise-example-labeling.md](exercise-example-labeling.md) — classification par contenu, interdits, incidents
- [notebook-conventions.md](notebook-conventions.md) — C.1 stubs, C.2 outputs, C.3 scope re-exec
- [anti-regression.md](anti-regression.md) — ne pas stripper les exemples resolu
- CLAUDE.md section C — regles notebooks user 2026-04-26
