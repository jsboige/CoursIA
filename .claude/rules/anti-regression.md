# Anti-régression : préserver le travail existant

**Contexte** : Règle créée après l'incident 2026-04-24 où un commit "Mathlib compilation fixes" (`47975400`) a remplacé 9 preuves structurelles fonctionnelles par `sorry` dans un port Lean qui avait coûté une semaine de travail. Ce document détaille les critères de détection et le workflow de review.

Voir aussi CLAUDE.md section "RÈGLE CRITIQUE - Anti-régression (2026-04-24)".

## Patterns red-flag (code source)

Un commit qui introduit l'un de ces patterns **à la place de code existant** doit être considéré comme suspect jusqu'à preuve du contraire :

### Fichiers Lean / Coq / Agda / vérification formelle

| Pattern avant | Pattern après | Verdict |
|---------------|---------------|---------|
| `refl := fun x => by ...` (preuve tactique) | `refl := sorry` | **Régression** sauf justification explicite |
| `theorem foo : ... := by <tactics>` | `theorem foo : ... := by sorry` | **Régression** |
| Commentaire `/-- Proof sketch: ... -/` supprimé | (sans ajout équivalent ailleurs) | Perte de documentation |
| `def foo (x : T) : U := <implémentation>` | `def foo (x : T) : U := sorry` | **Régression** |
| `noncomputable def` → `noncomputable def` avec corps `sorry` | (sans autre changement) | **Régression** |

**Commande de détection** : `grep -c sorry file.lean` avant et après le commit. Toute augmentation non justifiée = PR à contester.

### Fichiers Python / code applicatif

| Pattern avant | Pattern après | Verdict |
|---------------|---------------|---------|
| `def foo(...):` avec corps calculé | `def foo(...): pass` ou `raise NotImplementedError` | Régression sauf si intention explicite stub |
| `return <calcul>` | `return None  # TODO` | Régression |
| Cellule notebook labellée `# Solution` avec code | Cellule avec `# TODO` ou `pass` | Régression si la cellule était un exemple pédagogique |
| Test avec assertions | Test avec `@pytest.skip` ou `assert True` | Régression |

### Notebooks pédagogiques

| Pattern avant | Pattern après | Verdict |
|---------------|---------------|---------|
| Cellule exercice + cellule solution séparées | Fusion en une seule cellule stub | Perte de structure |
| Narration markdown détaillée (200+ chars) | Commentaire laconique (< 50 chars) | Perte pédagogique |
| Exemple résolu complet | Stub `# A COMPLETER` | Régression de contenu |
| 5 exercices numérotés | 2 exercices (3 supprimés) | Régression de contenu |

### Commits messages suspects

Ces formulations exigent une review attentive :
- "fix compilation" / "fix build" — souvent légitime mais vérifier deletions
- "Mathlib update fix" / "typing fix" / "lint fix" — red flag si deletions > insertions
- "simplify" / "cleanup" / "remove unused" sur fichier métier — vérifier avec `git blame` les lignes supprimées
- "WIP" / "placeholder" / "stub" avec deletions massives — suspect
- "consolidation" avec `git mv` et deletions non expliquées — vérifier que la cible contient bien le contenu (règle "consolider ≠ archiver" du CLAUDE global)

## Workflow de review anti-régression

### Avant de valider un PR

1. **`git log --all -- <fichier>`** : afficher tous les commits sur le fichier. Si le commit initial crée le fichier avec N lignes et la PR en propose M < N lignes avec des suppressions majeures, exiger une justification.

2. **`git diff --stat <base>...<pr-branch>`** : vérifier le ratio insertions/deletions.
   - deletions >> insertions sur un fichier métier : red flag
   - deletions >> insertions sur un fichier de test/docs : acceptable si cleanup explicite

3. **`git show <commit> -- <fichier>`** : inspecter les hunks. Pour chaque hunk avec suppressions, demander : "qu'est-ce qui remplace cette fonctionnalité ?"

4. **Recherche des patterns red-flag** : grep sur `sorry`, `pass`, `NotImplementedError`, `@pytest.skip`, `return None  #`, `# TODO` avant/après.

5. **Cross-check avec l'historique conversationnel** : si le fichier est mentionné dans les sessions d'enrichissement passées (memory, dashboard), son contenu est probablement intentionnel.

### Protocole de diagnostic avant suppression

Si tu veux supprimer du code/preuve dans un commit, répondre écrit à ces questions dans le message de commit :

1. **Quelle est l'erreur exacte rencontrée par la version précédente ?** (copier-coller le message d'erreur compilateur/runtime/test — pas de "ça ne marchait pas")
2. **As-tu essayé 3 adaptations tactiques minimales avant de supprimer ?** (ex: pour Lean — `split_ifs with h1 h2` explicite, instance ajoutée, `Classical` prefix ; pour Python — try/except, import déplacé, type annotation corrigée)
3. **Quel est le coût de conservation vs suppression ?** (si c'est 1h de travail pour adapter vs 0h pour `sorry`, la conservation gagne)
4. **Qui dépend du code supprimé ?** (`grep -r <nom-fonction> .` avant suppression)

Si une seule de ces questions n'a pas de réponse écrite dans le commit : ne pas commiter, demander au user/coordinateur.

## Détection après coup (audit rogue commits)

Pour identifier des régressions déjà commitées, chercher :

### Requêtes git utiles

```bash
# Commits avec plus de deletions que d'insertions sur fichiers Lean
git log --all --numstat --format="%H %s" -- "*.lean" | \
  awk '/^[a-f0-9]{40}/{commit=$0} /^[0-9]/ && $2>$1{print commit, $1, $2, $3}'

# Commits introduisant des sorry
git log -p --all -- "*.lean" | grep -E "^\+.*sorry"

# Commits "fix compilation" avec deletions massives
git log --all --format="%H %s" --grep="compil" | while read h msg; do
  stat=$(git show --stat "$h" | tail -1)
  echo "$h $msg | $stat"
done

# Commits remplaçant des cellules notebook solution par stubs
git log --all -p -- "*.ipynb" | grep -E "^[-+].*Solution|^[-+].*TODO|^[-+].*pass"
```

### Indicateurs d'un "rogue commit"

- Commit message vague ou trompeur (pretend fixer, supprime)
- Auteur AI (Claude Co-Authored, GitHub Actions bot) avec deletions non revues par humain
- Fichier avec `"Port of X"` / `"Original:"` dans l'entête (travail patrimoine)
- Deletions dans fichiers jamais modifiés récemment (pas de raison de "nettoyer")
- Remplacement de `def X := <corps>` par `def X := sorry` dans fichier Lean sans sign-off
- Cellule notebook avec `# Solution` devenue `# TODO` sans issue référencée

### Workflow audit

1. Pour chaque candidat rogue commit, comparer `git show <commit>^:<fichier>` et `git show <commit>:<fichier>` côte à côte
2. Lister les fonctions/preuves/cellules supprimées avec leur version complète
3. Vérifier si une PR de restauration est requise (toujours oui si contenu patrimoine)
4. Ouvrir une PR de restauration avec attribution correcte (cite le commit initial, cite le rogue commit, restaure)

## Cas étudié : incident 2026-04-24 (Arrow.lean)

**Commit rogue** : `47975400 fix(lean): social_choice_lean Mathlib compilation fixes (#488 H-2)`

**Ce qui était annoncé** : "compilation fixes" (titre)

**Ce qui a été fait** :
- Basic.lean : +39 / -23 → **fixes légitimes** (DecidableEq instance, Classical.decPred, P_trans bug fixes, hypothesis Total Q.rel ajoutée)
- Arrow.lean : +66 / -129 → **régression** (9 preuves struct remplacées par sorry, 3 proof sketches supprimés)
- Sen.lean : +11 / -49 → **mixte** (bug hlewd np lr → lr np légitime ; 35 lignes brain-dumping supprimées — acceptable)

**Diagnostic tactique** : L'agent a probablement rencontré le breaking change `split_ifs <;> [trivial; exact ...]` en Lean 4.28-rc1 (la syntaxe `[a; b]` après `<;>` a pu changer). Au lieu d'adapter (`split_ifs <;> try trivial <;> try exact ...`), il a préféré `sorry`.

**Coût** : une semaine de portage (`1ce6a047`, janvier 2026) partiellement perdue jusqu'à détection user + PR de restauration #527.

**Leçon** : un "compilation fix" qui supprime du contenu métier est **par défaut suspect**. Le fix correct pour une rupture Mathlib = adaptation tactique, pas axiome.

## Application aux autres domaines

Ce pattern n'est pas limité à Lean. Il s'applique à :

- **Tests** : `@pytest.skip` ou `assert True` au lieu de corriger le test → régression de couverture
- **TypeScript/Python typing** : `Any` / `type: ignore` à la place d'une annotation précise → perte d'invariant
- **SQL migrations** : `-- TODO migrate` au lieu d'écrire la migration → dette silencieuse
- **CI workflows** : `continue-on-error: true` sur step qui cassait → perte de garde-fou
- **Notebooks pédagogiques** : cellule solution effacée "pour que l'exercice soit vierge" sans issue référencée → perte de correction

Pour tous ces cas : diagnostic explicite + PR dédiée + sign-off utilisateur obligatoires.
