# CodeQL `# codeql[rule-id]` — suppressions inertes sur default setup

Source : issue **#12100** (CodeQL: les commentaires `# codeql[rule-id]` sont INERTES sur ce dépot, 2 commits déjà perdus dessus). Constat vérifié firsthand via check-run CodeQL `96714903857` (ee8823b55, terminé 2026-08-21T08:29:38Z) : les alertes restent ouvertes après déplacement des commentaires. Cause = pas un probleme de placement, mais une **mécanique du dépot** : CodeQL y tourne en **default setup** (géré par GitHub, hors du repo), donc il n'existe **aucun** point d'insertion pour `AlertSuppression.ql` ni pour `dismiss-alerts` au niveau du repo.

PRs illustratives :
- **#12294** (po-2024, MERGED 2026-08-22) : retrait du `# codeql[py/weak-sensitive-data-hashing]` inerte sur `scripts/secrets/render_settings_json.py:121` + consignation dans le commentaire.
- **#12102** (autre lane, MERGED) : autre aspect de #12100 (bcrypt inline de `validate_auth`).

## Regle HARD

**NE JAMAIS ajouter de commentaire `# codeql[rule-id]` au source pour « supprimer » une alerte CodeQL sur ce dépot.** Le commentaire **ne produit rien dans le SARIF** : il n'est pas lu par CodeQL (default setup = géré par GitHub, pas d'extension repo-level), il ne leve rien, il ajoute juste du bruit à la lecture et donne une fausse impression de sécurité. **Les commits déplaçant le commentaire sont du travail gaspillé** (#11905 a déjà payé 2 commits pour ça).

## Anti-patterns interdits

| Anti-pattern | Pourquoi c'est un piège | Alternative |
|---|---|---|
| Déplacer un `# codeql[...]` d'un endroit à l'autre du source en supposant « ça va lever l'alerte » | CodeQL default setup ne lit pas ces commentaires : l'alerte reste ouverte. Coût : 1 commit gaspillé + bruit visuel. | Ouvrir une **issue dédiée** (`codeql: alerte XYZ ouvre sur fichier:ligne — mécanisme de suppression absent`) pour escalader vers le coordinateur. Ne pas modifier le source avant résolution. |
| Ajouter un `# codeql[...]` à un nouveau fichier « par symétrie » avec un voisin qui en a un | Le voisin est lui-même inerte : la symétrie propage le pattern inutile. | Ne pas ajouter le `# codeql[...]`. Si la symétrie est visuelle (vieux réflexe), ignorer. |
| Mettre un `# noqa: S324` / `# noqa: ...` **et** un `# codeql[...]` sur la même ligne | Seul `# noqa: ...` est actif (lu par ruff/bandit/flake8). Le `# codeql[...]` est mort. | Garder `# noqa: ...` seul. Retirer le `# codeql[...]`. |
| Croire que `AlertSuppression.ql` dans le repo résoudra le probleme | Le dépot est en **default setup** GitHub. Il n'y a pas de `.github/codeql/` query pack custom ; CodeQL SARIF est produit par GitHub, pas par le repo. | Activer le **advanced setup** (`Enable GitHub Code Scanning` + `codeql-config.yml` dans le repo) avant d'écrire `AlertSuppression.ql`. Sinon le fichier sera ignoré comme les commentaires. |

## Verdict pour les commentaires existants

Pour chaque commentaire `# codeql[...]` rencontré :

1. **Vérifier qu'il est bien inerte** : la check-run CodeQL la plus récente sur la tete main doit montrer que l'alerte reste **non-resolved** malgré le commentaire. Si l'alerte a disparu = le setup a changé depuis, redocumenter dans le commentaire.
2. **Si inerte** : retirer le commentaire (consigner l'intention dans un commentaire explicatif de 3-4 lignes, comme le pattern #12294). Le retrait est lui-même un mini-gain de lisibilité.
3. **Si la suppression de l'alerte est légitime** (= faux positif, accepté) : la voie dépend du setup. **Default setup (état actuel)** : ajouter au PR un **commentaire PR body** avec la rationale (pour audit trail), **pas** un `# codeql[...]` dans le source. **Advanced setup** : `AlertSuppression.ql` dans le repo.

## Détection (sans modifier le dépot)

```bash
# Liste des # codeql[rule-id] dans le source
git grep -n '# codeql\[' 'MyIA.AI.Notebooks/**/*.py' 'scripts/**/*.py' 2>/dev/null

# Pour chacun, vérifier la check-run CodeQL sur origin/main :
#   https://github.com/jsboige/CoursIA/security/code-scanning
# Si l'alerte est résolue → le commentaire est actif (rare sur default setup, à redocumenter).
# Si l'alerte est ouverte → le commentaire est inerte (à retirer).
```

## Migration vers advanced setup (futur, sign-off user requis)

Si on veut rendre `# codeql[...]` et `AlertSuppression.ql` **actifs**, il faut basculer le dépot en **advanced setup** :

1. Créer `.github/codeql/codeql-config.yml` (langages, paths, query packs).
2. Créer `.github/workflows/codeql.yml` (cron + push sur main).
3. Désactiver le default setup dans Settings > Code security > Code scanning.
4. Sign-off user (breaking change sur la posture de sécurité).

Ce n'est **pas dans le scope** d'une PR worker : c'est une décision user-level (R5 coordinator discipline + global user-only). Le **présent fichier** consigne l'état actuel sans proposer la bascule.

## Acceptance #12100 — état

| Sous-acceptance | État | PR |
|---|---|---|
| Retrait du `# codeql[...]` inerte sur `render_settings_json.py:121` | FAIT | #12294 MERGED |
| Fix bcrypt inline de `validate_auth` | FAIT | #12102 MERGED |
| Consignation en `.claude/rules/` du constat d'inertie | **LIVRÉ (cette PR)** | (cette PR #12893) |
| Migration vers advanced setup (rendre `# codeql[...]` actifs) | **NON FAIT** — décision user requise | — |

Cette PR clôture l'acceptance **substantielle** de #12100 (le « comment ») sans engager la **option** (la bascule de setup). L'issue reste OPEN tant que la décision user n'est pas prise.

## Voir aussi

- Issue **#12100** — fil de discussion et verdict-delivered (po-2027 c.1331p483).
- PR **#12294** (po-2024, MERGED) — patron de retrait + consignation en commentaire.
- [verify-before-claiming.md](verify-before-claiming.md) — règle générale G.1 (vérifier avant de clamer « CodeQL va ignorer »).
- [secrets-hygiene.md](secrets-hygiene.md) règle 6 — Stop & Repair (fix cause + re-execute, ne pas maquiller).
- [sota-not-workaround.md](sota-not-workaround.md) — un workaround qui ne fait rien n'est pas un workaround, c'est du bruit.