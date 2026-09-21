# Posting gh : corps de fichier via `-f` = chaîne littérale — formes sûres + garde post-POST

S'applique à **toute lane qui poste un corps depuis un fichier** (commentaire d'issue/PR, review, edition de body) via `gh api` ou `gh pr comment`. Source : incident #16866 (3 occurrences mesurées, 2 sièges, 2 OS — Linux conteneur NanoClaw ET Windows po-2025).

## Règle HARD 1 — jamais `-f body=@fichier`

Le préfixe `@` n'est expansé **que par les champs typés `-F`**. Avec `-f` (chaîne brute), GitHub reçoit le texte littéral `@/tmp/f.md` — **échec 100 % silencieux** : 0 erreur, le commentaire atterrit avec un corps inutile de ~30-50 caractères.

| Intention | Correct | Piégé |
|---|---|---|
| Poster un corps de fichier via API | `gh api …/comments --input payload.json` (JSON `{"body": …}` construit par `json.dumps`) | ~~`gh api …/comments -f body=@f.md`~~ |
| Champ typé (rare) | `gh api …/comments -F body=@f.md` | ~~`-f body=@f.md`~~ |
| Expansion shell | `gh api … -f body="$(cat f.md)"` (fragile : backticks/quotes, préférer `--input`) | ~~`-f body=@f.md`~~ |
| PR body | `gh pr create --body-file f.md` / `gh pr edit --body-file f.md` | ~~`gh pr create -b @f.md`~~ |
| PR commentaire | `gh pr comment N --body-file f.md` | ~~`gh pr comment N --body @f.md`~~ |

Voir aussi le piège jumeau : **backticks dans un `-f body` / `--body` inline** (le shell les interprète) → là aussi, toujours `--input`/`--body-file`.

## Règle HARD 2 — garde longueur post-POST

Après tout POST d'un corps de fichier, **relire le corps publié et vérifier sa longueur** : un corps < 100 caractères après un POST de fichier = le piège a tiré.

```bash
gh api repos/jsboige/CoursIA/issues/comments/<id> --jq '.body | length'
```

## Règle 3 — remédiation PATCH

Corps piégé détecté : corriger par PATCH (pas de suppression si le contenu d'origine est traçable) —

```bash
gh api repos/jsboige/CoursIA/issues/comments/<id> -X PATCH --input payload.json
```

## Détection mesurable

```bash
python scripts/ci/check_gh_comment_traps.py            # fenêtre 48 h, exit 1 si corps piégé
python scripts/ci/check_gh_comment_traps.py --json     # verdict machine + ids + commandes de fix
```

Verdicts : `TRAPPED` (exit 1, liste + commande PATCH) · `CLEAN` · `UNKNOWN` (réseau — jamais un rouge forge, #14849). Le critère d'escalade NanoClaw (« 3ᵉ occurrence ») se mesure avec cet organe.

## Incidents de référence (2026-09-18/19)

- #16855 c.5740907673 — `@/tmp/…` — siège NanoClaw (conteneur Linux) — corrigé par PATCH au constat.
- #16766 — `@C:\Users\jsboi\AppData\Local\Temp/a16766.md` — siège po-2025 (Windows).
- #16723 c.5736850630 — idem, même batch 14 s plus tôt (Windows).

La classe n'est ni spécifique à un siège ni à un OS : elle frappe toute lane qui poste un corps de fichier via `-f`.

## Voir aussi

- [secrets-hygiene.md](secrets-hygiene.md) — jamais de valeur de secret dans les corps, même Piégés
- [lane-claim-protocol.md](lane-claim-protocol.md) — les commentaires `[CLAIMED]`/`[DELIVERED]` empruntent les mêmes formes sûres
- #16866 — issue fondateure (mesure, sièges, parade)
