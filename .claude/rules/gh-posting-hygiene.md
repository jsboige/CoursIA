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

## Règle HARD 2 — garde structurelle post-POST (2 prédicats)

Après tout POST d'un corps de fichier, **relire le corps publié** et vérifier **deux prédicats** — un métrique, un structurel :

1. **Longueur** : un corps < 100 caractères après un POST de fichier = le piège `-f body=@` a tiré.
2. **Structure** (#17326) : le corps publié ne doit **pas parser en objet JSON portant une clé `body`** — c'est le payload JSON complet passé comme corps, le vrai corps échappé à l'intérieur d'une valeur de chaîne. Le corps publié est alors **long** (la garde de longueur est structurellement aveugle) et se présente comme un bloc JSON plausible. Instance mesurée : #17270 — le rouge `tag_required` accusait une discipline absente alors que le corps source de la lane était correct.

```bash
gh api repos/jsboige/CoursIA/issues/comments/<id> --jq '.body | length'
# prédicat structurel (membre 2) — PAYLOAD-TRAP si le corps entier est l'objet payload :
gh api repos/jsboige/CoursIA/issues/comments/<id> --jq .body | python -c "import json,sys
try:
    p = json.loads(sys.stdin.read()); trap = isinstance(p, dict) and isinstance(p.get('body'), str)
except Exception:
    trap = False
print('PAYLOAD-TRAP' if trap else 'OK')"
```

## Règle 3 — remédiation PATCH

Corps piégé détecté : corriger par PATCH (pas de suppression si le contenu d'origine est traçable) —

```bash
gh api repos/jsboige/CoursIA/issues/comments/<id> -X PATCH --input payload.json
```

## Détection mesurable

```bash
python scripts/ci/check_gh_comment_traps.py            # fenêtre 48 h + PRs ouvertes, exit 1 si corps piégé
python scripts/ci/check_gh_comment_traps.py --json     # verdict machine + ids + commandes de fix
```

L'organe couvre **les deux membres** de la famille — le littéral `@<path>` (commentaires + bodies de PRs) et le payload-JSON-comme-corps (commentaires + bodies de PRs ouvertes, l'endpoint commentaires ne voit jamais un body de PR). Verdicts : `TRAPPED` (exit 1, liste + commande PATCH, corps extrait pour membre 2) · `CLEAN` · `UNKNOWN` (réseau — jamais un rouge forge, #14849). Le critère d'escalade NanoClaw (« 3ᵉ occurrence ») se mesure avec cet organe.

## Incidents de référence (2026-09-18/19 · 2026-09-21)

- #16855 c.5740907673 — `@/tmp/…` — siège NanoClaw (conteneur Linux) — corrigé par PATCH au constat.
- #16766 — `@C:\Users\jsboi\AppData\Local\Temp/a16766.md` — siège po-2025 (Windows).
- #16723 c.5736850630 — idem, même batch 14 s plus tôt (Windows).

La classe n'est ni spécifique à un siège ni à un OS : elle frappe toute lane qui poste un corps de fichier via `-f`.

- #17270 — payload JSON complet publié comme body de PR (3903 caractères, le vrai corps échappé dans la valeur `body`) — siège po-2023:CoursIA-2 — corrigé par extraction + PATCH `--input`. Rouge `tag_required` en trompe-l'œil : il nommait une discipline absente, pas l'accident de transport (#17326).

## Voir aussi

- [secrets-hygiene.md](secrets-hygiene.md) — jamais de valeur de secret dans les corps, même Piégés
- [lane-claim-protocol.md](lane-claim-protocol.md) — les commentaires `[CLAIMED]`/`[DELIVERED]` empruntent les mêmes formes sûres
- #16866 — issue fondatrice (mesure, sièges, parade)
- #17326 — second membre de la famille (payload JSON comme corps, angle mort structurel de la garde de longueur)
