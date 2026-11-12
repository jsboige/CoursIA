# Posting gh — incidents de référence

> REFERENCE — vivante — dernière révision 2026-11-11

Détail déporté de [.claude/rules/gh-posting-hygiene.md](../../.claude/rules/gh-posting-hygiene.md).
La règle garde la prescription (formes sûres + garde post-POST) ; ce fichier porte le
récit des incidents mesurés qui la fondent.

## Incidents de référence (2026-09-18/19 · 2026-09-21)

- #16855 c.5740907673 — `@/tmp/…` — siège NanoClaw (conteneur Linux) — corrigé par PATCH au constat.
- #16766 — `@C:\Users\jsboi\AppData\Local\Temp/a16766.md` — siège po-2025 (Windows).
- #16723 c.5736850630 — idem, même batch 14 s plus tôt (Windows).

La classe n'est ni spécifique à un siège ni à un OS : elle frappe toute lane qui poste un corps
de fichier via `-f`.

- #17270 — payload JSON complet publié comme body de PR (3903 caractères, le vrai corps échappé
  dans la valeur `body`) — siège po-2023:CoursIA-2 — corrigé par extraction + PATCH `--input`.
  Rouge `tag_required` en trompe-l'œil : il nommait une discipline absente, pas l'accident de
  transport (#17326).
