# Commentaire infra = action ou silence (P3 de #15511)

S'applique à **tous les agents** du cluster CoursIA (workers `po-*` + coordinateur `ai-01`) qui commentent une PR.

**Motif fondateur** : PR #14821 — 31 commentaires / 68 101 caractères d'infra-diagnostic sur 5 jours (25/28 sans action attachée), pour un livrable qui n'avait pas bougé depuis le commit du premier jour. Le commentaire de diagnostic pur coûte une lecture à chaque lane et ne fait pas avancer la PR : c'est une pompe, pas un apport.

## Règle

Tout commentaire de diagnostic infra sur une PR **doit** livrer dans le même cycle une action concrète — rebase, fix, rerun de check, amend de body. Sans action à attacher, le commentaire est **interdit** : l'état va sur le dashboard RooSync en `[INFO]` sec, pas sur la PR.

La taxonomie de première ligne (`[ACTION]` / `[DIAG]` / `[ASK]`) et la détection de boucle sont portées par l'organe B.0 : [`scripts/check_unaddressed_nits.py`](../../scripts/check_unaddressed_nits.py) — verdict `DIAG-LOOP` à plus de 3 `[DIAG]` consécutifs sans `[ACTION]` intercalé. Détail de l'émission des tags : [pr-review-discipline.md](pr-review-discipline.md) §« Commentaires de diagnostic ».

**Source** : issue #15511, préconisation P3 (effort 0 — règle de comportement, vérification par le détecteur P1).
