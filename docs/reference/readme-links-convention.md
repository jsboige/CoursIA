# Liens notebooks des READMEs — convention `.ipynb`, jamais `.html`

**Règle en vigueur (arbitrage user du 2026-10-08 — Concern sur [#19897](https://github.com/jsboige/CoursIA/pull/19897#issuecomment-6055971289), décision [`c.6076029168` sur #18911](https://github.com/jsboige/CoursIA/issues/18911)).** Un README lie toujours le notebook en **`.ipynb`**. La navigation de référence est celle de **github.com**, où un lien `.ipynb` s'ouvre dans la visionneuse intégrée (markdown, code, sorties rendus) ; un lien `.html` y produit un **404**, parce que les rendus Quarto ne sont pas committés dans le dépôt. C'est au **site** d'adapter les liens au moment du rendu (réécriture native de Quarto des cibles du projet), pas aux READMEs de s'adapter au site.

## Statut des liens (garde `readme-ipynb-links-guard.yml`)

| Lien dans un README d'un sous-arbre rendu | Statut |
|---|---|
| `X.ipynb`, cible committée | **Forme de référence** — jamais une violation |
| `X.html` vers un rendu non committé | **Violation `HTML_404`** (404 sur github.com) — garde bloquante, aucune nouvelle violation admise |
| `.ipynb` hors render-list (« source brute » légitime : garde `---` ou hors sous-arbre) | Population documentée (~7 liens, cf #18911) — à ne pas convertir |

L'énumération des violations est portée par `scripts/regen_quarto_render.py --check-readme-links` (classes `HTML_404` / `BROKEN`) ; la garde CI consomme cette sortie. L'ancienne classe `STALE_LINK` (« un `.ipynb` dont le rendu sibling existe devrait être lié en `.html` », #13025/#18970) est **retirée** — elle a produit la vague de conversion inversée depuis.

## Historique — la règle a changé deux fois, et pourquoi

1. **#13025 (08/2026)** : défaut fondateur — les READMEs liaient les `.ipynb` bruts et le site Pages servait du **JSON brut** au lieu d'une page rendue. Première règle : lier le rendu `.html` quand il existe (`STALE_LINK` sinon), garde #18970 + sweep #18911 (1740 liens mesurés).
2. **#19301 (05/10, décision mainteneur)** : durcissement proposé — ne lier `.html` que si la page publiée est **équivalente au carnet exécuté** (organe `check_equivalence.py`, #19305). Valide trois jours.
3. **Arbitrage user (08/10, c.6076029168)** : la politique « liens `.html` » est **abandonnée**. La navigation de référence est github.com ; 632 liens `.html` de 55 READMEs y rendaient 404. Quatre gestes : gel des conversions, **inversion de la garde** (`HTML_404` devient la classe bloquante), vérification côté site (Quarto réécrit déjà les liens `.ipynb` du projet vers leur rendu — mesuré, aucun changement nécessaire), retour mécanique des liens (648 liens / 46 READMEs par #20550, série Lean par #20342, 13/10).

L'énoncé de la règle vit ici ; son exécution vit dans le workflow et le script cités ci-dessus. Toute future évolution modifie les trois ensemble.

## L'organe d'équivalence — rôle post-arbitrage

[`scripts/notebook_tools/check_equivalence.py`](../../scripts/notebook_tools/check_equivalence.py) (livré par #19305) vérifie qu'une **page publiée** porte les sorties textuelles du carnet committé (lignes stream et `text/plain` hors lignes déjà présentes dans les sources, préfixes Lean et entités HTML normalisés). Verdicts : `EQUIVALENT` / `LOST_OUTPUTS` / `MISSING_PAGE` / `UNKNOWN` / `NOTEBOOK_ERROR` / `NOTHING_TO_COMPARE` (aucune ligne comparable — page non vérifiée, **ne pas confondre avec EQUIVALENT**).

Depuis l'abandon, **aucune garde ne le consomme — par design** : il n'y a plus de conversion `.html` à conditionner. Son rôle durable est le **spot-check qualité du site** : vérifier ponctuellement qu'un rendu Pages n'a pas perdu les sorties du carnet (le défaut d'origine de #13025, côté site cette fois).

Contrôles mesurés le 2026-10-15 (issue #19301) :

| Contrôle | Carnet | Verdict | Détail |
|---|---|---|---|
| Positif | `Search/Part1-Foundations/Search-03-Informed-CSharp.ipynb` | `EQUIVALENT` | HTTP 200, toutes les lignes retrouvées |
| Négatif | `MyIA.AI.Notebooks/GradeBook.ipynb` (hors render-list) | `MISSING_PAGE` | HTTP 404 |
| Nuance | `SymbolicAI/Lean/Serre100/08-serre-dans-mathlib-Lean.ipynb` | `NOTHING_TO_COMPARE` | tous les outputs portent `text/html` + `text/plain` : la règle du MIME riche (revue coord c.5994810325) exclut le `text/plain` non rendu — aucune ligne comparable, par construction |

La nuance explique pourquoi le contrôle positif de l'acceptance #19301 (« Serre100/08, EQUIVALENT ») a été délivré sur un carnet à sorties stream : pour un carnet dont tous les outputs ont un MIME riche, l'organe ne compare rien — la mesure manuelle d'équivalence du 05/10 (pré-règle MIME riche) reste la seule preuve pour ce carnet précis.

## Voir aussi

- [#18911](https://github.com/jsboige/CoursIA/issues/18911) — sweep fondateur, décision d'abandon et les quatre gestes
- [scripts-reference.md](scripts-reference.md) — catalogue des scripts (entrée de l'organe)
- `.github/workflows/readme-ipynb-links-guard.yml` — la garde (son en-tête porte l'historique complet)
