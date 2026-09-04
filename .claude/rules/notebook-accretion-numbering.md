# Renumerotation et reclassement de notebooks — `renum()` / `reclass()`

S'applique a **tout agent** qui envisage de renommer, renumeroter ou requalifier un notebook pedagogique, **et a tout reviewer** d'une PR `renum(...)` / `reclass(...)`. Source : convention d'accretion posee par le user, sign-off du 2026-09-04. Le geste avait ete re-derive a la main sur ~15 issues sans jamais etre ecrit ; c'est ce cout repete que cette regle ferme.

**Detail** (corpus des precedents, verdicts par famille, tables de mapping, residus) : [notebook-renumbering-detail.md](../../docs/reference/notebook-renumbering-detail.md).

## 1. Le fait qui gouverne : le canonique est ce qui n'a PAS de lettre

Convention de nommage : `<Prefixe>-<num><lettre?>-<Titre>.ipynb` — **la lettre est collee au numero**, sans separateur.

```python
ID_IN_NAME_RE = re.compile(r"^(?P<pre>.+?)[-_](?P<num>\d{1,3})(?P<let>[a-z])?[-_]", re.I)
```

**Lire les numeros nus dans l'ordre EST le parcours canonique** — le speed-run du programme par les grands principes. Une lettre dit « ceci approfondit », jamais « ceci prolonge le survol ». Poser une lettre est donc un acte **pedagogique**, pas un acte de rangement : c'est declarer qu'un contenu sort du chemin principal.

Mesure du 2026-09-04 (`MyIA.AI.Notebooks/**/*.ipynb`, hors `_archive`/checkpoints/`.lake`) :

| | N |
|---|---:|
| Notebooks portant un identifiant | 814 |
| Familles | 34 |
| Branches numerotees | 494 |
| … **sans accretion = le speed-run canonique** | **411** |
| … accretees | 83 |

## 2. La convention se constate, elle ne se decrete pas : la base compte comme `a`

Sur les 83 branches accretees, **80 commencent a `b`**. La base sans lettre occupe donc la place de `a`, et la premiere accretion est `b`. Trois branches s'en ecartent — ce sont des **defauts**, pas des variantes :

| Branche | Ecart | Etat |
|---|---|---|
| `GameTheory-03` | base presente **et** premiere accretion `a` (`a`..`h`) | a normaliser en `b`..`i`, ou fusionner (cf §4) |
| `Lean-16` | **aucune base** — la branche Conway commence a `16a` (`a`..`j`) | pas d'entree canonique du tout : la branche entiere est hors speed-run |
| `Tweety-7` | **aucune base** (`a`, `b`) | idem, blast-radius reduit |

Un `renum()` ne cree jamais une quatrieme convention. Si la branche visee est l'une de ces trois, la traiter **dans la meme tranche** ou dire explicitement pourquoi on ne le fait pas.

## 3. Le verdict par defaut est « aucune renum » (HARD)

Quatre analyses de famille sous #5081 ont conclu **aucune renumerotation** : #5656 (GameTheory, arc 1..17 canonique + suffixes intentionnels), #5662 (Sudoku, arc 0..19 + twin C#/Python intentionnel), #5667 (Search, prefixe par famille intentionnel), #5669 (SemanticWeb, `SW-` + suffixe `b` canoniques). **Une numerotation qui *parait* opportuniste est le plus souvent un arc.**

Des trous dans la suite des numeros ne justifient **rien**. Le geste ne se declenche que sur l'un de ces quatre tells, **nomme dans l'issue** :

| Tell | Ce qui le prouve | Precedent |
|---|---|---|
| **Collision d'identifiant** | deux fichiers portent le meme `<prefixe>-<num><lettre>` | #13771 (deux `Search-17`, merges a 8 h 23 d'intervalle) |
| **Faux prerequis sequentiel** | la position implique un prerequis que le contenu dement | #13770 (`Part3` declare Search-3 en prerequis, donc ne suit pas CSP) |
| **Numero d'opportunite** | l'historique montre un numero choisi sur la disponibilite du slot | #13771 (concu 15, puis 17, puis 18) |
| **Transversal en position canonique** | outillage/debug/diagnostic occupant un slot du survol | #13753 (`Infer-6-Debugging`) |

Le tell se lit **dans le contenu et l'historique**, jamais dans le titre seul.

## 4. Norme de profondeur : `e`-`f` au maximum par branche

Une branche s'epaissit legitimement — c'est ainsi que les series grandissent. Ce qui ne va pas, c'est qu'elle **s'etende** : au-dela de `f`, les accretions doivent **fusionner en notebooks plus lourds** plutot que se multiplier en lettres.

Mesure du 2026-09-04 : **80 des 83 branches accretees tiennent la norme** (≤ 4 accretions). Exactement trois la depassent — c'est la surface entiere du chantier, pas une campagne :

| Branche | Lettres | Notebooks |
|---|---|---:|
| `ICT-15` | `b`..`l` | 12 |
| `Lean-16` | `a`..`j` | 10 |
| `GameTheory-03` | `a`..`h` | 9 |

Fusionner **n'est pas supprimer** : « Consolider != Archiver » s'applique integralement — chaque contenu absorbe est preserve et cite, ligne a ligne, dans le notebook cible.

## 5. Protocole (HARD, l'ordre compte)

1. **Lire le contenu**, pas les titres. Un mapping derive de titres et de volumes est une hypothese : l'annoncer comme telle.
2. **Nommer le parent pedagogique et l'argument** : pourquoi ce notebook approfondit *ce* palier. Sans cet argument ecrit, pas de lettre.
3. **Garde de collision** — L898 (`git worktree list`, `gh pr list --search head:`, PRs ouvertes sur le **chemin**) **et** L1356 (`--state all` : une PR **mergee** en rider rend le grain deja livre).
4. **Gate de sequencement** : ne pas renommer un fichier pendant qu'une PR ouverte le touche. Le nommer dans l'issue (precedent #13771, gate sur #13576 et #12703).
5. **Table de mapping dans l'issue, avant la PR** — `actuel -> cible`, une ligne par fichier.
6. **`git mv`** : l'identite du fichier est preservee. **Aucun changement de contenu dans la meme PR** — un renommage et un enrichissement ne se relisent pas ensemble.
7. **Sweep des referents** — §6 ci-dessous.
8. **Catalogue non touche a la main** ([catalog-pr-hygiene.md](catalog-pr-hygiene.md)) : il appartient a l'automatisation.

## 6. Ce qu'une renum casse — et l'organe qui le rattrape

Le sweep n'est pas « chercher l'ancien nom ». Cinq surfaces cassent, et elles ont chacune leur organe :

| Surface | Organe |
|---|---|
| Liens 404 dans les notebooks | `scripts/notebook_tools/check_notebook_navlinks.py` |
| Liens 404 dans la doc | `scripts/check_docs_links.py` |
| Accents perdus dans les cibles | `scripts/notebook_tools/detect_link_target_regression.py` |
| Rendu des liens de README de serie | `scripts/notebook_tools/check_notebook_link_render.py` |
| **Libelle qui ment sur sa cible** | `scripts/notebook_tools/check_link_label_agreement.py` — **livre par la PR #14625, pas encore sur `main`** (#14624) |

**La cinquieme est celle que le sweep rate**, et c'est la sequelle propre a la renumerotation : les quatre premiers organes verifient que la cible **existe**, aucun ne verifie que le **libelle dit la verite**. Un `[Search-12](.../Search-03b-....ipynb)` passe les quatre. Mesure du 2026-09-04 : **32 desaccords sur 2194 fichiers**, dont la sequelle directe de #13770.

Deux residus supplementaires se traitent dans la meme tranche : les cles orphelines de `pedagogy_density_baseline.json` (#13815) et la liste de rendu Quarto (#13931).

## 7. Ce que la regle ne couvre pas

- **Le padding zero** (`Search-3` vs `GameTheory-03`, ordre lexicographique casse) — chantier propre, **#14545**.
- **Le suffixe de langage** des twins C#/Python — **#12933**.
- **La numerotation des en-tetes markdown *dans* un notebook** (`## 3.`) — [notebook-conventions.md](notebook-conventions.md).

## Voir aussi

- [notebook-renumbering-detail.md](../../docs/reference/notebook-renumbering-detail.md) — corpus des precedents, verdicts par famille, residus
- [notebook-conventions.md](notebook-conventions.md) — C.1/C.2/C.3, numerotation des en-tetes
- [catalog-pr-hygiene.md](catalog-pr-hygiene.md) — le catalogue appartient a l'automatisation
- [proactive-coordination.md](proactive-coordination.md) — L898 (garde de collision), L1356 (`--state all`)
- [verify-before-claiming.md](verify-before-claiming.md) — lire l'artefact et l'historique, pas le body date
- **#5081** — EPIC fondateur de l'analyse par famille · **#12375** — doctrine d'application · **#13769**, **#13755**, **#14545** — chantiers ouverts
