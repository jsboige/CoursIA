# Cure des accents FR & défense contre les régressions — #2876

Référence consolidée du registre [#2876](https://github.com/jsboige/CoursIA/issues/2876) : restauration des accents français dans les notebooks pédagogiques **ET** défense contre les 4 classes de défauts qu'une cure mal bornée introduit. Issue du travail convergent du cluster (cycles ~600-617, juil. 2026) — cette doc remplace la connaissance éparpillée dans les mémoires de session et le dashboard éphémère.

## Périmètre — markdown-only STRICT

**Décision actée (ai-01, 17/07/2026)** : la cure des accents s'applique **uniquement au markdown** des notebooks (`cell_type == "markdown"`, clé `source`). Sont **HORS scope** :

- **Identifiants de code** (variables, paramètres, propriétés, noms de fonctions) — dans toute cellule.
- **Commentaires de code** (`//`, `#`, `--`) — la cure ne doit pas les accentuer, même si le stripped form y apparaît.
- **stdout / string-literals** affichés dans les `outputs` — HorS scope par construction.
- **Cibles de liens markdown** `](…)` — doivent rester **non accentuées** (le fichier sur disque l'est). Seuls le **texte d'affichage** et la **prose** sont accentués.

Une zone grise (commentaire qui ressemble à de la prose, stdout qui contient un mot accentable) est **laissée inchangée** par défaut : ne pas toucher vaut mieux que risquer une régression. Le critère de sortie est la **défense-par-construction** (l'outil ne peut pas produire le défaut), pas la défense-par-revue.

## Les 5 classes de défauts

Une cure d'accents qui se contente de « remettre les accents » sans bornes strictes introduit 5 défauts distincts, chacun avec sa propre classe de détection :

### 1. Accent-stripping (le défaut initial)
Les notebooks pédagogiques FR ont perdu leurs accents (`systeme` au lieu de `système`) par traitement historique. **Cible** de la cure. Détecteur historique : `detect_accent_stripping.py` (dictionnaire conservateur `ACCENT_PAIRS` — le stripped form n'est pas un mot FR valide, donc non-ambigu : `a`/`ou`/`la`/`complete` exclus).

### 2. Identifier-over-reach (régression de cure)
Une cure trop large **accentue un identifiant de code** (`resultat` → `résultat`, `preference` → `préférence`) — casse le code. Détecteur : `check_identifier_regression.py` (PR #7157, **MERGÉ**, gate CI actif). Méthode : `_STRIP_RE` retire commentaires + chaînes (Python/C#/F#/Lean/Lisp) avant comparaison, puis compare identifiants base(main) vs head(branche).

### 3. Caps-regression (régression de cure)
Une cure accentue correctement le mot **MAIS minuscule l'initiale capitalisée** (ou tout-caps). Contextes positionnels où la capitale est obligatoire : `# Système` (H1), `## Modèle` (H2), `| **Équipes** |` (header table), `Après chaque match` (début phrase), `PARAMÈTRES` (all-caps). Détecteurs : `check_caps_regression.py` (PR #7197) ou `detect_caps_regression.py` (PR #7198) — les deux en revue, arbitrage ai-01 en cours. **Clé anti-faux-positif** : scan **line-aligned positionnel** (comparer la MÊME `(cell_index, line_index)`), jamais scan non-positionnel — un mot FR apparaît souvent en cap (titre) ligne 0 ET en lower (prose) ligne 1 ; curer le lower légitime ne doit pas être flaggué.

### 4. Blank-line collapse (régression de cure, structurelle)
Une cure dont le path `list-source` fait `join → split → re-chunk` **absorbe le chunk standalone `\n`** (séparateur de paragraphe nbformat) → collapse `\n\n` → `\n`. Les paragraph breaks markdown disparaissent. Non couvert par les 3 bright-lines « contenu » (code/outputs/liens/ec). **Fix** : cure **per-chunk in-place** (split le chunk en lignes, cure chaque ligne, rejoinde — jamais de concaténation cross-chunk).

### 5. Link-target regression (régression de cure, fonctionnelle — la + grave)

Une cure accente le **nom de fichier** à l'intérieur d'une cible de lien markdown `](Infer-10-Model-Selection.ipynb)` devient `](Infer-10-Model-sélection.ipynb)`. Le fichier pointé **n'existe pas** (le vrai fichier sur disque garde sa capitale non accentuée) → **lien cassé 404**. C'est le défaut fonctionnellement le plus grave (le lecteur clique → page introuvable), et il a été le **3e angle-mort découvert** : les gates identifiants (#7157, code-only) et caps (#7197/#7198, prose positionnelle) ne scannent **pas** les cibles de liens. Détecteur : `detect_link_target_regression.py` (PR #7210). **Incident firsthand** : #7196 Infer-18 portait 4 cibles cassées (`Infer-10-Model-sélection.ipynb` cells 0/12/14/22) — confirmé `git ls-tree origin/main` (fichier réel = `Infer-10-Model-Selection.ipynb`, capitale S). La cure canonique #7186 le couvre by construction (`_LINK_TARGET_RE` masque les cibles avant cure).

## Defense-in-depth — 4 rôles d'outils

La sortie du whack-a-mole #2876 repose sur 4 rôles complémentaires (un outil couvre **UNE** classe de défaut — ne pas assumer qu'il les couvre toutes) :

| Rôle | Outil | Classe couverte | Statut |
|------|-------|-----------------|--------|
| **CURE** (defense-by-construction) | `restore_accents_canonical.py` | Applique les accents en préservant casse + structure + cibles de liens | PR #7186 (revue, merge-ready après fix blank-line commit `a88090ad1`) |
| **GATE identifiants** | `check_identifier_regression.py` | Identifier-over-reach (code) | PR #7157 **MERGÉ** |
| **GATE caps** | `check_caps_regression.py` / `detect_caps_regression.py` | Caps-regression (markdown prose) | PR #7197 / #7198 (revue, arbitrage ai-01 ; #7198 subsume #7197, 41 tests) |
| **GATE link-targets** | `detect_link_target_regression.py` | Link-target regression (cibles de liens `](…)`) | PR #7210 (revue, firsthand-validé 17/17 tests) |

**Workflow recommandé** pour une PR d'accents : générer la cure via `restore_accents_canonical.py` (passe les gates par construction), puis les gates #7157 (identifiants) + caps + #7210 (link-targets) confirment. Ne **jamais** générer une cure via un script ad-hoc — c'était la cause racine de chaque régression #2876 répétée.

## Les bright-lines (vérifiées by construction)

Une cure canonique DOIT satisfaire ces 5 propriétés — les 4 premières sont « contenu », la 5e est « structure » :

1. **Markdown-only** : `if cell_type != 'markdown': continue`. Code (identifiants/commentaires/stdout) intouché.
2. **Cibles de liens masquées** : `]( … )` masqué avant cure, restauré après — la cible reste non accentuée.
3. **Skip code** : conséquence de 1.
4. **Outputs intacts** : seule la clé `source` des cellules markdown est réécrite ; `outputs`/`execution_count`/`metadata` intacts → diff accents-only, pas de delta de ré-exécution.
5. **Structure préservée** (la bright-line oubliée) : paragraph breaks `\n\n` préservés, chunk-count source-list inchangé, standalone blank-line chunks `\n` non absorbés. À comparer comptage base vs cured **par cellule**.

Une revue « VALIDATED » n'est valide **que sur les axes vérifiés**. Les 4 bright-lines contenu ne couvrent PAS la structure markdown — une revue de cure DOIT explicitement vérifier (a) la préservation des paragraph breaks ET (b) l'absence de cibles de liens accentuées (sinon, angle-mort, cf § Leçons). La saga a vu 3 angles-morts découverts successivement (blank-lines → caps → link-targets) : un reviewer qui ne liste pas EXPLICITEMENT chaque axe vérifié reproduit le pattern.

## Méthodologie — 3 axes forensiques obligatoires

Trois pièges méthodologiques ont produit de faux verdicts pendant la saga :

- **Line-aligned positionnel** : comparer `base[(cell, line)]` vs `head[(cell, line)]`. Un scan non-positionnel (« le mot apparaît-il en cap quelque part ? ») génère des faux positifs ET des faux négatifs.
- **Lowercase APRÈS deaccent** lors de la comparaison de deux formes du « même » mot. Une fonction `deaccent()` qui préserve la casse (`da('Systeme')='Systeme'`, `da('système')='systeme'`) fait échouer la précondition `da(head)==da(base)` pour toute paire différant par la casse → faux négatif systémique → verdict « 0 régression » artefactuel. Correct : `deaccent(head).lower() == base.lower()`.
- **Cibles de liens scannées séparément** : extraire les spans `](…)` AVANT toute comparaison de mots (regex `_LINK_TARGET_RE`), vérifier qu'aucune cible n'a été accentuée (`git ls-tree origin/main` confirme le vrai nom de fichier). Un scan caps-only ou identifiant-only est **aveugle** aux cibles de liens — c'est le 3e angle-mort (découvert po-2024 c.635, confirmé po-2023 c.614).

## Leçons durables

- **Une rétractation est un claim comme un autre** (G.1). Re-vérifier firsthand avant d'agir sur une rétractation — une sur-correction (alerte trop large → rétractation trop large dans l'autre sens) est aussi fausse que l'alerte initiale. Un 3e worker firsthand est l'arbitre. Incident : triple-correction c.610 (alerte) → c.611 (rétractation) → c.611b (re-rétractation).
- **Angle-mort structure** (G.9). 2 cycles de suite avec verdict antérieur incomplet = discipline forensic à durcir : lister EXPLICITEMENT propriétés vérifiées vs assumées. Un détecteur/outil couvre UNE classe de défaut ; ne pas assumer qu'il couvre TOUTES.
- **Defense-by-construction > defense-by-revue**. La sortie du whack-a-mole vient de ce que la cure ne PEUT PAS produire les défauts (bornes dans le code), pas de ce qu'une revue les attrape après coup.

## Voir aussi

- [scripts-reference.md](scripts-reference.md) — catalogue des scripts `scripts/notebook_tools/` (dont les outils ci-dessus)
- [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) §D — preuve d'exécution notebook, diff ne supprimant pas de cellules `# Solution`
- [anti-regression.md](../../.claude/rules/anti-regression.md) — ne pas stripper le code réel (la cure markdown-only est conforme, pas une régression)
- Issue [#2876](https://github.com/jsboige/CoursIA/issues/2876) — registre source, discussion du périmètre
