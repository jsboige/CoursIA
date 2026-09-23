# SCIENTIFIC_REVIEW_CARD — Template de revue scientifique

**Statut** : template canonique (c.997, refondu #14831 — sign-off user 2026-09-21)
**Usage** : copié/adapté par chaque reviewer qui ajoute une entrée à [scientific-review-registry.md](scientific-review-registry.md)
**Référence scope** : [scientific-review-registry.md §3.2](scientific-review-registry.md#32-portée-de-la-revue)
**Échelle** : [PARCOURS.md — axe 3](../PARCOURS.md#axe-3--scientific_review-revue-scientifique)

> **Quand cette carte se remplit.** À la première appréciation d'un notebook, et
> **chaque fois que le catalogue rend `scientific_review_stale: true`** — c'est-à-dire
> chaque fois que le *code* du notebook a changé depuis la dernière revue. C'est un
> régime d'**audit permanent**, et c'est voulu : une appréciation porte sur ce que le
> notebook calcule, donc elle ne survit pas à un changement de calcul.
>
> Lister ce qui est dû :
> ```bash
> python scripts/audit/check_scientific_review.py --check   # classe STALE_APPRECIATION
> ```

---

## Identification du notebook

- **Chemin relatif** : `MyIA.AI.Notebooks/<serie>/<notebook>.ipynb`
- **Titre** : `<titre du notebook>`
- **Owner logique** : `<po-XXXX ou alias>`
- **Dernière exécution vérifiée** : `<YYYY-MM-DD>`

## Portée de la revue

Cocher la portée effectivement couverte par la PR de revue (cf registre §3.2) :

- [ ] **factual** — corrections factuelles vérifiables (chiffres, dates, noms propres, théorèmes, références bibliographiques)
- [ ] **algo** — corrections algorithmiques (pseudo-code, complexité, structure)
- [ ] **proba** — corrections probabilistes (modèles, axiomes, hypothèses)
- [ ] **demo** — corrections de démonstrations mathématiques ou logiques
- [ ] **correctness** — corrections de bugs d'implémentation (off-by-one, edge case)
- [ ] **full** — toutes dimensions ci-dessus

> **La portée n'est plus ce qui promeut** (#14831). Elle dit *ce que la revue a couvert* ; l'appréciation, elle, se déclare explicitement au verdict ci-dessous. Faire dépendre la grade de la portée ou de l'identité du relecteur mesurait la provenance de la relecture, pas le risque du contenu.

## Constats

Liste des findings significatifs (1 ligne chacun) :

1. `<constat 1 — ex: cell[37] prétendait "réduction 10× speedup" mais commit af9b0cccc mesure 4.2×>`
2. `<constat 2>`
3. ...

## Verdict — l'appréciation de confiance

**Une seule case, et elle demande un argument écrit.** La question n'est pas « qui a
relu ? » mais **« quel risque ce notebook prend-il sur ce qu'il affirme ? »**.

- [ ] **ESTABLISHED** — contenu communément admis et universellement pratiqué. Le
      notebook n'avance rien qui puisse être contesté par un lecteur compétent.
- [ ] **ADVANCED** — protocoles plus avancés, exécutions moins contrôlées, théories
      récentes, interprétations discutables. Le contenu tient, mais il **engage**.
- [ ] **RESEARCH** — recherche active. Le contenu est explicitement en cours
      d'élaboration, et le dire est la seule position honnête.
- [ ] **DEFER** — la revue nécessite une seconde passe. L'entrée n'est pas écrite au
      registre, et le notebook reste `UNASSESSED` : **l'absence de jugement n'est pas
      un mauvais score**, c'est le défaut honnête.

**Justification (obligatoire, 2–5 lignes)** — ce qui fait pencher vers cette classe
plutôt que vers la voisine. Nommer le point le plus contestable du notebook et dire
pourquoi il tombe de ce côté :

```
<justification>
```

> **Ne pas confondre avec `PRODUCTION`.** Cette carte n'accorde aucun passage en
> production. `PRODUCTION` est le tampon du responsable pédagogique — il dit que le
> notebook est finalisé pour être utilisé en cours **par d'autres** — et il vit dans
> [production-scope.md](production-scope.md). L'appréciation scientifique en est une
> condition **nécessaire, jamais suffisante**.

## Ancre de péremption (obligatoire)

Sans ancre, l'appréciation est **immortelle par omission** : elle ne se périmera jamais,
quel que soit le code qui passera ensuite. Le validateur le signale
(`WARN_NO_CODE_ANCHOR`).

```bash
python - <<'EOF'
import json, sys
sys.path.insert(0, "scripts/notebook_tools")
from generate_catalog import code_source_sha
print(code_source_sha(json.load(open("MyIA.AI.Notebooks/<chemin>.ipynb", encoding="utf-8"))))
EOF
```

- **`reviewed_code_sha`** : `<sortie de la commande ci-dessus>`
- **Vérifié contre** : `git rev-parse HEAD` = `<sha>` — l'arbre sur lequel la revue a
  porté. Une revue menée sur une branche mesure autre chose que `main`.

## Preuves (G.1 obligatoires)

- **PR de revue** : `#NNNN` (URL GitHub)
- **Commit de merge** : `<sha 7-char>` vérifié via `git log --grep="#NNNN"`
- **Diff excerpt** (1-3 lignes du diff, cellule touchée + correction) :

```
<extrait verbatim du diff git show>
```

- **Vérification croisée** : `<comment le reviewer a vérifié que la correction est vraie (ex: re-execution, calcul manuel, cross-ref manuel)>`

## Signature du reviewer

- **Reviewer** : `<login GitHub ou email>` — rendu comme **preuve à côté** ; depuis #14831 il ne pilote plus la grade, donc une auto-revue n'est plus disqualifiante, elle est simplement *visible*
- **Date de revue** : `<YYYY-MM-DD>` (ISO 8601)
- **Notes** : `<libre, max 200 chars>`

---

**Note** : ce registre est volontairement plus restrictif que `EDITORIAL_REVIEW_CARD.md` — il exige une preuve de fond technique (algo/proba/demo/correctness), pas seulement pédagogique.

**Et il ne se clôt jamais.** Une carte remplie vaut pour l'état du code qu'elle ancre, pas pour le notebook à perpétuité. C'est la différence entre un audit ponctuel — qui vieillit en silence — et un régime permanent, qui se redéclare lui-même à chaque fois que le calcul change.
