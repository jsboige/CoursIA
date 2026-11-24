# Renumerotation de notebooks — corpus des precedents

> REFERENCE — vivante — dernière révision 2026-11-16

Detail de [`.claude/rules/notebook-accretion-numbering.md`](../../.claude/rules/notebook-accretion-numbering.md). La regle porte le geste ; ce fichier porte les precedents qui l'ont produite, mesures le 2026-09-04.

## 1. Pourquoi une regle : le geste a ete re-derive dix-neuf fois

Le geste `renum()` / `reclass()` a une histoire dense et aucune trace de protocole. Chaque issue a re-decouvert, seule, les memes questions : quel est le parent pedagogique, quels referents cassent, dans quel ordre renommer. Le tableau ci-dessous en porte **dix-neuf** : seize verdicts rendus, trois issues encore ouvertes (#13755, #13769, #14545) ou la question est posee sans etre tranchee.

| Issue | Famille | Verdict |
|---|---|---|
| #5637 | Probas/Infer | renum narrative — arc pedagogique, blast-radius borne |
| #5666 | Search | arc global canonique **mais** `Search-11` = collision reelle (6 nb, 2 traitements C#, split EN/FR) |
| #5656 | GameTheory | **aucune renum** — arc 1..17 canonique, suffixes `b`/`c` intentionnels |
| #5662 | Sudoku | **aucune renum** — arc 0..19 canonique, twin C#/Python intentionnel |
| #5667 | Search | **aucune renum** — prefixe par famille intentionnel (4 familles algorithmiques) |
| #5669 | SemanticWeb | **aucune renum** — prefixe `SW-` + suffixe `b` canoniques |
| #13753 | Probas/Infer | `Infer-6-Debugging` → accretion transversale (`Infer-2b` candidat) |
| #13754 | Search/Apps | `App-12` Connect Four → rattache au traitement canonique `App-14` |
| #13757 | GenAI/Video | `04-6` → `04-5b` |
| #13758 | GenAI/Image | Qwen Image Edit 2509 → rattache au palier `01-5` |
| #13761 | Lean | TorchLean Python → companion `Lean-11b` |
| #13762 | Planners | `Planners-14` LLM Space Reducer → side de 10 ou 12 |
| #13765 | Z3 | `Z3-Python-07` style declaratif LINQ → side |
| #13770 | Search | `Part3-Advanced` → accretions `Search-03b/03c/03d` |
| #13771 | Search | deux `Search-17` + `Search-18` → `09b`/`09c`/`11c` |
| #13822 | ICT | SAE-Calibration / SAE-Catastrophes → `ICT-21b` / `ICT-21c` |
| #13755 | QC-Py Cloud | **ouverte** — six collisions de concepts `Cloud-01`..`Cloud-06` |
| #13769 | Search | **ouverte** — fusionner la recherche avancee, rendre CSP autonome |
| #14545 | Search | **ouverte** — padding zero, ordre lexicographique casse |

## 2. Le verdict par defaut, et sa nuance

Quatre familles sur les six analysees sous #5081 ont conclu **aucune renumerotation**. C'est le fait le plus important du corpus : la numerotation du depot est majoritairement **saine**, et un agent qui aborde une famille en supposant le contraire fabrique du travail.

**La nuance est dans le grain.** #5667 (Search) conclut « aucune renum » pour la famille — et #5666, sur la **meme** famille, etablit que `Search-11` porte une collision reelle qui, elle, justifie le geste. Les deux verdicts sont justes : **le verdict se pose par branche, pas par famille.** Un « la famille est saine » ne dispense pas d'examiner une branche nommement suspecte, et un defaut sur une branche ne condamne pas la famille.

## 3. Le blast-radius reel : la grappe Probas

Le cas le plus instructif du depot. Une renumerotation narrative de la lane Infer.NET (#5637) a produit **cinq PRs**, dont quatre en aval du renommage lui-meme :

| PR | Ce qu'elle repare |
|---|---|
| #5807 | la renum elle-meme — cycle 5, 7, 9, 11, 14 |
| #5856 | le **miroir PyMC** : 12 deplacements pour restaurer la parite avec Infer (#4956) |
| #5849 | resync du **README** Probas apres la renum |
| #6471 | **derive de prose** : « Debugging is Infer-6 not 13 » — un libelle survivant dans le texte |
| #5846 | re-seed du **CSV de traduction** (#4957 Phase 2) |

Deux lecons s'en degagent, toutes deux ecrites dans la regle :

1. **La serie jumelle bouge aussi.** Renumeroter Infer sans PyMC casse une parite qui etait le produit d'un travail anterieur. Toute famille a twin (C#/Python, FR/EN, Infer/PyMC) double le mapping.
2. **La prose survit au renommage.** #6471 est exactement la classe de defaut que les quatre gardes de liens historiques ne voient pas : la cible existe, le lien fonctionne, et le texte nomme le mauvais numero. C'est ce qui a motive `check_link_label_agreement.py` (#14624).

## 4. Les residus, et l'ordre dans lequel ils apparaissent

Un renommage propage dans cinq surfaces de liens (table dans la regle) plus deux artefacts derives :

- **`pedagogy_density_baseline.json`** — les cles sont des chemins. La campagne de renum y a laisse **48 cles orphelines**, et aucun refresh automatique n'existait (#13815, ferme par l'organe `--check-orphans` de #13826).
- **Liste de rendu Quarto** — #13931 a du regenerer la liste apres le rename #13823, avec « residu ICT-21b/21c + drift accumule ». Le residu s'accumule silencieusement : il ne casse rien de visible tant qu'on ne regenere pas.

L'ordre observe est stable : le rename passe, puis les liens 404 sautent (visibles), puis les libelles mentent (invisibles), puis les artefacts derives divergent (invisibles jusqu'a la prochaine regeneration).

## 5. Etat mesure de l'arbre (2026-09-04)

Commande de mesure (a re-executer plutot qu'a recopier) :

```bash
python - <<'PY'
import re, collections
from pathlib import Path
ID = re.compile(r"^(?P<pre>.+?)[-_](?P<num>\d{1,3})(?P<let>[a-z])?[-_]", re.I)
fam = collections.defaultdict(lambda: collections.defaultdict(set))
for p in Path("MyIA.AI.Notebooks").rglob("*.ipynb"):
    s = str(p).replace("\\", "/")
    if "_archive" in s or ".ipynb_checkpoints" in s or "/.lake/" in s:
        continue
    m = ID.match(p.name)
    if m:
        fam[m.group("pre").lower()][int(m.group("num"))].add((m.group("let") or "").lower())
for f, nums in sorted(fam.items()):
    for n, lets in sorted(nums.items()):
        real = sorted(x for x in lets if x)
        if real and max(real) >= "g":
            print(f"{f}-{n}: {''.join(real)} ({len(lets)} slots)")
PY
```

| Mesure | Valeur |
|---|---:|
| Notebooks portant un identifiant | 814 |
| Familles | 34 |
| Branches numerotees | 494 |
| Branches **sans accretion** (speed-run canonique) | 411 |
| Branches accretees | 83 |
| … dont premiere accretion = `b` (convention) | 80 |
| … dont deviantes | 3 |
| Branches depassant la norme `e`-`f` | 3 |

Les trois deviations de convention et les trois depassements de norme **ne sont pas les memes ensembles** : `Tweety-7` devie (pas de base) sans depasser la norme, `ICT-15` depasse la norme sans devier de la convention. Deux mesures, deux chantiers.

## 6. Ce que la mesure dit du speed-run

411 branches canoniques. La cible enoncee par le user pour le parcours canonique est « plutot autour des 500 notebooks max, peut-etre moins » — le **nombre de slots canoniques y est deja**, ce qui deplace la question. Ce qui reste a faire n'est pas d'elaguer massivement mais :

1. de rendre le speed-run **lisible** (une branche sans base — `Lean-16`, `Tweety-7` — n'a aucune entree canonique, donc trouee dans le parcours) ;
2. de ramener les trois branches sur-etendues sous la norme par **fusion**, pas par suppression ;
3. de verifier que les numeros nus, lus dans l'ordre, forment bien un arc — c'est le travail que #5081 a fait par famille et que le compilateur de parcours de #14620 consomme.

Le compte de **notebooks** reste superieur au compte de **slots** (twins C#/Python, siblings FR/EN partagent un slot) : les deux ne se comparent pas directement.

## 7. La descente en sous-serie et la doctrine du cheminement (2026-11-15)

Le §4ter de la regle porte trois conventions. Le mainteneur les a acceptees le 2026-11-15 (« OK pour les 3 », question Q191 du registre), sur la serie ICT (#20298, arbitrage c.6902930137). Elles completent une decision plus ancienne, du 2026-09-25 (Q57) : une sous-serie qui descend en dossier laisse dans la serie mere un escalier, idealement un capstone a la racine qui la presente.

**Pourquoi la decision de septembre ne suffisait pas.** La descente ANALYSE de la serie Lean (#18015) a ete mergee sans capstone. Lean-20 a disparu de la racine, et le trou n'a ete vu qu'en preparant une presentation ; il a fallu le reparer apres coup (#18409). Aucune garde ne voit un carnet qui aurait du etre dans le diff. En novembre, ICT a montre le meme defaut a plus grande echelle :
- des sous-series sont descendues sans capstone ;
- des trous se sont ouverts a la racine ;
- des numeros eleves, ajoutes a la fin, ne sont jamais redescendus.

**La doctrine, en citation** (2026-11-15) :

> Le principe reste celui de numéros complétés par des accrétions, et éventuellement remplacés par un capstone une fois que trop d'accrétions rendent la lecture difficile, la série historique descendant le cas échéant en sous-série. La plupart des numéros élevés doivent redescendre dans les accrétions des numéros qui introduisent leur substrat/strate/mesure ou objet d'intérêt, car ils ont été rajoutés à la fin par défaut.
> Les carnets sans numéros devraient également en recevoir un ou rentrer dans une sous-série et être référencés ou consolidés dans les capstones numérotés. La numérotation est celle de la lecture d'un cheminement intellectuel.

**Ce que la doctrine change dans la lecture du §3.** Le §3 garde son verdict par defaut, et des trous seuls ne justifient toujours rien. Mais dans une serie dont les premiers numeros suivent une montee (ICT : les trente premiers suivent la montee en strates), un numero eleve qui ne fait qu'ajouter un concept est presque toujours un numero d'opportunite : sa place se lit dans le contenu, au numero qui introduit son objet.

**Instance ICT (contenu, pas regle).** Le mainteneur fait de GOL le substrat temoin de la strate 0 : il est Turing-complet, et ses formes utiles se detruisent a la moindre variation. Trois blocs sont a regrouper en accretions et en sous-series :
- les representations internes des LLM ;
- Argumentation (strate 6) ;
- Freebits, mecanismes sociaux et metamecanismes (strate 7).

La carte cible, carnet par carnet, vit dans le body de #20298.
