# Deploiement JupyterLite du lot Python (pli 2.2 de l'Epic #27543)

Ce document decrit le deploiement du lot de carnets Python **executes dans le
navigateur** (noyau Pyodide) sous `/jupyterlite/` du site Quarto publie.

Il ne decrit pas le critere d'eligibilite (pli 2.1) : celui-ci vit dans
[pyodide-eligibilite.md](pyodide-eligibilite.md), et son code dans
`scripts/notebook_tools/pyodide_eligibility.py`. Ici, le critere est une
**source de verite** dont on se sert, pas une regle reecrite.

## La chaine

| Etape | Qui | Ou |
|---|---|---|
| Critere d'eligibilite (pli 2.1) | `pyodide_eligibility.py` + `pyodide_eligibility_report.py` | `docs/reference/pyodide-eligibilite.md` |
| Selection du lot | `select_lot()` -- une serie par tour, series par ordre alphabetique, preference aux carnets sans roue pure a installer puis sans lecture de fichier du depot | meme module |
| Construction du site | `scripts/notebook_tools/build_jupyterlite_site.py` | ce document |
| Deploiement | job `build-jupyterlite` de `.github/workflows/quarto-pages-deploy.yml` | ce document |
| Garde post-deploiement | `scripts/ci/check_jupyterlite_lot.py`, joue par `site-links-post-deploy.yml` | ce document |

**Le lot n'est jamais une liste tenue a la main.** Il est recalcule a chaque
construction par le critere du pli 2.1. Un carnet qui devient ineligible
sort du lot a la construction suivante ; un carnet qui devient eligible y
entre. Le seul artefact fige est le **manifeste**, produit par la
construction -- et il est verifie sur le site publie, jamais dans le depot.

## Ce que publie la construction

1. **Le lot** : jusqu'a huit carnets eligibles, un par serie, choisis par
   `select_lot()`, puis **filtres par la regle de suffisance** (voir
   « La suffisance filtre le lot ») : un carnet dont les dependances ne sont
   pas dans la distribution n'est pas publie.
2. **Le site JupyterLite** : les carnets sont poses dans `files/` (le
   repertoire de contenus de JupyterLite) **par nom de fichier**, comme le
   site mesure au pli 2.1 (`?path=<fichier>.ipynb`). Deux carnets de series
   differentes qui porteraient le meme nom font echouer la construction :
   on ne publie pas l'un des deux sous le nom de l'autre.
3. **Les modules locaux de la serie** que le carnet importe, poses a plat a
   cote de lui (voir « Les modules locaux voyagent avec le carnet »).
4. **Le manifeste** (`manifest.json`, a la racine du site construit) : pour
   chaque carnet, son chemin dans le depot, sa serie, ses deux URLs
   publiques -- `files` (carnet brut) et `lab` (ouverture et execution) --
   et les modules locaux embarques avec lui. Il porte aussi la liste des
   **refus** et le nombre de candidats.

Quatre verifications ne laissent pas passer un site faux :

- le repertoire de contenus est **remis a zero** avant la pose et avant la
  construction (un reste de construction anterieure ne doit pas rester en
  ligne) ;
- apres la construction, le site est compare au lot : **ni carnet manquant,
  ni carnet en trop** -- l'ecart fait echouer la construction ;
- chaque module local embarque est present dans le site construit ;
- le manifeste est ecrit **sans BOM** (le garde post-deploiement le lit).

## La suffisance filtre le lot

Le critere d'eligibilite (pli 2.1) classe un module de la serie comme
*embarquable* : ce n'est pas un motif de refus du carnet. Mais le bundle
**publie des fichiers et n'installe rien** -- une dependance d'un module
local embarque doit donc faire partie de la **distribution** Pyodide (le
verrou `pyodide-lock.json`), et non etre une roue pure que le carnet
installerait lui-meme.

Le deploiement applique donc la regle de suffisance **du critere** (pli 2.1,
`scripts/notebook_tools/pyodide_suffisance.py`) : il l'**importe**, il ne la
reecrit pas. Pour chaque candidat du lot, la regle resout

1. les imports **du carnet lui-meme** ;
2. puis ceux des **modules locaux** que le carnet importe, recursivement.

Un import n'est satisfait que s'il est :

- dans la **stdlib** ;
- dans la **distribution** Pyodide (le verrou `pyodide-lock.json`) ;
- **installe par le carnet lui-meme** (`micropip.install`, `%pip install`,
  `!pip install` -- la regle lit ces appels dans les sources) ;
- fourni par un **module local** que le carnet embarque (et dont les
  dependances sont, elles aussi, satisfaites) ;
- un module **d'une autre serie** : refuse, car le bundle ne livre que la
  serie du carnet (`module hors serie non livre par le bundle`).

**L'ecart entre le critere et ce que le bundle livre est ferme** (#27583) :
la condition 4 du critere est desormais « tous les imports **satisfaits par
le bundle** ». Le deploiement n'ajoute plus de regle -- il en herite, et pose
les modules locaux que le critere declare embarquables.

Consequence mesuree : le lot passe de **sept carnets publies sur huit
candidats** a **huit sur huit**. Le huitieme candidat n'est plus
`Causalite-06-DoWhy-Instrument-Faible-Python.ipynb` (ecarte pour
`dowhy_iv_organs -> dowhy : absent de la distribution`) : le critere ne le
selectionne plus, donc le slot Causalite est pris par
`Causalite-00-Echelle-de-Pearl-Intro-Python.ipynb`, dont les dependances
sont satisfaites.

Le decompte de l'ecart est produit par l'organe, sur la population que le
critere acceptait avant l'alignement ; les valeurs chiffrees sont dans le
rapport de l'organe, pas dans cette prose. Les comptes que ce document
portait venaient d'une **mesure a la main** : ils ne se reproduisent pas
avec le lock et le cache commites. La regle du deploiement, rejouee sur la
meme population, rend les memes comptes que l'organe -- il n'y a plus qu'un
seul chiffre, produit par un seul code.

## Les modules locaux voyagent avec le carnet

Le critere d'eligibilite (pli 2.1) considere qu'un module Python **de la
serie** du carnet est *embarquable* dans le bundle JupyterLite : ce n'est
pas un motif de refus. Le deploiement doit donc l'embarquer pour de vrai.

Mesure (premiere passe d'execution du lot) : le carnet
`Causalite-06-DoWhy-Instrument-Faible-Python.ipynb` echoue a l'import en
navigation --

```text
ModuleNotFoundError: No module named 'dowhy_iv_organs'
```

-- parce que le carnet cherche son organe de serie
(`dowhy_iv_organs.py`, a cote de lui dans le depot) et que la pose a plat
ne l'avait pas embarque. La construction le pose desormais, au meme niveau
que le carnet, ce qui laisse au carnet sa propre decouverte (`sys.path`
sur le dossier du module trouve).

Un module homonyme fourni par deux series du lot fait echouer la
construction, comme pour les carnets : on ne publie pas l'un des deux sous
le nom de l'autre.

## Construction locale

```bash
# environnement : jupyterlite-core et le noyau Pyodide, versions egales
python -m pip install "jupyterlite-core==0.8.7" "jupyterlite-pyodide-kernel==0.8.7"

python scripts/notebook_tools/build_jupyterlite_site.py \
  --repo . \
  --taille 8 \
  --source-dir .tmp/jlite/site \
  --output-dir .tmp/jlite/site/_output \
  --base-url /CoursIA
```

Le script recalcule le lot, pose les carnets, lance `jupyter lite build`,
verifie le contenu publie et ecrit le manifeste. Options utiles :

- `--sans-build` : pose et manifeste sans construire (diagnostic) ;
- `--probe-pypi` : sonde PyPI pour les paquets absents du lock (reseau ; sans
  ce drapeau, aucun acces reseau n'est fait) ;
- `--base-url` : prefixe du site publie. En local, `/CoursIA` reproduit le
  chemin de Pages (`https://jsboige.github.io/CoursIA/`). La construction
  **refuse** un prefixe qui n'est pas une URL d'origine-racine : sous Git
  Bash, `/CoursIA` est converti en chemin Windows
  (`C:/Program Files/Git/CoursIA`), et le manifeste porterait alors des URL
  de liens morts que le garde rapporterait comme casses, pour une cause
  etrangere au lot. Sous Git Bash, passer le prefixe via
  `MSYS_NO_PATHCONV=1`.

Un point qui a cout une construction : **`--lite-dir` est explicite** dans la
ligne de commande. Sans lui, la construction prend le repertoire courant
comme racine du projet et le site construit ne contient aucun carnet
(`contents:` vide, pas de `files/` dans la sortie).

## Deploiement

Le job `build-jupyterlite` (`.github/workflows/quarto-pages-deploy.yml`) :

1. installe `jupyterlite-core` et `jupyterlite-pyodide-kernel` (versions
   egales) ;
2. appelle le script de construction avec `--base-url "/<nom-du-depot>"` ;
3. publie un artifact `jupyterlite-dist` (le site construit).

`assemble-pages` telecharge cet artifact dans `_site/jupyterlite/`, **en
fail-soft** : si le job de construction echoue, le site part sans
`/jupyterlite/` et un warning le dit. Le site Quarto n'est jamais tenu en
otage par le lot.

Le garde `scripts/ci/check_jupyterlite_lot.py` verifie ensuite, sur le site
publie, que chaque URL du manifeste repond :

```bash
python scripts/ci/check_jupyterlite_lot.py --json
```

Sorties : `0` (lot en ligne, ou lot absent -- rien n'est annonce, donc rien
n'est casse), `1` (une URL du lot est casse), `2` (instrument casse :
manifeste illisible ou reseau indisponible -- ce n'est pas un lien casse).

## Mesures

Les executions reelles sous JupyterLite (noyau Pyodide, Chromium) sont
produites par `scripts/notebook_tools/pyodide_browser_run.py` (pli 2.1), qui
sert le site construit en local et pilote le carnet par le menu **Run > Run
All Cells**. Il mesure, par carnet, le **temps jusqu'au premier resultat** et
la duree totale.

<!-- MESURES-LOCALES -->

### Mesure relevee (lot de huit carnets publies)

Site construit **en local** (JupyterLite 0.8.7, noyau Pyodide 314.0.6),
carnets servis par le site lui-meme, execution reelle dans Chromium
headless via `Run > Run All Cells`. « Premier resultat » est l'instant ou
la premiere cellule a produit une sortie lisible -- c'est la mesure que
demande le critere d'acceptation.

| Carnet | Cellules code | Executees | Erreurs | Duree (s) | Premier resultat (s) |
|---|---:|---:|---:|---:|---:|
| `10-SIG-3D-Tiles-Python.ipynb` | 6 | 6 | 0 | 29,6 | 9,9 |
| `AgentSystems-02-Perception-Active-Valeur-Information-Python.ipynb` | 6 | 6 | 0 | 15,8 | 6,7 |
| `Quotients-Fibres-Recollement-Python.ipynb` | 9 | 9 | 0 | 20,4 | 6,8 |
| `Argumentation-01-Toulmin-Model-Python.ipynb` | 7 | 7 | 0 | 14,4 | 6,8 |
| `06-3-AudioDiffusion-Comparison-A-vs-B.ipynb` | 1 | 1 | 0 | 14,1 | 6,6 |
| `Causalite-00-Echelle-de-Pearl-Intro-Python.ipynb` | 10 | 10 | 0 | 20,4 | 6,8 |
| `Chaines-05-Energie-Hamiltonien-Premiere-Puissance-Python.ipynb` | 8 | 8 | 0 | 17,5 | 6,9 |
| `Coalitions-04-Munkres-Affectation-Python.ipynb` | 10 | 10 | 0 | 34,0 | 6,8 |

**Huit carnets sur huit s'executent sans erreur.** Le temps jusqu'au premier
resultat est de **6,6 a 9,9 s** ; il est dominé par le demarrage du noyau
Pyodide, non par le carnet lui-meme -- c'est aussi pourquoi la duree totale
monte a 34,0 s sur le carnet le plus long (dix cellules) sans que le premier
resultat bouge.

Le huitieme carnet, `Causalite-00-Echelle-de-Pearl-Intro-Python.ipynb`,
echouait auparavant sur sa premiere cellule : la magic IPython
`%matplotlib inline` declenchait un `import matplotlib` **synchrone**, que
Pyodide ne peut pas attendre (son chargement de paquets est **asynchrone**).
L'echec etait **deterministe** (306,3 s au premier passage, 426,9 s en
re-execution isolee sur une page neuve). La magic a ete retiree du carnet
(PR #27715) ; le carnet s'execute alors sans erreur en 20,4 s.

Les sorties relevees sont bien celles d'une **execution reelle** et non
celles committes : le carnet `10-SIG-3D-Tiles` affiche `NumPy 2.4.6` a
l'execution, la sortie commitee annonce `NumPy 2.4.2`.

La preuve complete (sorties de chaque cellule) est versionnee dans
`docs/reference/jupyterlite-executions/` (`executions.json`,
[`executions.md`](jupyterlite-executions/executions.md)).

## Limites connues

- **Le site n'embarque pas la distribution Pyodide.** La construction ne pose
  que des **fichiers** : le noyau Pyodide (et ses paquets) est telecharge au
  premier usage. Mesure : la construction ne produit aucun repertoire
  `pyodide/`, et l'index piplite local ne contient que les roues du noyau
  (`ipykernel`, `piplite`, `pyodide-kernel`, `widgetsnbextension`). Une
  execution depend donc du **reseau** ; un echec de telechargement se lit
  comme un `ModuleNotFoundError` sur le paquet manquant, apres plusieurs
  centaines de secondes.
- **Le lot bouge avec le critere.** Le manifeste d'une construction n'a de
  sens que pour cette construction : le garde compare le manifeste **publie**
  aux URL repondantes, jamais a une liste du depot.
- **Nommage a plat.** Les carnets sont servis par nom de fichier ; deux
  carnets homonymes ne peuvent pas coexister dans le lot (la construction
  echoue). Le chemin d'origine reste dans le manifeste.
- **Taille de l'artifact.** Le site JupyterLite embarque la distribution
  Pyodide : l'artifact est de l'ordre de 70 Mo, retention 3 jours.
- **Le garde est advisory.** Il ne bloque aucune PR (workflow
  `workflow_run`) ; un rouge se lit dans le run du workflow.

## Voir aussi

- [pyodide-eligibilite.md](pyodide-eligibilite.md) -- le critere (pli 2.1)
- `scripts/notebook_tools/pyodide_eligibility.py` -- le critere, en code
- `scripts/notebook_tools/build_jupyterlite_site.py` -- la construction
- `scripts/ci/check_jupyterlite_lot.py` -- le garde post-deploiement
- Issue #27550 (pli 2.2) et #27543 (Epic)
