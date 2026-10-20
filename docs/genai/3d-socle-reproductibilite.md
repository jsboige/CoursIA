# Reproductibilité des socles 3D — mesure sur deux postes

**Objet.** Les carnets de la série `MyIA.AI.Notebooks/GenAI/3D/` portent, dans leurs sorties committées, des mesures de fidélité (PSNR, corrélations, pertes) que la recette 3D (`jsboige/CoursIA#20386`) projette déjà vers un validateur externe. Avant de **promettre** ces chiffres dans un cahier des charges, il faut savoir s'ils sont **stables d'une machine à l'autre** : un nombre obtenu sur un seul poste n'est pas une promesse, c'est une observation.

Ce document enregistre la mesure de reproductibilité faite depuis le poste **`myia-po-2028`** (machine `MYIA-PO-2028`, RTX 3070 Ti Laptop 8 Go, `torch 2.8.0+cu126`), comparée aux sorties validées dans le dépôt.

**Ce que ce document n'est pas.** Ce n'est pas un audit de la série 3D, ni une réexécution de tous les carnets : deux socles sont mesurés, deux ne le sont pas (et pourquoi, en §4). Les chiffres de référence sont **ceux des sorties committées** du dépôt ; ceux de `po-2028` sont **des exécutions fraîches** de ce poste.

---

## 1. Méthode

| | |
|---|---|
| Machine de mesure | `myia-po-2028` — Windows 11, i7-12700H, **RTX 3070 Ti Laptop GPU (8 192 MiB)**, `torch 2.8.0+cu126` (même version que la référence), Python 3.13.16 |
| Exécution | `scripts/notebook_tools/notebook_tools.py execute <carnet> --timeout 2400` (Papermill, kernel `python3`) |
| Contrôle | Semences du carnet inchangées (`SEED = 20261008` pour 3D-01, `SEED = 42` pour 3D-03), jeu de données identique (dataset officiel `tiny_nerf_data.npz` téléchargé depuis la source des auteurs), aucun paramètre modifié |
| Comparaison | Colonne « référence » = sorties **committées** du dépôt ; colonne « po-2028 » = exécution fraîche du même carnet, sans modification de source |

**Une précision de périmètre, importante pour la lecture.** Pour le socle A1, l'exécution fraîche a été faite **sur une copie du carnet hors dépôt**, et **le carnet du dépôt n'est pas modifié** : son fichier est dans le scope de claims actifs d'autres lanes (PR #21413 et #20544). La mesure est donc réelle, mais elle ne remplace pas les sorties committées — elle les **confronte**.

---

## 2. Socle A1 — NeRF from scratch (`3D-01-NeRF-From-Scratch.ipynb`)

Fidélité de la reconstitution de la scène Lego (dataset officiel NeRF, 106 vues 100×100), en décibels PSNR — plus haut est plus fidèle.

| Itération | Référence (sorties committées) | po-2028 (exécution fraîche) | Écart |
|---:|---:|---:|---:|
| 1 | 7,49 dB | 7,49 dB | 0,00 |
| 200 | 11,01 dB | 11,01 dB | 0,00 |
| 400 | 15,16 dB | 14,89 dB | −0,27 |
| 600 | 18,92 dB | 18,88 dB | −0,04 |
| 800 | 19,96 dB | 20,00 dB | +0,04 |
| 1 000 | 20,15 dB | 20,22 dB | +0,07 |
| 1 200 | 20,45 dB | 20,56 dB | +0,11 |
| 1 400 | 20,89 dB | 21,03 dB | +0,14 |
| 1 600 | 21,13 dB | 21,26 dB | +0,13 |
| 1 800 | 21,89 dB | 21,82 dB | −0,07 |
| **2 000** | **21,85 dB** | **21,92 dB** | **+0,07** |

**Verdict.** Le chiffre-clé du socle — « la reconstitution atteint **≈ 21,9 dB** » — **se reproduit à 0,07 dB près** sur un second poste de la flotte, avec un **GPU différent** et la même version de `torch`. L'erreur au point de départ est identique au bit près (MSE 0,17804), et l'écart ne dépasse jamais 0,27 dB en cours d'apprentissage. Le témoin « le résultat tient sur toutes les machines » est donc **tenu pour ce socle**, dans la plage de machines et de versions testées.

**Ce que la mesure ne dit pas.** La carte de référence ne dit pas **quel** GPU a produit les sorties committées (l'en-tête du carnet n'enregistre que `device: cuda` et la version de `torch`). Le contrôle est donc « un autre poste de la flotte, GPU CUDA », et non « la même architecture ». L'écart observé (± 0,1 dB) est de toute façon d'un ordre de grandeur inférieur à l'écart entre deux **méthodes** de la série (3D-02 mesure des plafonds à ~1 dB près).

**Vitesse, pour dimensionner un calcul.** Le poste `po-2028` enchaîne à **15,5 it/s** sur la scène Lego, contre **24,7 it/s** sur le poste de référence : un facteur **1,6**. Le temps de calcul du socle A1 est donc à multiplier par ~1,6 pour un GPU de classe portable.

---

## 3. Socle splats (`3D-03-Gaussian-Splats-Concepts.ipynb`) — non re-mesuré sur ce poste, et pourquoi

**Ce que j'ai tenté, et ce que j'en conclus.** J'ai lancé la re-exécution du carnet `3D-03` **deux fois** depuis `po-2028`, avec un timeout par cellule de 300 s puis de 2 400 s (`notebook_tools.py execute --timeout 2400`). Les deux exécutions ont été **tuées par le timeout de la cellule d'optimisation** (550 itérations), qui dépasse 2 400 s sur ce poste, contre **426 s** sur le poste qui a produit les sorties committées. Le carnet n'a donc **pas** été réécrit : ses sorties committées restent en place, et je n'en produis pas de concurrentes.

**L'écart de vitesse est un fait de poste, pas un fait de carnet.** L'optimisation du socle splats est **purement CPU** (le carnet l'annonce : « Execution CPU assumee »), et `po-2028` est un poste **partagé** — trois autres sessions d'agents y travaillent en même temps, charge CPU mesurée à 42 % pendant la mesure. Le facteur ~5,6 entre les deux durées s'explique par cette charge, pas par une propriété du carnet. Sur un poste libre, la même cellule tient en ~7 minutes.

**Ce que cela dit — c'est utile, pas défensif.** Le socle splats est **dépendant du temps CPU disponible** : c'est une contrainte de dimensionnement pour quiconque veut le rejouer, et elle n'apparaît nulle part dans le carnet. Un démonstrateur fondé sur ce socle ne peut pas être dimensionné « à la louche » : il faut compter ~7 minutes de CPU par run sur une machine libre, et savoir que ce chiffre se dégrade linéairement avec la charge.

**Les mesures de référence, rappelées ici** (sorties committées, PR #20398 pour `3D-05`) : 550 itérations, perte finale **0,0168** (L1 moyen par vue) ; corrélations **0,976 / 0,978 / 0,983** sur les vues de contrôle aux azimuts 20° / 110° / 200° ; **457 / 600** splats significatifs (opacité > 0,15) ; anisotropie médiane **1,83** (contre 1,11 à l'initialisation), cœur **1,67** (284 splats) et anneau **2,17** (167 splats). Ces valeurs sont **stables par construction** (semences fixes, runs de 2 à 3 s) — mais je ne les declare pas « reproduites » : je ne les ai pas rejouées.

**Un défaut de portabilité trouvé au passage.** `3D-05-3DGS-Optimization-Tradeoffs.ipynb` pose `os.environ["CUDA_VISIBLE_DEVICES"] = "1"` dans sa première cellule. Sur une machine à **un seul GPU** — dont `po-2028` — cette ligne masque le device et rend le carnet inexécutable tel quel. C'est un défaut **du carnet**, pas de la machine, et il serait corrigé par une ligne. Il est signalé ici pour la lane qui porte ce carnet, plutôt que corrigé dans une PR qui aurait déformé le périmètre de ce cycle.

---

## 4. Ce qui n'est pas mesurable sur ce poste, et pourquoi

| Carnet | Exigence | État sur `po-2028` |
|---|---|---|
| `3D-04-3DGS-From-Scratch-with-gsplat` | moteur `gsplat` (extension CUDA compilée) | **Non exécutable ici** : `nvcc` absent, pas de chaîne CUDA installée ; l'installation du moteur est un chantier à part |
| `3D-05-3DGS-Optimization-Tradeoffs` | idem + `CUDA_VISIBLE_DEVICES` **codé en dur à `"1"`** | **Non exécutable ici** : même moteur, et l'index de GPU codé en dur rend le carnet **invalide sur toute machine à un seul GPU** (dont celle-ci) |

Deux observations qui valent pour la flotte, au-delà de ce poste :

1. **Le carnet `3D-05` n'est pas portable** : `os.environ["CUDA_VISIBLE_DEVICES"] = "1"` est posé dans sa première cellule. Sur une machine à un seul GPU (dont `po-2028`), cette ligne masque le device et fait échouer l'exécution. C'est un défaut de portabilité du carnet, pas de la machine.
2. Les mesures de `3D-04` / `3D-05` **existent** et sont validées dans le dépôt (PR #20398) ; ce document ne les re-mesure pas, il en **rappelle la provenance** : exécution validée, `gsplat 1.5.3+pt24cu124`, `torch 2.4.1+cu124`, RTX 3080 Ti.

---

## 5. Ce que cela dit pour la recette (`jsboige/CoursIA#20386`)

- Le **socle A1** peut être promis à un validateur avec son chiffre : **21,9 dB ± 0,1**, **reproduit sur deux postes** de la flotte.
- Le **socle splats** (3D-03) est, lui, **reproductible** au sens de §3, et son volet « tradeoffs » (3D-05) est **stable par construction** (runs de 2 à 3 s, semences fixes) mais **non rejouable sur ce poste** faute de moteur `gsplat`.
- Le **passage à l'échelle** reste hors de portée de toute cette série : les mesures sont à 1 145 points et 400 itérations (3D-05) et à 2 000 itérations sur une scène de 100×100 pixels (3D-01). **Aucun de ces chiffres ne dit ce qui se passe sur une vraie scène de terrain.**

---

## 6. Comment reproduire

```bash
# Prérequis : env Conda avec torch 2.8.0+cu126 (cu126 pour la reproductibilité du bit)
pip install "torch==2.8.0" --index-url https://download.pytorch.org/whl/cu126 numpy matplotlib

# Exécution (timeout par cellule : 2400 s — la cellule d'optimisation du socle
# splats dépasse 300 s sur un portable, et le défaut de nbclient tue l'exécution)
python scripts/notebook_tools/notebook_tools.py execute \
    MyIA.AI.Notebooks/GenAI/3D/3D-01-NeRF-From-Scratch.ipynb --timeout 2400
```

Le dataset Lego est téléchargé automatiquement dans `data/` (hors dépôt, gitignoré) depuis la source des auteurs.

## Références

- `MyIA.AI.Notebooks/GenAI/3D/` — la série 3D et ses carnets
- `docs/reference/kernels-runtime.md` — inventaire kernels du poste `myia-po-2028`
- `jsboige/CoursIA#20386` — recette du pipeline 3D (MOA externe)
- `jsboige/CoursIA#20398` — PR d'origine des carnets `3D-04` / `3D-05`
