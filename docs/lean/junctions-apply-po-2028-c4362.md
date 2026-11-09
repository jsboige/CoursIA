# Mathlib WSL symlinks — Apply po-2028 (CoursIA-2, c.4362)

Issue : [#4362](https://github.com/jsboige/CoursIA/issues/4362) — Lean : harmoniser Mathlib, mutualiser les checkouts, regrouper les lakes (anti-prolifération).
Premier bloc de mesure : « Etat mesure au 2026-10-31 » dans le body de l'issue (cette lane, même jour).

**Lane** : `myia-po-2028:CoursIA-2`.
**Date** : 2026-10-31 (cycle c89).
**Périmètre** : WSL Ubuntu `/home/jesse` de MYIA-PO-2028 uniquement — les environnements de build manuels des lakes (la CI self-hosted tourne dans son propre checkout et ne touche pas ces répertoires). Côté NTFS, le clone principal `D:/dev/CoursIA-2` n'a aucun checkout mathlib matérialisé : rien à mutualiser (voir bloc de mesure).
**Statut** : **Apply exécuté — 3 symlinks posés, vérification `lake build Mathlib` rc=0 sur les trois** ; rollback intégral disponible dans `/home/jesse/.trash/` ; purge différée (la poubelle n'est pas une purge).

> **Ce rapport corrige le bloc de mesure qui l'a précédé.** Le comptage « 8 checkouts physiques à ~7,2 Go = ~57,5 Go » du bloc « Etat mesure au 2026-10-31 » **surcomptait** : la sonde mesurait des chemins concaténés (`<projet>/.lake/packages/mathlib`), et trois de ces « physiques » (`khovanov-knot-c43`, `khovanov-knot-c44`, `knot-22359t3`) avaient leur `.lake/packages` **entier déjà mutualisé par symlink** vers `perc19494` — le même magasin était compté quatre fois. C'est le même drift de portée que celui documenté dans [junctions-apply-po-2027-c1731.md](junctions-apply-po-2027-c1731.md) : une mesure par chemin ne voit pas la topologie des liens.

## Topologie réelle mesurée avant Apply (2026-10-31, ~15:15Z)

| Élément | État mesuré |
|---|---|
| Magasin physique `db584cd6` (le hub réel) | `perc19494/.lake/packages/mathlib` — 7,2 Go, 8322 oleans, `Mathlib.olean` présent |
| Consommateurs **déjà** branchés sur ce magasin | `perc19494` (propre), `khovanov-knot-c43`, `khovanov-knot-c44`, `knot-22359t3` (lien `packages/` entier) + `groth-map-2159` (lien `mathlib` seul) = **5 consommateurs préexistants** |
| Autres magasins physiques `db584cd6` (victimes) | `conway-17465-po2028` (7,2 Go), `conway_build_20261022` (7,2 Go), `dsnail-envelope` (7,1 Go) |
| Poubelle préexistante | `.trash/knot-22359t2-20261030` (7,2 Go, `db584cd6`) |
| Revs différentes (exclues du geste) | `pfr-lake` (625d8914, 6,9 Go), `torchlean-po2028` (56a00585, 9,0 Go), `analysis` (698d2b68) |
| Acteur concurrent | `dsnail-artifacts-2026-10-31` — clone **incomplet** (621 Mo) matérialisé à 16:14 locale **pendant** la sonde, setup actif d'une autre session : **exclu du geste** |
| Unicité réelle avant Apply | ~36 Go de mathlib `db584cd6` physiques (et non 57,5 Go) |

## Garde pré-geste

- Aucun process `lake`/`lean` réel actif (garde par `comm`, pas par args — les lignes de commande pytest de la CI contiennent `scripts/lean/tests` et faussent un grep sur les arguments).
- Contrôle positif AVANT mutation : `lake build Mathlib` dans `groth-map-2159` (déjà en état cible) — **rc=0 en 21 s, 8705 jobs, zéro recompilation** : le donateur sert les builds à travers un symlink.
- Complétude du donateur : 8322 oleans, seuil abort < 8000.

## Apply exécuté (mutation en root — `.trash` appartient à root)

Trois liens `mathlib` (et seulement `mathlib` — jamais le `packages/` entier, dont les autres dépendances peuvent diverger) :

```
conway-17465-po2028/.lake/packages/mathlib   -> /home/jesse/perc19494/.lake/packages/mathlib
conway_build_20261022/.lake/packages/mathlib -> /home/jesse/perc19494/.lake/packages/mathlib
dsnail-envelope/.lake/packages/mathlib       -> /home/jesse/perc19494/.lake/packages/mathlib
```

Le geste : `mv <mathlib> /home/jesse/.trash/<projet>-mathlib-20261031/` puis `ln -s` vers le magasin, `chown -h jesse` du lien. Chaque victime est gardée par triple prédicat avant mutation : `packages/` n'est pas lui-même un lien, `mathlib` est un vrai répertoire, manifest = `db584cd6`.

**Pourquoi le magasin `perc19494` et non `khovanov-knot-c44`** (donneur cité en exemple dans le bloc de mesure) : le `packages/` de c44 est un symlink vers perc19494 — lier vers c44 aurait chaîné deux liens et rendu les nouveaux consommateurs fragiles à la suppression du lien intermédiaire. On lie vers le magasin réel.

## Vérification (en utilisateur `jesse`, après mutation)

| Projet | `lake build Mathlib` | Durée | Baseline physique avant geste |
|---|---|---|---|
| `conway-17465-po2028` | rc=0, 8705 jobs | 9 s | rc=0, 15 s |
| `conway_build_20261022` | rc=0, 8705 jobs | 9 s | rc=0, 15 s |
| `dsnail-envelope` | rc=0, 8705 jobs | 10 s | rc=0, 13 s |

Aucune recompilation de Mathlib : le magasin partagé sert les trois builds.

## Rollback et purge

- **Rollback** (un par victime) : `rm` du lien puis `mv /home/jesse/.trash/<projet>-mathlib-20261031 <projet>/.lake/packages/mathlib`.
- **Purge différée** : `.trash` total 22 Go (3 × ~7,2 Go du jour + le `knot-22359t2` préexistant). Les copies sont prouvées redondantes (le magasin sert tous les builds vérifiés), mais la purge reste un geste séparé et explicite — la poubelle n'est pas une purge.

## Économie réelle

| Poste | Valeur |
|---|---|
| Déplacé en poubelle ce jour (récupérable à la purge) | **~21,5 Go** |
| Poubelle préexistante (récupérable aussi) | ~7,2 Go |
| Duplication restante `db584cd6` | 1 magasin (perc19494) + `dsnail-artifacts-2026-10-31` en cours de setup (à brancher quand son propriétaire aura fini) |
| Surcomptage du bloc de mesure initial | ~21,5 Go (quadruple comptage du magasin perc19494 via les liens `packages/`) |

## Leçons (durables, pour les Apply suivants sur les autres machines)

1. **La sonde par chemin concatigné est aveugle aux liens `packages/`** : toujours `readlink -f` le `mathlib` de chaque projet ET vérifier si `.lake/packages` lui-même est un lien avant de compter, et surtout avant de muter — un `mv` sur un chemin traversant un lien `packages/` déplace le **magasin partagé** d'une autre lane. C'est l'échec `Permission denied` (`.trash` root) qui a involontairement bloqué ce scénario lors de la première passe.
2. **La garde anti-build doit matcher `comm`, pas les arguments** : les process pytest de la CI self-hosted contiennent `lean` dans leurs chemins d'arguments.
3. **Un projet en cours de setup est un acteur concurrent** : un répertoire daté du jour, incomplet (621 Mo), dont l'état change entre deux sondes à 2 minutes d'intervalle, s'exclut — on n'édite pas dessous une session vivante.
4. **Lier vers le magasin réel, jamais vers un intermédiaire** : résoudre toute la chaîne de liens avant de choisir la cible du `ln -s`.
