# Artefacts de build Lean DarkSnail — 2026-10-31

Ce répertoire rend le verdict de
[`concern-2026-10-29-build-verification.md`](../concern-2026-10-29-build-verification.md)
**rejouable par un tiers** : il ne décrit plus le build, il en porte la trace
exécutable. La réserve du reviewer ([Hermes], 2026-10-31T07:36:24Z) portait
exactement là — « aucun artefact committé ne porte le résultat ».

Rien du code amont n'est livré ici : seuls la **requête** qui interroge Lean,
la **réponse** de Lean, la **sortie de build** et l'**épinglage** de
l'environnement sont présents.

## Contenu

| Fichier | Rôle |
|---|---|
| `lakefile.toml` | lakefile de l'enveloppe (cible, racine de la bibliothèque, exigence Mathlib) |
| `lean-toolchain` | version Lean déclarée par l'enveloppe |
| `lake-manifest.json` | révision Mathlib effectivement résolue (épinglage de l'artefact) |
| `versions.txt` | versions de `lake` et `lean`, révision Mathlib, commit amont mesuré, horodatage de la passe |
| `sources.sha256` | empreinte SHA-256 et identifiant de blob git des **deux sources réellement compilées** |
| `Axioms.query` | requête `#print axioms` (67 requêtes) produite par `scripts/lean/dsnail_axioms_query.py` |
| `lake-build-output.txt` | sortie de `lake build` (cibles explicites) |
| `lake-axioms-output.txt` | sortie de `lake env lean Axioms.query` — la réponse de Lean, ligne par ligne |
| `coherence.txt` | décomptes recalculés **sur les deux logs ci-dessus** |

## Rejeu

Le rejeu suppose un clone amont au commit mesuré et une toolchain Lean
épinglée par `lean-toolchain` ; l'enveloppe Mathlib est celle du manifeste.

```bash
# 1. sources amont, au commit exact
git clone --filter=blob:none https://github.com/sneed-and-feed/projectdarksnail
git -C projectdarksnail fetch --depth 1 origin 043c9d26fc86816e4272d37e755c5918282bfb52
git -C projectdarksnail checkout 043c9d26fc86816e4272d37e755c5918282bfb52

# 2. enveloppe : les fichiers d'artefacts ci-dessus, a la racine du projet
mkdir -p Formalization
cp projectdarksnail/formalization/OcclusionTriad.lean Formalization/
cp projectdarksnail/formalization/BlockBridge.lean Formalization/
cp <ce-repertoire>/lakefile.toml <ce-repertoire>/lean-toolchain <ce-repertoire>/lake-manifest.json .

# 3. requete d'axiomes (le generateur est livre dans le depot)
python3 scripts/lean/dsnail_axioms_query.py --out Axioms.query \
  Formalization/OcclusionTriad.lean Formalization/BlockBridge.lean

# 4. build et passe d'axiomes
lake exe cache get
lake build Formalization.OcclusionTriad Formalization.BlockBridge
lake env lean Axioms.query
```

Les sorties obtenues se comparent alors, ligne à ligne, avec `lake-build-output.txt` et
`lake-axioms-output.txt` du présent répertoire. Les octets réellement compilés se vérifient
par `sha256sum` sur les deux sources, et par identifiant de blob git.

## Ce que les artefacts portent

- **Build** : `Build completed successfully (3007 jobs).` — les deux modules
  amont sont recompilés dans la passe (`Built Formalization.BlockBridge`,
  `Built Formalization.OcclusionTriad`), la sortie est le journal complet du
  `lake build` exécuté avec les deux cibles explicites.
- **Axiomes** : 67 requêtes, 67 réponses, aucune erreur. Répartition exacte des
  ensembles d'axiomes, recalculée sur `lake-axioms-output.txt` :

  | Ensemble d'axiomes | Theorèmes |
  |---|---|
  | `[Classical.choice, Quot.sound, propext]` | 47 |
  | `[Quot.sound, propext]` | 13 |
  | `[Quot.sound]` | 1 |
  | `[propext]` | 1 |
  | aucun axiome | 5 |

  Aucun axiome hors de ce trio, **0 `sorryAx`**, **0 `native_decide`**.
- **Provenance** : `sources.sha256` porte les empreintes des octets compilés ;
  ils correspondent aux blobs amont cités au §7 de la page de référence.

## Deux pièges de rejeu (mesurés le 2026-10-31)

1. **`lake build` sans cible ne construit rien** : cette forme de lakefile n'a
   pas de cible par défaut, la commande rend « no default targets configured ».
   Les cibles se passent explicitement.
2. **Un cache de build peut survivre à un changement d'octets de la source** :
   lors du rejeu, `lake build` a réutilisé des `.olean` antérieurs alors que les
   sources venaient d'être remplacées par les octets amont (les copies
   locales étaient en CRLF, les octets amont en LF). Le build ne rejouait donc
   pas les sources affichées. La passe communiquée ci-dessus supprime les
   artefacts de build des deux modules amont avant de compiler — c'est ce qui
   rend le journal honnête.
