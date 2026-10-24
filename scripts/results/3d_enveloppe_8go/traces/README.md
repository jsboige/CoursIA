# Traces brutes des enveloppes VRAM 8 Go

Séries `nvidia-smi` des runs qui fondent les manifestes de
`scripts/results/3d_enveloppe_8go/` et le document
`docs/genai/3d-enveloppe-vram-8go.md`. Elles sont committées ici parce qu'elles
tiennent sous 512 Ko (`results-artifact-policy`), et parce que la valeur d'un
manifeste est de pouvoir être **re-dérivée** sans refaire le run : une RTX 3070
Ti 8 Go n'est pas disponible partout.

## Fichiers

| Fichier | Octets | sha256 | Run |
|---|---:|---|---|
| `vram-3d01.csv` | 2 060 | `bf2c924b8e825de51486837174e993d78b6809a82612f2703e92b028ed5dae1e` | `3D-01-NeRF-From-Scratch` (entraînement) |
| `3d01-enveloppe.log` | 1 324 | `62c6817842a5cd3d30e1939ee5b3b300ae38e2acfd4c6b32d75df606585312e0` | journal du même run |
| `vram-3d02.csv` | 11 656 | `81407a7191be24fcae8371c68f63edd500c4021d21cc2c296e443a4a1302e30e` | `3D-02-NeRF-Critic` (volet évaluatif) |
| `3d02-enveloppe.log` | 660 | `3e62a2013be2416b0f2aa52b89efd5fa9926a900309676eb4b7e760816eb8ccd` | journal du même run |

La trace du **Pli 1** (`3.4d-Fourier-Features`) n'existe pas : voir
« Ce qui manque » plus bas.

## Format des séries

En-tête, tel quel dans les deux CSV, encodage UTF-8 avec BOM :

```
horodatage,utilisation_gpu,memoire_mib,temp_gpu_c
```

Une ligne par échantillon, horodatage ISO-8601 avec décalage local `+02:00` et
sept décimales de fraction de seconde (`2026-10-20T18:42:41.6177096+02:00`).
`memoire_mib` est la mémoire utilisée de la carte en Mio, `utilisation_gpu` le
pourcentage d'occupation du moteur, `temp_gpu_c` la température en degrés Celsius.

## Provenance, run par run

| | 3D-01 | 3D-02 |
|---|---|---|
| Siège | `myia-po-2028` | `myia-po-2028` |
| Carte | RTX 3070 Ti Laptop, 8 192 Mio | idem |
| Début du run (journal) | `2026-10-20T18:42:40.93+02:00` | `2026-10-21T01:17:41.53+02:00` |
| Premier échantillon (trace) | `2026-10-20T18:42:41.62+02:00` | `2026-10-21T01:17:43.03+02:00` |
| Dernier échantillon (trace) | `2026-10-20T18:46:09.46+02:00` | `2026-10-21T01:38:08.89+02:00` |
| Échantillons | 42 | 242 |
| Couverture | 207,8 s | 1 225,9 s |
| Cadence déclarée | 5 s | 5 s |
| Cadence **observée** (médiane des écarts) | 5,07 s (min 5,06 · max 5,10) | 5,09 s (min 5,06 · max 5,26) |
| Fin du run (journal) | `rc=0 duree_s=210.9`, Papermill `Total time: 207.6s` | `rc=0 duree_s=1226.7`, Papermill `Total time: 1222.3s` |

**Commande de sonde : non archivée.** Elle n'a été retrouvée ni dans le dépôt ni
dans le dossier GDrive d'où les fichiers ont été récupérés. Ce que les fichiers
établissent d'eux-mêmes, et qui suffit à rejouer un format équivalent :

- l'en-tête est en français et non celui de `nvidia-smi --query-gpu` (qui rend
  des noms anglais) : la boucle reformatait donc la sortie, elle n'était pas un
  `--format=csv` direct ;
- les horodatages ont sept décimales de fraction et un décalage `+02:00`, forme
  produite par un `DateTimeOffset` .NET, donc très probablement une boucle
  PowerShell (inférence de format, pas un fait vérifié) ;
- l'instrument du dépôt `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/probe_15099_vram_sampler.py`
  n'est **pas** le producteur : il écrit du JSONL à champs anglais et un sidecar
  `.meta.json`.

Une demande de la boucle exacte a été adressée à la lane qui a archivé ces
fichiers (`myia-po-2028:CoursIA-2`) ; si elle répond, cette section gagne la
commande verbatim et rien d'autre ne change.

## Re-dériver un chiffre

Chaque valeur des manifestes se recalcule depuis ces CSV. Les fenêtres de phase
du manifeste `3d02` se retrouvent d'elles-mêmes dans la trace, aux points de
rupture près (saut de plus de 60 Mio d'un échantillon au suivant) :

| Fenêtre déclarée du manifeste (3D-02) | Indices | n | min | max | médiane | mode | Ce que la fenêtre contient en plus du palier |
|---|---|---:|---:|---:|---:|---:|---|
| *aucune* — repos avant run | 0-4 | 5 | 425 | 428 | 427 | 427 | — |
| `0-300` « scène jouet + grille du critic » | 0-58 | 59 | 425 | 3 018 | 2 992 | 2 989 | indices 0-6 : repos puis rampe (331 → 581 → 2 912) ; palier réel sur 7-58 (médiane 2 993) |
| `300-1200` « Lego, bruit de pose, focales » | 59-235 | 177 | 4 195 | **4 228** | **4 202** | 4 202 | rien : la fenêtre est un palier du début à la fin |
| `1200-1226` « comptage de points N=256 » | 236-241 | 6 | 427 | **7 740** | 5 977 | — | indice 241 (t = 1 226 s) : déchargement du modèle, retour à 427 Mio |

Les ruptures mesurées tombent à `t = 300,4 s` (entrée en phase 2) et
`t = 1 210,6 s` (saut vers le pic) : les fenêtres `300-1200` et `1200-1226` du
manifeste sont donc corroborées à un échantillon près.

L'organe `python scripts/audit/check_vram_envelope_rederivable.py` refait ce
calcul, compare aux champs des manifestes et échoue si un champ a dérivé.

## L'arbitrage 4228 / 4217

Les deux valeurs sont **des lignes réelles de la trace**, à des instants
différents — l'écart de 11 Mio n'est pas un désaccord de mesure :

| Valeur | Où elle vit dans la trace |
|---|---|
| **4 217** | indices **184** (t = 936 s) et **231** (t = 1 175 s) — deux échantillons, aucun rôle de borne |
| **4 228** | indice **235** (t = 1 195 s) — le **maximum** de la phase 2, 15 s avant le saut |
| **4 202** | médiane et mode de la phase 2 (179 échantillons, 4 195-4 228) |

Le champ `profil_par_phase_mib[1].plateau_mib = 4217` et la prose « de 4228 à
7740 » désignent donc **deux échantillons du même palier**, et ni l'un ni l'autre
n'est la statistique du palier, qui vaut 4 202 Mio. La trace tranche : les deux
nombres sont vrais, ils diffèrent parce qu'ils sont pris à deux instants d'une
queue montante (4 203 à t = 1 109 s → 4 209 à t = 1 149 → 4 218 à t = 1 165 →
4 228 à t = 1 195 → 7 736 à t = 1 211).

Conséquence sur l'amplitude citée par le document : « montée de 3 523 Mio » est
`7 740 − 4 217` ; depuis le maximum du palier elle vaut `7 740 − 4 228 = 3 512`,
et entre deux échantillons consécutifs `7 736 − 4 219 = 3 517` (indices 237→238).
Les trois chiffres sont justes, chacun avec sa définition.

Aucune valeur de manifeste n'est réécrite : c'est la **lecture** du champ
`plateau_mib` qui change — un échantillon de palier, pas la valeur du palier.

## Le repos : 322, 331, 428

Le constat de l'issue opposait 322 Mio (manifeste 3D-01) et 331 Mio (prose du
manifeste Fourier, qui décrit un autre run). La trace les sépare :

- `vram-3d01.csv` indices **0 et 1** (t = 0 et 5 s) : **331** Mio — la lecture
  d'avant-run, celle que le journal répète à l'identique (`GPU avant : ... 331 MiB`
  et `GPU apres : ... 331 MiB`) ;
- indice **2** (t = 10 s) : **322** Mio — un unique échantillon, le minimum de
  toute la série, pris après le démarrage du noyau ; c'est lui que le manifeste
  porte sous `idle_mib`.

Les deux valeurs sont donc réelles, à deux instants différents : 331 Mio est le
repos avant run, 322 Mio le creux transitoire du début. Même remarque que pour
`plateau_mib` — le champ nomme un échantillon selon une règle non écrite.

Pour `3D-02`, `idle_mib = 428` est cohérent des deux côtés : indice 2 de la trace
(t = 10 s) et ligne `GPU avant : ... 428 MiB` du journal. La série descend
ensuite à 425 (indice 4) et revient à 427 au dernier échantillon.

## Ce qui manque : la trace du Pli 1 (3D-4d)

La série `nvidia-smi` du run Fourier (échantillonnage à 2 s de la carte et de la
RSS de l'arbre de processus) n'a pas été conservée : ni sur le siège d'origine,
ni dans le dossier GDrive, ni dans le dépôt. Les agrégats du manifeste
`3d4d_fourier_8go.json` (427 → 444 Mio, delta 17, `contexte_cuda_cree: false`,
pic RSS hôte 288 Mio) sont donc **non re-dérivables** : ils ne se vérifient plus
que par la lecture du code du carnet, qui n'importe ni `torch` ni moteur CUDA.

C'est une perte mesurée, pas une absence constatée : le run a bien été
échantillonné (le manifeste cite la cadence de 2 s et le manifeste comme le
document en tirent la conclusion « carte au repos »), mais les fichiers ont
disparu avant d'être rapatriés. La conclusion « 0 Mio de VRAM attribuable » ne
dépend pas de cette série : elle repose sur l'absence d'import CUDA et sur la
carte restée au niveau du repos pendant tout le run — un fait que le manifeste
atteste, et qu'un rejeu court rejouerait.
