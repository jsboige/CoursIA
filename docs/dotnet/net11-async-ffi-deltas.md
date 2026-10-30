# .NET 10 → 11 — Delta runtime mesuré sur l'axe 1 (awaits profonds) du carnet Aspire AsyncFFI

> **Issue** : #23444 (organe de mesure multi-runtime + première application).
> **Grain de l'axe 1** : #23441 (EPIC .NET 11 #18695, P1 #18771) — le grain reste **non claimé**,
> le plafond EPIC #22500 s'appliquant cette semaine ; le coordinateur en arbitre la clôture.
> **Sibling** : [`net11-runtime-deltas.md`](net11-runtime-deltas.md) (bancs BDN). Ce document ne le
> remplace pas et ne l'édite pas : il porte le **volet carnets — axe 1**, qui y est encore noté
> `non mesuré`.
> **Mesure** : myia-po-2023, 2026-10-30, hôte `myia-po-2023` (Windows 11).

## Conditions (reproductibles)

| Paramètre | Valeur |
|---|---|
| CPU | 12th Gen Intel Core i7-12700H (20 processeurs logiques) |
| Runtimes comparés | .NET **10.0.14** (`C:\Program Files\dotnet`) · .NET **11.0.0-rc.3.26522.148** (`C:\Users\jsboi\.dotnet-r11`, install `dotnet-install` user-local sans UAC — règle F) |
| Build de kernel | **un seul** : `microsoft.dotnet-interactive` **1.0.712001** (pin canonique #18766), exécuté tel quel sous les deux runtimes — seul le `DOTNET_ROOT` change |
| Roll-forward | `DOTNET_ROLL_FORWARD=LatestMajor` + `DOTNET_ROLL_FORWARD_TO_PRERELEASE=1`, posés **à l'identique** pour les deux runtimes (la RC doit être atteignable) |
| Preuve du runtime effectif | **dans la sortie**, pas supposée : `RuntimeInformation.FrameworkDescription`, `Environment.Version` et le répertoire de runtime chargé, rendus par une cellule de provenance exécutée **dans le même kernel** que la cellule mesurée |
| Grandeur mesurée | §4 de `08-Aspire-AsyncFFI-Dotnet.ipynb` : **temps que le thread natif reste bloqué dans `SetResult`** pendant que la continuation s'exécute en ligne — la grandeur réellement sensible au runtime (le wall-clock du carnet est dominé par le démarrage kernel + Roslyn et ne distingue rien) |
| Passes | 5 répétitions par runtime, chaque répétition exécutant les 5 runs internes de l'instrument → **n = 25 runs** par runtime et par configuration |
| Agrégation | médiane sur les 25 runs, min/max sur les 25 ; les médianes par répétition sont conservées (elles portent la dispersion) |
| Verdict | `DELTA ETABLI` si les intervalles [min,max] des deux runtimes sont **disjoints** ; `INCONCLUSIF` sinon ; `NON RESOLU` sous le plancher de résolution (0,5 ms) |
| Organe | [`scripts/notebook_tools/multiruntime_probe.py`](../../scripts/notebook_tools/multiruntime_probe.py) (lecture seule sur le carnet) |

## Compatibilité .NET 11 — établie

Le carnet s'exécute **sans erreur** sous .NET 11 : les 9 cellules de code ont été passées sous
`11.0.0-rc.3.26522.148` (exécution complète du carnet, 0 cellule en erreur, 0 cellule sans
`execution_count`), et le runtime effectif est **prouvé dans la sortie** — par la cellule de
provenance de l'organe, et par une cellule de provenance insérée en tête du carnet lors de cette
exécution complète :

```text
runtime net10 : .NET 10.0.14 (10.0.14) — chargé depuis C:\Program Files\dotnet\shared\Microsoft.NETCore.App\10.0.14\
runtime net11 : .NET 11.0.0-rc.3.26522.148 (11.0.0) — chargé depuis C:\Users\jsboi\.dotnet-r11\shared\Microsoft.NETCore.App\11.0.0-rc.3.26522.148\
```

> La RC mesurée ici (`rc.3.26522.148`) est **plus récente** que celle du document de famille
> (`rc.1.26425.128`, 2026-10-02) : les deux lignes ne mesurent pas exactement le même binaire.

## Résultats (n = 25 runs par runtime et par configuration)

| Configuration | net10 — médiane [min-max] | net11 — médiane [min-max] | delta | verdict |
|---|---:|---:|---:|---|
| **[A]** `ExecuteSynchronously`, **sans** `RunContinuationsAsynchronously` | 80,04 ms [71,82 – 103,48] | 81,45 ms [70,59 – 116,79] | **+1,76 %** | **INCONCLUSIF** (intervalles chevauchants) |
| **[B]** `ExecuteSynchronously`, **avec** `RunContinuationsAsynchronously` | 0,01 ms [0,01 – 0,02] | 0,01 ms [0,01 – 0,02] | +0,00 % | **NON RESOLU** (sous le plancher de résolution) |

Médianes par répétition (5 par runtime) — c'est là que se lit la dispersion :

| Runtime | répétition 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|
| net10 | 80,04 | 73,94 | 86,36 | 75,21 | 98,79 |
| net11 | 98,98 | 75,55 | 101,13 | 73,42 | 82,72 |

### Le mécanisme est intact sous .NET 11

L'instrument ne mesure pas seulement un temps : il **discrimine** encore les deux leviers, sous les
deux runtimes.

- **[A]** : identifiants de thread natif/reprise **identiques** dans les 5 runs et sous les 2 runtimes
  → la continuation s'exécute toujours **en ligne** sur le thread natif ;
- **[B]** : identifiants **différents** dans les 5 runs et sous les 2 runtimes → la continuation part
  toujours sur le pool managé.

La .NET 11 RC ne change donc **pas** la sémantique des deux leviers : ce qui est mesuré est bien la
même chose des deux côtés.

## Verdict

**Aucun gain .NET 11 n'est établi sur l'axe 1 des awaits profonds.** À n = 25, l'écart de médiane
mesuré est de **+1,76 %** (80,04 → 81,45 ms), soit l'ordre de grandeur de la dispersion
intra-runtime : les deux intervalles [min,max] se chevauchent largement (71,82–103,48 contre
70,59–116,79). La lecture honnête est **INCONCLUSIF**, pas « pas de différence » : l'instrument
permet de dire qu'aucun gain significatif n'est visible à cette taille d'échantillon, pas
d'établir l'absence d'effet.

**La répétition était nécessaire, et elle l'a montré.** Trois passes à n = 5 (5 runs internes, une
répétition) ont été faites sur cette machine. Elles n'ont **aucun accord entre elles** :

| Passe | net10 (médiane) | net11 (médiane) | delta annoncé | verdict |
|---|---:|---:|---:|---|
| manuelle, avant l'organe (cf. commentaire de claim de #23444) | 80,81 ms | 76,72 ms | −5,07 % | INCONCLUSIF |
| smoke de l'organe, n = 5 (`probe_smoke.json`) | 98,28 ms | 88,09 ms | −10,37 % | INCONCLUSIF |
| smoke de l'organe après refonte des imports, n = 5 | 110,20 ms | 112,98 ms | +2,52 % | INCONCLUSIF |
| **organe, n = 25** | **80,04 ms** | **81,45 ms** | **+1,76 %** | **INCONCLUSIF** |

À n = 5, le delta annoncé varie de **−10,37 % à +2,52 %** d'une passe à l'autre, et le signe
lui-même n'est pas stable : deux passes annoncent un gain de .NET 11, la troisième une perte.
C'est exactement le comportement d'un bruit de mesure — et la raison pour laquelle le verdict à
n = 5 n'avait pas de valeur, quel que soit le nombre qu'il affiche. La taille d'échantillon
n'est pas un détail de forme : c'est elle qui décide si un écart existe.

### Ce que cette mesure ne dit pas

- **[B] n'est pas comparable**, et ce n'est pas un échec : la grandeur y est le coût d'une simple
  notification (0,01–0,02 ms), sous le plancher de résolution de la mesure. Le bruit de la mesure
  y décide de l'écart, pas le runtime.
- **Ce n'est pas un banc BDN** : l'instrument §4 vise la grandeur runtime-sensible du carnet, pas
  le débit d'un banc de compilation. Les bancs du document de famille mesurent autre chose.
- **Une seule machine, une seule charge** : la dispersion intra-runtime (≈ ±20 %) est large ; un
  hôte au repos ou une charge CI plus faible réduirait cette dispersion et permettrait un seuil plus
  fin. Le verdict ci-dessus vaut pour les conditions **du tableau « Conditions »**.
- **Le wall-clock du carnet n'est pas rejoué** : il est dominé par le démarrage kernel + Roslyn et
  ne distingue pas les runtimes (le document de famille le dit déjà). La valeur `11,0 s` de la
  colonne `net10` du document de famille n'a donc pas de pendant `net11` à comparer — c'est la
  grandeur §4 qui est comparée ici.

## Reproduction

```bash
python scripts/notebook_tools/multiruntime_probe.py \
  --notebook MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/08-Aspire-AsyncFFI-Dotnet.ipynb \
  --index 8 \
  --runtime "net10=C:/Program Files/dotnet" \
  --runtime "net11=C:/Users/jsboi/.dotnet-r11" \
  --repeats 5 --timeout 900 --json probe_net10_net11_n25.json
```

L'organe **n'écrit jamais dans le carnet** : il lit la cellule source, exécute dans un kernel
jetable et garde les sorties en mémoire.

## Ligne à reporter dans le document de famille

Le document de famille (`net11-runtime-deltas.md`) porte encore `non mesuré` pour
`08-Aspire-AsyncFFI-Dotnet.ipynb`. Ses deux PRs (#23326, #23421) étant en cours sur ce fichier, le
renvoi croisé est **laissé à qui mergera** pour éviter un conflit sur une PR déjà relue. La ligne à
reporter, une fois le fichier déverrouillé :

> `08-Aspire-AsyncFFI-Dotnet.ipynb` | 11,0 s | **80,04 ms [71,82 – 103,48] (n=25, instrument §4)** | **+1,76 %** — **INCONCLUSIF** (intervalles chevauchants) ; compat .NET 11 **établie** (RC 11.0.0-rc.3.26522.148) | voir `net11-async-ffi-deltas.md`
