# Controleur de debordement CI (phase B) — `CI_OVERFLOW_LOCAL`

Volet 1 de [#22937](https://github.com/jsboige/CoursIA/issues/22937) : la **phase B** de la repartition hebergee / local.

## Ce que la variable decide

La **phase A** ([#22921](https://github.com/jsboige/CoursIA/pull/22921)) a pose la **forme hybride** des workflows de garde : une seule variable de depot, `CI_OVERFLOW_LOCAL`, decide si un job part sur le parc local (legende Linux) ou sur l'offre GitHub-hosted.

```yaml
runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository && vars.CI_OVERFLOW_LOCAL == 'true') && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-latest' }}
```

- variable a `true` -> PR meme-depot : jambe **locale** ;
- variable absente ou a `false` -> **GitHub-hosted** ;
- les forks, le `workflow_dispatch` et les crons restent heberges (la garde est liee a l'evenement `pull_request`).

La phase A est **manuelle** (un operateur pose la variable). La phase B, decrite ici, la **pilote**.

## La regle de decision

| etat mesure | decision |
|---|---|
| offre hebergee **saturee** (au moins `--saturation-jobs` jobs `ubuntu-latest` en file depuis plus de `--saturation-minutes`) **et** parc local libre (au moins `--min-free-slots` slots en ligne **et libres**) | variable a `true` |
| file hebergee **videe** (au plus `--drain-jobs` job en file) | variable a `false` |
| parc local **lui-meme affame** (des jobs `coursia-linux` attendent) | variable a `false` (on rend la main a l'heberge) |
| sinon | **HOLD** (rien n'est ecrit) |

Un **dwell** de `--dwell-minutes` (30 par defaut) interdit deux bascules rapprochees : une variable qui oscille est pire qu'une variable stable.

L'organe est **fail-CLOSED** : une mesure illisible (listing incomplet, inventaire des runners inaccessible) ne produit **aucune** ecriture.

## Usage

```bash
# verdict seul (defaut : dry-run, aucune ecriture)
python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --json

# application effective
python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --apply --json
```

Codes de retour : `0` nominal (HOLD ou bascule), `1` mesure illisible (`UNREADABLE`), `2` refus (`REFUSED` : jeton absent ou droit insuffisant).

## Prerequis — a installer, jamais suppose

Un jeton (GitHub App installee ou PAT) avec le droit **`variables: write`** sur `jsboige/CoursIA`, expose au workflow comme secret de depot **`ACTIONS_VARIABLES_PAT`** :

```
gh secret set ACTIONS_VARIABLES_PAT --repo jsboige/CoursIA
```

Tant que le secret n'est pas provisionne, le workflow rend un verdict en **lecture seule** (avec le jeton du workflow) et n'ecrit rien : l'absence de bascule apparait dans le resume de job, elle n'est pas silencieuse.

> Le `GITHUB_TOKEN` d'un workflow ne porte pas le droit `variables: write` : le controleur ne peut pas s'appuyer dessus pour la bascule.

## Mesure de reference (2026-10-27, `origin/main`)

```json
{
  "verdict": "HOLD",
  "reason": "deja a true -- offre hebergee saturee (148 job(s) en file depuis plus de 15 min, plus ancien 86 min) et parc local libre (29 slot(s)) -- le local absorbe",
  "current": "true",
  "hosted": {"queued": 151, "old": 148, "oldest_age_min": 86.3, "complete": true},
  "local": {"online": 32, "free": 29, "starved": 0, "complete": true}
}
```

Lecture : au moment de la mesure, l'offre hebergee portait **151 jobs en file** (dont 148 de plus de 15 min, le plus ancien a 86 min) pendant que le parc local availait **29 slots libres sur 32 en ligne**. La variable etait deja a `true` : le controleur **n'ecrit rien** (etat deja au bout).

## Cout de l'organe

Deux lectures de file, plafonnees (`--job-budget` 120, `--local-job-budget` 40 lectures de jobs). Le volume d'appels API est precisement l'objet du **volet 5** de #22937 : un organe de controle ne doit pas en devenir la cause. Le workflow ne fait **qu'une seule mesure** par passage (verdict et bascule dans le meme appel).

## Cadence et tolerance

Le workflow tourne deux fois par heure (`23,53 * * * *`). La **livraison** des crons du depot est tardive et irreguliere (mesure : 22 % des tics horaires servis, mediane 289 min pour une cadence declaree de 60 min sur `pr-gate-stale-sweep` -- cf [volet 6](#22937)). Le controleur est **une machine a etat sur une variable** : un passage tardif agit sur l'etat courant, il n'accumule pas de retard. C'est aussi pourquoi le dwell est court (30 min) : il ne sert qu'a amortir l'oscillation, pas a cadencer.

## Voir aussi

- [#22921](https://github.com/jsboige/CoursIA/pull/22921) — phase A, la forme hybride des 25 workflows ;
- `scripts/ci/check_self_hosted_runner_policy.py` — l'instrument qui enumere les formes de `runs-on` auditees ;
- `scripts/ci/check_runner_starvation.py` — l'organe de sante du parc, dont le controleur reutilise la mesure de file et l'inventaire des slots ;
- [volet 5 — debit DNS vers api.github.com](dns-rate-measurement.md) — l'autre moitie du cout de la CI.
