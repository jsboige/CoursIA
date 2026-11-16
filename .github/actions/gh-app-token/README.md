# Action composite `gh-app-token`

Rend un jeton pour les appels REST, dans un **seau de quota distinct** de celui
de `GITHUB_TOKEN` quand une App GitHub est configuree, et se replie sur
`GITHUB_TOKEN` sinon.

## Pourquoi

Le jeton du depot (`GITHUB_TOKEN`) plafonne a **1 000 appels/h pour
l'ensemble du depot**, partage par tous les jobs qui l'utilisent. Le
recensement du volet B de #26739 (mesure du 2026-11-15) attribute a un seul
cron horaire ~630 appels/h -- soit 63 % du plafond pour un seul consommateur.
Quand le seau est vide, une jambe `PR gate` attend le reset en tenant un
runner : 59 min de runner pour 3 appels (jobs 132806296573 et 132806304780,
le 15/11).

Le jeton d'installation d'une App a son **propre** seau de quota. Utiliser ce
jeton la ou le travail est de LECTURE (lister des files, des runs, des PRs)
retire cette depense du seau partage, sans changer le comportement du job.

## Usage

```yaml
      - name: Resolve the REST token
        id: gh-token
        uses: ./.github/actions/gh-app-token
        with:
          app-id: ${{ secrets.APP_ID }}
          private-key: ${{ secrets.APP_PRIVATE_KEY }}

      - name: Mesure
        env:
          GH_TOKEN: ${{ steps.gh-token.outputs.token }}
        run: gh api ...
```

L'appel est **local** (`./.github/actions/...`) : le checkout du job doit
donc inclure `.github/actions` dans son `sparse-checkout`. Un appel distant
(`jsboige/CoursIA/.github/actions/gh-app-token@main`) ferait telecharger
l'archive codeload du depot **entier** a l'etape « Set up job » -- de quoi
faire tomber la totalite des workflows qui l'utilisent (mesure eteffee sur
`heal-worktree`, cf `scripts/tests/test_heal_worktree_action.py`).

## Inertie

Tant que le secret n'est pas pose, l'etape App est **sautee** et le repli
rend `github.token` : le job se comporte exactement comme avant. Le mecanisme
ne peut donc pas casser un workflow par lui-meme. La sortie `source` dit
lequel des deux s'est applique (`app` / `github-token`), et le journal porte
une ligne `api-quota: source=...`.

Si l'App existe mais que le jeton ne peut pas etre cree (App desinstallee,
secret expire), l'etape App echoue **sans faire echouer le job**
(`continue-on-error: true`) et le repli s'applique.

## Droits requis de l'App

Les droits d'un jeton d'installation viennent de l'installation de l'App, pas
du bloc `permissions:` du workflow. Pour les consommateurs listes ci-dessous :

| consommateur | droits de l'App |
|---|---|
| `ci-overflow-controller.yml` (lecture de files et de runs, annulation/relance de cohortes) | `actions: read` + `actions: write`, `contents: read` |
| consommateurs en ecriture (`gh pr edit`, `gh pr comment`, `gh api --method PATCH`, `gh run rerun`) | `pull-requests: write`, `issues: write`, `checks: write`, `actions: write` |

Le secret et l'installation de l'App sont un geste du coordinateur.

## Test

`scripts/tests/test_gh_app_token_action.py` -- le repli **sans secret** est
execute pour de vrai (le script du depot est lance dans un bash honnete) :
sortie `token=<repli>` + `source=github-token`, code retour 0. Les deux
autres branches -- jeton d'App present, aucun jeton du tout -- sont executees
aussi.

Commande :

```bash
python -m pytest scripts/tests/test_gh_app_token_action.py -q
```
