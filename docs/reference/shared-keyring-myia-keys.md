# Trousseau partagé `MyIA-Keys` — organe d'accès, bootstrap par machine, empreinte de preuve

Détail durable de l'organe `scripts/secrets/agent_keyring.py`. La règle qui le gouverne reste
[.claude/rules/secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — ce fichier ne pose
aucune prescription nouvelle, il documente un outil et l'état vérifié de son déploiement.

## Ce que c'est, et ce que ce n'est pas

Le user a créé le 2026-09-22 un coffre KeePass partagé et y a exporté son dossier `Agents` :

```
G:\Mon Drive\Synchronisation\RooSync\.shared-state\MyIA-Keys.kdbx
```

La passphrase maîtresse est saisie dans un PDF de secours (§ « Le PDF d'urgence » ci-dessous).

**Le coffre porte aujourd'hui des mots de passe de connexion GitHub, pas des PAT.** C'est le
constat le plus important de cette page, et il est mesurable : `verify` rend `secret=mot de passe`
sur les entrées peuplées. Conséquence opérationnelle — **le coffre n'est pas encore un canal de
distribution de jetons**. `gh auth login --with-token` refuse un mot de passe de compte, avec un
message d'erreur qui ne nomme pas la cause ; c'est précisément pour éviter ce diagnostic à
l'aveugle que l'organe tranche lui-même sur la **forme** du secret et refuse avant d'appeler `gh`.

Émettre un PAT par compte (scopes minimaux) et le ranger dans son entrée reste la **phase C**
de #17418 : entièrement devant nous, pas un résidu.

## L'organe — `scripts/secrets/agent_keyring.py`

**Règle cardinale : aucune sous-commande n'imprime un secret par défaut.** Une valeur est soit
tubée vers son consommateur (`gh-login`, `--to-env-file`), soit rendue masquée. Il n'existe pas de
sous-commande « affiche-moi la clé ».

| Sous-commande | Ce qu'elle fait |
|---|---|
| `bootstrap` | Extrait la passphrase du PDF d'urgence et la pose dans le gestionnaire d'identifiants Windows. `--from-stdin` en repli si l'extraction échoue. |
| `doctor` | État du dispositif sur CETTE machine + **empreinte de la passphrase** (voir ci-dessous). |
| `list` | Titres et usernames des entrées. Aucun secret. |
| `show <entrée>` | Métadonnées d'une entrée : titre, groupe, user, url, **nature** du secret, date de modification. |
| `verify` | Chaque compte attendu a-t-il une entrée, et son secret est-il utilisable comme jeton ? |
| `get <entrée>` | Écrit la valeur vers un `.env` (`--to-env-file`), **après avoir vérifié que git l'ignore**. |
| `gh-login <entrée>` | Tube le jeton dans `gh auth login --with-token`. Refuse si le secret n'est pas un jeton. |

### Deux gardes qui méritent d'être connus

**`get` refuse d'écrire dans un fichier que git ne prouve pas ignoré.** « Non suivi » ne suffit
pas : un fichier peut n'être ignoré que par `.git/info/exclude`, **local au clone et non
versionné**, donc pas ignoré chez le voisin. L'organe emprunte la mesure de l'organe de couverture
des secrets (`scripts/ci/check_secret_paths_ignored.py`, #17442) : `git check-ignore -v --no-index`
**nomme la source gagnante**. Une source locale au clone (`.git/info/exclude`, `core.excludesFile`)
est refusée en la nommant, un motif de négation `!` gagnant compte comme « non ignoré », et l'organe
refuse (`EXIT_UNKNOWN`) quand il n'a pas pu mesurer plutôt que de supposer. `--allow-unignored` existe et se justifie dans le body de la PR qui l'emploie.

**La nature du secret se tranche sur la FORME, jamais sur le nom de l'entrée.** Un titre
`github ai-01` ne prouve pas que l'entrée contient un PAT. `secret_kind()` rend `vide` / `jeton` /
`mot de passe` en confrontant la valeur au format documenté des jetons GitHub.

### L'entrée se cherche par son titre ET par son username

Une entrée est demandable sous son **titre** (`github ai-01`) ou sous son **username**
(`myia-ai-01`). Ces deux clés ne coïncident pas dans ce coffre, et ne pas le savoir a produit
deux défauts opposés de même racine : `verify` rendait `0/6` sur un coffre qui en portait 5
(sur-accusation), et `gh-login` comparait à `None` — donc **le contrôle de compte ne s'exécutait
jamais** et un jeton du mauvais compte serait passé en silence (sous-accusation muette).

## Bootstrap : pourquoi il n'y a pas d'alternative à une empreinte publiée

La passphrase est rangée dans le **gestionnaire d'identifiants Windows** (DPAPI), via `keyring`.
Ce stockage est **lié au profil utilisateur Windows** : il n'est ni exportable, ni transférable,
ni interrogeable à distance. Aucune machine ne peut donc vérifier qu'une autre a bootstrappé.

C'est la contrainte qui dicte tout le reste : **une empreinte publiée est le seul moyen de preuve
cross-machine disponible.** Chaque lane lance `doctor`, lit son empreinte, et la compare à la
référence publiée sur le dashboard `global`.

```bash
python scripts/secrets/agent_keyring.py bootstrap
python scripts/secrets/agent_keyring.py doctor     # imprime l'empreinte à comparer
```

- **Empreinte identique** → la machine est enregistrée.
- **Empreinte différente** → **ne rien écrire dans le coffre**, et le signaler. Une divergence est
  soit une passphrase différente, soit une copie GDrive en retard : les deux se traitent, aucune
  ne se contourne.

### L'empreinte est un PBKDF2, et le sel est public par nécessité

```
empreinte : <32 car.> pbkdf2:85bd9366fb37
```

`fingerprint()` est un **PBKDF2-HMAC-SHA256 à 600 000 tours** (recommandation OWASP 2023), sel
public et fixe. Les trois propriétés sont voulues, et chacune répond à une contrainte :

1. **Déterministe** — sans quoi deux machines ne pourraient pas comparer. C'est aussi ce qui
   impose un sel **fixe** : un sel aléatoire rendrait la comparaison impossible. Ce sel ne cache
   rien, il sépare les domaines.
2. **Coûteuse à forcer** — l'empreinte est **publiée sur un dashboard partagé**, ce qui en fait un
   oracle hors-ligne : deviner, hacher, comparer. Un sha256 y répondrait en microsecondes ; PBKDF2
   600k y met ~0,3 s. Sur une passphrase à haute entropie le risque restait théorique ; il ne
   l'est pas sur un secret faible, et un organe générique ne choisit pas ce qu'on lui donne.
   CodeQL a ouvert `py/weak-sensitive-data-hashing` sur la version sha256, et l'alerte portait.
3. **Payée une fois** — `doctor` l'appelle une seule fois, mesure de bout en bout : 0,9 s.

**La longueur (`<32 car.>`) est conservée délibérément.** Quand deux machines divergent, l'écart
de longueur rend la cause **lisible** — une extraction tronquée — là où un écart de hash est muet.
Sur un secret de 32 caractères à haute entropie, la divulgation est négligeable face à ce gain de
diagnostic. La même longueur a en revanche été **retirée** de `show` et `verify` sur les entrées :
là elle ne tranchait aucune décision (`secret_kind()` distingue déjà `vide`), donc elle n'était
que de la surface en plus. Une longueur qui diagnostique se garde ; une longueur qui décore se
retire.

### Les entrées du coffre n'ont pas d'empreinte, et c'est structurel

Le coffre est **partagé** : ses entrées sont identiques sur toutes les machines par construction.
Il n'y a rien à comparer, donc rien à empreindre. Le seul cas réel — détecter une copie GDrive en
retard — est déjà couvert par le champ `modifiee` que `show` affiche. Seule la passphrase garde
une empreinte, parce qu'elle est la seule chose stockée **par machine**.

## Le PDF d'urgence, et son critère de retrait

```
G:\Mon Drive\MyIA\IA\Emergency MyIA Keys.pdf
```

Ce PDF porte la passphrase maîtresse, saisie par le user via PDFgear en annotation `/FreeText`.
L'extraction lit `/Contents` (jumeau texte brut) **et** `/RC` (XHTML riche, dont les runs de style
peuvent découper une valeur en plusieurs fragments) ; c'est ce second cas qui avait fait échouer
les premières tentatives.

**Le PDF est la seule voie de rattrapage tant qu'une machine n'a pas bootstrappé.** Le user a
donné son feu vert à la suppression le 2026-09-22 — il détient la passphrase dans son propre
KeePass, le risque de perte est donc levé — **conditionné à ce que toutes les machines soient
enregistrées**.

Critère de retrait, mesurable : **7/7 empreintes concordantes**.

| Machine | Compte GitHub |
|---|---|
| `myia-ai-01` | `myia-ai-01` |
| `myia-po-2023` | `myia-po-2023` |
| `myia-po-2024` | `myia-po-2024` |
| `myia-po-2025` | `myia-po-2025` |
| `myia-po-2026` | `myia-po-2026` |
| `myia-po-2027` | `myia-po-2027` |
| `myia-web1` | `MyIA-Web1` |

**La flotte compte sept machines, pas six.** `web1` n'apparaît pas dans
[cluster-agents.md](cluster-agents.md) — non par omission de ce document, mais parce qu'il décrit
les machines portant des **grains CoursIA**, et que web1 travaille sur `roo-extensions`. Pour le
trousseau, la population pertinente est « toute machine de la flotte », et elle est plus large.
Un document fait autorité sur **la population qu'il décrit**, pas au-delà.

## Le trou `.secrets/` — fermé par #17442

`.gitignore` énumérait des fichiers de secrets un par un, et **`.secrets/master.env` — la source
unique désignée par `secrets-hygiene.md` — n'y figurait pas**. Il ne devait son exclusion qu'à
`.git/info/exclude`, local à un clone et non versionné : sur toute autre machine, un `git add -A`
l'aurait stagé.

Cette PR portait d'abord son propre correctif ; #17442 l'a livré entre-temps, avec une garde CI
(`scripts/ci/check_secret_paths_ignored.py`) qui sépare une source versionnée d'une source locale.
L'organe du trousseau réutilise cette mesure pour `get` au lieu d'en tenir une seconde. La leçon
générale reste : **un test d'ignorance lancé dans ce clone mesure ce clone, pas le dépôt** — et une
énumération est par construction aveugle au fichier qu'on ajoutera demain.

## Voir aussi

- [.claude/rules/secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — la règle
- [genai/secrets-management.md](../genai/secrets-management.md) — `.secrets/master.env` + `render_envs.py`
- [.claude/rules/codeql-suppressions-inertes.md](../../.claude/rules/codeql-suppressions-inertes.md) — pourquoi la rationale d'une alerte va dans le body de la PR
- #17418 — provisionnement d'un jeton par lane (phase C : émettre les PAT)
