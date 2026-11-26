# Instance jetable « Maison Valmont »

[← AI Engine (WordPress)](../README.md) | [↑ Plateformes conversationnelles](../../README.md) | [Les fonctionnalités par l'API →](../03-Functional/README.md)

Un WordPress local, monté sous Docker, sur lequel s'exécutent les carnets qui
présentent **AI Engine par son API** — à commencer par
[`presenter-ai-engine-par-son-api.ipynb`](../03-Functional/03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb) —
et d'où proviennent les captures du [tour de la plateforme](../00-Tour-Plateforme/README.md).

Pourquoi une instance dédiée : ces carnets appellent une API réelle, et leurs
sorties sont publiées avec eux. Un site en service contient des données qui
n'ont pas leur place dans un dépôt public (catalogue, noms, manuscrits).
Cette instance-ci ne contient que du fictif — un WordPress vierge, un chatbot
au nom d'une maison d'édition imaginaire, « Maison Valmont », et ce que les
carnets y créent eux-mêmes — et elle se détruit d'une commande
(`docker compose down -v` efface tout).

## Contenu

| Fichier | Rôle |
|---------|------|
| [`docker-compose.jetable.example.yml`](docker-compose.jetable.example.yml) | Pile WordPress 6.8.3, MariaDB 10.11 et wp-cli ; port `8093` par défaut |
| [`seed-valmont.php`](seed-valmont.php) | Branche AI Engine sur le moteur de langage local, déclare actifs les modules du plugin, crée le chatbot « valmont », ouvre l'API publique |
| [`.env.example`](.env.example) | Variables attendues (à copier vers `.env` ; ne jamais commiter `.env`) |

## Prérequis

- Docker (Desktop sous Windows et macOS, ou daemon natif sous Linux) ;
- un **moteur de langage local compatible OpenAI** (`/v1/chat/completions`) :
  Ollama (`http://localhost:11434/v1`), vLLM, LM Studio… — la variable
  `VALMONT_LLM_BASE_URL` donne son adresse ;
- Python 3.10 ou plus récent, avec `requests` et `python-dotenv`, pour exécuter
  les carnets ;
- pour le carnet `mesurer-la-derive-dun-copilot.ipynb`, un **modèle
  d'embeddings** servi par le même moteur (`/v1/embeddings`) —
  `ollama pull bge-m3`. Sans lui, la partie du carnet qui rejoue la chaîne sur
  l'instance se met d'elle-même en retrait (ses cellules le signalent) et le
  reste s'exécute.

## Montage en 5 étapes

### 1. Configurer `.env`

```powershell
Copy-Item .env.example .env
# puis éditer .env : port, admin, URL du LLM local (host.docker.internal pour Docker Desktop)
```

> Sur Linux natif, `host.docker.internal` n'existe pas : utiliser l'IP de la
> passerelle Docker, par exemple `http://172.17.0.1:11434/v1`.

Docker Compose lit ce fichier de lui-même ; la session PowerShell, non. Les
commandes des étapes 3 et 5 utilisent `$env:VALMONT_ADMIN_USER` et ses
voisines : il faut donc charger le fichier dans la session avant de les lancer.

```powershell
foreach ($l in Get-Content .env) { if ($l -match '^([A-Z_]+)=(.*)$') { Set-Item "env:$($Matches[1])" $Matches[2] } }
```

### 2. Lancer la pile

```powershell
docker compose -f docker-compose.jetable.example.yml up -d
# attendre que wordpress soit healthy (docker ps)
```

### 3. Installer WordPress et AI Engine

```powershell
# URL à aligner sur VALMONT_PORT
docker exec valmont-wordpress_cli-1 sh -c "wp core install --url=http://localhost:8093 --title='Maison Valmont' --admin_user=$env:VALMONT_ADMIN_USER --admin_password=$env:VALMONT_ADMIN_PASSWORD --admin_email=$env:VALMONT_ADMIN_EMAIL --skip-email --allow-root"

# AI Engine 3.7.0 — version gratuite, téléchargée depuis wordpress.org (reproductible)
docker exec valmont-wordpress_cli-1 sh -c "curl -sL -o /tmp/ai-engine.zip https://downloads.wordpress.org/plugin/ai-engine.3.7.0.zip && wp plugin install /tmp/ai-engine.zip --activate --allow-root"
```

### 4. Peupler (seed)

```powershell
docker cp seed-valmont.php valmont-wordpress_cli-1:/tmp/seed-valmont.php
docker exec valmont-wordpress_cli-1 sh -c "php /tmp/seed-valmont.php"
```

Le script branche AI Engine sur le moteur local (variables `VALMONT_LLM_*`),
déclare actifs les modules du plugin (chatbots, embeddings, serveur MCP,
formulaires, entre autres), crée le chatbot « valmont » et autorise les mots de
passe d'application.

### 5. Créer le mot de passe d'application, puis exécuter les carnets

```powershell
docker exec valmont-wordpress_cli-1 sh -c "wp user application-password create $env:VALMONT_ADMIN_USER notebooks --porcelain --allow-root"
# -> copier la clé dans .env, variable VALMONT_APP_PASSWORD
```

Les carnets lisent `instance-jetable/.env` : adresse de l'instance, compte
administrateur, mot de passe d'application. Rien d'autre n'est requis pour la
plupart d'entre eux — ils appellent l'API de l'instance en HTTP local.

## Variables du fichier `.env`

| Variables | Ce qu'elles portent | Qui les lit |
|-----------|---------------------|-------------|
| `VALMONT_PORT`, `VALMONT_BASE_URL` | Port publié par Docker, et adresse de l'instance vue depuis la machine hôte | La pile Docker pour le port ; les carnets pour l'adresse |
| `VALMONT_DB_*` | Base MariaDB de la pile | La pile Docker |
| `VALMONT_ADMIN_USER`, `VALMONT_ADMIN_PASSWORD`, `VALMONT_ADMIN_EMAIL` | Compte administrateur créé à l'étape 3 | L'installation ; les carnets, pour le nom du compte |
| `VALMONT_LLM_BASE_URL`, `VALMONT_LLM_API_KEY`, `VALMONT_LLM_MODEL`, `VALMONT_LLM_MODEL_NAME` | Moteur de langage, tel que le voit le conteneur | Le script de l'étape 4 ; quelques carnets, pour le nom du modèle |
| `VALMONT_APP_PASSWORD` | Mot de passe d'application créé à l'étape 5 | Les carnets |
| `VALMONT_EDITOR_PASSWORD` | Mot de passe du compte de test au rôle éditeur | Les carnets qui créent ou réutilisent ce compte |
| `VALMONT_LLM_BASE_URL_MOTEUR`, `VALMONT_LLM_API_KEY_MOTEUR` | Le même moteur, vu cette fois depuis la machine hôte (facultatif) | Les carnets qui interrogent le moteur sans passer par WordPress |

Deux précisions sur les trois dernières lignes.

**Le moteur vu de deux endroits.** Le conteneur atteint le moteur par
`host.docker.internal` ; un carnet, qui tourne sur la machine hôte, l'atteint
par `127.0.0.1`. D'où deux variables pour un seul service. Les carnets qui
s'adressent au moteur directement — pour le comparer à ce que rend le plugin,
l'évaluer seul ou calculer des embeddings — lisent la seconde.
`mesurer-la-derive-dun-copilot.ipynb` est de ceux-là : il mesure la dérive sur
les embeddings du **même** moteur que celui qui réécrit le texte, et il lui
faut donc un modèle d'embeddings déjà tiré.

```powershell
ollama pull bge-m3
```

**Le compte de test.** Le compte `consent.editor` est créé par le carnet sur
l'OAuth du serveur MCP, puis réutilisé par ceux qui interrogent l'assistant de
l'éditeur et la mémoire éphémère du chatbot. Son mot de passe se choisit
librement dans `VALMONT_EDITOR_PASSWORD` : aucun carnet ne porte de valeur par
défaut.

## Vérification rapide

```powershell
curl http://localhost:8093/wp-json/    # répond {name: "Maison Valmont", ...}
```

Pour vérifier l'accès authentifié (chatbots, completions), exécuter
`presenter-ai-engine-par-son-api.ipynb` : c'est exactement ce que font ses
premières cellules de code, avec le mot de passe d'application lu dans `.env`.

## Maintenance

### Dépôt de fichiers : permission du dossier `uploads`

Si un appel à `mwai-ui/v1/files/upload` rend 500 « Could not move the file. »,
le dossier `wp-content/uploads/` du conteneur n'appartient pas à WordPress (le
volume monté peut être créé par root au premier démarrage) :

```bash
docker exec valmont-wordpress-1 sh -c "chown -R www-data:www-data /var/www/html/wp-content/uploads"
```

Après quoi le dépôt passe. Les carnets qui joignent un fichier au chatbot ou
lui donnent une mémoire éphémère rappellent cette précondition dans leurs
prérequis.

## Nettoyage

```powershell
docker compose -f docker-compose.jetable.example.yml down -v   # détruit volumes et données
```

## Règles

- Aucune donnée réelle, aucun secret, aucune adresse de fournisseur dans le
  dépôt : tout passe par `.env` (le gabarit est versionné, les valeurs réelles
  ne le sont jamais).
- Les sorties publiées avec les carnets proviennent d'exécutions réelles contre
  cette instance. Plusieurs carnets passent les réponses du modèle par une
  fonction d'affichage (`clean_text`) qui retire pictogrammes et balisage : un
  moteur local en émet parfois malgré les consignes.
