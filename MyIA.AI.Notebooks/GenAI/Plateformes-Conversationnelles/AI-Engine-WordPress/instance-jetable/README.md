# Instance jetable « Maison Valmont »

Instance WordPress jetable, dediee a la serie de notebooks
`presenter-ai-engine-par-son-api.ipynb` et suivants : ils presentent
**AI Engine par son API** — fonctionnalites de base et avancees, et ce qu'on
en a fait dans le projet Livres Agites.

Pourquoi une instance dediee : les notebooks appellent une API reelle.
L'instance du projet contient des donnees client (livres, noms, manuscrits) —
elle est donc exclue du depôt public. Cette instance-ci est 100 % jetable
(`docker compose down -v` efface tout) et peuplée d'un corpus synthetique
« Maison Valmont », maison d'edition fictive.

## Contenu

| Fichier | Role |
|---------|------|
| `docker-compose.jetable.example.yml` | Pile WordPress 6.8.3 + MariaDB + wp-cli, port 8093 |
| `seed-valmont.php` | Branche AI Engine sur le LLM local, cree le chatbot « valmont », active l'API publique |
| `.env.example` | Variables attendues (copier vers `.env`, ne jamais commiter `.env`) |

## Prérequis

- Docker (Desktop sur Windows/macOS, ou daemon natif sous Linux) ;
- Un **LLM local compatible OpenAI** (`/v1/chat/completions`) : Ollama
  (`http://localhost:11434/v1`), vLLM, LM Studio, ... — la variable
  `VALMONT_LLM_BASE_URL` le decrit ;
- Python 3.10+ avec `requests` et `python-dotenv` pour executer les notebooks.

## Montage en 5 étapes

### 1. Configurer `.env`

```powershell
Copy-Item .env.example .env
# puis editer .env : port, admin, URL du LLM local (host.docker.internal pour Docker Desktop)
```

> Sur Linux natif, `host.docker.internal` n'existe pas : utiliser l'IP de la
> passerelle Docker, par exemple `http://172.17.0.1:11434/v1`.

### 2. Lancer la pile

```powershell
docker compose -f docker-compose.jetable.example.yml up -d
# attendre que wordpress soit healthy (docker ps)
```

### 3. Installer WordPress + AI Engine

```powershell
# URL a aligner sur VALMONT_PORT
docker exec valmont-wordpress_cli-1 sh -c "wp core install --url=http://localhost:8093 --title='Maison Valmont' --admin_user=$env:VALMONT_ADMIN_USER --admin_password=$env:VALMONT_ADMIN_PASSWORD --admin_email=$env:VALMONT_ADMIN_EMAIL --skip-email --allow-root"

# AI Engine 3.7.0 — version gratuite, telechargee depuis wordpress.org (reproductible)
docker exec valmont-wordpress_cli-1 sh -c "curl -sL -o /tmp/ai-engine.zip https://downloads.wordpress.org/plugin/ai-engine.3.7.0.zip && wp plugin install /tmp/ai-engine.zip --activate --allow-root"
```

### 4. Peupler (seed)

```powershell
docker cp seed-valmont.php valmont-wordpress_cli-1:/tmp/seed-valmont.php
docker exec valmont-wordpress_cli-1 sh -c "php /tmp/seed-valmont.php"
```

Le seed branche AI Engine sur le LLM local (`VALMONT_LLM_*`), cree le chatbot
« valmont » et autorise les application passwords.

### 5. Creer l'application password, puis executer les notebooks

```powershell
docker exec valmont-wordpress_cli-1 sh -c "wp user application-password create $env:VALMONT_ADMIN_USER notebooks --porcelain --allow-root"
# -> copier la cle dans .env, variable VALMONT_APP_PASSWORD
```

Les notebooks lisent `instance-jetable/.env` (base URL + admin + app password).
Rien d'autre n'est requis : ils appellent l'API de l'instance en HTTP local.

## Verification rapide

```powershell
curl http://localhost:8093/wp-json/    # repond {name: "Maison Valmont", ...}
```

Pour verifier l'acces authentifie (chatbots, completions), executer
`presenter-ai-engine-par-son-api.ipynb` : c'est exactement ce que font ses
cellules 3 a 6, avec l'application password lu depuis `.env`.

## Nettoyage

```powershell
docker compose -f docker-compose.jetable.example.yml down -v   # detruit volumes et donnees
```

## Regles du chantier (rappel)

- Aucune donnee client, aucun secret, aucune IP de provider dans le depôt :
  tout passe par `.env` (exemple versionne, valeurs reelles jamais commitees).
- Les sorties commitees des notebooks proviennent d'executions reelles contre
  cette instance ; les reponses du modele sont normalisees par du code
  (le LLM local peut emettre des emojis/markdown malgre les consignes).
