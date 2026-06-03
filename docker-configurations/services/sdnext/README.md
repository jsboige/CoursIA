# SD.Next - Stable Diffusion WebUI

## Vue d'ensemble

| Propriete | Valeur |
|-----------|--------|
| Modele | SDXL / SD1.5 |
| Port | 7861 |
| GPU | GPU 1 (RTX 3090) |
| VRAM | ~3 GB |
| URL cloud | https://sdnext.myia.io |

## Demarrage

```bash
# Construire et lancer
docker-compose up -d --build

# Arreter
docker-compose down

# Voir les logs
docker-compose logs -f sdnext
```

## Configuration (.env)

| Variable | Description | Defaut |
|----------|-------------|--------|
| `SDNEXT_API_KEY` | Cle API pour l'acces programmatique | - |
| `WEB_USER` | Utilisateur Gradio (via `FORGE_USER`) | `admin` |
| `WEB_PASSWORD` | Mot de passe Gradio (via `FORGE_PASSWORD`) | `changeme` |

Parametres fixes dans `FORGE_ARGS` :

- `--gpu-device-id 1` : utilise le GPU 1 (RTX 3090)
- `--xformers` : acceleration memoire optimisee
- `--api --api-log` : API REST activee avec logs
- `--listen` : acces reseau (0.0.0.0)
- `--gradio-auth` : authentification activee
- `--skip-install` : pas de reinstallation au demarrage

## Fonctionnalites

- Interface web Gradio avec authentification
- Optimisation xformers pour generation rapide
- Support multi-modeles (SDXL et SD1.5)
- Stockage partage des modeles et sorties entre services
- Base image ai-dock/stable-diffusion-webui-forge avec corrections numpy/opencv

## Architecture

```
Dockerfile (ai-dock/sd-webui-forge + numpy fix)
    |
docker-compose.yml
    |- Port 7861:7860 (externe:interne)
    |- GPU 1 (RTX 3090)
    |- Volumes partages
        |- ../../shared/models -> /opt/storage/stable_diffusion/models
        |- ../../shared/outputs -> /opt/storage/stable_diffusion/outputs
```

## Fichiers

| Fichier | Description |
|---------|-------------|
| `docker-compose.yml` | Configuration du service Docker |
| `Dockerfile` | Image personnalisee avec corrections de dependances |
| `.env.example` | Template des variables d'environnement |

## Volumes

Les modeles et sorties sont partages avec les autres services SD via les volumes communs :

- `../../shared/models` : checkpoints, LoRA, VAE
- `../../shared/outputs` : images generees

## Notes

Le port externe 7861 est utilise au lieu de 7860 (port interne par defaut de Gradio) pour eviter un conflit avec le service `sd-forge-main` qui tourne sur le port 7860 sur la meme machine.
