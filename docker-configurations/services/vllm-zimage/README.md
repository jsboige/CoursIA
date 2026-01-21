# vLLM Z-Image Service

Service vLLM-omni exposant une API OpenAI-compatible pour la generation d'images Z-Image (Lumina-Next-SFT).

## Vue d'ensemble

| Parametre | Valeur |
|-----------|--------|
| **Modele** | Alpha-VLLM/Lumina-Next-SFT-diffusers |
| **Port** | 8001 (configurable) |
| **GPU** | GPU 1 (RTX 3080 Ti) |
| **VRAM** | ~10GB |
| **API** | OpenAI Images API compatible |

## Demarrage

```bash
# Configuration
cp .env.example .env
# Editer .env avec votre HF_TOKEN

# Demarrage
docker-compose up -d

# Verification
curl http://localhost:8001/health
```

## API Endpoints

### Health Check
```bash
curl http://localhost:8001/health
```

### Generation d'image (OpenAI-compatible)
```bash
curl http://localhost:8001/v1/images/generations \
  -H "Content-Type: application/json" \
  -d '{
    "model": "z-image",
    "prompt": "A serene mountain landscape at sunset",
    "size": "1024x1024",
    "n": 1
  }'
```

### Liste des modeles
```bash
curl http://localhost:8001/v1/models
```

## Integration Open Web-UI

Pour utiliser ce service avec Open Web-UI :

1. Dans Open Web-UI, aller dans Settings > Images
2. Configurer l'URL de l'API : `http://localhost:8001/v1`
3. Selectionner le modele `z-image`

## Coexistence avec Forge-Turbo

Ce service est configure pour utiliser GPU 1 (RTX 3080 Ti, 16GB).
Forge-Turbo utilise egalement GPU 1 avec ~6GB VRAM.

**Attention:** La coexistence depend de la VRAM disponible :
- vLLM Z-Image : ~10GB
- Forge-Turbo : ~6GB
- Total : ~16GB (limite GPU)

Si les deux services ne peuvent coexister, utiliser des profils de deploiement mutuellement exclusifs.

## Logs et Debug

```bash
# Logs en temps reel
docker-compose logs -f vllm-zimage

# Stats GPU
nvidia-smi -l 1
```

## References

- [vLLM-omni](https://github.com/vllm-project/vllm-omni)
- [Lumina-Next-SFT](https://huggingface.co/Alpha-VLLM/Lumina-Next-SFT-diffusers)
- [vLLM-omni Z-Image PR #149](https://github.com/vllm-project/vllm-omni/pull/149)
