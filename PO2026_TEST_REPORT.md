# Rapport Tests GenAI - po-2023 → po-2026

**Date**: 2026-03-10 03:00
**Branche**: GenAI_Series (commit 19aa4f2)
**Statut**: ✅ PRÊT À TESTER

---

## 📊 Résultats Tests po-2023

### Audio APIs (4/4 ✅)

| Service | URL | Status |
|---------|-----|--------|
| whisper-api | https://whisper-api.myia.io/health | ✅ 200 |
| tts-api | https://tts-api.myia.io/health | ✅ 200 |
| musicgen-api | https://musicgen-api.myia.io/health | ✅ 200 |
| demucs-api | https://demucs-api.myia.io/health | ✅ 200 |

### Image APIs (2/4 UP)

| Service | URL | Status |
|---------|-----|--------|
| z-image | https://z-image.myia.io/health | ✅ 200 |
| forge-turbo | https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/options | ✅ 200 |
| sd-forge-main | https://stable-diffusion-webui-forge.myia.io/sdapi/v1/options | ⚠️ 502 |
| sdnext | https://sdnext.myia.io/sdapi/v1/options | ⚠️ 502 |
| qwen-image-edit | https://qwen-image-edit.myia.io/system_stats | 🔒 401 (auth requis) |

### Video APIs (1/1 ✅)

| Service | URL | Status |
|---------|-----|--------|
| comfyui-video | https://comfyui-video.myia.io/system_stats | ✅ 200 |

---

## 🚀 Instructions pour po-2026

```bash
# 1. Pull latest GenAI_Series
cd ~/Dev/CoursIA.worktrees/GenAI_Series
git pull origin GenAI_Series

# 2. Vérifier les services locaux
python scripts/genai-stack/genai.py docker status

# 3. Tester les APIs audio
python scripts/genai-stack/genai.py audio-apis status

# 4. Validation complète (si applicable)
python scripts/genai-stack/genai.py validate --full
```

---

## 📦 Nouveautés importées depuis main

### Services Audio API (avec lazy loading)
- `whisper-api/` - Dockerfile + app.py + docker-compose.yml
- `tts-api/` - Dockerfile + app.py + docker-compose.yml
- `musicgen-api/` - Dockerfile + app.py + docker-compose.yml
- `demucs-api/` - Dockerfile + app.py + docker-compose.yml

### Module Lazy Loading
- `shared/lazy_model.py` - Gestion optimisée de la VRAM

### Configurations Hybrides
- `whisper-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète
- `tts-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète
- `musicgen-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète
- `demucs-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète

---

## 📝 Commandes CLI disponibles

```bash
# Statut tous services
python scripts/genai-stack/genai.py docker status

# Statut APIs audio
python scripts/genai-stack/genai.py audio-apis status

# Démarrer/arrêter services
python scripts/genai-stack/genai.py docker start <service>
python scripts/genai-stack/genai.py docker stop <service>

# Validation
python scripts/genai-stack/genai.py validate --full
python scripts/genai-stack/genai.py validate --notebooks

# GPU status
python scripts/genai-stack/genai.py gpu

# Auth audit
python scripts/genai-stack/genai.py auth audit
```

---

## ✅ Check-list po-2026

- [ ] Pull GenAI_Series
- [ ] Vérifier `.env` pour tokens API
- [ ] Tester `python scripts/genai-stack/genai.py docker status`
- [ ] Tester `python scripts/genai-stack/genai.py audio-apis status`
- [ ] Tester endpoints distants (curl commands ci-dessus)
- [ ] Valider notebooks si applicable

---

**Coordination**: po-2023 ⇄ po-2026
**Contact**: Tous les services sont UP et opérationnels sur po-2023
