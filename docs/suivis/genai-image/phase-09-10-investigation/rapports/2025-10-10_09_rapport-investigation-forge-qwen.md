# Phase 9: Rapport Investigation Infrastructure Forge + Qwen Image-Edit

**Date**: 2025-10-10 17:12:04  
**Objectif**: Investigation complète infrastructure Stable Diffusion Forge + Requirements Qwen Image-Edit

---

## 1. INFRASTRUCTURE FORGE EXISTANTE

### 1.1 Configuration Docker Compose

**Répertoire principal**: `D:\Production\stable-diffusion-webui-forge`

#### Docker Compose principal
```yaml
version: "3.8"

services:
  myia:
    container_name: myia
    image: ghcr.io/ai-dock/stable-diffusion-webui-forge:${IMAGE_TAG:-cuda-12.1.1-base-22.04}
    build:
      context: ./build
      args:
        PYTHON_VERSION: ${PYTHON_VERSION:-3.10}
        PYTORCH_VERSION: ${PYTORCH_VERSION:-2.4.1}
        FORGE_TAG: ${FORGE_TAG:-}
        IMAGE_BASE: ${IMAGE_BASE:-ghcr.io/ai-dock/python:${PYTHON_VERSION:-3.10}-v2-cuda-12.1.1-base-22.04}
    env_file:
      - myia.env
    restart: unless-stopped
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              device_ids: ['0']
              capabilities: [gpu]
    devices:
      - "/dev/dri:/dev/dri"
    volumes:
      - \\wsl.localhost\Ubuntu\home\jesse\SD\workspace:${WORKSPACE:-/workspace/}:rshared
      - ./config/authorized_keys:/root/.ssh/authorized_keys_mount
      - ./config/provisioning/default.sh:/opt/ai-dock/bin/provisioning.sh
    ports:
      - ${SSH_PORT_HOST:-2222}:${SSH_PORT_LOCAL:-22}
      - ${SERVICEPORTAL_PORT_HOST:-1111}:${SERVICEPORTAL_PORT_HOST:-1111}
      - ${FORGE_PORT_HOST:-7860}:${FORGE_PORT_LOCAL:-17860}
      - ${JUPYTER_PORT_HOST:-8888}:${JUPYTER_PORT_HOST:-8888}
      - ${SYNCTHING_UI_PORT_HOST:-8384}:${SYNCTHING_UI_PORT_HOST:-8384}
      - ${SYNCTHING_TRANSPORT_PORT_HOST:-22999}:${SYNCTHING_TRANSPORT_PORT_HOST:-22999}

  myia-turbo:
    container_name: myia-turbo
    image: ghcr.io/ai-dock/stable-diffusion-webui-forge:${IMAGE_TAG:-cuda-12.1.1-base-22.04}
    build:
      context: ./build
      args:
        PYTHON_VERSION: ${PYTHON_VERSION:-3.10}
        PYTORCH_VERSION: ${PYTORCH_VERSION:-2.4.1}
        FORGE_TAG: ${FORGE_TAG:-}
        IMAGE_BASE: ${IMAGE_BASE:-ghcr.io/ai-dock/python:${PYTHON_VERSION:-3.10}-v2-cuda-12.1.1-base-22.04}
    env_file:
      - myia-turbo.env
    restart: unless-stopped
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              device_ids: ['1']
              capabilities: [gpu]
    devices:
      - "/dev/dri:/dev/dri"
    volumes:
      - \\wsl.localhost\Ubuntu\home\jesse\SD\workspace:${WORKSPACE:-/workspace/}:rshared
      - ./config/authorized_keys:/root/.ssh/authorized_keys_mount
      - ./config/provisioning/default.sh:/opt/ai-dock/bin/provisioning.sh
    ports:
      - ${SSH_PORT_HOST:-2223}:${SSH_PORT_LOCAL:-22}
      - ${SERVICEPORTAL_PORT_HOST:-1112}:${SERVICEPORTAL_PORT_HOST:-1112}
      - ${FORGE_PORT_HOST:-17861}:${FORGE_PORT_LOCAL:-17860}
      - ${JUPYTER_PORT_HOST:-8889}:${JUPYTER_PORT_HOST:-8889}
      - ${SYNCTHING_UI_PORT_HOST:-8385}:${SYNCTHING_UI_PORT_HOST:-8385}
      - ${SYNCTHING_TRANSPORT_PORT_HOST:-22998}:${SYNCTHING_TRANSPORT_PORT_HOST:-22999}

```

#### Fichier myia.env
```env
IMAGE_TAG=latest-cuda
AUTO_UPDATE=true
FORGE_REF=05b01da01f76c97011358a415820360546d284fb
FORGE_BUILD_REF=05b01da01f76c97011358a415820360546d284fb
SERVERLESS=true
# CF_QUICK_TUNNELS=true
# SERVICEPORTAL_URL= https://service.stable-diffusion-webui-forge.myia.io
FORGE_PORT_HOST=36525
FORGE_URL=https://stable-diffusion-webui-forge.myia.io/
# WEB_ENABLE_AUTH=true
# WEB_USER=admin
# WEB_PASSWORD=goldman
FORGE_ARGS=--ui-settings-file config-myia.json --ui-config-file ui-config-myia.json --api --api-log --listen --gradio-auth admin:goldman --gpu-device-id 0 --cuda-malloc --xformers 
CIVITAI_TOKEN=XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
HF_TOKEN=hf_XXXXXXXXXXXXXXXXXXXXXXXXXXXX

SSH_PORT_HOST=20000

SERVICEPORTAL_PORT_HOST=1113
JUPYTER_PORT_HOST=8890
SYNCTHING_UI_PORT_HOST=8386
SYNCTHING_TRANSPORT_PORT_HOST=22997

```

#### Fichier myia-turbo.env
```env
IMAGE_TAG=latest-cuda
AUTO_UPDATE=true
FORGE_REF=05b01da01f76c97011358a415820360546d284fb
FORGE_BUILD_REF=05b01da01f76c97011358a415820360546d284fb
SERVERLESS=true
FORGE_PORT_HOST=17861
FORGE_URL=https://turbo.stable-diffusion-webui-forge.myia.io/
SSH_PORT_HOST=2223
SERVICEPORTAL_PORT_HOST=1112
SYNCTHING_UI_PORT_HOST=8385
JUPYTER_PORT_HOST=8889
SYNCTHING_TRANSPORT_PORT_HOST=22998
WEB_ENABLE_AUTH=false
FORGE_ARGS=--ui-settings-file config-turbo.json --ui-config-file ui-config-turbo.json --api --api-log --listen --gradio-auth jesse:v4ñþ3Ò½Áçq --gpu-device-id 1 --cuda-malloc --xformers
# --api-auth jesse:dmtjqni45ù
CIVITAI_TOKEN=XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
HF_TOKEN=hf_XXXXXXXXXXXXXXXXXXXXXXXXXXXX

```

### 1.2 Configuration Reverse Proxies IIS

#### stable-diffusion-webui-forge.myia.io
```xml
<configuration>
    <system.webServer>
        <httpErrors errorMode="Detailed" />
        <staticContent>
            <mimeMap fileExtension=".*" mimeType="application/octet-stream" />
        </staticContent>
        <proxy>
            <preserveHostHeader>true</preserveHostHeader>
        </proxy>
        <rewrite>
            <rules>
                <rule name="AuthorizationHeader">
                    <match url=".*" />
                    <action type="Rewrite" url="{R:0}" />
                    <serverVariables>
                        <set name="HTTP_AUTHORIZATION" value="{HTTP_AUTHORIZATION}" />
                    </serverVariables>
                </rule>
                <!-- Redirection pour stable-diffusion-webui-forge.myia.io -->
                <rule name="ReverseProxyInboundRule_Forge" stopProcessing="true">
                    <match url="(.*)" />
                    <conditions>
                        <add input="{HTTP_HOST}" pattern="^stable-diffusion-webui-forge.myia.io$" />
                    </conditions>
                    <action type="Rewrite" url="http://192.168.0.46:36525/{R:1}" logRewrittenUrl="true" />
                    <serverVariables>
                        <!-- <set name="HTTP_HOST" value="stable-diffusion-webui-forge.myia.io" /> -->
                        <set name="HTTP_X_FORWARDED_HOST" value="stable-diffusion-webui-forge.myia.io" />
                        <set name="HTTP_X_FORWARDED_PROTO" value="https" />
                        <set name="HTTP_X_FORWARDED_FOR" value="{REMOTE_ADDR}" />
                    </serverVariables>
                </rule>

                <!-- Redirection pour service.stable-diffusion-webui-forge.myia.io -->
                <rule name="ReverseProxyInboundRule_ServicePortal" stopProcessing="true">
                    <match url="(.*)" />
                    <conditions>
                        <add input="{HTTP_HOST}" pattern="^service.stable-diffusion-webui-forge.myia.io$" />
                    </conditions>
                    <action type="Rewrite" url="http://192.168.0.46:1111/{R:1}" logRewrittenUrl="true" />
                    <serverVariables>
                        <!-- <set name="HTTP_HOST" value="service.stable-diffusion-webui-forge.myia.io" /> -->
                        <set name="HTTP_X_FORWARDED_HOST" value="service.stable-diffusion-webui-forge.myia.io" />
                        <set name="HTTP_X_FORWARDED_PROTO" value="https" />
                        <set name="HTTP_X_FORWARDED_FOR" value="{REMOTE_ADDR}" />
                    </serverVariables>
                </rule>
            </rules>
        </rewrite>
    </system.webServer>
</configuration>

```

#### turbo.stable-diffusion-webui-forge.myia.io
```xml
<configuration>
    <system.webServer>
        <httpErrors errorMode="Detailed" />
        <staticContent>
            <mimeMap fileExtension=".*" mimeType="application/octet-stream" />
        </staticContent>
        <proxy>
            <preserveHostHeader>true</preserveHostHeader>
        </proxy>
        <rewrite>
            <rules>
                <rule name="AuthorizationHeader">
                    <match url=".*" />
                    <action type="Rewrite" url="{R:0}" />
                    <serverVariables>
                        <set name="HTTP_AUTHORIZATION" value="{HTTP_AUTHORIZATION}" />
                    </serverVariables>
                </rule>
                <!-- Redirection pour stable-diffusion-webui-forge.myia.io -->
                <rule name="ReverseProxyInboundRule_Forge" stopProcessing="true">
                    <match url="(.*)" />
                    <action type="Rewrite" url="http://192.168.0.46:17861/{R:1}" logRewrittenUrl="true" />
                    <serverVariables>
                        <set name="HTTP_HOST" value="turbo.stable-diffusion-webui-forge.myia.io" />
                        <set name="HTTP_X_FORWARDED_HOST" value="turbo.stable-diffusion-webui-forge.myia.io" />
                        <set name="HTTP_X_FORWARDED_PROTO" value="https" />
                        <set name="HTTP_X_FORWARDED_FOR" value="{REMOTE_ADDR}" />
                    </serverVariables>
                </rule>
            </rules>
        </rewrite>
    </system.webServer>
</configuration>

```

**Ports identifiés**:
- Forge principal (GPU 0): Port **36525** → https://stable-diffusion-webui-forge.myia.io
- Forge Turbo (GPU 1): Port **17861** → https://turbo.stable-diffusion-webui-forge.myia.io

### 1.3 Workspace WSL et Modèles

**Chemin workspace**: `\\wsl.localhost\Ubuntu\home\jesse\SD\workspace`

#### Structure workspace:
```.Trash-1000/
environments/
home/
stable-diffusion-webui-forge/
storage/
```

#### Modèles Stable Diffusion détectés:

**Stable-diffusion** (31 fichiers):
- Petzl_2_1000.safetensors - 3.97GB
- Petzl_SITTA_600_lora.safetensors - 3.97GB
- Petzl_SITTA_64_1200_lora.safetensors - 3.97GB
- absolutereality_v1.safetensors - 1.99GB
- aetherverseLightning_v10.safetensors - 6.46GB
- dreamshaperXL_turboDpmppSDEKarras.safetensors - 6.46GB
- dreamshaperXL_v21TurboDPMSDE.safetensors - 6.46GB
- Epicrealismxl_Hades.safetensors - 6.46GB
- flux1-dev-bnb-nf4-v2.safetensors - 11.22GB
- Juggernaut-X-RunDiffusion-NSFW.safetensors - 6.62GB
- juggernautXL_juggXIByRundiffusion.safetensors - 6.62GB
- juggernautXL_juggXILightningByRD_828456.safetensors - 6.62GB
- LexicaAperture.ckpt - 3.97GB
- openjourney_V4.ckpt - 1.99GB
- pixelArtDiffusionXL_spriteShaper_291175.safetensors - 6.46GB
- pixelwave_08.safetensors - 6.46GB
- pixelwave_11_630807.safetensors - 6.46GB
- pixelwave_flux1Dev03.safetensors - 5.72GB
- pixelwaveturbo_01.safetensors - 6.46GB
- pixelwaveturboExcellent_03_250995.safetensors - 6.46GB
- sd_xl_base_1.0_0.9vae.safetensors - 6.46GB
- sd_xl_base_1.0.safetensors - 6.46GB
- sd_xl_refiner_1.0_0.9vae.safetensors - 5.66GB
- sd_xl_refiner_1.0.safetensors - 5.66GB
- sd-v1-4.ckpt - 3.97GB
- sd-v1-5-inpainting.ckpt - 3.97GB
- sdxl_vae.safetensors - 0.31GB
- turbovisionxlSuperFastXLBasedOnNew_beta0131Bakedvae.safetensors - 6.46GB
- turbovisionxlSuperFastXLBasedOnNew_tvxlV431Bakedvae_213383.safetensors - 6.46GB
- v1-5-pruned.ckpt - 7.17GB
- v2-1_768-ema-pruned.ckpt - 4.86GB
*Total: 172.24GB*

**Lora** (47 fichiers):
- Alfons_Mocha_v1.safetensors - 0.28GB
- Alphonse Mucha Style.safetensors - 0.21GB
- Color_Icons.safetensors - 0.02GB
- ColoringBookRedmond-ColoringBook-ColoringBookAF.safetensors - 0.16GB
- epiNoiseoffset_v2.safetensors - 0.08GB
- F2D-000003.safetensors - 0.21GB
- FLUX_Polyhedron_all_Kohya_ss-000001.safetensors - 0.14GB
- FLUX_polyhedron_chin_teeth_mouth-epoch000002_716420.safetensors - 0.14GB
- FLUX.1-Turbo-Alpha.safetensors - 0.65GB
- flux1DevNF46StepsNSFW2_finessefp16lora_903009.safetensors - 0.3GB
- ghibli_style_offset.safetensors - 0.14GB
- GTA_Style.safetensors - 0.02GB
- jnbasdf-woman-2.safetensors - 0.14GB
- jnbasdf-woman.safetensors - 0.14GB
- kl1m.safetensors - 0.85GB
- logo-xl.safetensors - 0.05GB
- logoarchive.safetensors - 0.14GB
- LogoRedmondV2-Logo-LogoRedmAF.safetensors - 0.16GB
- minimalism_pop_last.safetensors - 0GB
- modernlogo.safetensors - 0.16GB
- mouth_51612.safetensors - 0.14GB
- onePieceWanoSagaStyle_v2Offset.safetensors - 0.28GB
- Optimazed-TurboFLUX-Accelerater_PAseer_860299.safetensors - 0.15GB
- pixai style_61668.safetensors - 0.14GB
- pixel-art-xl-v1.1_99321.safetensors - 0.16GB
- pixel-portrait-v1_86630.safetensors - 0.14GB
- PixelArtRedmond-Lite64_121079.safetensors - 0.16GB
- PixelArtRedmond15V-PixelArt-PIXARFK_178934.safetensors - 0.03GB
- pixelatedv2_88430.safetensors - 0.04GB
- pixelportraits192-v1-2151_333835.safetensors - 0.32GB
- PX64NOCAP_epoch_10_551053.safetensors - 0.04GB
- RagnarokSpriteNoob_byKonan_1302975.safetensors - 0.1GB
- Rembrandt.safetensors - 0.04GB
- SDXLStencilStyleFAE.safetensors - 0.21GB
- stencil_v1.safetensors - 0.07GB
- studioGhibliStyle_offset.safetensors - 0.14GB
- TeethXL_103236.safetensors - 0.21GB
- TurboRender_flux_dev_lora_weights.safetensors - 1.29GB
- vscharacter64-v1_89053.safetensors - 0.14GB
- xsarchitectural_19houseplan.safetensors - 0.04GB
- xsarchitectural_5Safetensors.safetensors - 0.04GB
- xsarchitectural_9scienceFiction.safetensors - 0.04GB
- xsarchitectural_Safetensors.safetensors - 0.04GB
- xsarchitectural2wooden_xsarchitectural2.safetensors - 0.04GB
- xsarchitectural3aerial_xsarchitectural3.safetensors - 0.04GB
- xsarchitectural6modern_xsarchitectural6.safetensors - 0.04GB
- xsarchitectural9advanced_xsarchitectural.safetensors - 0.04GB
*Total: 8.11GB*

**VAE** (4 fichiers):
- ae.safetensors - 0.31GB
- sdxl_vae.safetensors - 0GB
- vae-ft-mse-840000-ema-pruned.vae.pt - 0.31GB
- vaeFtMse840000Ema_v10.safetensors - 0.31GB
*Total: 0.93GB*

**ControlNet** (52 fichiers):
- control_v1p_sd15_qrcode_monster_v2.safetensors - 0.67GB
- controlnet11Models_animeline.safetensors - 0.67GB
- controlnet11Models_canny.safetensors - 0.67GB
- controlnet11Models_depth.safetensors - 0.67GB
- controlnet11Models_inpaint.safetensors - 0.67GB
- controlnet11Models_lineart.safetensors - 0.67GB
- controlnet11Models_mlsd.safetensors - 0.67GB
- controlnet11Models_normal.safetensors - 0.67GB
- controlnet11Models_openpose.safetensors - 0.67GB
- controlnet11Models_pix2pix.safetensors - 0.67GB
- controlnet11Models_scribble.safetensors - 0.67GB
- controlnet11Models_seg.safetensors - 0.67GB
- controlnet11Models_shuffle.safetensors - 0.67GB
- controlnet11Models_softedge.safetensors - 0.67GB
- controlnet11Models_tileE.safetensors - 0.67GB
- diffusers_xl_canny_full.safetensors - 2.33GB
- diffusers_xl_canny_mid.safetensors - 0.51GB
- diffusers_xl_canny_small.safetensors - 0.3GB
- diffusers_xl_depth_full.safetensors - 2.33GB
- diffusers_xl_depth_mid.safetensors - 0.51GB
- diffusers_xl_depth_small.safetensors - 0.3GB
- ioclab_sd15_recolor.safetensors - 0.67GB
- kohya_controllllite_xl_blur_anime_beta.safetensors - 0.02GB
- kohya_controllllite_xl_blur_anime.safetensors - 0.04GB
- kohya_controllllite_xl_blur.safetensors - 0.04GB
- kohya_controllllite_xl_canny_anime.safetensors - 0.04GB
- kohya_controllllite_xl_canny.safetensors - 0.04GB
- kohya_controllllite_xl_depth.safetensors - 0.04GB
- kohya_controllllite_xl_openpose_anime_v2.safetensors - 0.04GB
- kohya_controllllite_xl_openpose_anime.safetensors - 0.04GB
- kohya_controllllite_xl_scribble_anime.safetensors - 0.04GB
- sai_xl_depth_128lora.safetensors - 0.37GB
- sai_xl_depth_256lora.safetensors - 0.72GB
- sai_xl_recolor_128lora.safetensors - 0.37GB
- sai_xl_recolor_256lora.safetensors - 0.72GB
- sai_xl_sketch_128lora.safetensors - 0.37GB
- sai_xl_sketch_256lora.safetensors - 0.72GB
- sargezt_xl_depth_faid_vidit.safetensors - 2.33GB
- sargezt_xl_depth_zeed.safetensors - 2.33GB
- sargezt_xl_depth.safetensors - 2.33GB
- sargezt_xl_softedge.safetensors - 2.33GB
- t2i-adapter_diffusers_xl_canny.safetensors - 0.15GB
- t2i-adapter_diffusers_xl_depth_midas.safetensors - 0.15GB
- t2i-adapter_diffusers_xl_depth_zoe.safetensors - 0.15GB
- t2i-adapter_diffusers_xl_lineart.safetensors - 0.15GB
- t2i-adapter_diffusers_xl_openpose.safetensors - 0.15GB
- t2i-adapter_diffusers_xl_sketch.safetensors - 0.15GB
- t2i-adapter_xl_canny.safetensors - 0.14GB
- t2i-adapter_xl_openpose.safetensors - 0.15GB
- t2i-adapter_xl_sketch.safetensors - 0.14GB
- thibaud_xl_openpose_256lora.safetensors - 0.72GB
- thibaud_xl_openpose.safetensors - 2.33GB
*Total: 34.31GB*

---

## 2. CONFIGURATION GPU ACTUELLE

### 2.1 Allocation GPU Forge

Selon docker-compose.yaml:
- **GPU 0 (RTX 3080 - 16GB)**: Service myia - Port 36525
  - Args: --gpu-device-id 0 --cuda-malloc --xformers
  
- **GPU 1 (RTX 3090 - 24GB)**: Service myia-turbo - Port 17861
  - Args: --gpu-device-id 1 --cuda-malloc --xformers

### 2.2 Objectif Mission Phase 9+

**Target nouvelle allocation**:
- **RTX 3080 (16GB)** → SD XL Turbo Forge (conserver)
- **RTX 3090 (24GB)** → Qwen Image-Edit (nouveau service)

---

## 3. REQUIREMENTS QWEN IMAGE-EDIT

### 3.1 Modèle de base

**Qwen2-VL-7B-Instruct**:
- Modèle multimodal vision-language
- Capacités: Image understanding, editing, generation
- Taille base: ~14GB en FP16

### 3.2 Quantization pour RTX 3090 24GB

Options identifiées:
1. **AWQ (4-bit)**: ~3.5-4GB VRAM - Recommandé
2. **GPTQ (4-bit)**: ~4-4.5GB VRAM - Alternative
3. **GGUF (Q4_K_M)**: ~4GB VRAM - Pour llama.cpp/Ollama
4. **FP16 (no quant)**: ~14GB VRAM - Possible avec marge

**Recommandation**: AWQ 4-bit permet ~20GB libre pour contexte et batch processing

### 3.3 Méthodes de déploiement

#### Option A: ComfyUI + Qwen Node
**Avantages**:
- Interface visuelle workflow
- Intégration native SD + Qwen
- Workflow image-to-image avec édition

**Inconvénients**:
- Setup plus complexe
- Moins optimisé pour API

#### Option B: vLLM
**Avantages**:
- API OpenAI-compatible native
- Performance optimale (PagedAttention)
- Quantization AWQ intégrée

**Inconvénients**:
- Pas de GUI
- Focus LLM (vision en beta)

#### Option C: Text-Generation-WebUI (Oobabooga)
**Avantages**:
- GUI existante
- Support vision models
- Déjà utilisé sur infrastructure

**Inconvénients**:
- API moins standard
- Performance moyenne

### 3.4 Recommandation préliminaire

**vLLM avec AWQ quantization**:
```bash
# Installation
pip install vllm

# Lancement Qwen2-VL-7B-AWQ
vllm serve Qwen/Qwen2-VL-7B-Instruct-AWQ \
  --gpu-memory-utilization 0.9 \
  --max-model-len 4096 \
  --tensor-parallel-size 1
```

**Port suggéré**: 8000 (ou 8001 si conflit)  
**API OpenAI-compatible**: http://localhost:8000/v1/

---

## 4. ARCHITECTURE CIBLE PROPOSÉE

### 4.1 Services GPU

| Service | GPU | VRAM | Port | Domain |
|---------|-----|------|------|--------|
| SD Forge | RTX 3080 (16GB) | ~12GB | 36525 | stable-diffusion-webui-forge.myia.io |
| SD Turbo | RTX 3080 (16GB) | ~8GB | 17861 | turbo.stable-diffusion-webui-forge.myia.io |
| Qwen Image-Edit | RTX 3090 (24GB) | ~4GB (AWQ) | 8000 | qwen-image-edit.myia.io |

### 4.2 Configuration IIS à créer

Nouveau site IIS pour Qwen:
```xml
<configuration>
    <system.webServer>
        <rewrite>
            <rules>
                <rule name="ReverseProxy_Qwen" stopProcessing="true">
                    <match url="(.*)" />
                    <action type="Rewrite" url="http://localhost:8000/{R:1}" />
                </rule>
            </rules>
        </rewrite>
    </system.webServer>
</configuration>
```

### 4.3 Docker Compose à créer

Nouveau service dans docker-compose ou fichier séparé:
```yaml
services:
  qwen-image-edit:
    image: vllm/vllm-openai:latest
    container_name: qwen-image-edit
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              device_ids: ['0']  # RTX 3090
              capabilities: [gpu]
    volumes:
      - /path/to/models:/models
    ports:
      - "8000:8000"
    command: >
      --model Qwen/Qwen2-VL-7B-Instruct-AWQ
      --gpu-memory-utilization 0.9
      --max-model-len 4096
    restart: unless-stopped
```

---

## 5. ÉTAT CONTAINERS ACTUEL

**Docker via WSL**: Disponible
```
CONTAINER ID   IMAGE                                                      COMMAND                  CREATED        STATUS                   PORTS                                                                                                                                               NAMES 29bed8116b9e   epita-symbolic-ai                                          "python -c 'print('A…"   6 weeks ago    Exited (0) 6 weeks ago                                                                                                                                                       intelligent_greider 21678af751b1   ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda   "init.sh"                3 months ago   Up 4 hours               0.0.0.0:1112->1112/tcp, 0.0.0.0:8385->8385/tcp, 0.0.0.0:8889->8889/tcp, 0.0.0.0:22998->22998/tcp, 0.0.0.0:2223->22/tcp, 0.0.0.0:17861->17860/tcp    myia-turbo-supervisor-1 4fab4fb2ef7e   ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda   "init.sh"                3 months ago   Up 4 hours               0.0.0.0:1113->1113/tcp, 0.0.0.0:8386->8386/tcp, 0.0.0.0:8890->8890/tcp, 0.0.0.0:22997->22997/tcp, 0.0.0.0:20000->22/tcp, 0.0.0.0:36525->17860/tcp   myia-supervisor-1 7947171a4a16   ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda   "init.sh"                3 months ago   Created                                                                                                                                                                      myia-sd-forge-supervisor-1 8b600dd4f3f8   jhj0517/whisper-webui:latest                               "python app.py --ser…"   5 months ago   Up 4 hours               0.0.0.0:36540->7860/tcp                                                                                                                             myia-whisper-webui-app-1 77c58373c003   sdnext/sdnext-cuda                                         "python launch.py --…"   6 months ago   Up 4 hours               0.0.0.0:36325->7860/tcp                                                                                                                             sdnext-container
```

---

## 6. VOLUMES ET STOCKAGE

### 6.1 Volumes Docker identifiés

Selon docker-compose:
- **Workspace partagé**: `\\wsl.localhost\Ubuntu\home\jesse\SD\workspace`
- Monté en 
shared pour les deux services Forge
- Contient: models, outputs, configurations

### 6.2 Espace disque requis

**Pour Qwen Image-Edit**:
- Modèle AWQ: ~4GB
- Cache et outputs: ~10GB recommandé
- **Total estimé**: 15-20GB

**Vérification espace disponible**:
*Note*: Espace WSL non mesurable directement depuis Windows

---

## 7. PROBLÈMES IDENTIFIÉS

### 7.1 Containers arrêtés

D'après mission: "Containers avaient problèmes démarrage, fonctionnaient avant"

**Actions requises**:
1. Diagnostiquer logs des containers
2. Vérifier GPU allocation
3. Tester redémarrage avec docker-compose up

### 7.2 Conflits potentiels

- GPU 1 actuellement assigné à myia-turbo (Forge)
- Nécessite réaffectation pour Qwen Image-Edit
- Potentiel conflit de ports si plusieurs services

---

## 8. PLAN D'ACTION PHASES 10-14

### Phase 10: Diagnostic et Réparation Forge
- [ ] Analyser logs containers Forge
- [ ] Identifier causes problèmes démarrage
- [ ] Réparer configuration si nécessaire
- [ ] Valider fonctionnement Forge GPU 0

### Phase 11: Préparation Infrastructure Qwen
- [ ] Télécharger Qwen2-VL-7B-Instruct-AWQ
- [ ] Créer docker-compose pour vLLM
- [ ] Configurer GPU allocation (RTX 3090)
- [ ] Créer reverse proxy IIS

### Phase 12: Déploiement Qwen Image-Edit
- [ ] Lancer container vLLM + Qwen
- [ ] Tester API OpenAI-compatible
- [ ] Configurer certificat HTTPS
- [ ] Tests fonctionnels basiques

### Phase 13: Intégration et Tests
- [ ] Tests charge GPU
- [ ] Validation API endpoints
- [ ] Tests image editing
- [ ] Documentation API

### Phase 14: Validation Finale
- [ ] Tests end-to-end
- [ ] Performance benchmarks
- [ ] Documentation complète
- [ ] Handover et formation

---

## 9. RESSOURCES ET RÉFÉRENCES

### Documentation Qwen
- HuggingFace: https://huggingface.co/Qwen/Qwen2-VL-7B-Instruct
- GitHub: https://github.com/QwenLM/Qwen2-VL
- AWQ Quantization: https://huggingface.co/Qwen/Qwen2-VL-7B-Instruct-AWQ

### Documentation vLLM
- Docs: https://docs.vllm.ai/
- OpenAI API: https://docs.vllm.ai/en/latest/serving/openai_compatible_server.html
- Vision Models: https://docs.vllm.ai/en/latest/models/vlm.html

### Infrastructure existante
- Forge Docker: https://github.com/ai-dock/stable-diffusion-webui-forge
- IIS Reverse Proxy: Docs Microsoft ARR

---

## 10. CHECKPOINTS SÉMANTIQUES

### Checkpoint 1: Infrastructure Forge ✓
- Configuration Docker Compose analysée
- Reverse proxies IIS identifiés
- Volumes et modèles listés
- GPU allocation comprise

### Checkpoint 2: Requirements Qwen (En cours)
- Modèle identifié: Qwen2-VL-7B-Instruct
- Quantization: AWQ 4-bit recommandé
- Déploiement: vLLM recommandé
- VRAM: ~4GB (laisse 20GB libres)

### Checkpoint 3: Architecture cible (En cours)
- 2 GPUs, 3 services
- Ports: 36525, 17861, 8000
- APIs OpenAI-compatible pour les 2 services
- IIS reverse proxy avec HTTPS

---

## 11. DÉCISIONS TECHNIQUES

| Décision | Justification |
|----------|---------------|
| vLLM pour Qwen | API OpenAI-compatible native, performance optimale |
| AWQ quantization | Meilleur ratio qualité/VRAM (4GB) |
| GPU 0 → Forge | VRAM suffisant pour SD XL (16GB) |
| GPU 1 → Qwen | VRAM optimal pour VLM (24GB) |
| Port 8000 | Standard vLLM, pas de conflit |
| IIS ARR | Cohérent avec infrastructure existante |

---

**Fin du rapport Phase 9**

*Prochaine étape*: Phase 10 - Diagnostic et réparation containers Forge
