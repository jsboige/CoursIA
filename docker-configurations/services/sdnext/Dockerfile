FROM ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda

# SD.Next - Full SDXL/SD1.5 support with advanced features
# Using ai-dock base image similar to forge-turbo

SHELL ["/bin/bash", "-c"]

# Fix numpy compatibility (similar to forge-turbo)
RUN find /opt/stable-diffusion-webui-forge -name "requirements*.txt" -exec sed -i 's/opencv-python/opencv-python-headless/g' {} +

RUN source /opt/environments/python/forge/bin/activate && \
    pip uninstall -y numpy opencv-python opencv-python-headless scikit-image Pillow && \
    pip install "numpy<2" opencv-python-headless scikit-image Pillow

RUN chown -R 1000:1000 /opt/environments/python/forge /opt/stable-diffusion-webui-forge

RUN source /opt/environments/python/forge/bin/activate && \
    python -c "import numpy; import cv2; import skimage; print('Imports successful')"

RUN groupadd -g 1000 appuser && \
    useradd -u 1000 -g appuser -m -s /bin/bash appuser

# #14941: ai-dock's env-store.sh echoes every stored env var's VALUE to stdout
# (-> docker logs): at boot, init.sh calls it for ALL env vars, leaking
# FORGE_ARGS (contains --gradio-auth admin:<password>) and WEB_PASSWORD.
# Drop the value from the log line; the persistence append to
# /opt/ai-dock/etc/environment.sh (required by the app) is kept intact.
# Before USER appuser (file is root-owned); after the cached pip layers.
RUN sed -i "/Stored environment variable/ s|': %s|'|; /Stored environment variable/ s|\" \"[$]value\"|\"|" /opt/ai-dock/bin/env-store.sh

USER appuser
