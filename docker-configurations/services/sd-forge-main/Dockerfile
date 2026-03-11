FROM ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda

# SD Forge Main - SDXL 1.0 full model support
# Based on forge-turbo but configured for standard SDXL 1.0 models

SHELL ["/bin/bash", "-c"]

# Fix numpy binary incompatibility issue (same as forge-turbo)
RUN find /opt/stable-diffusion-webui-forge -name "requirements*.txt" -exec sed -i 's/opencv-python/opencv-python-headless/g' {} +

RUN source /opt/environments/python/forge/bin/activate && \
    pip uninstall -y numpy opencv-python opencv-python-headless scikit-image Pillow && \
    pip install "numpy<2" opencv-python-headless scikit-image Pillow

RUN chown -R 1000:1000 /opt/environments/python/forge /opt/stable-diffusion-webui-forge

RUN source /opt/environments/python/forge/bin/activate && \
    python -c "import numpy; import cv2; import skimage; print('Imports successful')"
