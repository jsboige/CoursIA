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
