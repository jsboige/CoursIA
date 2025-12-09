FROM ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda

# Fix numpy binary incompatibility issue
# We need to force numpy<2 and ensure opencv-python-headless is used instead of opencv-python
# to avoid conflicts with scikit-image and other libraries.

SHELL ["/bin/bash", "-c"]

# 1. Modify internal requirements to prefer opencv-python-headless
# This targets both standard requirements.txt and the specific requirements_versions.txt used by launch.py
RUN find /opt/stable-diffusion-webui-forge -name "requirements*.txt" -exec sed -i 's/opencv-python/opencv-python-headless/g' {} +

# 2. Force install compatible versions in the forge venv
# We also force reinstall Pillow to ensure it's compatible with the current environment
RUN source /opt/environments/python/forge/bin/activate && \
    pip uninstall -y numpy opencv-python opencv-python-headless scikit-image Pillow && \
    pip install "numpy<2" opencv-python-headless scikit-image Pillow

# 3. Fix permissions so the runtime user (1000) can modify these files if needed
# The base image uses user 1000 (often named 'user' or 'webui')
RUN chown -R 1000:1000 /opt/environments/python/forge /opt/stable-diffusion-webui-forge

# 4. Pre-flight check to ensure imports work
RUN source /opt/environments/python/forge/bin/activate && \
    python -c "import numpy; import cv2; import skimage; print('Imports successful')"