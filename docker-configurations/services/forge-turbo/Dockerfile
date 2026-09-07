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

# #14941: ai-dock's env-store.sh echoes every stored env var's VALUE to stdout
# (-> docker logs): at boot, init.sh calls it for ALL env vars, leaking
# FORGE_ARGS (contains --gradio-auth admin:<password>) and WEB_PASSWORD.
# Drop the value from the log line; the persistence append to
# /opt/ai-dock/etc/environment.sh (required by the app) is kept intact.
# Before USER appuser (file is root-owned); after the cached pip layers.
RUN sed -i "/Stored environment variable/ s|': %s|'|; /Stored environment variable/ s|\" \"[$]value\"|\"|" /opt/ai-dock/bin/env-store.sh

# #14941 (vecteur 2/2) : modules/launch_utils.py (app Forge) imprime argv au
# boot ("Launching Web UI with arguments: ...") -> gradio-auth admin:<pw> dans
# les logs. Redaction de la paire credential dans CE print seulement ; le flag
# atteint l'app inchangé. NB : fichier app — une mise à jour git au runtime
# peut le restaurer (même précarité que le sed requirements ci-dessus).
RUN python3 - <<'PYEOF'
BS = chr(92)
p = "/opt/stable-diffusion-webui-forge/modules/launch_utils.py"
src = open(p, encoding="utf-8").read()
anchor = '    print(f"Launching '
pattern = "r'(--gradio-auth[ =])[^ ]*'"
repl = "r'" + BS + "1***'"
helper = (
    "    _redacted_args = re.sub(" + pattern + ", " + repl
    + ", shlex.join(sys.argv[1:]))\n"
)
assert src.count(anchor) == 1, "anchor not unique: print(f Launching"
assert src.count("{shlex.join(sys.argv[1:])}") == 1, "fragment not unique"
src = src.replace(anchor, helper + anchor)
src = src.replace("{shlex.join(sys.argv[1:])}", "{_redacted_args}")
open(p, "w", encoding="utf-8").write(src)
print("launch_utils.py patched: gradio-auth redacted in startup print")
PYEOF

RUN groupadd -g 1000 appuser && \
    useradd -u 1000 -g appuser -m -s /bin/bash appuser

USER appuser

# 4. Pre-flight check to ensure imports work
RUN source /opt/environments/python/forge/bin/activate && \
    python -c "import numpy; import cv2; import skimage; print('Imports successful')"