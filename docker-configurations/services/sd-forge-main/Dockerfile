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

# #14941: ai-dock's env-store.sh echoes every stored env var's VALUE to stdout
# (-> docker logs): at boot, init.sh calls it for ALL env vars, leaking
# FORGE_ARGS (contains --gradio-auth admin:<password>) and WEB_PASSWORD.
# Drop the value from the log line; the persistence append to
# /opt/ai-dock/etc/environment.sh (required by the app) is kept intact.
# Last layer, after the cached pip layers, to keep rebuilds cheap.
RUN sed -i "/Stored environment variable/ s|': %s|'|; /Stored environment variable/ s|\" \"[$]value\"|\"|" /opt/ai-dock/bin/env-store.sh

# #14941 (vecteur 2/2) + #14956 : modules/launch_utils.py (app Forge) imprime
# argv au boot ("Launching Web UI with arguments: ...") -> gradio-auth ET
# api-auth admin:<pw> dans les logs. Redaction de la paire credential dans CE
# print seulement ; les flags atteignent l'app inchangés. NB : fichier app —
# une mise à jour git au runtime peut le restaurer (même précarité que le sed
# requirements ci-dessus).
RUN python3 - <<'PYEOF'
BS = chr(92)
p = "/opt/stable-diffusion-webui-forge/modules/launch_utils.py"
src = open(p, encoding="utf-8").read()
anchor = '    print(f"Launching '
pattern = "r'(--(?:gradio|api)-auth[ =])[^ ]*'"
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
