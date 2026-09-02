# Runner GitHub Actions Linux conteneurise (mission #13378, dispatch ai-01
# 2026-08-31 : levier Docker plutot que WSL nu sur po-2024).
#
# Cycle de vie : conteneur --rm, runner --ephemeral (AU PLUS UN JOB puis
# desenregistrement natif). Toute l'invocation passe par l'environnement
# ACTIONS_RUNNER_INPUT_* (jamais --token en argv) -- cf manage_self_hosted_runner.py
# et docs/ci/self-hosted-runners.md.
#
# Isolation : utilisateur non-root, no-new-privileges au lancement, AUCUN
# passthrough GPU (contrainte user : la machine sert aussi de workstation
# GPU). Work dir sur volume nomme PAR SLOT (persistant, #14285 -- cache de
# depot, jamais un bind hote) : sur grace UNIQUEMENT parce qu'aucun code de
# fork n'atteint ces runners ; retirer la persistance avant tout trigger
# pull_request. Cf supervise.sh et docs/ci/self-hosted-runners.md.

FROM ubuntu:24.04

ARG RUNNER_VERSION=2.336.0
# Checksum officiel de la release v2.336.0 (notes de release actions/runner).
ARG RUNNER_SHA256=04cf0be1aff4c3ec3554466c39124ca250e3effd8873bb7e8d68535aa9505d5d

ENV DEBIAN_FRONTEND=noninteractive
# python-is-python3 : les workflows stdlib-only appellent `python` nu
# (check-navlinks, job 100021313259 : exit 127 "python: not found" alors
# que python3 etait present).
# lsb-release : actions/setup-python@v5 avec `cache: pip` appelle
# `lsb_release -i -r -s` pour construire la cle de cache -- sans lui, le job
# meurt sur "Unable to locate executable file: lsb_release" APRES avoir installe
# Python (Scripts Tests (CPU), run 33618470607). zstd : actions/cache et
# upload-artifact l'utilisent, sinon repli gzip (fonctionne, plus lent).
# Deliberement PAS sudo : les conteneurs tournent en --security-opt=no-new-
# privileges, il serait inerte et affaiblirait la posture.
# PEP 668 : Debian marque son Python systeme `externally-managed`, donc
# `pip install <x>` est REFUSE la ou il passe sur ubuntu-latest -- un workflow
# qui fait `import yaml || pip install pyyaml` meurt sur le pip (run
# 33651913220, Unique Check-Run Names Guard). Le conteneur est jetable : lui
# rendre le comportement de la machine GitHub-hosted qu'il remplace est le
# but, pas un risque. python3-yaml en plus, pour que le cas courant n'ait meme
# pas besoin de pip (pas d'aller-retour reseau).
ENV PIP_BREAK_SYSTEM_PACKAGES=1

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates curl git jq unzip tar gzip xz-utils python3 python3-pip python-is-python3 python3-yaml \
       libicu74 \
       lsb-release zstd wget \
    && rm -rf /var/lib/apt/lists/*

# Tarball runner epingle par SHA-256 (meme discipline que les profils
# self_hosted_runner_profiles.json).
ADD https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz /tmp/runner.tar.gz
RUN echo "${RUNNER_SHA256}  /tmp/runner.tar.gz" | sha256sum -c - \
    && mkdir -p /opt/runner \
    && tar xzf /tmp/runner.tar.gz -C /opt/runner \
    && rm /tmp/runner.tar.gz

# /opt/hostedtoolcache : point de montage du volume persistant (supervise.sh).
# Cree ET possede par runner ici pour que le volume nomme herite cette
# propriete a sa premiere creation -- sinon il serait root:root et les
# actions setup-* echoueraient en EACCES sous l'utilisateur non-root.
RUN useradd -m -u 1001 runner \
    && mkdir -p /home/runner/_work /opt/hostedtoolcache \
    && chown -R runner:runner /opt/runner /home/runner /opt/hostedtoolcache

# gh CLI : requis par les guards metadata (check_pr_perimeter POST sa label
# via gh ; sans gh, les organs sous `2>/dev/null || true` rendent exit 0 SANS
# poster -- un vert fabrique, cf #14294). Pin SHA-256 comme le tarball runner.
ARG GH_VERSION=2.99.0
ARG GH_SHA256=ed4960225d2833e04a61590d9fa2b5773d147f3aa375459e5466a40c102f3832
ADD https://github.com/cli/cli/releases/download/v${GH_VERSION}/gh_${GH_VERSION}_linux_amd64.tar.gz /tmp/gh.tar.gz
RUN echo "${GH_SHA256}  /tmp/gh.tar.gz" | sha256sum -c - \
    && tar xzf /tmp/gh.tar.gz -C /tmp \
    && install -m 0755 /tmp/gh_${GH_VERSION}_linux_amd64/bin/gh /usr/local/bin/gh \
    && rm -rf /tmp/gh.tar.gz /tmp/gh_${GH_VERSION}_linux_amd64

USER runner
WORKDIR /opt/runner

COPY --chown=runner:runner entrypoint.sh /opt/runner/entrypoint.sh
RUN chmod +x /opt/runner/entrypoint.sh

ENTRYPOINT ["/opt/runner/entrypoint.sh"]
