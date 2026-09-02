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
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates curl git jq unzip tar gzip xz-utils python3 python3-pip python-is-python3 \
       libicu74 \
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

USER runner
WORKDIR /opt/runner

COPY --chown=runner:runner entrypoint.sh /opt/runner/entrypoint.sh
RUN chmod +x /opt/runner/entrypoint.sh

ENTRYPOINT ["/opt/runner/entrypoint.sh"]
