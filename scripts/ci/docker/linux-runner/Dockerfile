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
# GPU), work dir interne au conteneur (aucun montage hote).

FROM ubuntu:24.04

ARG RUNNER_VERSION=2.336.0
# Checksum officiel de la release v2.336.0 (notes de release actions/runner).
ARG RUNNER_SHA256=04cf0be1aff4c3ec3554466c39124ca250e3effd8873bb7e8d68535aa9505d5d

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates curl git jq unzip tar gzip xz-utils python3 python3-pip \
       libicu74 \
    && rm -rf /var/lib/apt/lists/*

# Tarball runner epingle par SHA-256 (meme discipline que les profils
# self_hosted_runner_profiles.json).
ADD https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz /tmp/runner.tar.gz
RUN echo "${RUNNER_SHA256}  /tmp/runner.tar.gz" | sha256sum -c - \
    && mkdir -p /opt/runner \
    && tar xzf /tmp/runner.tar.gz -C /opt/runner \
    && rm /tmp/runner.tar.gz

RUN useradd -m -u 1001 runner \
    && mkdir -p /home/runner/_work \
    && chown -R runner:runner /opt/runner /home/runner

USER runner
WORKDIR /opt/runner

COPY --chown=runner:runner entrypoint.sh /opt/runner/entrypoint.sh
RUN chmod +x /opt/runner/entrypoint.sh

ENTRYPOINT ["/opt/runner/entrypoint.sh"]
