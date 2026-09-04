# Runner GitHub Actions Linux specialise LEAN (#14337 tranche 1 : pools
# specialises par labels plutot qu'une image unique qui grossit).
#
# RATIONALE (cf issue #14337) : le cout d'un job Lean n'est pas le toolchain,
# c'est MATHLIB. Deux etats chauds, deux supports :
#   - elan + toolchain stable : dans l'IMAGE (couche figee, reproductible,
#     pincee par SHA-256 comme le tarball runner et gh du Dockerfile de base).
#   - .lake/packages et .lake/build des lakes : dans le VOLUME _work PAR SLOT
#     (pattern #14285 -- le checkout persiste, lake build devient incremental
#     et `lake exe cache get` ne re-telecharge plus les oleans Mathlib).
#     Aucune image, si grosse soit-elle, ne peut porter cet etat : il depend
#     du lake et vit cote slot.
#
# Le toolchain par defaut est EPINGLE sur v4.32.1 : mesure du 2026-09-04,
# 13/14 lakes du depot portent leanprover/lean4:v4.32.1 (seul conway_cgt_lean
# pinne v4.31.0-rc2). Une image sur "stable" (v4.33.1 au jour du build) serait
# alignee sur zero lake : chaque job paierait un telechargement elan a la volee
# dans ~/.elan (ephemere par conteneur) -- exactement le cout que ce pool
# existe pour eviter. Un lake qui pinne une autre version declenche quand meme
# ce telechargement ; si le cas devient frequent, monter un volume dedie sur
# /home/runner/.elan au deploiement (tranche 2+).
#
# Labels du pool : self-hosted,coursia-ephemeral,coursia-lean -- JAMAIS
# coursia-linux : le label distinct EST la garantie de routage (un garde
# Python ne doit pas atterrir sur un slot Lean, et inversement).

FROM coursia-linux-runner:2.336.0

# elan pince par SHA-256, meme discipline que le Dockerfile de base.
# v4.2.4, asset elan-x86_64-unknown-linux-gnu.tar.gz (contient elan-init).
ARG ELAN_VERSION=4.2.4
ARG ELAN_SHA256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63

USER root
ADD https://github.com/leanprover/elan/releases/download/v${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz /tmp/elan.tar.gz
RUN echo "${ELAN_SHA256}  /tmp/elan.tar.gz" | sha256sum -c - \
    && tar xzf /tmp/elan.tar.gz -C /tmp \
    && chown runner:runner /tmp/elan-init \
    && rm /tmp/elan.tar.gz

# Installation sous l'utilisateur runner : elan est un installeur par-compte
# (style rustup), ~/.elan doit appartenir a runner pour que les toolchains
# telecharges au runtime soient accessibles sous l'UID 1001 du conteneur.
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.32.1
USER runner
# ENV AVANT le RUN : --no-modify-path laisse ~/.elan/bin hors du PATH du shell,
# donc le meme RUN ne retrouverait pas `elan` sans cette ligne (mesure :
# "/bin/sh: 1: elan: not found", exit 127).
ENV PATH=/home/runner/.elan/bin:$PATH
RUN /tmp/elan-init -y --no-modify-path --default-toolchain ${LEAN_TOOLCHAIN} \
    && rm /tmp/elan-init \
    && elan default ${LEAN_TOOLCHAIN} \
    && lake --version
