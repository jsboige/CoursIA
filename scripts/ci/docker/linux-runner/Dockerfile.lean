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
# Le toolchain "stable" de l'image couvre les lakes qui suivent stable ; un
# lake qui pinne une autre version declenche un telechargement elan a la volee
# dans ~/.elan (ephemere par conteneur). Si ce cas devient frequent, monter un
# volume dedie sur /home/runner/.elan au deploiement (tranche 2+).
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
USER runner
RUN /tmp/elan-init -y --no-modify-path --default-toolchain stable \
    && rm /tmp/elan-init \
    && elan default stable \
    && lake --version
ENV PATH=/home/runner/.elan/bin:$PATH
