# syntax=docker/dockerfile:1
# Service tts-zonos3 : serveur natif zonos3.cpp (ggml/CUDA) de Zyphra/ZONOS3-Mini.
#
# Deux etapes. Le runtime est compile depuis le commit epingle de l'amont (le
# depot ne publie aucun binaire pret-a-l'emploi), puis l'image finale ne garde
# que les executables et les bibliotheques ggml compilees avec eux. Les poids
# ne sont JAMAIS dans l'image : ils viennent du volume monte (README.md,
# section Modeles).
#
# Versions epingles :
#   - runtime : ZONOS3_COMMIT, depot github.com/Zyphra/ZONOS3-Mini (licence MIT) ;
#   - poids   : la revision HF portee par fetch_models.py.
#
# On appelle le runtime officiel, on ne copie aucun de ses sources dans ce depot.

ARG CUDA_VERSION=12.8.1
ARG UBUNTU_VERSION=24.04

# ---------------------------------------------------------------------------
# Etape 1 : compilation du runtime
# ---------------------------------------------------------------------------
FROM nvidia/cuda:${CUDA_VERSION}-devel-ubuntu${UBUNTU_VERSION} AS builder

# Commit du runtime : message « Space: the gold pronunciation lexicon ships
# with the Space », date de commit 2026-11-17T23:22:47Z. C'etait la tete de
# main le 2026-11-27 (jour de la mesure, pas la date du commit).
ARG ZONOS3_COMMIT=a50e14117d99181ba7f28047b451ba03ba1a09a9
# Architecture CUDA unique : 86 = RTX 3090 et RTX 3080 Ti (Ampere). Construire
# le jeu complet d'architectures de ggml multiplie le temps de compilation.
ARG CUDA_ARCH=86
# Parallélisme de compilation, borné : nvcc occupe plus de 1 Go par unite.
ARG BUILD_JOBS=6
# Chaine Rust epinglee. L'amont ne livre aucun rust-toolchain.toml et ne
# declare qu'un MSRV (1.88, dans third_party/zyphra-textnorm/Cargo.toml) :
# « stable » est une cible mouvante, qui rendrait le commit epingle non
# reproductible d'une construction a l'autre. 1.100.0 est la version servie
# par « stable » lors de la construction mesuree du 2026-11-27.
ARG RUST_TOOLCHAIN=1.100.0

ENV DEBIAN_FRONTEND=noninteractive

# git : clone epingle ; cmake + ninja + build-essential : compilation ;
# curl + rustup : la normalisation de texte (third_party/zyphra-textnorm)
# est une bibliotheque Rust que CMake construit avec cargo.
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential \
        ca-certificates \
        cmake \
        curl \
        git \
        ninja-build \
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
        | sh -s -- -y --profile minimal --default-toolchain "${RUST_TOOLCHAIN}"
ENV PATH="/root/.cargo/bin:${PATH}"

# Sous-modules requis par le serveur ggml seulement : ggml et la normalisation
# de texte. FuseAlign (alignement force, edition de parole) n'est pas embarque.
RUN git clone https://github.com/Zyphra/ZONOS3-Mini.git /src/zonos3 \
    && git -C /src/zonos3 checkout --detach "${ZONOS3_COMMIT}" \
    && git -C /src/zonos3 submodule update --init --depth 1 \
        servers/ggml/ggml third_party/zyphra-textnorm \
    && rustc --version && cmake --version | head -1 && nvcc --version | tail -1

WORKDIR /src/zonos3/servers/ggml

# Cibles serveur et CLI uniquement (pas l'application de bureau, ni les outils
# de conversion). Le cache de cargo evite de retélécharger les crates a chaque
# reconstruction de l'image.
# A la configuration, le CMake amont applique lui-meme ses correctifs
# (servers/ggml/patches/*.patch) au sous-module ggml : aucun correctif local.
#
# CMAKE_EXE_LINKER_FLAGS : l'edition de liens des executables a besoin des
# symboles du pilote CUDA (cuMemCreate, cuDeviceGet, ...), que libggml-cuda.so
# reference sans les definir. L'image « devel » livre le toolkit, pas le
# pilote : ses stubs de liaison sont dans lib64/stubs. Ils ne servent QU'ICI,
# dans le builder ; a l'execution le pilote reel est injecte par le runtime
# NVIDIA. Ne jamais les recopier dans l'image finale ni les mettre dans son
# LD_LIBRARY_PATH : un stub masquerait le pilote injecte. Le drapeau n'ecrit
# aucun RUNPATH dans les executables (verifie par readelf sur l'image).
# Mesure du 2026-11-27 sur cette image de base : « -L stubs » seul ne resout
# pas une dependance transitive, il faut « -L stubs -lcuda ».
RUN --mount=type=cache,target=/root/.cargo/registry \
    --mount=type=cache,target=/root/.cargo/git \
    cmake -B build-cuda -G Ninja \
        -DCMAKE_BUILD_TYPE=Release \
        -DGGML_CUDA=ON \
        -DCMAKE_CUDA_ARCHITECTURES="${CUDA_ARCH}" \
        -DCMAKE_EXE_LINKER_FLAGS="-L/usr/local/cuda/lib64/stubs -lcuda" \
    && cmake --build build-cuda --target zonos3-server zonos3-cli -j "${BUILD_JOBS}"

# ---------------------------------------------------------------------------
# Etape 2 : image d'execution
# ---------------------------------------------------------------------------
FROM nvidia/cuda:${CUDA_VERSION}-runtime-ubuntu${UBUNTU_VERSION}

ENV DEBIAN_FRONTEND=noninteractive

# curl : sonde de sante ; ffmpeg : decodage d'un clip de reference brut
# (clonage zero-shot) ; libgomp1 : OpenMP du backend CPU de ggml.
RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        ffmpeg \
        libgomp1 \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /src/zonos3/servers/ggml/build-cuda/zonos3-server /usr/local/bin/zonos3-server
COPY --from=builder /src/zonos3/servers/ggml/build-cuda/zonos3-cli /usr/local/bin/zonos3-cli

# L'amont construit ggml en bibliotheques partagees : sans elles les deux
# executables ne demarrent pas (leurs RUNPATH visent des dossiers du builder,
# absents ici). Elles sont declarees par un fichier ld.so.conf.d plutot que par
# LD_LIBRARY_PATH, pour ne pas ecraser la valeur posee par l'image NVIDIA.
# 0.27.0 est la version de ggml au sous-module epingle ; un changement de pin
# qui la deplacerait fait echouer cette copie, a dessein.
COPY --from=builder /src/zonos3/servers/ggml/build-cuda/ggml/src/libggml.so.0.27.0 \
                    /src/zonos3/servers/ggml/build-cuda/ggml/src/libggml-base.so.0.27.0 \
                    /src/zonos3/servers/ggml/build-cuda/ggml/src/libggml-cpu.so.0.27.0 \
                    /src/zonos3/servers/ggml/build-cuda/ggml/src/ggml-cuda/libggml-cuda.so.0.27.0 \
                    /usr/local/lib/zonos3/
RUN echo "/usr/local/lib/zonos3" > /etc/ld.so.conf.d/zonos3.conf \
    && ldconfig

# Mentions de licence : l'image distribue des binaires construits depuis ces
# sources, et leurs licences exigent que les textes accompagnent toute copie
# (MIT : avis de copyright et de permission ; Apache-2.0 : reproduction du
# NOTICE). Aucun poids n'est distribue avec l'image.
COPY --from=builder /src/zonos3/LICENSE /src/zonos3/NOTICE /usr/local/share/zonos3/
COPY --from=builder /src/zonos3/third_party/licenses/ /usr/local/share/zonos3/third_party/licenses/
COPY --from=builder /src/zonos3/third_party/zyphra-textnorm/LICENSE \
                    /src/zonos3/third_party/zyphra-textnorm/NOTICE \
                    /usr/local/share/zonos3/zyphra-textnorm/
COPY --from=builder /src/zonos3/third_party/zyphra-textnorm/licenses/ /usr/local/share/zonos3/zyphra-textnorm/licenses/
COPY --from=builder /src/zonos3/servers/ggml/ggml/LICENSE /usr/local/share/zonos3/ggml/LICENSE
COPY --from=builder /src/zonos3/servers/ggml/vendor/json-schema-validator/LICENSE \
                    /usr/local/share/zonos3/vendor/json-schema-validator-LICENSE
COPY --from=builder /src/zonos3/servers/ggml/vendor/lmdb/LICENSE \
                    /src/zonos3/servers/ggml/vendor/lmdb/COPYRIGHT \
                    /usr/local/share/zonos3/vendor/lmdb/

COPY entrypoint.sh /usr/local/bin/entrypoint.sh
RUN chmod +x /usr/local/bin/entrypoint.sh

# Utilisateur non root. Le serveur n'ecrit rien tant que --studio-projects-dir
# n'est pas donne (aucun repertoire de projet n'est cree) : le service n'a donc
# besoin d'aucun volume inscriptible, les poids sont montes en lecture seule.
# uid/gid 10001 : l'image de base definit deja « ubuntu » en 1000:1000 (mesure
# du 2026-11-27), ou groupadd rend « GID '1000' already exists » (code 4).
RUN groupadd --gid 10001 appuser \
    && useradd --uid 10001 --gid appuser --create-home --shell /bin/bash appuser

USER appuser
ENV HOME=/home/appuser
WORKDIR /home/appuser

EXPOSE 1919

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
