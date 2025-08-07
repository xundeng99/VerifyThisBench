# Dockerfile: Frama-C with WP + Alt-Ergo on Ubuntu 22.04
#FROM ocaml/opam:ubuntu-22.04-ocaml-4.14
FROM ubuntu:latest

# Install system deps as root
# USER root
ENV DEBIAN_FRONTEND=noninteractive
SHELL ["/bin/bash", "-c"]
RUN apt-get update \
 && apt-get install -y --no-install-recommends software-properties-common \
 && add-apt-repository universe \
 && apt-get update \
 && apt-get install -y --no-install-recommends \
      m4 autoconf pkg-config libgmp-dev \
      graphviz libcairo2-dev libexpat1-dev \
      libgtk-3-dev libgtksourceview-3.0-dev \
      zlib1g-dev z3 git wget unzip curl gcc ocaml \
      ocaml-native-compilers \
      camlp5 \
      opam \
 && rm -rf /var/lib/apt/lists/*

# Switch to opam user, init OPAM and install Frama-C + WP provers
#USER opam
#WORKDIR /home/opam

RUN opam init --disable-sandboxing -y && \
    opam update && \
    opam switch create 4.14.0 && \
    eval $(opam env)

SHELL ["/bin/bash", "-c"]
RUN echo "eval \$(opam env)" >> ~/.bashrc

RUN opam init --disable-sandboxing --no-setup -y \
 && eval "$(opam env)" \
 && opam install frama-c alt-ergo why3 -y \
 && eval "$(opam env)" \
 && why3 config detect

# Prepare workspace and copy source files
#WORKDIR /workspace
#COPY example.c example.h ./

# Default to running the WP proof with Alt-Ergo + RTE
# ENTRYPOINT ["bash","-lc","frama-c -wp -wp-rte -wp-prover alt-ergo example.c example.h"]

# no ENTRYPOINT
#CMD ["bash","-lc","frama-c -wp -wp-rte example.c example.h"]
#USER root
RUN ln -s /root/.opam/4.14.0/bin/frama-c /usr/local/bin/frama-c

