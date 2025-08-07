FROM ubuntu:latest

ENV DEBIAN_FRONTEND=noninteractive \
    OPAMYES=true \
    WHY3_VERSION=1.6.0

# Install system dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    m4 \
    curl \
    git \
    wget \
    unzip \
    bubblewrap \
    sudo \
    software-properties-common \
    pkg-config \
    libgmp-dev \
    zlib1g-dev \
    ocaml \
    ocaml-native-compilers \
    camlp5 \
    opam \
    python3 \
    python3-pip \
    cmake \
    autoconf \
    automake \
    libtool \
    libboost-all-dev \
    libsqlite3-dev \
    && apt-get clean

# Initialize OPAM and switch to compatible OCaml version
RUN opam init --disable-sandboxing -y && \
    opam update && \
    opam switch create 4.14.0 && \
    eval $(opam env)

SHELL ["/bin/bash", "-c"]
RUN echo "eval \$(opam env)" >> ~/.bashrc

# Install Why3 from OPAM
RUN eval $(opam env) && \
    opam install -y why3.${WHY3_VERSION}

# -----------------------------
# Install Z3 4.8.10
# -----------------------------
RUN wget https://github.com/Z3Prover/z3/archive/z3-4.8.10.tar.gz && \
    tar -xzf z3-4.8.10.tar.gz && \
    cd z3-z3-4.8.10 && \
    python3 scripts/mk_make.py && \
    cd build && \
    make -j$(nproc) && \
    make install && \
    cd ../.. && rm -rf z3*

# -----------------------------
# Install Alt-Ergo 2.4.0 via OPAM
# -----------------------------
RUN eval $(opam env) && \
    opam install -y alt-ergo.2.4.0

# -----------------------------
# Install CVC4 1.8 from source
# -----------------------------
RUN wget -nv https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt && \
    mv cvc4-1.8-x86_64-linux-opt /usr/local/bin/cvc4 && \
    chmod +x /usr/local/bin/cvc4 && \
    cvc4 --version

# -----------------------------
# Install CVC5 1.0.2 from source
# -----------------------------
RUN wget -nv https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.2/cvc5-Linux && \
    mv cvc5-Linux /usr/local/bin/cvc5 && \
    chmod +x /usr/local/bin/cvc5 && \
    cvc5 --version

# Detect provers
RUN eval $(opam env) && \
    why3 config detect

RUN ln -s /root/.opam/4.14.0/bin/why3 /usr/local/bin/why3
RUN ln -s /usr/bin/python3 /usr/bin/python