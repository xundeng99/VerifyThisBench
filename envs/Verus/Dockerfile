# Prepare Python+Verus environment
FROM rust:latest AS rust-base

# Add Rust environment
RUN rustup component add rustfmt
#RUN cargo install verusfmt


# Set default shell to bash
SHELL ["/bin/bash", "-c"]

# Install any other system tools
RUN apt-get update && \
    apt-get install -y \
    git \
    wget \
    unzip \
    curl \
    gcc \
    pkg-config \
    libssl-dev \
    python3 \
    python3-pip \
    python3-venv

RUN ln -s /usr/bin/python3 /usr/bin/python
# Install Verus and any dependencies
COPY /get-z3.sh .
COPY /get-verus.sh .
RUN chmod +x /get-z3.sh /get-verus.sh

RUN /get-z3.sh
RUN /get-verus.sh

COPY /example.rs .
