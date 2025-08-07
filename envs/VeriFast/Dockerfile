# Prepare environment
FROM ubuntu:latest

# Set default shell to bash
SHELL ["/bin/bash", "-c"]
ENV DEBIAN_FRONTEND=noninteractive

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
RUN apt update

RUN curl -L -o verifast.tar.gz https://github.com/verifast/verifast/releases/download/25.02/verifast-25.02-linux.tar.gz
RUN tar xzf verifast.tar.gz
RUN rm verifast.tar.gz

RUN ln -s /verifast-25.02/bin/verifast /usr/local/bin/verifast


# COPY example.c .
# RUN /verifast-25.02/bin/verifast -c example.c

# bin/verifast
# dafny build -t:py example.dfy
# python3 example-py/example.py
