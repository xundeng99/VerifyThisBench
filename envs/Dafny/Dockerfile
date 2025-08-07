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
RUN apt update

RUN wget https://packages.microsoft.com/config/ubuntu/22.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
RUN dpkg -i packages-microsoft-prod.deb
RUN rm packages-microsoft-prod.deb
RUN apt-get update
RUN apt install -y dotnet-sdk-6.0

RUN curl -L -o dafny.zip https://github.com/dafny-lang/dafny/releases/download/v4.10.0/dafny-4.10.0-x64-ubuntu-20.04.zip
RUN unzip dafny.zip
RUN rm dafny.zip

RUN ln -s $PWD/dafny/dafny /usr/local/bin/dafny

RUN ln -s /usr/bin/python3 /usr/bin/python
#COPY example.dfy .

# dafny verify example.dfy
# dafny build -t:py example.dfy
# python3 example-py/example.py
