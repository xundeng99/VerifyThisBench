# Use a base image with Java 17
FROM eclipse-temurin:17-jdk-jammy

# Install dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
    git \
    wget \
    ca-certificates \
    cmake \
    make \
    && rm -rf /var/lib/apt/lists/*

# Clone VerCors repository (shallow clone for faster download)
WORKDIR /opt
RUN wget https://github.com/utwente-fmt/vercors/archive/refs/tags/v2.3.0.tar.gz\
    && tar xzf v2.3.0.tar.gz \
    && mv vercors-2.3.0 vercors

# Build VerCors using mill (as per official instructions)
WORKDIR /opt/vercors
RUN ./mill vercors.main.compile

# Enable VCLLVM (optional)
RUN touch .include-vcllvm && \
    ./mill vercors.main.compile

# Create symlink for easy access
RUN ln -s /opt/vercors/bin/vct /usr/local/bin/vct

# Set working directory for volume mounts
#WORKDIR /workspace

# Test that the installation works
#RUN ./vct examples/concepts/basic/induction-lemma.pvl
