FROM diffblue/cbmc:6.5.0

# Install Python and pip
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        python3 \
        python3-pip && \
    rm -rf /var/lib/apt/lists/*

# Set Python 3 as default
RUN ln -s /usr/bin/python3 /usr/bin/python

# Verify installations
RUN cbmc --version && \
    python --version
