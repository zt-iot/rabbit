FROM ocaml/opam:debian-11-ocaml-5.3

ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8
ENV PATH="/home/opam/.local/bin:$PATH"


RUN sudo apt update && sudo apt install -y \
  graphviz \
  maude 

# Install Haskell Stack
RUN curl -sSL https://get.haskellstack.org/ | sh && \
    echo 'export PATH="/home/opam/.local/bin:$PATH"' >> /home/opam/.bashrc

# Clone and build Tamarin
RUN git clone https://github.com/tamarin-prover/tamarin-prover.git /home/opam/tamarin-prover
WORKDIR /home/opam/tamarin-prover
RUN git checkout master && make default

# Copy Rabbit source into image
COPY . /home/opam/rabbit
WORKDIR /home/opam/rabbit

# Build and install Rabbit
RUN opam install . --deps-only -y && \
    opam install . -y

# Make sure evaluate.sh is executable
RUN chmod +x evaluate.sh

# Default command: run evaluate.sh
CMD ["./evaluate.sh"]