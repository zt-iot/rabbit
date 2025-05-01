FROM ocaml/opam:debian-11-ocaml-5.3 AS builder
#FROM ocaml/opam:debian-11-ocaml-5.3

ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8
ENV PATH="/home/opam/.local/bin:$PATH"


RUN sudo apt update && sudo apt install -y \
  graphviz \
  maude \
  pkg-config \
  libgtk2.0-dev \
  libgmp-dev \
  libz-dev \
  bubblewrap \
  z3 \
  gcc \
  make \
  curl \
  git

# Copy Rabbit source into image
COPY . /home/opam/rabbit
RUN sudo chown -R opam:opam /home/opam/rabbit
WORKDIR /home/opam/rabbit

# Build and install Rabbit
RUN opam update  && \
    opam install . --deps-only -y && \
    opam install . -y


# Install Haskell Stack
#RUN curl -sSL https://get.haskellstack.org/ | sh && \
#    echo 'export PATH="/home/opam/.local/bin:$PATH"' >> /home/opam/.bashrc

# Clone and build Tamarin
#RUN git clone https://github.com/tamarin-prover/tamarin-prover.git /home/opam/tamarin-prover
#WORKDIR /home/opam/tamarin-prover
#RUN git checkout master && make default


# Make sure evaluate.sh is executable
#RUN chmod +x evaluate.sh

# Default command: run evaluate.sh
#CMD ["./evaluate.sh"]


# Stage 2: Slim runtime
FROM debian:bullseye-slim

ENV LANG=en_US.UTF-8
ENV LANGUAGE=en_US:en
ENV LC_ALL=en_US.UTF-8

RUN apt update && apt install -y \
    graphviz \
    maude \
    z3 \
    bubblewrap \
    libgmp-dev \
    libtinfo-dev \
    libz-dev \
    make \
    bash \
    locales \
 && apt clean

RUN echo "en_US.UTF-8 UTF-8" > /etc/locale.gen && \
    locale-gen

# Copy rabbit, tamarin-prover, and proverif executables
COPY --from=builder /home/opam/.opam/5.3/bin/rabbit /usr/local/bin/rabbit
#COPY --from=builder /home/opam/.local/bin/tamarin-prover /usr/local/bin/tamarin-prover
#COPY --from=builder /home/opam/.opam/5.3/bin/proverif /usr/local/bin/proverif



#COPY evaluate.sh /usr/local/bin/evaluate.sh

# Make evaluate.sh executable
#RUN chmod +x /usr/local/bin/evaluate.sh
#CMD ["/usr/local/bin/evaluate.sh"]


WORKDIR /home/opam

