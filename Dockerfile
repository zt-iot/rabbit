FROM ocaml/opam:debian-11-ocaml-5.3 AS builder
#FROM ocaml/opam:debian-11-ocaml-5.3

ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8
ENV PATH="/home/opam/.local/bin:$PATH"


RUN sudo apt update && sudo apt install -y \
  pkg-config \
  libgtk2.0-dev \
  libz-dev \
  bubblewrap \
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

# Stage 2: Slim runtime
FROM debian:bullseye-slim

ENV LANG=en_US.UTF-8
ENV LANGUAGE=en_US:en
ENV LC_ALL=en_US.UTF-8

RUN apt update && apt install -y \
    locales \
 && apt clean

RUN echo "en_US.UTF-8 UTF-8" > /etc/locale.gen && \
    locale-gen

# Copy rabbit, tamarin-prover, and proverif executables
COPY --from=builder /home/opam/.opam/5.3/bin/rabbit /usr/local/bin/rabbit

WORKDIR /home/opam

