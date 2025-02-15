FROM rust:1.80-slim-bullseye

WORKDIR /project

ARG RUST_LOG
ARG REDIS_VERSION
ARG REDIS_USERNAME
ARG REDIS_PASSWORD
ARG FRED_REDIS_CENTRALIZED_HOST
ARG FRED_REDIS_CENTRALIZED_PORT
ARG CIRCLECI_TESTS

RUN USER=root apt-get update && apt-get install -y build-essential libssl-dev dnsutils curl pkg-config
RUN echo "REDIS_VERSION=$REDIS_VERSION"

# For debugging
RUN cargo --version && rustc --version