FROM ubuntu:20.04

# prevent tzdata from asking for timezone
ARG DEBIAN_FRONTEND=noninteractive

# change apt source
RUN sed -i 's@archive.ubuntu.com@mirror.kakao.com@g' /etc/apt/sources.list

# install package for fuzzing
RUN apt-get update && apt-get install -y \
    build-essential \
    git \
    curl \
    clang \
    make \
    cmake \
    python3 \
    python3-pip \
    csmith \
    libcsmith-dev \
    creduce \
    gcc-riscv64-linux-gnu \
    g++-riscv64-linux-gnu \
    qemu-user-static \
    gdb-multiarch \
    m4 \
    && rm -rf /var/lib/apt/lists/*


RUN pip3 install tqdm

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN rustup toolchain install 1.85.0 \
 && rustup default 1.85.0 \
 && rustup component add rustfmt clippy rust-analyzer

WORKDIR /home/kecc

# ===== Cargo 依赖缓存 =====
COPY Cargo.toml Cargo.lock rust-toolchain.toml ./
RUN cargo fetch