#!/bin/sh
# Rebuild the images in a Linux container and compare them with the pins: evidence that the
# pinned bytes do not depend on the host the pinned LLVM release runs on. Needs Docker.
# The suite is mounted read-only and copied inside the container; the Linux toolchain is kept in
# the Docker volume `openssl-suite-llvm`. Nothing in the working tree is written.
set -eu
cd "$(dirname "$0")/.."
exec docker run --rm -v "$PWD":/suite:ro -v openssl-suite-llvm:/toolchain \
  -e OPENSSL_SUITE_TOOLCHAIN=/toolchain python:3.13-slim sh -c '
    set -e
    apt-get -qq update >/dev/null && apt-get -qq install -y curl ca-certificates >/dev/null
    mkdir /work && cd /suite
    tar -cf - --exclude=.toolchain --exclude=.lake --exclude=out . | tar -xf - -C /work
    # reuse an archive the host already downloaded (it is verified against the pin either way)
    for a in /suite/.toolchain/linux/*.tar.xz; do [ -f "$a" ] && [ ! -e /toolchain/llvm-* ] && cp "$a" /toolchain/; done
    cd /work && python3 tools/build.py'
