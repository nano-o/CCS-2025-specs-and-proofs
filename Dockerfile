FROM python:3.12-slim

# Toolchain image for checking the artifacts in this repo:
#  - TLA+ model checker (TLC) via tla2tools.jar (Java)
#  - Ivy proof checker (Python venv)
#  - Isabelle/HOL proof assistant (downloaded tarball)
#
# Nothing is pre-checked at image build time; checks are run on demand
# inside the container with `make check-ivy`, `make check-isabelle`, or
# `make run-tlc TLA_SPEC=...` (see README.md and Makefile).
#
# We base on python:3.12-slim because Ivy still imports `tkinter.tix`,
# which was removed in CPython 3.13. Once Ivy drops that import we
# could move back to debian:stable-slim (which now ships Python 3.13).

ARG ISABELLE_VERSION=Isabelle2025-2
# Cambridge mirror (the TUM primary at isabelle.in.tum.de rate-limits aggressively).
ARG ISABELLE_URL=https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2025-2_linux.tar.gz
# Pinned Ivy commit (head of kenmcmil/ivy main at image authoring time).
ARG IVY_COMMIT=912e29603ee6b92502d4d1d82197f0683eacdc4e

ENV DEBIAN_FRONTEND=noninteractive

# Minimal packages needed to fetch and run Isabelle. This layer is
# deliberately placed before the Ivy tooling so that edits to those
# later layers do not invalidate the ~1 GB Isabelle download.
#  - default-jre-headless: TLC + TLA+ tooling
#  - wget / ca-certificates / tar: fetching the Isabelle tarball
#  - make: running the Makefile targets
RUN apt-get update && apt-get install -y --no-install-recommends \
        default-jre-headless \
        wget ca-certificates tar \
        make \
    && rm -rf /var/lib/apt/lists/*

# Install Isabelle into /opt/Isabelle and put its binary on PATH.
# TEMPORARILY DISABLED while iterating on the rest of the image. Re-enable
# when Ivy/TLC are confirmed working in the container.
# RUN wget --progress=dot:giga -O /tmp/isabelle.tar.gz "$ISABELLE_URL" \
#     && mkdir -p /opt \
#     && tar -xzf /tmp/isabelle.tar.gz -C /opt \
#     && mv "/opt/${ISABELLE_VERSION}" /opt/Isabelle \
#     && rm /tmp/isabelle.tar.gz \
#     && ln -s /opt/Isabelle/bin/isabelle /usr/local/bin/isabelle

# Additional packages for Ivy and developer convenience. python:3.12-slim
# already ships python3, pip and venv; we just need tk and a few extras.
#  - tk: Ivy imports tkinter / tkinter.tix unconditionally, even on CLI
#  - git: cloning Ivy from upstream
#  - build-essential: fallback for building z3-solver if no wheel matches
#  - graphviz: pydot rendering for Ivy
#  - sudo, nano, vim: developer convenience inside the container
RUN apt-get update && apt-get install -y --no-install-recommends \
        tk \
        git build-essential \
        graphviz \
        sudo nano vim \
    && rm -rf /var/lib/apt/lists/*

# Install Ivy from a pinned commit into a dedicated venv. The venv uses
# --system-site-packages so that tkinter (which ships with CPython and
# cannot be pip-installed) is visible to ivy_check.
RUN python3 -m venv --system-site-packages /opt/ivy-venv \
    && /opt/ivy-venv/bin/pip install --no-cache-dir --upgrade pip \
    && git clone https://github.com/kenmcmil/ivy.git /opt/ivy-src \
    && git -C /opt/ivy-src checkout "$IVY_COMMIT" \
    && /opt/ivy-venv/bin/pip install --no-cache-dir -e /opt/ivy-src
ENV PATH=/opt/ivy-venv/bin:$PATH

# Non-root user.
RUN useradd -m -s /bin/bash imageuser \
    && echo "imageuser ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/imageuser \
    && chmod 0440 /etc/sudoers.d/imageuser

# Pre-build the Isabelle HOL session as the non-root user so its heap
# lives in the user's home and the first `make check-isabelle` only
# has to build the OptiRBC session itself. Done before the COPY below
# so edits to repo files do not invalidate this layer.
# TEMPORARILY DISABLED along with the Isabelle install above.
USER imageuser
# RUN isabelle build -b HOL

WORKDIR /artifact
COPY --chown=imageuser:imageuser . /artifact

# Translate the PlusCal modules in place so `make run-tlc` works out of
# the box. pcal.trans rewrites the .tla file, so the files in the image
# include a BEGIN/END TRANSLATION block that the host copies do not.
RUN make trans TLA_SPEC=Sailfish.tla \
    && make trans TLA_SPEC=TwoStepOptimiticBroadcast.tla

CMD ["/bin/bash"]

# Build and run:
#   docker build -t ccs2025-formal-specs-artifacts .
#   docker run --rm -it ccs2025-formal-specs-artifacts
# Inside the container:
#   make check-ivy        # check the Ivy proof
#   make check-isabelle   # build the Isabelle session
#   make run-tlc TLA_SPEC=TLCSailfish1.tla   # model-check Sailfish
