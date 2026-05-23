JAR=tla2tools.jar
JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/$(JAR)
TLC_WORKERS=8
TLC_OFFHEAP_MEMORY=12G
TLC_HEAP=4G
TLA_SPEC?=
TLA_FILES := $(wildcard *.tla)
TLA_PDFS := $(TLA_FILES:.tla=.pdf)
TLC_CFG ?= $(abspath $(basename $(TLA_SPEC))).cfg
TLC_CMD=java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} \
	-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet \
	-Dtlc2.tool.ModelChecker.BAQueue=true \
	-jar $(abspath $(JAR)) \
	-workers ${TLC_WORKERS} \
	-checkpoint 30 \
	-noGenerateSpecTE \
	-config '$(TLC_CFG)'

# Download the JAR if it does not exist
$(JAR):
	wget -O $@ $(JAR_URL)

# Don't redownload
.PRECIOUS: $(JAR)

sany: $(JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make sany TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	java -cp $(JAR) tla2sany.SANY $(TLA_SPEC)

%.pdf: %.tla $(JAR)
	java -cp tla2tools.jar tla2tex.TLA -ps -latexCommand pdflatex $<
	@latexmk -c -quiet -e '$$clean_ext .= " synctex.gz fdb_latexmk dvi ps tex";' $(basename $<).tex

trans: $(JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	java -cp $(JAR) pcal.trans -nocfg $(TLA_SPEC)


run-tlc: $(JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	$(TLC_CMD) $(TLA_SPEC)

pdfs: $(TLA_PDFS)

block-dag-test: TLA_SPEC=BlockDagTest.tla
block-dag-test: $(JAR)
	$(TLC_CMD) $(TLA_SPEC)

# Ivy proof check. Re-run with a different random seed if it times out.
# The seed is generated portably (dash does not implement $RANDOM).
check-ivy:
	ivy_check seed=$$(od -An -N2 -tu2 /dev/urandom | tr -d ' ') opti_rbc.ivy

# Isabelle session build. The OptiRBC session does not build a PDF by
# default (ROOT no longer sets document = pdf) so this works without a
# LaTeX toolchain. To also regenerate OptiRBC/browser_info/document.pdf
# locally, run `isabelle build -o document=pdf -D OptiRBC` instead.
check-isabelle:
	isabelle build -D OptiRBC

# --- Docker image -----------------------------------------------------------
#
# Build and publish the toolchain image to Docker Hub. Override the
# DOCKERHUB_USER / IMAGE_VERSION variables on the command line to push under
# a different account or tag, e.g.
#   make docker-push DOCKERHUB_USER=someone IMAGE_VERSION=v5
#
DOCKERHUB_USER ?= giulianolosa
IMAGE_NAME     ?= ccs2025-formal-specs-artifacts
IMAGE_VERSION  ?= v1
IMAGE          := $(DOCKERHUB_USER)/$(IMAGE_NAME)

docker-build:
	docker build -t $(IMAGE):$(IMAGE_VERSION) -t $(IMAGE):latest .

docker-push: docker-build
	docker push $(IMAGE):$(IMAGE_VERSION)
	docker push $(IMAGE):latest

.PHONY: sany trans run-tlc pdfs block-dag-test run-tlc-diskcap check-ivy check-isabelle docker-build docker-push
