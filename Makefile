# `make` downloads the prebuilt Mathlib, builds the proof, and checks it (a few hours).
.PHONY: all build check kernel-replay comparator clean
all: check

build:
	lake exe cache get
	lake build

check: build
	lake env lean Check.lean

# ---- optional ---------------------------------------------------------------------------------------------
kernel-replay: build   ## re-check every module's declarations with leanchecker (slow)
	find StatementChecks Proof Bindings -name '*.lean' | sed 's|/|.|g; s|\.lean$$||' | \
	  xargs -P $$(getconf _NPROCESSORS_ONLN) -I{} lake env leanchecker {}
	lake env leanchecker Statement
	lake env leanchecker Statement_Wire_3_5
	lake env leanchecker MainTheorem_Wire_3_5

COMPARATOR ?= comparator
comparator:            ## comparator check (README); run it in a fresh clone, so the proof is built only in its sandbox
	lake exe cache get
	systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$$PATH" --working-directory $(CURDIR) -- bash -c 'ulimit -s unlimited && lake env $(COMPARATOR) comparator.json'

clean:
	rm -rf .lake/build
