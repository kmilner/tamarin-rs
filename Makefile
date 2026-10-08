# Cargo initializes missing sources and builds the embedded GUI automatically.
.DEFAULT_GOAL := build

PREFIX ?= $(HOME)/.local
DESTDIR ?=
CARGO ?= cargo
CARGO_TARGET_DIR ?= target
CARGO_BUILD = $(CARGO) build --locked --bin tamarin-rs --target-dir "$(CARGO_TARGET_DIR)"

.PHONY: all tamarin install setup frontend build debug check test clean
all tamarin: build

setup:
	./setup.sh

frontend: setup
	bash scripts/build_gui.sh "$(CARGO_TARGET_DIR)/gui"

build:
	$(CARGO_BUILD) --release

debug:
	$(CARGO_BUILD)

install:
	@set -eu; \
	artifacts=$$(mktemp); \
	trap 'rm -f "$$artifacts"' EXIT HUP INT TERM; \
	$(CARGO_BUILD) --release --message-format=json-render-diagnostics > "$$artifacts"; \
	binary=$$(node scripts/cargo_binary_path.mjs < "$$artifacts"); \
	install -d "$(DESTDIR)$(PREFIX)/bin"; \
	install -m 755 "$$binary" "$(DESTDIR)$(PREFIX)/bin/tamarin-rs.new"; \
	mv -f "$(DESTDIR)$(PREFIX)/bin/tamarin-rs.new" "$(DESTDIR)$(PREFIX)/bin/tamarin-rs"
	@echo "Installed $(DESTDIR)$(PREFIX)/bin/tamarin-rs (GUI embedded)"

check:
	$(CARGO) fmt --all --check
	$(CARGO) clippy --workspace --all-targets --target-dir "$(CARGO_TARGET_DIR)" -- -D warnings

test:
	$(CARGO) test --profile ci --workspace --target-dir "$(CARGO_TARGET_DIR)"

clean:
	$(CARGO) clean --target-dir "$(CARGO_TARGET_DIR)"
