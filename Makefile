# =============================================================================
# Radix — Development Task Runner
# =============================================================================
# Usage: make <target>
# Run `make help` to see all available targets.
# =============================================================================

.DEFAULT_GOAL := help
.PHONY: help build build-baseline build-ffi test proptest comptest test-all examples bench lint clean check setup fmt sorry-check stats stats-check pre-commit-install pre-commit-run

# ---------------------------------------------------------------------------
# Help
# ---------------------------------------------------------------------------

help: ## Show this help message
	@echo "Radix — Formally Verified Foundation Library for Lean 4"
	@echo ""
	@echo "Usage: make <target>"
	@echo ""
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | \
		awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-18s\033[0m %s\n", $$1, $$2}'
	@echo ""

# ---------------------------------------------------------------------------
# Setup
# ---------------------------------------------------------------------------

setup: ## Install dependencies and fetch Mathlib cache
	lake update
	lake exe cache get 2>/dev/null || true
	@if command -v pre-commit >/dev/null 2>&1; then \
		pre-commit install --install-hooks; \
	else \
		echo "Optional: install pre-commit, then run 'make pre-commit-install'"; \
	fi

# ---------------------------------------------------------------------------
# Build
# ---------------------------------------------------------------------------

build: ## Build the entire library
	lake build

build-baseline: ## Build the C benchmark baseline
	@compiler=""; \
	for candidate in /usr/bin/gcc gcc cc clang; do \
		if command -v "$$candidate" >/dev/null 2>&1; then \
			if printf 'int main(void){return 0;}\n' | "$$candidate" -x c - -o /tmp/radix-cc-check >/dev/null 2>&1; then \
				compiler="$$candidate"; \
				break; \
			fi; \
		fi; \
	done; \
	if [ -n "$$compiler" ]; then \
		rm -f /tmp/radix-cc-check; \
		"$$compiler" -O2 -fno-builtin -o benchmarks/baseline benchmarks/baseline.c; \
		echo "Built C baseline with $$compiler"; \
	else \
		echo "Skipping baseline build: no working C compiler found"; \
	fi

build-ffi: build-baseline ## Deprecated alias for the C benchmark baseline
	@echo "build-ffi is deprecated; use build-baseline"

# ---------------------------------------------------------------------------
# Test
# ---------------------------------------------------------------------------

test: ## Run unit tests
	lake exe test

proptest: ## Run property-based tests
	lake exe proptest

comptest: ## Run comprehensive regression tests
	lake exe comptest

test-all: test proptest comptest ## Run all tests (unit + property + comprehensive)

# ---------------------------------------------------------------------------
# Examples & Benchmarks
# ---------------------------------------------------------------------------

examples: ## Run all examples
	lake exe examples

bench: build-baseline ## Run Lean benchmarks and the C baseline when available
	lake exe bench
	@if [ -x benchmarks/baseline ]; then \
		./benchmarks/baseline; \
	else \
		echo "Skipping C baseline run: benchmarks/baseline not available"; \
	fi

# ---------------------------------------------------------------------------
# Quality
# ---------------------------------------------------------------------------

stats: ## Refresh README/docs/project statistics from scripts/project_stats.json
	python3 scripts/update_project_stats.py

stats-check: ## Verify README/docs/project statistics are up to date
	python3 scripts/update_project_stats.py --check

pre-commit-install: ## Install local pre-commit hooks
	@command -v pre-commit >/dev/null 2>&1 || { echo "Install pre-commit first: python3 -m pip install pre-commit"; exit 1; }
	pre-commit install --install-hooks

pre-commit-run: ## Run pre-commit on all files
	@command -v pre-commit >/dev/null 2>&1 || { echo "Install pre-commit first: python3 -m pip install pre-commit"; exit 1; }
	pre-commit run --all-files

sorry-check: ## Verify zero sorry statements in codebase
	@echo "Scanning for sorry statements..."
	@result=$$(grep -rn "sorry" Radix/ --include="*.lean" 2>/dev/null); \
	if [ -n "$$result" ]; then \
		echo "ERROR: Found sorry statements:"; \
		echo "$$result"; \
		exit 1; \
	else \
		echo "OK: Zero sorry statements found."; \
	fi

lint: sorry-check stats-check ## Run all lint checks

check: build test-all examples lint ## Run full verification (build + all tests + examples + lint)

# ---------------------------------------------------------------------------
# Clean
# ---------------------------------------------------------------------------

clean: ## Remove build artifacts
	lake clean
	rm -rf build/ .lake/build/

# ---------------------------------------------------------------------------
# Documentation
# ---------------------------------------------------------------------------

docs: ## Open documentation index
	@echo "Documentation available at:"
	@echo "  English:  docs/en/README.md"
	@echo "  Japanese: docs/ja/README.md"

# ---------------------------------------------------------------------------
# Release
# ---------------------------------------------------------------------------

release-check: check ## Pre-release verification (full check + changelog review)
	@echo ""
	@echo "Pre-release checklist:"
	@echo "  [✓] Build succeeds"
	@echo "  [✓] Unit, property, and comprehensive tests pass"
	@echo "  [✓] Examples execute successfully"
	@echo "  [✓] Zero sorry statements"
	@echo ""
	@echo "Manual steps remaining:"
	@echo "  [ ] Review CHANGELOG.md"
	@echo "  [ ] Update version in README.md badges"
	@echo "  [ ] Create git tag: git tag -s v<VERSION>"
	@echo "  [ ] Push tag: git push origin v<VERSION>"
