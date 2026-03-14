# =============================================================================
# Radix — Development Task Runner
# =============================================================================
# Usage: make <target>
# Run `make help` to see all available targets.
# =============================================================================

.DEFAULT_GOAL := help
.PHONY: help build test proptest examples bench lint clean check setup fmt sorry-check

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

# ---------------------------------------------------------------------------
# Build
# ---------------------------------------------------------------------------

build: ## Build the entire library
	lake build

build-ffi: ## Build only the FFI C library
	lake build radixffi

# ---------------------------------------------------------------------------
# Test
# ---------------------------------------------------------------------------

test: ## Run unit tests
	lake exe test

proptest: ## Run property-based tests
	lake exe proptest

test-all: test proptest ## Run all tests (unit + property-based)

# ---------------------------------------------------------------------------
# Examples & Benchmarks
# ---------------------------------------------------------------------------

examples: ## Run all examples
	lake exe examples

bench: ## Run benchmarks with C baseline
	lake exe bench

# ---------------------------------------------------------------------------
# Quality
# ---------------------------------------------------------------------------

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

lint: sorry-check ## Run all lint checks

check: build test-all lint ## Run full verification (build + test + lint)

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
	@echo "  [✓] All tests pass"
	@echo "  [✓] Zero sorry statements"
	@echo ""
	@echo "Manual steps remaining:"
	@echo "  [ ] Review CHANGELOG.md"
	@echo "  [ ] Update version in README.md badges"
	@echo "  [ ] Create git tag: git tag -s v<VERSION>"
	@echo "  [ ] Push tag: git push origin v<VERSION>"
