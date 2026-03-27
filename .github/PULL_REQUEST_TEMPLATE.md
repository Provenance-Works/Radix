## Description

<!-- Brief description of what this PR does. -->

## Type of Change

- [ ] Bug fix (non-breaking change which fixes an issue)
- [ ] New feature (non-breaking change which adds functionality)
- [ ] New theorem / proof (adds or strengthens formal verification)
- [ ] Breaking change (fix or feature that would cause existing functionality to not work as expected)
- [ ] Documentation update
- [ ] Refactoring (no functional changes, no new proofs)
- [ ] Test improvement
- [ ] Build / CI change

## Import Surface

- [ ] `Radix`
- [ ] `Radix.Pure`
- [ ] `Radix.Trusted`
- [ ] `Radix.ProofAutomation`
- [ ] Leaf modules only

## Module(s) Affected

### Pure modules
- [ ] Word
- [ ] Bit
- [ ] Bytes
- [ ] Memory
- [ ] Binary
- [ ] Alignment
- [ ] RingBuffer
- [ ] Bitmap
- [ ] CRC
- [ ] MemoryPool
- [ ] UTF8
- [ ] ECC
- [ ] DMA
- [ ] Timer

### Trusted-boundary modules
- [ ] System
- [ ] Concurrency
- [ ] BareMetal

### Meta / project-wide
- [ ] ProofAutomation
- [ ] Docs / Examples
- [ ] Build / CI / Release

## Verification Checklist

- [ ] `make check` succeeds, or I explained below why narrower validation was appropriate
- [ ] Zero `sorry` in library, tests, and examples (`rg -n "sorry" Radix tests examples` returns nothing)
- [ ] Relevant tests/examples pass for the affected surface
- [ ] New specifications added to `*.Spec.lean` (if applicable)
- [ ] Implementation proven correct against specification (if applicable)
- [ ] New/updated tests or examples added
- [ ] Documentation updated (English + Japanese, if applicable)
- [ ] CHANGELOG.md updated when the change is user-visible or release-note-worthy

## Checklist

- [ ] My code follows the project's [style guide](CONTRIBUTING.md#style-guide)
- [ ] I have performed a self-review
- [ ] Commit messages follow [Conventional Commits](https://www.conventionalcommits.org/) format
- [ ] My changes follow the [three-layer architecture](docs/en/architecture/README.md)
- [ ] I updated grouped import surfaces if I changed the public module boundary

## Related Issues

<!-- Closes #<issue-number> -->

## Additional Notes

<!-- Any additional context for reviewers. -->
