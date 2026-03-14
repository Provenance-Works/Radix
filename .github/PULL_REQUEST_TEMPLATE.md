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

## Module(s) Affected

- [ ] Word
- [ ] Bit
- [ ] Bytes
- [ ] Memory
- [ ] Binary
- [ ] System
- [ ] Concurrency
- [ ] BareMetal
- [ ] Infrastructure / Build

## Verification Checklist

- [ ] `lake build` succeeds with zero errors
- [ ] Zero `sorry` in entire codebase (`grep -r "sorry" Radix/` returns nothing)
- [ ] All tests pass (`lake exe test && lake exe proptest`)
- [ ] New specifications added to `*.Spec.lean` (if applicable)
- [ ] Implementation proven correct against specification (if applicable)
- [ ] New/updated tests added
- [ ] Documentation updated (English + Japanese, if applicable)
- [ ] CHANGELOG.md updated under `[Unreleased]`

## Checklist

- [ ] My code follows the project's [style guide](CONTRIBUTING.md#style-guide)
- [ ] I have performed a self-review
- [ ] Commit messages follow [Conventional Commits](https://www.conventionalcommits.org/) format
- [ ] My changes follow the [three-layer architecture](docs/en/architecture/README.md)

## Related Issues

<!-- Closes #<issue-number> -->

## Additional Notes

<!-- Any additional context for reviewers. -->
