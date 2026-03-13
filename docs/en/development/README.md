# Development

> **Audience**: Contributors

Guides for developers contributing to Radix.

| Document | Description |
|----------|-------------|
| [Setup](setup.md) | Development environment setup |
| [Build](build.md) | Build system and targets |
| [Testing](testing.md) | Test strategy and execution |
| [Project Structure](project-structure.md) | Annotated codebase layout |

## Quick Start for Contributors

```bash
# Clone
git clone <repo-url> radix
cd radix

# Build
lake update
lake build

# Test
lake exe test
lake exe proptest

# Examples
lake exe examples
```

## See Also

- [Architecture](../architecture/) — System design
- [Design](../design/) — Design principles and decisions
- [日本語版](../../ja/development/) — Japanese version
