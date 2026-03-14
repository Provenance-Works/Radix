# Security Policy

## Supported Versions

| Version | Supported          |
|---------|--------------------|
| 0.1.x   | :white_check_mark: |

## Reporting a Vulnerability

**Please do NOT open a public issue for security vulnerabilities.**

If you discover a security vulnerability in Radix, please report it responsibly using one of the following methods:

### Preferred: GitHub Private Vulnerability Reporting

1. Go to the [Security Advisories](https://github.com/provenance-works/radix/security/advisories/new) page
2. Click "Report a vulnerability"
3. Provide a detailed description of the vulnerability

### What to Include

- Description of the vulnerability
- Steps to reproduce
- Potential impact assessment
- Suggested fix (if any)

### Response Timeline

- **Acknowledgment**: Within 48 hours
- **Initial assessment**: Within 7 days
- **Fix timeline**: Depends on severity, but we aim for:
  - Critical: 72 hours
  - High: 2 weeks
  - Medium/Low: Next release

### Disclosure Policy

We follow coordinated disclosure:

1. Reporter notifies us privately
2. We confirm and assess the vulnerability
3. We develop and test a fix
4. We release the fix and publish a security advisory
5. Reporter is credited (unless they prefer anonymity)

We ask that you give us reasonable time to address the issue before any public disclosure.

## Security Considerations

### Trusted Computing Base (TCB)

Radix's security model relies on a minimal trusted computing base:

- **Lean 4 kernel** — Type-checks all proofs
- **Mathlib** — Provides mathematical foundations (formally verified)
- **Named trust assumptions** — All axioms about external-world behavior (POSIX, hardware) use the `trust_*` prefix and are explicitly documented

### What Radix Does NOT Guarantee

- **Timing side-channels** — Radix does not claim constant-time execution. If you're building cryptographic code on top of Radix, you must handle timing independently.
- **Hardware correctness** — `trust_*` axioms assume hardware behaves as documented. Hardware bugs (e.g., CPU errata) are outside our scope.
- **Lean compiler correctness** — Proofs are verified by Lean's kernel, but the compiled executable depends on the Lean compiler's correctness.

### Dependency Security

- Radix depends on **Mathlib** (Apache 2.0, formally verified)
- We track Mathlib updates and verify compatibility with each release
- No network access, no file system access beyond what the user explicitly invokes via the System module
