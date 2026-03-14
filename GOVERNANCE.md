# Governance

This document describes the governance model for the Radix project.

## Overview

Radix uses a **Benevolent Dictator** governance model appropriate for its current size and stage. As the community grows, governance will evolve toward a more distributed model.

## Roles

### Users

Anyone who uses Radix. Users are encouraged to participate by:

- Filing bug reports and feature requests
- Participating in Discussions
- Sharing their experience and use cases

### Contributors

Anyone who has had a pull request merged. Contributors can:

- Open pull requests
- Review code (non-binding)
- Participate in RFCs
- Be credited in the contributors list

### Maintainers

Listed in [MAINTAINERS.md](MAINTAINERS.md). Maintainers can:

- Merge pull requests
- Triage issues
- Manage releases
- Set project direction

### Lead Maintainer (Benevolent Dictator)

**[@Aqua-218](https://github.com/Aqua-218)** — has final decision authority on:

- Architecture and design decisions
- Release timing and content
- Maintainer appointments
- Conflict resolution

## Decision Making

### Standard Decisions

Most decisions are made through the pull request process:

1. Author opens a PR
2. Maintainer(s) review
3. Maintainer merges or requests changes

### Significant Decisions (RFC Process)

For changes that affect architecture, public API, or project direction:

1. Open a [Discussion](https://github.com/provenance-works/radix/discussions) with the `RFC` label
2. Community comment period (minimum 7 days)
3. Lead maintainer makes final decision, documenting rationale
4. Decision recorded as an [ADR](docs/en/design/adr.md)

### Conflict Resolution

1. Attempt to reach consensus in the PR or Discussion
2. If consensus cannot be reached, the lead maintainer makes the final call
3. Decisions can be revisited if significant new information emerges

## Code of Conduct

All participants must follow the [Code of Conduct](CODE_OF_CONDUCT.md). The lead maintainer is responsible for enforcement.

## Changes to Governance

This governance model may be updated as the project grows. Changes require:

1. A public proposal in Discussions
2. A 14-day comment period
3. Lead maintainer approval
