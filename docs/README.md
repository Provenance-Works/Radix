# Radix -- Documentation

Version: 0.1.0-draft
Last updated: 2026-03-07

## Overview

Radix is a formally verified low-level systems programming library for Lean4.
Lean4 lacks native support for many systems programming primitives.
Radix fills this gap by providing C-equivalent capabilities with Mathlib-grade formal proofs.

## Sections in Use

- requirements/ -- Requirements definition
- design/ -- Design and architecture
- research/ -- Research results on existing verified systems
- adr/ -- Architecture Decision Records

## Sections Not in Use

- api/ -- No REST API
- ui/ -- No GUI
- operations/ -- No deployment (library)
- cli/ -- No CLI (library)
- protocols/ -- Protocols are built ON this library, not in it
- syscalls/ -- Modeled in design/architecture.md (System module section)
- drivers/ -- Future scope

Note: design/components/ contains the detailed component designs (Word, System, Memory, Binary).
Until then, architecture.md is the authoritative design reference.

## How to Read

1. Start with requirements/functional.md for what Radix provides
2. Read design/architecture.md for the three-layer model
3. Check adr/ for key design decisions
4. See TODO.md for implementation plan
