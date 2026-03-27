#!/usr/bin/env python3

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import TypeVar


ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "tests" / "data" / "unicode" / "17.0.0"
UNICODE_DATA_PATH = DATA_DIR / "UnicodeData.txt"
COMPOSITION_EXCLUSIONS_PATH = DATA_DIR / "CompositionExclusions.txt"
OUTPUT_PATH = ROOT / "Radix" / "UTF8" / "NormalizationTables.lean"


@dataclass(frozen=True)
class NormalizationData:
    canonical_combining_classes: dict[int, int]
    canonical_decompositions: dict[int, list[int]]
    compatibility_decompositions: dict[int, list[int]]
    canonical_compositions: dict[tuple[int, int], int]
    max_canonical_depth: int
    max_compatibility_depth: int


def parse_unicode_data(path: Path) -> tuple[dict[int, int], dict[int, list[int]], dict[int, list[int]]]:
    canonical_combining_classes: dict[int, int] = {}
    canonical_decompositions: dict[int, list[int]] = {}
    compatibility_decompositions: dict[int, list[int]] = {}

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        if not raw_line:
            continue

        fields = raw_line.split(";")
        if len(fields) < 6:
            raise ValueError(f"Invalid UnicodeData row: {raw_line}")

        code_point = int(fields[0], 16)
        combining_class = int(fields[3])
        if combining_class != 0:
            canonical_combining_classes[code_point] = combining_class

        decomposition = fields[5].strip()
        if not decomposition:
            continue

        tokens = decomposition.split()
        if tokens[0].startswith("<"):
            compatibility_decompositions[code_point] = [int(token, 16) for token in tokens[1:]]
        else:
            canonical_decompositions[code_point] = [int(token, 16) for token in tokens]

    return canonical_combining_classes, canonical_decompositions, compatibility_decompositions


def parse_explicit_composition_exclusions(path: Path) -> set[int]:
    exclusions: set[int] = set()
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        exclusions.add(int(line, 16))
    return exclusions


def derive_full_composition_exclusions(
    canonical_combining_classes: dict[int, int],
    canonical_decompositions: dict[int, list[int]],
    explicit_exclusions: set[int],
) -> set[int]:
    exclusions = set(explicit_exclusions)
    for source, mapping in canonical_decompositions.items():
        if len(mapping) == 1:
            exclusions.add(source)
            continue

        if len(mapping) > 1:
            source_ccc = canonical_combining_classes.get(source, 0)
            first_ccc = canonical_combining_classes.get(mapping[0], 0)
            if source_ccc != 0 or first_ccc != 0:
                exclusions.add(source)

    return exclusions


def derive_canonical_compositions(
    canonical_decompositions: dict[int, list[int]],
    full_exclusions: set[int],
) -> dict[tuple[int, int], int]:
    compositions: dict[tuple[int, int], int] = {}

    for source, mapping in canonical_decompositions.items():
        if source in full_exclusions or len(mapping) != 2:
            continue

        pair = (mapping[0], mapping[1])
        existing = compositions.get(pair)
        if existing is not None and existing != source:
            raise ValueError(
                f"Duplicate canonical composition pair {pair!r}: {existing:#x} vs {source:#x}"
            )
        compositions[pair] = source

    return compositions


def compute_max_depths(
    canonical_decompositions: dict[int, list[int]],
    compatibility_decompositions: dict[int, list[int]],
) -> tuple[int, int]:
    @lru_cache(maxsize=None)
    def canonical_depth(code_point: int) -> int:
        mapping = canonical_decompositions.get(code_point)
        if mapping is None:
            return 0
        return 1 + max((canonical_depth(value) for value in mapping), default=0)

    @lru_cache(maxsize=None)
    def compatibility_depth(code_point: int) -> int:
        compatibility_mapping = compatibility_decompositions.get(code_point)
        if compatibility_mapping is not None:
            return 1 + max((compatibility_depth(value) for value in compatibility_mapping), default=0)

        canonical_mapping = canonical_decompositions.get(code_point)
        if canonical_mapping is not None:
            return 1 + max((compatibility_depth(value) for value in canonical_mapping), default=0)

        return 0

    max_canonical_depth = max((canonical_depth(code_point) for code_point in canonical_decompositions), default=0)
    all_codes = set(canonical_decompositions) | set(compatibility_decompositions)
    max_compatibility_depth = max((compatibility_depth(code_point) for code_point in all_codes), default=0)
    return max_canonical_depth, max_compatibility_depth


def collect_normalization_data() -> NormalizationData:
    canonical_combining_classes, canonical_decompositions, compatibility_decompositions = parse_unicode_data(
        UNICODE_DATA_PATH
    )
    explicit_exclusions = parse_explicit_composition_exclusions(COMPOSITION_EXCLUSIONS_PATH)
    full_exclusions = derive_full_composition_exclusions(
        canonical_combining_classes,
        canonical_decompositions,
        explicit_exclusions,
    )
    canonical_compositions = derive_canonical_compositions(canonical_decompositions, full_exclusions)
    max_canonical_depth, max_compatibility_depth = compute_max_depths(
        canonical_decompositions,
        compatibility_decompositions,
    )

    return NormalizationData(
        canonical_combining_classes=canonical_combining_classes,
        canonical_decompositions=canonical_decompositions,
        compatibility_decompositions=compatibility_decompositions,
        canonical_compositions=canonical_compositions,
        max_canonical_depth=max_canonical_depth,
        max_compatibility_depth=max_compatibility_depth,
    )


def format_hex(value: int) -> str:
    return f"0x{value:X}"


def format_nat_list(values: list[int]) -> str:
    return "[" + ", ".join(format_hex(value) for value in values) + "]"


def emit_match_function(
    lines: list[str],
    signature: str,
    cases: list[str],
    default_case: str,
) -> None:
    lines.append(signature)
    lines.append("  match value with")
    lines.extend(cases)
    lines.append(f"  | _ => {default_case}")
    lines.append("")


T = TypeVar("T")


def chunk_entries(entries: list[T], chunk_size: int) -> list[list[T]]:
    return [entries[index : index + chunk_size] for index in range(0, len(entries), chunk_size)]


def emit_chunked_unary_lookup(
    lines: list[str],
    base_name: str,
    return_type: str,
    entries: list[tuple[int, list[int]]],
    chunk_size: int,
) -> None:
    chunk_names: list[str] = []
    for index, chunk in enumerate(chunk_entries(entries, chunk_size), start=1):
        chunk_name = f"{base_name}Chunk{index}"
        chunk_names.append(chunk_name)
        lines.append(f"private def {chunk_name} (value : Nat) : Option (List Nat) :=")
        lines.append("  match value with")
        for code_point, mapping in chunk:
            lines.append(f"  | {format_hex(code_point)} => some {format_nat_list(mapping)}")
        lines.append("  | _ => none")
        lines.append("")

    lines.append(f"def {base_name} (value : Nat) : {return_type} :=")
    for index, chunk_name in enumerate(chunk_names):
        indent = "  " * (index + 1)
        lines.append(f"{indent}match {chunk_name} value with")
        lines.append(f"{indent}| some mapping => some mapping")
        lines.append(f"{indent}| none =>")
    lines.append(f"{'  ' * (len(chunk_names) + 1)}none")
    lines.append("")


def emit_chunked_nat_lookup(
    lines: list[str],
    base_name: str,
    entries: list[tuple[int, int]],
    chunk_size: int,
) -> None:
    chunk_names: list[str] = []
    for index, chunk in enumerate(chunk_entries(entries, chunk_size), start=1):
        chunk_name = f"{base_name}Chunk{index}"
        chunk_names.append(chunk_name)
        lines.append(f"private def {chunk_name} (value : Nat) : Nat :=")
        lines.append("  match value with")
        for code_point, result in chunk:
            lines.append(f"  | {format_hex(code_point)} => {result}")
        lines.append("  | _ => 0")
        lines.append("")

    lines.append(f"def {base_name} (value : Nat) : Nat :=")
    for index, chunk_name in enumerate(chunk_names):
        indent = "  " * (index + 1)
        lines.append(f"{indent}let candidate := {chunk_name} value")
        lines.append(f"{indent}if candidate != 0 then")
        lines.append(f"{indent}  candidate")
        lines.append(f"{indent}else")
    lines.append(f"{'  ' * (len(chunk_names) + 1)}0")
    lines.append("")


def emit_chunked_binary_lookup(
    lines: list[str],
    base_name: str,
    entries: list[tuple[tuple[int, int], int]],
    chunk_size: int,
) -> None:
    chunk_names: list[str] = []
    for index, chunk in enumerate(chunk_entries(entries, chunk_size), start=1):
        chunk_name = f"{base_name}Chunk{index}"
        chunk_names.append(chunk_name)
        lines.append(f"private def {chunk_name} (starter mark : Nat) : Option Nat :=")
        lines.append("  match starter, mark with")
        for (starter, mark), composed in chunk:
            lines.append(f"  | {format_hex(starter)}, {format_hex(mark)} => some {format_hex(composed)}")
        lines.append("  | _, _ => none")
        lines.append("")

    lines.append(f"def {base_name} (starter mark : Nat) : Option Nat :=")
    for index, chunk_name in enumerate(chunk_names):
        indent = "  " * (index + 1)
        lines.append(f"{indent}match {chunk_name} starter mark with")
        lines.append(f"{indent}| some composed => some composed")
        lines.append(f"{indent}| none =>")
    lines.append(f"{'  ' * (len(chunk_names) + 1)}none")
    lines.append("")


def render_module(data: NormalizationData) -> str:
    lines: list[str] = [
        "/-",
        "Copyright (c) 2026 Radix Contributors. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "-/",
        "",
        "/-!",
        "# Unicode 17 Normalization Tables",
        "",
        "Generated tables derived from the official Unicode 17 UnicodeData.txt and",
        "CompositionExclusions.txt data.",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "namespace Radix.UTF8.NormalizationTables",
        "",
        f"def maxCanonicalDecompositionDepth : Nat := {data.max_canonical_depth}",
        f"def maxCompatibilityDecompositionDepth : Nat := {data.max_compatibility_depth}",
        "",
    ]

    emit_chunked_nat_lookup(
        lines,
        "canonicalCombiningClass",
        sorted(data.canonical_combining_classes.items()),
        32,
    )

    emit_chunked_unary_lookup(
        lines,
        "canonicalDecomposition?",
        "Option (List Nat)",
        sorted(data.canonical_decompositions.items()),
        32,
    )
    emit_chunked_unary_lookup(
        lines,
        "compatibilityDecomposition?",
        "Option (List Nat)",
        sorted(data.compatibility_decompositions.items()),
        32,
    )
    emit_chunked_binary_lookup(
        lines,
        "canonicalComposition?",
        sorted(data.canonical_compositions.items()),
        32,
    )
    lines.append("end Radix.UTF8.NormalizationTables")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    data = collect_normalization_data()
    OUTPUT_PATH.write_text(render_module(data), encoding="utf-8")


if __name__ == "__main__":
    main()