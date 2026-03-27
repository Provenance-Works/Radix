#!/usr/bin/env python3

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import TypeVar


ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "tests" / "data" / "unicode" / "17.0.0"
UNICODE_DATA_PATH = DATA_DIR / "UnicodeData.txt"
OUTPUT_PATH = ROOT / "Radix" / "UTF8" / "UnicodeDataTables.lean"


BROAD_CATEGORY_NAMES = {
    "L": "letter",
    "M": "mark",
    "N": "number",
    "P": "punctuation",
    "S": "symbol",
    "Z": "separator",
}

EXACT_CATEGORY_NAMES = {
    "Lu": "uppercaseLetter",
    "Ll": "lowercaseLetter",
    "Lt": "titlecaseLetter",
    "Lm": "modifierLetter",
    "Lo": "otherLetter",
    "Mn": "nonspacingMark",
    "Mc": "spacingMark",
    "Me": "enclosingMark",
    "Nd": "decimalNumber",
    "Nl": "letterNumber",
    "No": "otherNumber",
    "Pc": "connectorPunctuation",
    "Pd": "dashPunctuation",
    "Ps": "openPunctuation",
    "Pe": "closePunctuation",
    "Pi": "initialPunctuation",
    "Pf": "finalPunctuation",
    "Po": "otherPunctuation",
    "Sm": "mathSymbol",
    "Sc": "currencySymbol",
    "Sk": "modifierSymbol",
    "So": "otherSymbol",
    "Zs": "spaceSeparator",
    "Zl": "lineSeparator",
    "Zp": "paragraphSeparator",
    "Cc": "control",
    "Cf": "format",
    "Cs": "surrogate",
    "Co": "privateUse",
    "Cn": "unassigned",
}


@dataclass(frozen=True)
class UnicodeDataTables:
    broad_ranges: dict[str, list[tuple[int, int]]]
    exact_ranges: dict[str, list[tuple[int, int]]]
    simple_lower_mappings: dict[int, int]
    simple_upper_mappings: dict[int, int]


def format_hex(value: int) -> str:
    return f"0x{value:X}"


def to_pascal_case(name: str) -> str:
    return f"{name[:1].upper()}{name[1:]}"


def coalesce_ranges(ranges: list[tuple[int, int]]) -> list[tuple[int, int]]:
    if not ranges:
        return []

    merged: list[tuple[int, int]] = []
    current_start, current_end = sorted(ranges)[0]
    for start, end in sorted(ranges)[1:]:
        if start <= current_end + 1:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    return merged


def parse_unicode_data(path: Path) -> UnicodeDataTables:
    broad_ranges: dict[str, list[tuple[int, int]]] = {
        name: [] for name in BROAD_CATEGORY_NAMES.values()
    }
    exact_ranges: dict[str, list[tuple[int, int]]] = {
        code: [] for code in EXACT_CATEGORY_NAMES
    }
    simple_lower_mappings: dict[int, int] = {}
    simple_upper_mappings: dict[int, int] = {}
    pending_range: tuple[int, str, str] | None = None

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        if not raw_line:
            continue

        fields = raw_line.split(";")
        if len(fields) < 14:
            raise ValueError(f"Invalid UnicodeData row: {raw_line}")

        code_point = int(fields[0], 16)
        name = fields[1]
        category = fields[2]
        broad_name = BROAD_CATEGORY_NAMES.get(category[:1])

        if name.endswith(", First>"):
            if pending_range is not None:
                raise ValueError(f"Nested UnicodeData range start: {raw_line}")
            if broad_name is None:
                pending_range = (code_point, "other", category)
            else:
                pending_range = (code_point, broad_name, category)
            continue

        if name.endswith(", Last>"):
            if pending_range is None:
                raise ValueError(f"UnicodeData range end without start: {raw_line}")
            start_code_point, start_broad_name, start_exact_category = pending_range
            pending_range = None
            if broad_name is None:
                broad_name = "other"
            if broad_name != start_broad_name:
                raise ValueError(
                    "UnicodeData range endpoints disagree on broad category: "
                    f"{start_broad_name!r} vs {broad_name!r}"
                )
            if category != start_exact_category:
                raise ValueError(
                    "UnicodeData range endpoints disagree on exact category: "
                    f"{start_exact_category!r} vs {category!r}"
                )
            if broad_name != "other":
                broad_ranges[broad_name].append((start_code_point, code_point))
            exact_ranges[category].append((start_code_point, code_point))
            continue

        if pending_range is not None:
            raise ValueError(f"UnicodeData range start not terminated before: {raw_line}")

        if broad_name is not None:
            broad_ranges[broad_name].append((code_point, code_point))
        exact_ranges[category].append((code_point, code_point))

        uppercase_field = fields[12].strip()
        lowercase_field = fields[13].strip()
        if uppercase_field:
            simple_upper_mappings[code_point] = int(uppercase_field, 16)
        if lowercase_field:
            simple_lower_mappings[code_point] = int(lowercase_field, 16)

    if pending_range is not None:
        raise ValueError("UnicodeData range start was never terminated")

    return UnicodeDataTables(
        broad_ranges={
            name: coalesce_ranges(ranges)
            for name, ranges in broad_ranges.items()
        },
        exact_ranges={
            name: coalesce_ranges(ranges)
            for name, ranges in exact_ranges.items()
        },
        simple_lower_mappings=simple_lower_mappings,
        simple_upper_mappings=simple_upper_mappings,
    )


def emit_range_list(lines: list[str], name: str, ranges: list[tuple[int, int]]) -> None:
    lines.append(f"def {name} : List CodepointRange :=")
    if not ranges:
        lines.append("  []")
        lines.append("")
        return

    lines.append("  [")
    for index, (start_value, end_value) in enumerate(ranges):
        suffix = "," if index + 1 < len(ranges) else ""
        lines.append(f"    ({format_hex(start_value)}, {format_hex(end_value)}){suffix}")
    lines.append("  ]")
    lines.append("")


T = TypeVar("T")


def chunk_entries(entries: list[T], chunk_size: int) -> list[list[T]]:
    return [entries[index : index + chunk_size] for index in range(0, len(entries), chunk_size)]


def emit_chunked_nat_lookup(
    lines: list[str],
    helper_base_name: str,
    public_name: str,
    entries: list[tuple[int, int]],
    chunk_size: int,
) -> None:
    chunk_names: list[str] = []
    for index, chunk in enumerate(chunk_entries(entries, chunk_size), start=1):
        chunk_name = f"{helper_base_name}Chunk{index}"
        chunk_names.append(chunk_name)
        lines.append(f"private def {chunk_name} (value : Nat) : Option Nat :=")
        lines.append("  match value with")
        for code_point, mapped_value in chunk:
            lines.append(f"  | {format_hex(code_point)} => some {format_hex(mapped_value)}")
        lines.append("  | _ => none")
        lines.append("")

    lines.append(f"def {public_name} (value : Nat) : Option Nat :=")
    for index, chunk_name in enumerate(chunk_names):
        indent = "  " * (index + 1)
        lines.append(f"{indent}match {chunk_name} value with")
        lines.append(f"{indent}| some mapped => some mapped")
        lines.append(f"{indent}| none =>")
    lines.append(f"{'  ' * (len(chunk_names) + 1)}none")
    lines.append("")


def render_module(data: UnicodeDataTables) -> str:
    lines: list[str] = [
        "/-",
        "Copyright (c) 2026 Radix Contributors. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "-/",
        "",
        "/-!",
        "# Unicode 17 Core Data Tables",
        "",
        "Generated tables derived from the official Unicode 17 UnicodeData.txt data.",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "namespace Radix.UTF8.UnicodeDataTables",
        "",
        "abbrev CodepointRange := Nat × Nat",
        "",
        "private def inCodepointRanges (value : Nat) : List CodepointRange → Bool",
        "  | [] => false",
        "  | (startValue, endValue) :: rest =>",
        "    (startValue ≤ value && value ≤ endValue) || inCodepointRanges value rest",
        "",
    ]

    for broad_name in ("letter", "mark", "number", "punctuation", "symbol", "separator"):
        emit_range_list(lines, f"{broad_name}Ranges", data.broad_ranges[broad_name])
        lines.append(f"def is{broad_name[:1].upper() + broad_name[1:]} (value : Nat) : Bool :=")
        lines.append(f"  inCodepointRanges value {broad_name}Ranges")
        lines.append("")

    for category_code, category_name in EXACT_CATEGORY_NAMES.items():
        range_name = f"{category_name}Ranges"
        predicate_name = f"is{to_pascal_case(category_name)}"
        emit_range_list(lines, range_name, data.exact_ranges[category_code])
        lines.append(f"def {predicate_name} (value : Nat) : Bool :=")
        lines.append(f"  inCodepointRanges value {range_name}")
        lines.append("")

    lines.append("def isUppercase (value : Nat) : Bool :=")
    lines.append("  isUppercaseLetter value")
    lines.append("")

    lines.append("def isLowercase (value : Nat) : Bool :=")
    lines.append("  isLowercaseLetter value")
    lines.append("")

    lines.append("def isDecimalDigit (value : Nat) : Bool :=")
    lines.append("  isDecimalNumber value")
    lines.append("")

    emit_chunked_nat_lookup(
        lines,
        "simpleLowerNat",
        "simpleLowerNat?",
        sorted(data.simple_lower_mappings.items()),
        32,
    )
    emit_chunked_nat_lookup(
        lines,
        "simpleUpperNat",
        "simpleUpperNat?",
        sorted(data.simple_upper_mappings.items()),
        32,
    )

    lines.append("end Radix.UTF8.UnicodeDataTables")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    data = parse_unicode_data(UNICODE_DATA_PATH)
    OUTPUT_PATH.write_text(render_module(data), encoding="utf-8")


if __name__ == "__main__":
    main()