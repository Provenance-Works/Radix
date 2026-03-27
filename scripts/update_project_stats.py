#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


ROOT = Path(__file__).resolve().parents[1]
STATS_PATH = ROOT / "scripts" / "project_stats.json"


@dataclass(frozen=True)
class ModuleStat:
    name: str
    description: str
    theorems: int


@dataclass(frozen=True)
class ProjectStats:
    modules: list[ModuleStat]
    leaf_modules: list[str]
    pure_modules: list[str]
    trusted_modules: list[str]
    example_count: int

    @property
    def theorem_total(self) -> int:
        return sum(module.theorems for module in self.modules)

    @property
    def theorem_label(self) -> str:
        return f"{self.theorem_total}+"

    @property
    def leaf_module_count(self) -> int:
        return len(self.leaf_modules)

    @property
    def pure_module_count(self) -> int:
        return len(self.pure_modules)

    @property
    def trusted_module_count(self) -> int:
        return len(self.trusted_modules)

    @property
    def runtime_model_count(self) -> int:
        return self.leaf_module_count - 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Update README/docs statistics from a single project stats manifest."
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit non-zero if tracked files are out of date instead of rewriting them.",
    )
    return parser.parse_args()


def load_module_imports(path: Path) -> list[str]:
    pattern = re.compile(r"^import\s+Radix\.([A-Za-z0-9_]+)$")
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = pattern.match(line.strip())
        if match:
            imports.append(match.group(1))
    return imports


def load_stats() -> ProjectStats:
    data = json.loads(STATS_PATH.read_text(encoding="utf-8"))
    modules = [ModuleStat(**entry) for entry in data["modules"]]

    leaf_modules = sorted(
        path.stem
        for path in (ROOT / "Radix").glob("*.lean")
        if path.name not in {"Pure.lean", "Trusted.lean"}
    )
    pure_modules = load_module_imports(ROOT / "Radix" / "Pure.lean")
    trusted_modules = load_module_imports(ROOT / "Radix" / "Trusted.lean")
    manifest_names = [module.name for module in modules]

    if sorted(manifest_names) != leaf_modules:
        missing = sorted(set(leaf_modules) - set(manifest_names))
        extra = sorted(set(manifest_names) - set(leaf_modules))
        problems: list[str] = []
        if missing:
            problems.append(f"missing manifest entries: {', '.join(missing)}")
        if extra:
            problems.append(f"unknown manifest entries: {', '.join(extra)}")
        raise SystemExit(f"project_stats.json is out of sync with Radix/*.lean: {'; '.join(problems)}")

    if sorted(pure_modules + trusted_modules + ["ProofAutomation"]) != leaf_modules:
        raise SystemExit(
            "Radix/Pure.lean and Radix/Trusted.lean no longer partition the leaf modules cleanly"
        )

    example_count = len(
        [path for path in (ROOT / "examples").glob("*.lean") if path.name != "Main.lean"]
    )

    return ProjectStats(
        modules=modules,
        leaf_modules=leaf_modules,
        pure_modules=pure_modules,
        trusted_modules=trusted_modules,
        example_count=example_count,
    )


def replace_once(
    text: str,
    pattern: str,
    repl: str | Callable[[re.Match[str]], str],
    file_path: Path,
    *,
    flags: int = 0,
) -> str:
    updated, count = re.subn(pattern, repl, text, count=1, flags=flags)
    if count != 1:
        raise SystemExit(f"Expected exactly one match for pattern in {file_path}: {pattern}")
    return updated


def render_module_table(stats: ProjectStats) -> str:
    lines = [
        "| Module | Description | Theorems |",
        "|--------|-------------|----------|",
    ]
    for module in stats.modules:
        lines.append(
            f"| **{module.name}** | {module.description} | {module.theorems} |"
        )
    return "\n".join(lines)


def update_readme(text: str, stats: ProjectStats, file_path: Path) -> str:
    text = replace_once(
        text,
        r"\[!\[Theorems\]\(https://img\.shields\.io/badge/theorems-\d+%2B-brightgreen\.svg\)\]\(#verification-status\)",
        f"[![Theorems](https://img.shields.io/badge/theorems-{stats.theorem_total}%2B-brightgreen.svg)](#verification-status)",
        file_path,
    )
    text = replace_once(
        text,
        r"\*\d+\+ verified theorems\. Zero `sorry`\. Proofs erase at runtime\.\*",
        f"*{stats.theorem_label} verified theorems. Zero `sorry`. Proofs erase at runtime.*",
        file_path,
    )
    text = replace_once(
        text,
        r"Radix exposes \d+ leaf modules plus grouped public import surfaces",
        f"Radix exposes {stats.leaf_module_count} leaf modules plus grouped public import surfaces",
        file_path,
    )
    text = replace_once(
        text,
        r"(?:Zero|One|Two|Three|Four|Five|Six|Seven|Eight|Nine|Ten|Eleven|Twelve|Thirteen|Fourteen|Fifteen|Sixteen|Seventeen|Eighteen|Nineteen|Twenty|\d+) leaf runtime and\s+model modules",
        f"{number_word(stats.runtime_model_count)} leaf runtime and model modules",
        file_path,
    )
    text = replace_once(
        text,
        r"Fourteen leaf modules stay entirely within Layers 2-3\.",
        f"{number_word(stats.pure_module_count)} leaf modules stay entirely within Layers 2-3.",
        file_path,
    )
    text = replace_once(
        text,
        r"import Radix\.Pure             -- \d+ pure Layer 2-3 modules",
        f"import Radix.Pure             -- {stats.pure_module_count} pure Layer 2-3 modules",
        file_path,
    )
    text = replace_once(
        text,
        r"\| Module \| Description \| Theorems \|\n\|[-| ]+\|\n(?:\|.*\n)+?(?=\n### Architecture)",
        render_module_table(stats) + "\n",
        file_path,
        flags=re.MULTILINE,
    )
    text = replace_once(
        text,
        r"\| Total theorems \| \d+\+ \|",
        f"| Total theorems | {stats.theorem_label} |",
        file_path,
    )
    text = replace_once(
        text,
        r"# Run unit tests \(all \d+ (?:leaf )?modules\)",
        f"# Run unit tests (all {stats.leaf_module_count} leaf modules)",
        file_path,
    )
    text = replace_once(
        text,
        r"See \[examples/\]\(examples/\) for \d+ complete, runnable examples covering the core and composable modules\.",
        f"See [examples/](examples/) for {stats.example_count} complete, runnable examples covering the core and composable modules.",
        file_path,
    )
    text = replace_once(
        text,
        r"- \*\*\[Examples\]\(examples/\)\*\* — \d+ runnable examples",
        f"- **[Examples](examples/)** — {stats.example_count} runnable examples",
        file_path,
    )
    text = replace_once(
        text,
        r'^- \*\*(?P<version>[^*]+)\*\* .*?"(?P<name>[^"]+)" — \d+\+ theorems, \d+ (?:leaf )?modules,',
        lambda match: (
            f'- **{match.group("version")}** (latest release) '
            f'"{match.group("name")}" — {stats.theorem_label} theorems, '
            f'{stats.leaf_module_count} leaf modules,'
        ),
        file_path,
        flags=re.MULTILINE,
    )
    return text


def update_roadmap(text: str, stats: ProjectStats, file_path: Path) -> str:
    text = replace_once(
        text,
        r"Radix now ships \d+ (?:top-level|leaf) modules,\n\d+\+ theorems,",
        f"Radix now ships {stats.leaf_module_count} leaf modules,\n{stats.theorem_label} theorems,",
        file_path,
    )
    return text


def update_vision(text: str, stats: ProjectStats, file_path: Path) -> str:
    text = replace_once(
        text,
        r"- All \d+\+ theorems remain `sorry`-free across Lean/Mathlib upgrades\.",
        f"- All {stats.theorem_label} theorems remain `sorry`-free across Lean/Mathlib upgrades.",
        file_path,
    )
    return text


def update_docs_en_readme(text: str, stats: ProjectStats, file_path: Path) -> str:
    return replace_once(
        text,
        r"Internal component breakdown \(\d+ (?:leaf )?modules\)",
        f"Internal component breakdown ({stats.leaf_module_count} leaf modules)",
        file_path,
    )


def update_docs_ja_readme(text: str, stats: ProjectStats, file_path: Path) -> str:
    return replace_once(
        text,
        r"内部コンポーネントの詳細（\d+(?: leaf modules|モジュール)）",
        f"内部コンポーネントの詳細（{stats.leaf_module_count} leaf modules）",
        file_path,
    )


def update_docs_en_testing(text: str, stats: ProjectStats, file_path: Path) -> str:
    replacements = [
        (
            r"Concrete input/output correctness for all \d+ leaf modules",
            f"Concrete input/output correctness for all {stats.leaf_module_count} leaf modules",
        ),
        (
            r"All \d+ leaf modules × concrete values",
            f"All {stats.leaf_module_count} leaf modules × concrete values",
        ),
        (
            r"Core walkthrough \+ \d+ runnable example modules",
            f"Core walkthrough + {stats.example_count} runnable example modules",
        ),
        (
            r"# Unit tests — all \d+ leaf modules",
            f"# Unit tests — all {stats.leaf_module_count} leaf modules",
        ),
        (
            r"Covers all \d+ leaf modules with concrete test values:",
            f"Covers all {stats.leaf_module_count} leaf modules with concrete test values:",
        ),
    ]
    for pattern, repl in replacements:
        text = replace_once(text, pattern, repl, file_path)
    return text


def update_docs_ja_testing(text: str, stats: ProjectStats, file_path: Path) -> str:
    replacements = [
        (
            r"全\d+ leaf modules の具体的な入出力の正しさ",
            f"全{stats.leaf_module_count} leaf modules の具体的な入出力の正しさ",
        ),
        (
            r"全\d+ leaf modules × 具体値",
            f"全{stats.leaf_module_count} leaf modules × 具体値",
        ),
        (
            r"コア説明 \+ \d+個の実行可能例",
            f"コア説明 + {stats.example_count}個の実行可能例",
        ),
        (
            r"# ユニットテスト — 全\d+ leaf modules",
            f"# ユニットテスト — 全{stats.leaf_module_count} leaf modules",
        ),
        (
            r"全\d+ leaf modules を具体的なテスト値でカバー：",
            f"全{stats.leaf_module_count} leaf modules を具体的なテスト値でカバー：",
        ),
    ]
    for pattern, repl in replacements:
        text = replace_once(text, pattern, repl, file_path)
    return text


def update_docs_en_project_structure(text: str, stats: ProjectStats, file_path: Path) -> str:
    replacements = [
        (
            r"full grouped surface over all \d+ leaf modules",
            f"full grouped surface over all {stats.leaf_module_count} leaf modules",
        ),
        (
            r"Source modules \(\d+ leaf modules \+ grouped import surfaces\)",
            f"Source modules ({stats.leaf_module_count} leaf modules + grouped import surfaces)",
        ),
        (
            r"Grouped import for the \d+ pure leaf modules",
            f"Grouped import for the {stats.pure_module_count} pure leaf modules",
        ),
        (
            r"Grouped import for the \d+ trusted-boundary leaf modules",
            f"Grouped import for the {stats.trusted_module_count} trusted-boundary leaf modules",
        ),
        (
            r"Execution tests \(all \d+ leaf modules\)",
            f"Execution tests (all {stats.leaf_module_count} leaf modules)",
        ),
        (
            r"\*\.lean                 # \d+ runnable example modules",
            f"*.lean                 # {stats.example_count} runnable example modules",
        ),
        (
            r"spanning all \d+ leaf modules",
            f"spanning all {stats.leaf_module_count} leaf modules",
        ),
        (
            r"All \d+ pure leaf modules that stay within Layers 2-3",
            f"All {stats.pure_module_count} pure leaf modules that stay within Layers 2-3",
        ),
        (
            r"The \d+ trusted-boundary leaf modules: `System`, `Concurrency`, `BareMetal`",
            f"The {stats.trusted_module_count} trusted-boundary leaf modules: `System`, `Concurrency`, `BareMetal`",
        ),
    ]
    for pattern, repl in replacements:
        text = replace_once(text, pattern, repl, file_path)
    return text


def update_docs_ja_project_structure(text: str, stats: ProjectStats, file_path: Path) -> str:
    replacements = [
        (
            r"全\d+ leaf modules を束ねる grouped surface",
            f"全{stats.leaf_module_count} leaf modules を束ねる grouped surface",
        ),
        (
            r"ソースモジュール（\d+ leaf modules \+ grouped import surfaces）",
            f"ソースモジュール（{stats.leaf_module_count} leaf modules + grouped import surfaces）",
        ),
        (
            r"\d+ 個の pure leaf modules を束ねる grouped import",
            f"{stats.pure_module_count} 個の pure leaf modules を束ねる grouped import",
        ),
        (
            r"\d+ 個の trusted-boundary leaf modules を束ねる grouped import",
            f"{stats.trusted_module_count} 個の trusted-boundary leaf modules を束ねる grouped import",
        ),
        (
            r"実行テスト（全\d+ leaf modules）",
            f"実行テスト（全{stats.leaf_module_count} leaf modules）",
        ),
        (
            r"\*\.lean                 # \d+ ?個の実行可能(?:使用)?例",
            f"*.lean                 # {stats.example_count}個の実行可能使用例",
        ),
        (
            r"\d+ leaf modules 全体を束ねる grouped public surface",
            f"{stats.leaf_module_count} leaf modules 全体を束ねる grouped public surface",
        ),
        (
            r"Layer 2-3 に留まる \d+ 個の pure leaf modules",
            f"Layer 2-3 に留まる {stats.pure_module_count} 個の pure leaf modules",
        ),
        (
            r"`System`、`Concurrency`、`BareMetal` の \d+ 個の trusted-boundary leaf modules",
            f"`System`、`Concurrency`、`BareMetal` の {stats.trusted_module_count} 個の trusted-boundary leaf modules",
        ),
    ]
    for pattern, repl in replacements:
        text = replace_once(text, pattern, repl, file_path)
    return text


def update_docs_en_components(text: str, stats: ProjectStats, file_path: Path) -> str:
    replacements = [
        (
            r"Radix exposes \d+ leaf modules plus grouped public import surfaces",
            f"Radix exposes {stats.leaf_module_count} leaf modules plus grouped public import surfaces",
        ),
        (
            r"(?:Zero|One|Two|Three|Four|Five|Six|Seven|Eight|Nine|Ten|Eleven|Twelve|Thirteen|Fourteen|Fifteen|Sixteen|Seventeen|Eighteen|Nineteen|Twenty|\d+) leaf runtime and\s+model modules",
            f"{number_word(stats.runtime_model_count)} leaf runtime and model modules",
        ),
        (
            r"\| `Radix\.Pure` \| \d+ pure leaf modules \| Layer 2-3 only surface \|",
            f"| `Radix.Pure` | {stats.pure_module_count} pure leaf modules | Layer 2-3 only surface |",
        ),
        (
            r"\| `Radix` \| All \d+ leaf modules \| Full public surface \|",
            f"| `Radix` | All {stats.leaf_module_count} leaf modules | Full public surface |",
        ),
    ]
    for pattern, repl in replacements:
        text = replace_once(text, pattern, repl, file_path)
    return text


def update_docs_ja_components(text: str, stats: ProjectStats, file_path: Path) -> str:
    replacements = [
        (
            r"Radix は \d+ 個の leaf modules と grouped public import surfaces",
            f"Radix は {stats.leaf_module_count} 個の leaf modules と grouped public import surfaces",
        ),
        (
            r"\d+ 個の leaf runtime/model modules",
            f"{stats.runtime_model_count} 個の leaf runtime/model modules",
        ),
        (
            r"\| `Radix\.Pure` \| \d+ 個の pure leaf modules \| Layer 2-3 のみの surface \|",
            f"| `Radix.Pure` | {stats.pure_module_count} 個の pure leaf modules | Layer 2-3 のみの surface |",
        ),
        (
            r"\| `Radix` \| 全\d+ leaf modules \| 完全な公開 surface \|",
            f"| `Radix` | 全{stats.leaf_module_count} leaf modules | 完全な公開 surface |",
        ),
    ]
    for pattern, repl in replacements:
        text = replace_once(text, pattern, repl, file_path)
    return text


def update_contributing(text: str, stats: ProjectStats, file_path: Path) -> str:
    replacements = [
        (
            r"Root import \(all \d+ (?:leaf )?modules\)",
            f"Root import (all {stats.leaf_module_count} leaf modules)",
        ),
        (
            r"examples/               # \d+ runnable usage examples",
            f"examples/               # {stats.example_count} runnable usage examples",
        ),
    ]
    for pattern, repl in replacements:
        text = replace_once(text, pattern, repl, file_path)
    return text


def number_word(value: int) -> str:
    words = {
        0: "Zero",
        1: "One",
        2: "Two",
        3: "Three",
        4: "Four",
        5: "Five",
        6: "Six",
        7: "Seven",
        8: "Eight",
        9: "Nine",
        10: "Ten",
        11: "Eleven",
        12: "Twelve",
        13: "Thirteen",
        14: "Fourteen",
        15: "Fifteen",
        16: "Sixteen",
        17: "Seventeen",
        18: "Eighteen",
        19: "Nineteen",
        20: "Twenty",
    }
    return words.get(value, str(value))


UPDATERS = {
    ROOT / "README.md": update_readme,
    ROOT / "ROADMAP.md": update_roadmap,
    ROOT / "VISION.md": update_vision,
    ROOT / "CONTRIBUTING.md": update_contributing,
    ROOT / "docs" / "en" / "README.md": update_docs_en_readme,
    ROOT / "docs" / "ja" / "README.md": update_docs_ja_readme,
    ROOT / "docs" / "en" / "architecture" / "components.md": update_docs_en_components,
    ROOT / "docs" / "en" / "development" / "project-structure.md": update_docs_en_project_structure,
    ROOT / "docs" / "en" / "development" / "testing.md": update_docs_en_testing,
    ROOT / "docs" / "ja" / "architecture" / "components.md": update_docs_ja_components,
    ROOT / "docs" / "ja" / "development" / "project-structure.md": update_docs_ja_project_structure,
    ROOT / "docs" / "ja" / "development" / "testing.md": update_docs_ja_testing,
}


def main() -> int:
    args = parse_args()
    stats = load_stats()
    changed_files: list[Path] = []
    rendered: dict[Path, tuple[str, str]] = {}

    for file_path, updater in UPDATERS.items():
        original = file_path.read_text(encoding="utf-8")
        updated = updater(original, stats, file_path)
        rendered[file_path] = (original, updated)
        if updated != original:
            changed_files.append(file_path)

    if args.check:
        if changed_files:
            print("Project stats are out of date in:")
            for file_path in changed_files:
                print(file_path.relative_to(ROOT))
            print("Run: python3 scripts/update_project_stats.py")
            return 1
        print("Project stats are up to date.")
        return 0

    for file_path in changed_files:
        _, updated = rendered[file_path]
        file_path.write_text(updated, encoding="utf-8")

    if changed_files:
        print("Updated project stats in:")
        for file_path in changed_files:
            print(file_path.relative_to(ROOT))
    else:
        print("Project stats already up to date.")
    return 0


if __name__ == "__main__":
    sys.exit(main())