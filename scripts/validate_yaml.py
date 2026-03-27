#!/usr/bin/env python3

from __future__ import annotations

import sys
from pathlib import Path

import yaml
from yaml.nodes import MappingNode, ScalarNode, SequenceNode


class PermissiveLoader(yaml.SafeLoader):
    pass


def construct_tagged_node(loader: PermissiveLoader, tag_suffix: str, node: yaml.Node):
    del tag_suffix
    if isinstance(node, ScalarNode):
        return loader.construct_scalar(node)
    if isinstance(node, SequenceNode):
        return loader.construct_sequence(node)
    if isinstance(node, MappingNode):
        return loader.construct_mapping(node)
    raise TypeError(f"Unsupported YAML node: {type(node)!r}")


PermissiveLoader.add_multi_constructor("!", construct_tagged_node)


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("usage: validate_yaml.py <path> [<path> ...]", file=sys.stderr)
        return 2

    failures = 0
    for raw_path in argv[1:]:
        path = Path(raw_path)
        try:
            yaml.load(path.read_text(encoding="utf-8"), Loader=PermissiveLoader)
            print(f"OK: {path}")
        except Exception as exc:
            print(f"ERROR: {path}: {exc}", file=sys.stderr)
            failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))