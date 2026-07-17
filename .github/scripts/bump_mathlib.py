#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
VERSION_PATTERN = re.compile(r"^v(\d+)\.(\d+)\.(\d+)$")


def replace_once(path: Path, pattern: str, replacement: str) -> None:
    source = path.read_text()
    updated, count = re.subn(pattern, replacement, source, count=1, flags=re.MULTILINE)
    if count != 1:
        raise RuntimeError(f"expected exactly one match in {path}")
    path.write_text(updated)


def bump_package_patch() -> str:
    lakefile = ROOT / "lakefile.toml"
    source = lakefile.read_text()
    match = re.search(r'^version = "(\d+)\.(\d+)\.(\d+)"$', source, re.MULTILINE)
    if match is None:
        raise RuntimeError("package version is missing from lakefile.toml")
    major, minor, patch = (int(part) for part in match.groups())
    next_version = f"{major}.{minor}.{patch + 1}"
    replace_once(lakefile, r'^version = "[^"]+"$', f'version = "{next_version}"')
    return next_version


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("tag")
    args = parser.parse_args()
    if VERSION_PATTERN.fullmatch(args.tag) is None:
        raise SystemExit(f"invalid stable release tag: {args.tag}")

    next_version = bump_package_patch()
    replace_once(
        ROOT / "lakefile.toml",
        r'^(name = "mathlib"\nscope = "leanprover-community"\nrev = ")[^"]+(")$',
        rf"\g<1>{args.tag}\g<2>",
    )
    replace_once(
        ROOT / "blueprint-verso" / "lakefile.lean",
        r'^(require VersoBlueprint from git "[^"]+" @ ")[^"]+(")$',
        rf"\g<1>{args.tag}\g<2>",
    )
    toolchain = f"leanprover/lean4:{args.tag}\n"
    (ROOT / "lean-toolchain").write_text(toolchain)
    (ROOT / "blueprint-verso" / "lean-toolchain").write_text(toolchain)
    print(next_version)


if __name__ == "__main__":
    main()
