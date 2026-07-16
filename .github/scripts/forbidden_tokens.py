#!/usr/bin/env python3
"""Reject forbidden Lean commands while ignoring comments and string literals."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCES = [ROOT / "ProbabilityApproximation.lean", ROOT / "ProbabilityApproximation"]
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b")


def code_only(text: str) -> str:
    """Replace comments and strings with spaces while preserving newlines."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while index < len(text):
        current = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""
        if in_line_comment:
            if current == "\n":
                in_line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
            continue
        if block_depth:
            if current == "/" and following == "-":
                block_depth += 1
                result.extend((" ", " "))
                index += 2
            elif current == "-" and following == "/":
                block_depth -= 1
                result.extend((" ", " "))
                index += 2
            else:
                result.append("\n" if current == "\n" else " ")
                index += 1
            continue
        if in_string:
            if escaped:
                escaped = False
                result.append(" ")
            elif current == "\\":
                escaped = True
                result.append(" ")
            elif current == '"':
                in_string = False
                result.append(" ")
            else:
                result.append("\n" if current == "\n" else " ")
            index += 1
            continue
        if current == "-" and following == "-":
            in_line_comment = True
            result.extend((" ", " "))
            index += 2
        elif current == "/" and following == "-":
            block_depth = 1
            result.extend((" ", " "))
            index += 2
        elif current == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(current)
            index += 1
    return "".join(result)


def lean_sources() -> list[Path]:
    files = [SOURCES[0]]
    files.extend(sorted(SOURCES[1].rglob("*.lean")))
    return files


def main() -> None:
    offenders: list[str] = []
    for path in lean_sources():
        stripped = code_only(path.read_text())
        for line_number, line in enumerate(stripped.splitlines(), start=1):
            for match in FORBIDDEN.finditer(line):
                offenders.append(
                    f"{path.relative_to(ROOT)}:{line_number}: forbidden token {match.group(0)}"
                )
    if offenders:
        print("\n".join(offenders), file=sys.stderr)
        raise SystemExit(1)
    print(f"forbidden token audit ok: {len(lean_sources())} production files")


if __name__ == "__main__":
    main()
