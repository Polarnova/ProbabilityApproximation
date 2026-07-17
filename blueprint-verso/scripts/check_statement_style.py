#!/usr/bin/env python3
"""Validate curated ProbabilityApproximation Blueprint statements and citations."""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCES = (
    ROOT / "ProbabilityApproximationBlueprint" / "NonuniformBerryEsseen.lean",
    ROOT / "ProbabilityApproximationBlueprint" / "ConvexSetApproximation.lean",
)
EXPECTED_USES = {
    "indicator-stein-solution": (),
    "nonuniform-stein-derivative-bounds": ("indicator-stein-solution",),
    "uniform-leave-one-out-concentration": (),
    "uniform-third-moment-berry-esseen": (
        "indicator-stein-solution", "uniform-leave-one-out-concentration"),
    "bennett-hoeffding-mgf": (),
    "exponential-leave-one-out-concentration": ("bennett-hoeffding-mgf",),
    "one-sided-truncation-comparison": (),
    "upper-truncated-stein-exchange": (
        "indicator-stein-solution", "one-sided-truncation-comparison"),
    "upper-truncated-residual-decomposition": (
        "nonuniform-stein-derivative-bounds", "upper-truncated-stein-exchange"),
    "upper-truncated-r1-r3-bounds": (
        "bennett-hoeffding-mgf", "upper-truncated-residual-decomposition"),
    "upper-truncated-r2-expected-kernel": ("upper-truncated-residual-decomposition",),
    "upper-truncated-indicator-residual": (
        "exponential-leave-one-out-concentration", "upper-truncated-r2-expected-kernel"),
    "stein-product-increment": (
        "nonuniform-stein-derivative-bounds", "bennett-hoeffding-mgf"),
    "upper-truncated-product-residual": (
        "upper-truncated-r2-expected-kernel", "stein-product-increment"),
    "upper-truncated-central-decay": (
        "upper-truncated-r1-r3-bounds", "upper-truncated-indicator-residual",
        "upper-truncated-product-residual"),
    "scalar-release-reduction": (
        "uniform-third-moment-berry-esseen", "one-sided-truncation-comparison",
        "upper-truncated-central-decay"),
    "convex-parallel-sets": (),
    "metric-projection": (),
    "squared-distance-calculus": ("metric-projection",),
    "bentkus-smooth-cutoff": ("squared-distance-calculus",),
    "gaussian-companions-and-transport": (),
    "gaussian-fourth-moment-control": (),
    "gaussian-companion-second-moment-match": (
        "gaussian-companions-and-transport",),
    "gaussian-companion-third-moment-comparison": (
        "gaussian-fourth-moment-control", "gaussian-companion-second-moment-match"),
    "gaussian-companion-mixed-moment": (
        "gaussian-companions-and-transport", "gaussian-companion-second-moment-match"),
    "bentkus-rotation-cancellation": ("gaussian-companions-and-transport",),
    "bentkus-rotation-fubini": (
        "gaussian-companions-and-transport", "bentkus-rotation-cancellation",
        "covariance-additivity-and-leave-one-out", "bentkus-smoothing-inequality"),
    "covariance-additivity-and-leave-one-out": ("gaussian-companions-and-transport",),
    "bentkus-whitening-covariance-identity": (),
    "bentkus-whitening-gaussian-pushforward": (
        "bentkus-whitening-covariance-identity",),
    "bentkus-identity-covariance-contract": (
        "bentkus-whitening-covariance-identity",),
    "bentkus-whitening-one-set-transport": (
        "bentkus-whitening-gaussian-pushforward",
        "bentkus-identity-covariance-contract"),
    "gaussian-signed-distance-eikonal": ("squared-distance-calculus",),
    "gaussian-signed-distance-level-frontiers": (
        "gaussian-signed-distance-eikonal", "convex-parallel-sets"),
    "gaussian-shell-signed-distance-slabs": (
        "gaussian-signed-distance-eikonal", "convex-parallel-sets"),
    "gaussian-affine-codimension-one-slicing": (),
    "lipschitz-area-formula": (),
    "scalar-coarea-formula": ("lipschitz-area-formula",),
    "gaussian-signed-distance-coarea-profiles": (
        "gaussian-signed-distance-level-frontiers",
        "gaussian-shell-signed-distance-slabs",
        "scalar-coarea-formula"),
    "intrinsic-sphere-hausdorff-normalization": ("scalar-coarea-formula",),
    "ball-projection-jacobian-charts": ("lipschitz-area-formula",),
    "ball-cauchy-projection-formula": (
        "intrinsic-sphere-hausdorff-normalization",
        "ball-projection-jacobian-charts"),
    "ball-spherical-projection-average": (),
    "ball-spherical-rearrangement": ("ball-spherical-projection-average",),
    "ball-radial-gamma-peak": (),
    "ball-radial-majorant": ("ball-radial-gamma-peak",),
    "ball-spherical-density-majorization": (
        "intrinsic-sphere-hausdorff-normalization",
        "ball-cauchy-projection-formula",
        "ball-spherical-rearrangement",
        "ball-radial-majorant"),
    "ball-boundary-projection-area": (
        "ball-projection-jacobian-charts", "ball-radial-majorant"),
    "ball-gaussian-perimeter": (
        "gaussian-affine-codimension-one-slicing",
        "ball-spherical-density-majorization",
        "ball-boundary-projection-area"),
    "gaussian-convex-shell": (
        "gaussian-signed-distance-coarea-profiles",
        "ball-gaussian-perimeter"),
    "bentkus-smoothing-inequality": ("bentkus-smooth-cutoff",),
    "density-derivative-integral-bound": (),
    "gaussian-density-third-derivative": (),
    "gaussian-density-ibp": (
        "density-derivative-integral-bound", "gaussian-density-third-derivative"),
    "cutoff-derivative-shell-ibp": (
        "bentkus-smoothing-inequality", "gaussian-density-ibp"),
    "bentkus-taylor-remainders": (),
    "gaussian-density-second-order-remainder": (
        "gaussian-density-third-derivative",),
    "bentkus-angle-integrals": (),
    "bentkus-coordinate-piece-assembly": ("bentkus-angle-integrals",),
    "bentkus-parameter-closure": (),
    "bentkus-trivial-induction-branches": (
        "covariance-additivity-and-leave-one-out",),
    "bentkus-leave-one-out-whitening": (
        "covariance-additivity-and-leave-one-out",
        "bentkus-whitening-covariance-identity"),
    "bentkus-standardized-induction": (
        "gaussian-convex-shell", "bentkus-smoothing-inequality",
        "density-derivative-integral-bound",
        "gaussian-density-ibp", "cutoff-derivative-shell-ibp",
        "bentkus-taylor-remainders", "gaussian-density-second-order-remainder",
        "bentkus-angle-integrals", "bentkus-rotation-fubini",
        "bentkus-coordinate-piece-assembly",
        "bentkus-parameter-closure",
        "bentkus-rotation-cancellation", "covariance-additivity-and-leave-one-out",
        "gaussian-companion-third-moment-comparison",
        "gaussian-companion-mixed-moment", "bentkus-trivial-induction-branches",
        "bentkus-leave-one-out-whitening", "bentkus-identity-covariance-contract"),
    "nonuniform-berry-esseen": ("scalar-release-reduction",),
    "bentkus-convex-set": (
        "bentkus-standardized-induction", "bentkus-whitening-one-set-transport"),
}
EXPECTED_OPEN: set[str] = set()
START = re.compile(
    r'^:::(definition|theorem|proposition|corollary|lemma_)\s+"([^"]+)"(.*)$'
)
LABEL = re.compile(r"^\*[^*]+\.\*(?:\s|$)")
MARKDOWN_LINK = re.compile(r"\[[^]]+\]\([^)]+\)")
IMPLEMENTATION_TERMS = re.compile(
    r"\b(?:Lean|Mathlib|repository|library|declaration|implementation|implemented|"
    r"formalized|compiled|source-open|kernel-checked)\b",
    re.IGNORECASE,
)
CITATION = re.compile(r"\{Citations\.cite[pt]\s+[^}]+\}\[\]")
PAGES = re.compile(r"\bprinted\s+pp?\.", re.IGNORECASE)
LOCATOR = re.compile(
    r"\b(?:Section|Theorem|Lemma|Proposition|equation|equations|condition)\b",
    re.IGNORECASE,
)
USES = re.compile(r'\(uses := "([^"]+)"\)')


@dataclass(frozen=True)
class StatementBlock:
    source: Path
    line: int
    identifier: str
    header: str
    body: str
    citation: str


def statement_blocks(source: Path) -> list[StatementBlock]:
    """Parse statement directives and the source paragraph immediately following each one."""
    lines = source.read_text().splitlines()
    blocks: list[StatementBlock] = []
    index = 0
    while index < len(lines):
        match = START.match(lines[index])
        if match is None:
            index += 1
            continue
        start = index
        header = lines[index]
        index += 1
        body: list[str] = []
        while index < len(lines) and lines[index].strip() != ":::":
            body.append(lines[index])
            index += 1
        if index == len(lines):
            raise ValueError(f"unterminated statement: {source}:{start + 1}")
        index += 1
        citation: list[str] = []
        while index < len(lines) and START.match(lines[index]) is None:
            citation.append(lines[index])
            index += 1
        blocks.append(StatementBlock(
            source=source,
            line=start + 1,
            identifier=match.group(2),
            header=header,
            body="\n".join(body).strip(),
            citation="\n".join(citation).strip(),
        ))
    return blocks


def parsed_uses(header: str) -> tuple[str, ...]:
    match = USES.search(header)
    if match is None:
        return ()
    return tuple(part.strip() for part in match.group(1).split(","))


def main() -> None:
    blocks = [block for source in SOURCES for block in statement_blocks(source)]
    errors: list[str] = []
    labels = [block.identifier for block in blocks]
    if len(labels) != len(set(labels)):
        errors.append("duplicate statement labels")
    if set(labels) != set(EXPECTED_USES):
        errors.append(
            "unexpected statement labels: "
            + ", ".join(sorted(set(labels).symmetric_difference(EXPECTED_USES)))
        )

    for block in blocks:
        location = f"{block.source.relative_to(ROOT)}:{block.line}"
        first_line = next(
            (line.strip() for line in block.body.splitlines() if line.strip()), ""
        )
        if LABEL.match(first_line) is None:
            errors.append(f"{location}: {block.identifier} lacks an italicized mathematical label")
        if "$" + chr(96) not in block.body:
            errors.append(f"{location}: {block.identifier} contains no mathematical notation")
        if MARKDOWN_LINK.search(block.body):
            errors.append(f"{location}: {block.identifier} contains a link inside the statement")
        term = IMPLEMENTATION_TERMS.search(block.body)
        if term is not None:
            errors.append(
                f"{location}: {block.identifier} contains implementation term {term.group(0)!r}"
            )
        if "fidelity-" not in block.header:
            errors.append(f"{location}: {block.identifier} lacks fidelity metadata")
        if "source-" not in block.header:
            errors.append(f"{location}: {block.identifier} lacks source metadata")
        if parsed_uses(block.header) != EXPECTED_USES.get(block.identifier, ()):
            errors.append(f"{location}: {block.identifier} has unreviewed dependency metadata")
        is_open = block.identifier in EXPECTED_OPEN
        has_lean = "(lean :=" in block.header
        has_open_tag = "source-open" in block.header
        if is_open and (has_lean or not has_open_tag):
            errors.append(f"{location}: open node has a declaration or lacks source-open")
        if not is_open and (not has_lean or has_open_tag):
            errors.append(f"{location}: proved node lacks a declaration or is marked source-open")
        if (
            CITATION.search(block.citation) is None
            or PAGES.search(block.citation) is None
            or LOCATOR.search(block.citation) is None
        ):
            errors.append(
                f"{location}: {block.identifier} lacks an author-year citation, source locator, "
                "or printed-page citation"
            )

    if errors:
        print("\n".join(errors), file=sys.stderr)
        raise SystemExit(1)
    print(
        f"statement style ok: {len(blocks)} curated nodes "
        f"({len(blocks) - len(EXPECTED_OPEN)} formalized, {len(EXPECTED_OPEN)} open)"
    )


if __name__ == "__main__":
    main()
