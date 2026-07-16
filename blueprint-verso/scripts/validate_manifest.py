#!/usr/bin/env python3
"""Validate the generated curated ProbabilityApproximation Blueprint manifest."""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path


EXPECTED_LABELS = {
    "indicator-stein-solution", "uniform-leave-one-out-concentration",
    "uniform-third-moment-berry-esseen", "bennett-hoeffding-mgf",
    "exponential-leave-one-out-concentration", "one-sided-truncation-comparison",
    "upper-truncated-stein-exchange", "upper-truncated-residual-decomposition",
    "upper-truncated-r1-r3-bounds", "upper-truncated-r2-expected-kernel",
    "upper-truncated-indicator-residual", "stein-product-increment",
    "upper-truncated-product-residual", "upper-truncated-central-decay",
    "scalar-release-reduction",
    "convex-parallel-sets", "metric-projection", "squared-distance-calculus",
    "bentkus-smooth-cutoff", "gaussian-companions-and-transport",
    "gaussian-fourth-moment-control", "gaussian-companion-second-moment-match",
    "gaussian-companion-third-moment-comparison", "gaussian-companion-mixed-moment",
    "bentkus-rotation-cancellation", "covariance-additivity-and-leave-one-out",
    "bentkus-whitening-covariance-identity",
    "bentkus-whitening-gaussian-pushforward",
    "bentkus-identity-covariance-contract",
    "bentkus-whitening-one-set-transport",
    "gaussian-signed-distance-eikonal",
    "gaussian-signed-distance-level-frontiers",
    "gaussian-shell-signed-distance-slabs",
    "gaussian-affine-codimension-one-slicing",
    "lipschitz-area-formula", "scalar-coarea-formula",
    "gaussian-signed-distance-coarea-profiles",
    "intrinsic-sphere-hausdorff-normalization",
    "ball-projection-jacobian-charts", "ball-cauchy-projection-formula",
    "ball-spherical-projection-average",
    "ball-spherical-rearrangement", "ball-radial-gamma-peak",
    "ball-radial-majorant",
    "gaussian-convex-shell",
    "bentkus-smoothing-inequality",
    "density-derivative-integral-bound", "gaussian-density-third-derivative",
    "gaussian-density-ibp", "cutoff-derivative-shell-ibp",
    "bentkus-taylor-remainders", "gaussian-density-second-order-remainder",
    "bentkus-angle-integrals",
    "bentkus-parameter-closure",
    "bentkus-trivial-induction-branches",
    "bentkus-leave-one-out-whitening",
    "bentkus-standardized-induction",
    "nonuniform-berry-esseen", "bentkus-convex-set",
}
EXPECTED_OPEN = {
    "gaussian-convex-shell",
    "bentkus-standardized-induction", "bentkus-convex-set",
}
EXPECTED_DECLARATIONS = 289
EXPECTED_EDGES = 81


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    manifest_path = (
        Path(sys.argv[1])
        if len(sys.argv) > 1
        else Path("_out/site/html-multi/-verso-data/blueprint-manifest.json")
    )
    if not manifest_path.exists():
        fail(f"manifest missing: {manifest_path}")
    data = json.loads(manifest_path.read_text())
    previews = data.get("previews", [])
    blocks = [
        preview for preview in previews
        if preview.get("targetKind") == "block" and preview.get("facet") == "statement"
    ]
    lean_decls = [preview for preview in previews if preview.get("targetKind") == "leanDecl"]
    if data.get("vbpInternalSchemaVersion") != 2:
        fail("unexpected Blueprint schema version")
    if len(blocks) != len(EXPECTED_LABELS):
        fail(f"expected {len(EXPECTED_LABELS)} statement blocks, found {len(blocks)}")
    if len(previews) != len(blocks) + len(lean_decls):
        fail("manifest contains previews other than statements and associated Lean declarations")

    labels = [block.get("authoredLabel") for block in blocks]
    if set(labels) != EXPECTED_LABELS:
        fail("unexpected statement labels: " + ", ".join(sorted(str(x) for x in labels)))
    duplicates = sorted(label for label, count in Counter(labels).items() if count != 1)
    if duplicates:
        fail("duplicate statement labels: " + ", ".join(duplicates))

    block_decls = {
        block["authoredLabel"]: ((block.get("codeData") or {}).get("external") or {}).get("decls", [])
        for block in blocks
    }
    formalized = {label for label, declarations in block_decls.items() if declarations}
    open_labels = {label for label, declarations in block_decls.items() if not declarations}
    if open_labels != EXPECTED_OPEN:
        fail("unexpected open statement set: " + ", ".join(sorted(open_labels)))
    if formalized != EXPECTED_LABELS - EXPECTED_OPEN:
        fail("unexpected formalized statement set")

    malformed = []
    for block in blocks:
        label = block["authoredLabel"]
        tags = block.get("tags", [])
        if (
            not any(tag.startswith("source-") and tag != "source-open" for tag in tags)
            or not any(tag.startswith("fidelity-") for tag in tags)
            or (label in EXPECTED_OPEN) != ("source-open" in tags)
            or not block.get("sourceLocation", {}).get("ok")
        ):
            malformed.append(label)
    if malformed:
        fail("invalid statement metadata: " + ", ".join(sorted(malformed)))

    declaration_records = [decl for associated in block_decls.values() for decl in associated]
    declarations = [
        decl.get("canonical") if isinstance(decl, dict) else decl
        for decl in declaration_records
    ]
    if any(not isinstance(decl, str) or not decl for decl in declarations):
        fail("associated declaration record lacks a canonical name")
    if len(declarations) != EXPECTED_DECLARATIONS:
        fail(f"expected {EXPECTED_DECLARATIONS} associated declarations, found {len(declarations)}")
    if len(set(declarations)) != len(declarations):
        fail("a Lean declaration is associated with more than one mathematical node")
    if len(lean_decls) != EXPECTED_DECLARATIONS:
        fail(f"expected {EXPECTED_DECLARATIONS} Lean declaration previews, found {len(lean_decls)}")
    if any(block.get("leanCodePreviewKeys") for block in blocks if block["authoredLabel"] in EXPECTED_OPEN):
        fail("open statements unexpectedly reference Lean declaration previews")

    graphs = data.get("graphs", [])
    if len(graphs) != 1:
        fail("expected exactly one dependency graph")
    graph = graphs[0]
    nodes = graph.get("nodes", [])
    edges = graph.get("edges", [])
    if len(nodes) != len(blocks):
        fail("graph node count does not match statement block count")
    if len(edges) != EXPECTED_EDGES:
        fail(f"expected {EXPECTED_EDGES} dependency edges, found {len(edges)}")
    block_keys = {block["key"] for block in blocks}
    if block_keys != {node.get("previewKey") for node in nodes}:
        fail("graph nodes do not match statement preview keys")
    if sum(len(block.get("statementUses", [])) for block in blocks) != EXPECTED_EDGES:
        fail("statement dependency counts disagree with the graph")
    if sum(len(block.get("uses", [])) for block in blocks) != EXPECTED_EDGES:
        fail("rendered dependency counts disagree with the graph")
    if any(block.get("proofUses") for block in blocks):
        fail("proof-only dependency edges are not permitted")
    if any(edge.get("axes") != ["statement"] for edge in edges):
        fail("dependency graph contains a non-statement edge")

    nodes_by_key = {node["previewKey"]: node for node in nodes}
    warnings = [node.get("label") for node in nodes if any(node.get("warnings", {}).values())]
    if warnings:
        fail("dependency graph warnings: " + ", ".join(str(label) for label in warnings))
    invalid_statuses = []
    for block in blocks:
        node = nodes_by_key[block["key"]]
        if node.get("statementStatus") not in {"ready", "blocked", "formalized"}:
            invalid_statuses.append(block["authoredLabel"])
    if invalid_statuses:
        fail("invalid statement status: " + ", ".join(sorted(invalid_statuses)))

    print(
        f"manifest ok: {len(EXPECTED_LABELS)} statements "
        f"({len(EXPECTED_LABELS) - len(EXPECTED_OPEN)} formalized, "
        f"{len(EXPECTED_OPEN)} open), "
        f"{EXPECTED_DECLARATIONS} declarations, {EXPECTED_EDGES} edges"
    )


if __name__ == "__main__":
    main()
