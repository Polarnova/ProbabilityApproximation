#!/usr/bin/env bash

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="$root/_out/site"
book_output="$root/_out/book"

if command -v lake >/dev/null 2>&1; then
  lake_cmd="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_cmd="$HOME/.elan/bin/lake"
else
  echo "lake is not available on PATH or under \$HOME/.elan/bin" >&2
  exit 127
fi

build_library() {
  cd "$root"
  python3 "$root/scripts/check_statement_style.py"
  echo "Checking compiled Blueprint modules with Lake..."
  "$lake_cmd" build ProbabilityApproximationBlueprint
}

validate_site() {
  local manifest="$output/html-multi/-verso-data/blueprint-manifest.json"

  "$lake_cmd" exe vbp check --site "$output" >/dev/null
  python3 "$root/scripts/validate_manifest.py" "$manifest"
}

build_site() {
  build_library
  echo "Rendering Blueprint HTML..."
  rm -rf -- "$output/html-multi"
  "$lake_cmd" lean ProbabilityApproximationBlueprintMain.lean -- --run \
    ProbabilityApproximationBlueprintMain.lean --output "$output"
  test -f "$output/html-multi/index.html"
  test -f "$output/html-multi/-verso-data/blueprint-manifest.json"
  test -f "$output/html-multi/-verso-data/blueprint-html-cache.json"
  validate_site
  touch "$output/html-multi/.nojekyll"
}

build_pdf() {
  build_library
  echo "Rendering the book PDF..."
  "$lake_cmd" lean ProbabilityApproximationBookMain.lean -- --run \
    ProbabilityApproximationBookMain.lean --output "$book_output" --without-html-multi --pdf
  test -f "$book_output/pdf/main.pdf"
  mkdir -p "$output/pdf"
  cp "$book_output/pdf/main.pdf" "$output/pdf/main.pdf"
}

case "${1:-build}" in
  build)
    build_site
    ;;
  serve)
    build_site
    exec python3 -m http.server --directory "$output/html-multi" "${PORT:-8000}"
    ;;
  pdf)
    build_pdf
    ;;
  *)
    echo "usage: $0 [build|serve|pdf]" >&2
    exit 2
    ;;
esac
