#!/usr/bin/env bash
# Build the pinned upstream frontend without modifying the submodule.
# Cargo passes a directory inside OUT_DIR; standalone use defaults to target/gui.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
for tool in node npm; do
    command -v "$tool" >/dev/null || {
        echo "ERROR: $tool is required to build the GUI (install Node.js 22.12+ or 24+)." >&2
        exit 1
    }
done
gui_dir="${1:-$root/target/gui}"
mkdir -p "$gui_dir"
gui_dir="$(cd "$gui_dir" && pwd)"
build_dir=$(mktemp -d "$gui_dir/.build.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT
mkdir "$build_dir/frontend"
cp "$root/tamarin-prover/frontend/"{package.json,package-lock.json,tsconfig.json,vite.config.js} "$build_dir/frontend/"
cp -R "$root/tamarin-prover/frontend/src" "$build_dir/frontend/src"
(
    cd "$build_dir/frontend"
    npm ci --cache "${npm_config_cache:-$gui_dir/npm-cache}" --include=dev --no-audit --no-fund
    npm run build
)
for asset in intdot-graph.es.js intdot-staticgraph.es.js intdot-dynamicgraph.es.js intdot-style.css; do
    test -s "$build_dir/frontend/dist/$asset" || {
        echo "ERROR: frontend build did not produce $asset" >&2
        exit 1
    }
done
# Keep the previous compiled assets until the build succeeds.
mkdir -p "$gui_dir/frontend"
if diff -qr "$build_dir/frontend/dist" "$gui_dir/frontend/dist" >/dev/null 2>&1; then
    echo "GUI assets already current"
    exit 0
fi
rm -rf "$gui_dir/frontend/dist"
mv "$build_dir/frontend/dist" "$gui_dir/frontend/dist"
echo "GUI assets ready in $gui_dir"
