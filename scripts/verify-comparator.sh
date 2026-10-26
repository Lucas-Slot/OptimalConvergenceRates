#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
if [ -n "${COMPARATOR_CACHE:-}" ]; then
  cache_root=$COMPARATOR_CACHE
  remove_cache=false
else
  cache_root=$(mktemp -d "${TMPDIR:-/tmp}/comparator.XXXXXX")
  remove_cache=true
fi
if $remove_cache; then
  trap 'rm -rf -- "$cache_root"' EXIT
fi

bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

comparator_commit=e3dcf3083fc53d44b27a4431fabf7d43181583f5
lean4export_commit=5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe
lean4export_source_tag=v4.35.0
project_lean_tag=v4.35.0
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

configs=(
  Comparator/AllResults/comparator.json
  Comparator/SphereDimensionBounds/comparator.json
)

use_landrun=${COMPARATOR_USE_LANDRUN:-false}
case "$use_landrun" in
  true|false) ;;
  *)
    echo "error: COMPARATOR_USE_LANDRUN must be true or false" >&2
    exit 1
    ;;
esac

required_commands=(cargo elan git lake)
if $use_landrun; then
  required_commands+=(go)
fi
for required_command in "${required_commands[@]}"; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git \
  "$lean4export_dir" "$lean4export_commit"

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "leanprover/lean4:$project_lean_tag" ]; then
  echo "error: project toolchain does not match the verified release $project_lean_tag" >&2
  exit 1
fi
if [ "$lean4export_toolchain" != "leanprover/lean4:$lean4export_source_tag" ]; then
  echo "error: pinned lean4export source does not match release $lean4export_source_tag" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git \
  "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git \
  "$nanoda_dir" "$nanoda_commit"

comparator_landrun="$comparator_dir/scripts/fake-landrun.sh"
comparator_landrun_bin=
if $use_landrun; then
  CGO_ENABLED=0 GOBIN="$bin_dir" \
    go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"
  comparator_landrun="$repository_root/scripts/landrun-wrapper.sh"
  comparator_landrun_bin="$bin_dir/landrun"
fi

(cd "$comparator_dir" && lake build comparator)
# Build the exporter with the project toolchain so it reads this project's oleans.
(cd "$lean4export_dir" && elan run "$project_toolchain" lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
for config in "${configs[@]}"; do
  echo "Verifying $config"
  GIT_CONFIG_GLOBAL=/dev/null \
  GIT_CONFIG_NOSYSTEM=1 \
  GIT_TERMINAL_PROMPT=0 \
  LEAN_ABORT_ON_PANIC=1 \
  COMPARATOR_LANDRUN_BIN="$comparator_landrun_bin" \
  COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
  COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
  COMPARATOR_LANDRUN="$comparator_landrun" \
    lake env "$comparator_dir/.lake/build/bin/comparator" "$config"
done
