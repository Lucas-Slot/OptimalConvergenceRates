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

comparator_commit=575674928e239f5bc452aab72d1dd7b0f1326494
lean4export_commit=d065b0009aed0520e9e99752847a33b337661690
lean4export_tag=v4.28.0
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

configs=(
  Comparator/AllResults/comparator.json
)

for required_command in cargo git go lake; do
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
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match" >&2
  echo "the pinned lean4export toolchain $lean4export_toolchain" >&2
  exit 1
fi
if [ "$project_toolchain" != "leanprover/lean4:$lean4export_tag" ]; then
  echo "error: project toolchain does not match lean4export release $lean4export_tag" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git \
  "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git \
  "$nanoda_dir" "$nanoda_commit"

CGO_ENABLED=0 GOBIN="$bin_dir" \
  go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
for config in "${configs[@]}"; do
  echo "Verifying $config"
  GIT_CONFIG_GLOBAL=/dev/null \
  GIT_CONFIG_NOSYSTEM=1 \
  GIT_TERMINAL_PROMPT=0 \
  LEAN_ABORT_ON_PANIC=1 \
  COMPARATOR_LANDRUN_BIN="$bin_dir/landrun" \
  COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
  COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
  COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
    lake env "$comparator_dir/.lake/build/bin/comparator" "$config"
done
