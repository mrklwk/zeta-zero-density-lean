#!/bin/bash
set -euo pipefail
project_root="$(cd "$(dirname "$0")/.." && pwd)"
toolchain="$(tr -d '\r\n' < "$project_root/lean/lean-toolchain")"
if [[ ! "$toolchain" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
  echo 'BLOCKED: expected an exact official Lean release in lean/lean-toolchain.' >&2
  exit 2
fi
directory="${toolchain//\//--}"
directory="${directory//:/---}"
toolchain_bin="${DENSITY_LEAN_BIN:-${ELAN_HOME:-$HOME/.elan}/toolchains/$directory/bin}"
if [ ! -x "$toolchain_bin/lean" ] || [ ! -x "$toolchain_bin/lake" ]; then
  echo "BLOCKED: pinned toolchain is not installed at $toolchain_bin" >&2
  echo 'No automatic installation attempted.' >&2
  exit 2
fi
expected_version="${toolchain#leanprover/lean4:v}"
actual_version="$("$toolchain_bin/lean" --version)"
if [[ "$actual_version" != *"version $expected_version,"* ]]; then
  echo "BLOCKED: installed compiler does not match $toolchain" >&2
  exit 2
fi
export PATH="$toolchain_bin:$PATH"
cd "$project_root/lean"
exec "$@"
