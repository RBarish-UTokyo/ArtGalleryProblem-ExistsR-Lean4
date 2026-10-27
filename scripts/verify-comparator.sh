#!/usr/bin/env bash
set -euo pipefail

# Judge Solution against Challenge the way Palomar does: with the `lake
# comparator` that ships in this project's own toolchain, replaying the proof
# through Lean's kernel and the toolchain's bundled independent kernels
# (NanoDa and con-ron). Nothing is built from a pin; everything that judges
# comes from `lean-toolchain`, which Palomar requires to be v4.35.0-rc2 or
# later.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This
# generated copy does the same, so the local check judges as the registry does.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
if grep -q '"external_kernels"' comparator.json; then
  echo "error: comparator.json: external_kernels is not a submitter field; Palomar rejects it" >&2
  exit 1
fi
if ! grep -Eq '^[[:space:]]*"enable_nanoda":[[:space:]]*(true|false)[[:space:]]*$' comparator.json; then
  echo "error: comparator.json must end with an \"enable_nanoda\" entry" >&2
  exit 1
fi
awk -v prefix="$prefix" '
  /^[[:space:]]*"enable_nanoda":/ {
    print "  \"external_kernels\": {"
    print "    \"nanoda\": [\"" prefix "/bin/nanoda_bin\"],"
    print "    \"con-ron\": [\"" prefix "/bin/con-ron\"]"
    print "  }"
    next
  }
  { print }
' comparator.json > "$config"

lake exe cache get
lake comparator --config "$config"
