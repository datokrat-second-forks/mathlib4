#!/usr/bin/env bash
#
# dump_decls.sh — dump the public declarations of every built Mathlib module.
#
# For each module `Mathlib.Foo.Bar` it writes `<OUTDIR>/Mathlib.Foo.Bar.txt`,
# containing one `name : type` line per non-internal, non-private declaration the
# module adds.
#
# All modules are imported into a SINGLE `printDecls` process (one shared import
# of the dependency closure), instead of one process per file. This is far faster
# than the per-file approach for a library the size of Mathlib (>8000 modules).
#
# Run from the repository root:
#
#     scripts/dump_decls.sh
#
# Options (environment variables):
#     OUTDIR=dir  output directory (default: decls)
#     PREFIX=p    only dump modules whose name starts with `p`
#                 (e.g. PREFIX=Mathlib.Topology)
#
# The whole library must be built: importing the union of all modules requires
# every module in their transitive closure to have an `.olean`. Requested modules
# that are not built are skipped with a warning; a missing *dependency*, however,
# aborts the import (run `lake build` first). See `PrintDecls.lean` for details.

set -uo pipefail

OUTDIR="${OUTDIR:-decls}"
PREFIX="${PREFIX:-Mathlib}"

lake build printDecls || { echo "failed to build printDecls" >&2; exit 1; }
BIN="$PWD/.lake/build/bin/printDecls"
export LEAN_PATH; LEAN_PATH="$(lake env printenv LEAN_PATH)"

mkdir -p "$OUTDIR"

# Enumerate modules from source files (`Mathlib/Foo/Bar.lean` -> `Mathlib.Foo.Bar`),
# keep those matching PREFIX, and dump them all in one process.
find Mathlib -name '*.lean' \
  | sed 's/\.lean$//; s#/#.#g' \
  | grep "^${PREFIX//./\\.}" \
  | sort \
  | "$BIN" --out "$OUTDIR"

echo "Done. Wrote $(find "$OUTDIR" -name '*.txt' | wc -l) files to $OUTDIR/."
