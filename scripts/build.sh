#!/usr/bin/env bash
# Low-impact `lake build` for a shared 15 GB machine. Usage: scripts/build.sh [lake build args...]
# * LEAN_NUM_THREADS caps both lake's parallel jobs and the threads of each Lean process
#   (override with BUILD_THREADS, default 2).
# * nice / ionice keep the desktop responsive.
# * A systemd scope caps the memory of the whole build (BUILD_MEM, default 8G); if the cap is hit
#   the build is killed, not the rest of the machine. Falls back to no cap without systemd-run.
cd "$(dirname "$0")/.." || exit 2
threads=${BUILD_THREADS:-2}
mem=${BUILD_MEM:-8G}
cmd=(nice -n 19 ionice -c3 env LEAN_NUM_THREADS="$threads" lake build "$@")
if command -v systemd-run >/dev/null 2>&1; then
  exec systemd-run --user --scope --quiet -p MemoryMax="$mem" -p MemorySwapMax=0 "${cmd[@]}"
else
  exec "${cmd[@]}"
fi
