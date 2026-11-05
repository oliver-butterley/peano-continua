#!/usr/bin/env bash
# Memory watchdog for Lean sessions with Lean language servers (editor and MCP agents) running.
# Every INTERVAL seconds it reads MemAvailable. Below SOFT_MB it kills the largest Lean file worker
# (`lean --worker`) or REPL (`repl`); below HARD_MB it kills every Lean file worker and REPL.
# It never kills compilations (`lean <file> -o …`, from `lake build` in this or any other project)
# nor the language-server processes themselves (`lean --server`), so builds are never interrupted
# and a killed worker is simply restarted by its server on the next request.
# Only processes whose command name is `lean` or `repl` are touched. Every kill goes to LOG.
# Usage: scripts/lean_watchdog.sh [SOFT_MB] [HARD_MB] [INTERVAL]
cd "$(dirname "$0")/.." || exit 2
SOFT_MB=${1:-4096}
HARD_MB=${2:-2048}
INTERVAL=${3:-10}
LOG=.lake/watchdog.log
mkdir -p .lake
echo "$(date -Is) watchdog started pid=$$ soft=${SOFT_MB}MB hard=${HARD_MB}MB (workers and REPLs only)" >> "$LOG"
avail_mb() { awk '/^MemAvailable:/ {print int($2/1024)}' /proc/meminfo; }
# Killable processes, largest first, as "pid rss_kB comm": `repl`, or `lean` with `--worker`.
killable() {
  ps -eo pid=,rss=,comm= --sort=-rss | while read -r pid rss comm; do
    case "$comm" in
      repl) echo "$pid $rss $comm" ;;
      lean) tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null | grep -q -e '--worker' && echo "$pid $rss $comm" ;;
    esac
  done
}
kill_one() {  # pid rss_kB comm level avail
  local args
  args=$(tr '\0' ' ' < "/proc/$1/cmdline" 2>/dev/null | cut -c1-200)
  kill -9 "$1" 2>/dev/null && echo "$(date -Is) $4 avail=${5}MB killed $3 pid=$1 rss=$(($2/1024))MB args=$args" >> "$LOG"
}
while true; do
  a=$(avail_mb)
  if [ "$a" -lt "$HARD_MB" ]; then
    killable | while read -r pid rss comm; do kill_one "$pid" "$rss" "$comm" HARD "$a"; done
  elif [ "$a" -lt "$SOFT_MB" ]; then
    read -r pid rss comm < <(killable | head -n1)
    [ -n "$pid" ] && kill_one "$pid" "$rss" "$comm" SOFT "$a"
  fi
  sleep "$INTERVAL"
done
