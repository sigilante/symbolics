#!/bin/sh
#
# run.sh -- boot a fake ship, install the desks, run every suite
#
# Follows urbit/urbit's nix/test-fake-ship.nix: boot in daemon mode with the
# output going to a log, drive the ship with click over conn.c, then decide
# pass/fail from that log plus the thread's own return value.
#
# Locally, scripts/test.sh is the thing to use -- it talks to the ship you
# already have running.  This is for a cold machine, and is what CI runs.
#
#   PIER    where to boot           (default ./ci-pier)
#   VERE    the urbit binary        (default ./urbit)
#   CLICK   urbit/tools click       (default ./tools/pkg/click/click)
#
set -eu

root=$(cd "$(dirname "$0")/../.." && pwd)
pier="${PIER:-$root/ci-pier}"
vere="${VERE:-$root/urbit}"
click="${CLICK:-$root/tools/pkg/click/click}"
log="${LOG:-$root/ci-pier.log}"

say() { printf '\n=== %s ===\n' "$1"; }

say "boot a fake zod"
# no -B: vere fetches the pill itself, which removes a URL we would
# otherwise have to keep correct
rm -rf "$pier"
"$vere" -d -F zod -c "$pier" > "$log" 2>&1 &
# a bad launch fails immediately, so look before settling in to wait
sleep 10
if grep -qiE 'already exists|normal usage|boot failed' "$log"; then
  echo "launch failed:"; tail -20 "$log"; exit 1
fi
i=0
while [ ! -S "$pier/.urb/conn.sock" ]; do
  i=$((i + 5))
  [ "$i" -gt 600 ] && { echo "no conn.sock after 10m:"; tail -20 "$log"; exit 1; }
  sleep 5
done
echo "booted in ~${i}s"

say "mount %base"
"$click" -b "$vere" -k -i "$root/scripts/ci/mount.hoon" "$pier"
sleep 5
[ -d "$pier/base" ] || { echo "mount produced no $pier/base"; tail -20 "$log"; exit 1; }

say "install the desks"
# sync.sh defaults to the dev pier; point it at ours
SYMBOLICS_PIER="$pier" "$root/racoon/scripts/sync.sh"
SYMBOLICS_PIER="$pier" "$root/baloon/scripts/sync.sh"

say "commit"
"$click" -b "$vere" -k -i "$root/scripts/ci/commit.hoon" "$pier"
sleep 20

say "run every suite"
# %fyrd argument 0 means everything under /=base=/tests, so new test files
# need no registration anywhere
res=$("$click" -b "$vere" -c "$pier" "[0 %fyrd %base %test %noun %noun 0]" | tail -1)
echo "$res" | cut -c1-120

say "result"
fail=0
# urbit/urbit's checkPhase: the per-arm lines are %slog and land in the log
if grep -qE 'FAILED|CRASHED' "$log"; then
  echo "log reports failures:"; grep -E 'FAILED|CRASHED' "$log" | head -20; fail=1
fi
# and the thread's own loobean: %noun 0 is %.y, %noun 1 is %.n
case "$res" in
  *"%avow 0 %noun 0"*) [ "$fail" -eq 0 ] && echo "pass" ;;
  *"%avow 0 %noun 1"*) echo "FAIL: a test arm failed"; fail=1 ;;
  *)                   echo "ERROR: the thread did not complete"; fail=1 ;;
esac
echo "arms run: $(grep -cE '^/?OK ' "$log" || true)"
exit "$fail"
