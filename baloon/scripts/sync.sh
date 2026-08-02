#!/bin/sh
#
# sync.sh -- copy desk/ into the development pier's %base
#
# Baloon's desk files sit alongside Racoon's in %base.  /lib/baloon imports
# /lib/racoon, so Racoon must already be synced there; run racoon's own
# sync.sh first if %base is fresh.
#
# SPEC S4 edit-test loop:
#
#   |mount %base          (once, in the dojo)
#   scripts/sync.sh
#   |commit %base         (in the dojo)
#   -test /=base=/tests/lib/baloon ~
#
# The pier defaults to the fake ~zod in the emissary-dev harness.  Override
# with BALOON_PIER.
#
# This script only copies files.  It never boots, commits, or otherwise
# pokes the ship: Clay is authoritative for what is built, and conflating
# the copy with the commit makes a failed build hard to attribute.

set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
desk="$here/desk"
pier="${BALOON_PIER:-$HOME/urbit/ships/emissary-dev/zod}"
base="$pier/base"

if [ ! -d "$desk" ]; then
  echo "sync.sh: no desk at $desk" >&2
  exit 1
fi

if [ ! -d "$base" ]; then
  echo "sync.sh: $base does not exist." >&2
  echo "  Is the pier at $pier, and has %base been mounted?" >&2
  echo "  In the dojo:  |mount %base" >&2
  exit 1
fi

# Copy only the files this project owns.  A blanket rsync of desk/ over
# base/ would be fine today, but %base carries the kernel; being explicit
# means a stray file here can never shadow a sys/ file there.
files="
sur/baloon.hoon
lib/baloon.hoon
lib/baloon-fmt.hoon
lib/baloon-vectors.hoon
tests/lib/baloon.hoon
gen/baloon-bench.hoon
gen/baloon-det.hoon
"

copied=0
for f in $files; do
  src="$desk/$f"
  [ -f "$src" ] || continue
  dst="$base/$f"
  mkdir -p "$(dirname "$dst")"
  cp -f "$src" "$dst"
  echo "  $f"
  copied=$((copied + 1))
done

echo "sync.sh: copied $copied file(s) to $base"
echo "next:  |commit %base"
