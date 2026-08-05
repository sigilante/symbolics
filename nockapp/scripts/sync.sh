#!/bin/sh
#
# sync.sh -- copy desk/ into the development pier's %base
#
# Same shape as racoon/scripts/sync.sh and baloon/scripts/sync.sh: it only
# copies, never boots or commits, because conflating the copy with the
# commit makes a failed build hard to attribute.
#
#   scripts/sync.sh
#   |commit %base                          (in the dojo)
#   -test /=base=/tests/lib/tip5 ~         (in the dojo)
#
# THIS DESK NEEDS BOTH OTHERS.  /lib/tip5 consumes Racoon for its field
# arithmetic and Baloon for the MDS layer, so run racoon/scripts/sync.sh
# and baloon/scripts/sync.sh first on a fresh pier.
#
# Override the pier with SYMBOLICS_PIER=/path/to/zod.

set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
desk="$here/desk"
pier="${SYMBOLICS_PIER:-$HOME/urbit/ships/emissary-dev/zod}"
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

files="
lib/tip5.hoon
lib/tip5-constants.hoon
lib/tip5-vectors.hoon
tests/lib/tip5.hoon
gen/tip5.hoon
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
