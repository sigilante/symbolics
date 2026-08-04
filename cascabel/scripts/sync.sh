#!/bin/sh
#
# sync.sh -- copy the cascabel desk into a pier's %cascabel
#
# Unlike Racoon's and Baloon's, this targets its OWN desk rather than
# %base: cascabel is an agent, and an agent wants a desk it controls.
# The Racoon and Baloon libraries reach it as symlinks under desk/lib,
# which cp dereferences, so the desk ends up self-contained.
#
# First time on a ship:
#   |merge %cascabel our %base
#   |mount %cascabel
#   scripts/sync.sh && |commit %cascabel && |install our %cascabel
#
# After that, sync.sh + |commit %cascabel is the loop.
#
# Override the pier with SYMBOLICS_PIER.
#
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)
desk="$here/desk"
pier="${SYMBOLICS_PIER:-$HOME/urbit/ships/emissary-dev/zod}"
dest="$pier/cascabel"

[ -d "$dest" ] || {
  echo "sync.sh: $dest does not exist." >&2
  echo "  In the dojo:  |merge %cascabel our %base   then  |mount %cascabel" >&2
  exit 1
}

n=0
for f in $(cd "$desk" && find . -name '*.hoon' -o -name 'desk.bill' -o -name 'sys.kelvin'); do
  mkdir -p "$dest/$(dirname "$f")"
  cp -Lf "$desk/$f" "$dest/$f"
  n=$((n + 1))
done
echo "sync.sh: copied $n file(s) to $dest"
echo "next:  |commit %cascabel"
