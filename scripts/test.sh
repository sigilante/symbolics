#!/bin/sh
#
# test.sh -- run the test suites headlessly, with a real exit code
#
# Drives a RUNNING fake ship through click, which sends a %fyrd card to
# conn.c.  This is urbit/urbit's own CI mechanism, from
# nix/test-fake-ship.nix; click itself is a bash script from urbit/tools.
#
# It replaces scraping the tmux pane, which was the real source of trouble
# here: timing skew between a commit and the command after it, and OK lines
# swallowed by terminal redraws -- which undercounted this project's test
# totals for several commits before anyone noticed.
#
# The %test thread returns a loobean, so the exit code is exact:
#   [0 %avow 0 %noun 0]  ->  %.y, everything passed
#   [0 %avow 0 %noun 1]  ->  %.n, something failed
# Per-arm lines are %slog and go to the ship's own output, so the detail is
# in the pane (or, under `urbit -d`, in the daemon log -- which is where
# urbit/urbit greps for FAILED and CRASHED).
#
# NOTE: this does not commit.  Clay builds what is committed, so run
#   racoon/scripts/sync.sh && baloon/scripts/sync.sh
# and `|commit %base` in the dojo first.  Committing over conn.c needs a
# hood poke rather than a thread, which click's -k mode can do but is not
# worth the indirection while a dojo is open anyway.
#
# Requires, overridable by environment:
#   CLICK           urbit/tools/pkg/click/click
#   VERE            the urbit binary
#   SYMBOLICS_PIER  the pier
#
set -eu

here=$(cd "$(dirname "$0")" && pwd)
pier="${SYMBOLICS_PIER:-$HOME/urbit/ships/emissary-dev/zod}"
vere="${VERE:-$HOME/urbit/ships/emissary-dev/urbit}"
click="${CLICK:-$HOME/urbit/tools/pkg/click/click}"

[ -r "$click" ] || { echo "test.sh: no click at $click" >&2; exit 2; }
[ -x "$vere"  ] || { echo "test.sh: no urbit at $vere"  >&2; exit 2; }
[ -S "$pier/.urb/conn.sock" ] || {
  echo "test.sh: no conn.sock at $pier -- is the ship running?" >&2; exit 2; }

# click shells out to `nc -U -W 1`; macOS netcat has no -W, so scripts/nc
# is a symlink to the nc-unix stand-in beside this file
[ -e "$here/nc" ] || ln -s nc-unix "$here/nc"

res=$(PATH="$here:$PATH" bash "$click" -b "$vere" -c "$pier" \
        "[0 %fyrd %base %test %noun %noun 0]" 2>/dev/null | tail -1)

case "$res" in
  *"%avow 0 %noun 0"*)
    echo "pass   (all tests under /=base=/tests)"
    exit 0 ;;
  *"%avow 0 %noun 1"*)
    echo "FAIL   -- see the ship's output for the failing arms" >&2
    exit 1 ;;
  *)
    echo "ERROR  -- the thread did not complete:" >&2
    echo "$res" | cut -c1-200 >&2
    exit 1 ;;
esac
