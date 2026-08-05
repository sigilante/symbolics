#!/bin/sh
#
# bench.sh -- run a benchmark and get a number back, not a terminal
#
# Drives a RUNNING fake ship through click, which sends a %fyrd card to
# conn.c and waits for the thread's product.  Same mechanism as test.sh;
# the difference is that these threads return a DURATION rather than a
# loobean.
#
# WHY.  The generators time themselves with ~>(%bout ...), which is a
# slog: it lands in the ship's output and nowhere a script can reach.
# Reading it back means scraping the tmux pane, and that produced four
# distinct failures in one afternoon --
#
#   1. the baseline sampled AFTER the send, so a 40 ms command finished
#      before the "before" reading and the wait never terminated;
#   2. counting `took` lines is not monotonic: the pane holds 2.000
#      lines and one SD_4 run emits ~1.800 `fund:` jet-miss warnings, so
#      old timings scroll out and the count FALLS;
#   3. clear-history empties the scrollback but leaves the visible
#      screen, so a stale timing can still be the only one present;
#   4. worst -- a -test that ran BEFORE its |commit landed, and reported
#      a NEGATIVE CONTROL as passing.  A harness that can silently
#      measure the wrong build is worse than no harness.
#
# %fyrd is synchronous and returns the product, so none of the four is
# possible here.  Commit first anyway: Clay builds what is committed.
#
# Usage:
#   scripts/bench.sh nop                    the harness's own floor
#   scripts/bench.sh vh 5 0                 SD_5, Zassenhaus
#   scripts/bench.sh vh 5 1                 SD_5, van Hoeij
#   scripts/bench.sh lll 17 1 136           +lll on a 17-row lattice
#   scripts/bench.sh alg 'x^2 - 2' 'x^2 - 3'   algebraic sum, default
#   scripts/bench.sh alg -f 'x^2 - 2' 'x^2 - 3'  same, van Hoeij bound
#
# Every run prints "us check", where .check is derived from the answer:
# a benchmark that measured a crash, or an arm that returned instantly
# because it did nothing, is exactly what a bare duration cannot show.
#
# Requires, overridable by environment:
#   CLICK           urbit/tools/pkg/click/click
#   VERE            the urbit binary
#   SYMBOLICS_PIER  the pier
#   REPS            how many times to run each job (default 1)
#
set -eu

here=$(cd "$(dirname "$0")" && pwd)
pier="${SYMBOLICS_PIER:-$HOME/urbit/ships/emissary-dev/zod}"
vere="${VERE:-$HOME/urbit/ships/emissary-dev/urbit}"
click="${CLICK:-$HOME/urbit/tools/pkg/click/click}"
reps="${REPS:-1}"

[ -r "$click" ] || { echo "bench.sh: no click at $click" >&2; exit 2; }
[ -x "$vere"  ] || { echo "bench.sh: no urbit at $vere"  >&2; exit 2; }
[ -S "$pier/.urb/conn.sock" ] || {
  echo "bench.sh: no conn.sock at $pier -- is the ship running?" >&2; exit 2; }

# click shells out to `nc -U -W 1`; macOS netcat has no -W, so scripts/nc
# is a symlink to the nc-unix stand-in beside this file
[ -e "$here/nc" ] || ln -s nc-unix "$here/nc"

[ "$#" -ge 1 ] || { sed -n '2,40p' "$0"; exit 2; }
kind=$1
shift

# thread and argument, per benchmark family
case "$kind" in
  nop)  thread=baloon-bench; arg="[%nop 0 0 0]" ;;
  vh)   [ "$#" -eq 2 ] || { echo "usage: bench.sh vh <k> <side>" >&2; exit 2; }
        thread=baloon-bench; arg="[%vh $1 $2 0]" ;;
  lll)  [ "$#" -eq 3 ] || { echo "usage: bench.sh lll <r> <m> <bits>" >&2; exit 2; }
        thread=baloon-bench; arg="[%lll $1 $2 $3]" ;;
  alg)
        # the two bindings live in different desks on purpose, so the
        # -f flag picks the THREAD, not a field: /ted/racoon-bench is
        # Racoon-only and defaults to +firr:zx, /ted/baloon-bench binds
        # +factor:vh.  See racoon/SPEC-QUESTIONS.md R4.
        thread=racoon-bench
        if [ "${1:-}" = "-f" ]; then thread=baloon-bench; shift; fi
        [ "$#" -eq 2 ] || { echo "usage: bench.sh alg [-f] <poly> <poly>" >&2; exit 2; }
        arg="[%alg '$1' '$2' 0]" ;;
  *)    echo "bench.sh: unknown benchmark '$kind'" >&2; exit 2 ;;
esac

# the label carries the THREAD as well as the arguments: `alg` and
# `alg -f` differ only in which desk answered, and a table that does not
# say which binding produced a row is not a comparison
label="$kind $*"

i=1
while [ "$i" -le "$reps" ]; do
  # host-side wall clock as a CROSS-CHECK on the ship's own number.  It
  # includes click's process spawn and the socket round trip, which is
  # why it is printed rather than used: two clocks disagreeing is worth
  # seeing, and `nop` says how much of the gap is fixed overhead.
  t0=$(date +%s)
  res=$(PATH="$here:$PATH" bash "$click" -b "$vere" -c "$pier" \
          "[0 %fyrd %base %$thread %noun %noun $arg]" 2>/dev/null | tail -1)
  t1=$(date +%s)

  # the product arrives as  [0 %avow 0 %noun [us check]]
  case "$res" in
    *"%avow 0 %noun"*) ;;
    *) echo "ERROR  $label -- the thread did not complete:" >&2
       echo "$res" | cut -c1-200 >&2
       exit 1 ;;
  esac
  # click prints an untyped atom as decimal below 2^16 and as HEX above
  # it, so the same benchmark changes format as it gets slower:
  #   [0 %avow 0 %noun 31036 1]       SD_3, 31 ms
  #   [0 %avow 0 %noun 0x4aa7a 1]     SD_4, 306 ms
  # Both forms may carry dot separators.  Reading only the first would
  # have silently mangled every number above 65.536 microseconds, which
  # is every measurement worth taking.
  denum() {
    v=$(printf '%s' "$1" | tr -d '.')
    case "$v" in
      0x*) printf '%d' "$v" ;;
      *)   printf '%s' "$v" ;;
    esac
  }
  nums=$(echo "$res" | sed 's/.*%noun *//; s/[][]//g')
  us=$(denum "$(echo "$nums" | awk '{print $1}')")
  chk=$(denum "$(echo "$nums" | awk '{print $2}')")
  case "$us" in
    ''|*[!0-9]*) echo "ERROR  $label -- unparseable product: $res" >&2; exit 1 ;;
  esac

  printf '%-34s %12s us   check %-4s   %s\n' \
    "$label" "$us" "${chk:-?}" "$thread"
  i=$((i + 1))
done
