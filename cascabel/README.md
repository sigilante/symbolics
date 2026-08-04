# Cascabel — exact symbolic computation as a caderno kernel

A `/lib/shoe` agent that answers `%eval-command`, so [caderno][c] can drive
it as a notebook kernel. It is also an ordinary CLI: `|link %cascabel`.

[c]: https://github.com/sigilante/caderno

```
factor x^4 - 1              x^4 - 1  =  (x - 1) * (x + 1) * (x^2 + 1)
roots x^3 - x - 1             1.324717957244...  in [-2, 2]
gcd x^2 - 1 ; x^2 + 2x + 1  x + 1
zfac 360                    360  =  2^3 * 3^2 * 5
det [[1 2] [3 4]]           -2
hnf [[2 4 4] [-6 6 12] [10 -4 -16]]
                            [  2  4  4 ]
                            [  0  6  0 ]
                            [  0  0 12 ]
```

## Stateless, deliberately

There is no session map, no accumulated subject, nothing in state at all.
Every command is answered from its own text. Re-running a cell, running
cells out of order, or pointing a second notebook at the same agent all
behave identically — which is the property that makes a kernel safe to
drive from a notebook, where none of those orderings is under its control.

It is a **command** language, not an expression language: a verb and its
arguments, each argument parsed by the same `+red*` arm the generators
already use. There is no nesting, no precedence, and no feeding one result
into another. `raccoon-spec.md` §13 fences out a symbolic expression front
end and this does not cross that line.

Arguments that come in pairs are separated by `;`, since polynomials and
matrices both contain spaces and commas of their own.

**Nothing crashes.** Every command is wrapped in `+mule`, and a parse
failure, a domain error, or an unknown verb comes back as a line of text.
A kernel that bails takes the notebook with it.

## The kernel contract

Caderno watches `/sole/[ship]/[ses]`, pokes `%eval-command` with
`[ses=@ta src=tape]`, and reads `%sole-effect` facts back; a terminal
`%pro` signals completion. That handling lives in the vendored
`lib/shoe.hoon`, along with the `/x/sole/sessions` scry that powers kernel
discovery — so `app/cascabel.hoon` needs no special code, and a poked
command takes exactly the same path as a typed one.

Both are lifted from [aviary][a], which is where the pattern comes from.

[a]: https://github.com/sigilante/aviary

## Vendored shoe

`lib/shoe.hoon` differs from base in three ways:

- `%eval-command` in `on-poke` and the `/x/sole/sessions` scry, per above.
- **`+tab` is a no-op.** Stock shoe completes against
  `/lib/language-server-complete`, which base at this kelvin imports but
  does not ship. Cascabel is call-and-response and has no vocabulary to
  complete against, so the honest fix was to drop the dependency rather
  than vendor a library from a different kernel version to power a feature
  nobody here uses. `+option` is inlined in its place.

## Layout

`desk/lib` and `desk/sur` reach Racoon and Baloon through **symlinks**, so
there is one copy of each library in the repo and the desk still syncs
self-contained (`cp -L` dereferences them).

```
|merge %cascabel our %base
|mount %cascabel
scripts/sync.sh && |commit %cascabel && |install our %cascabel
```

After that, `scripts/sync.sh` plus `|commit %cascabel` is the loop.
