# SPEC-QUESTIONS — escalation log

Per SPEC §14. Each entry states the question, the pinned material it touches,
and a proposed resolution. Unanswered entries block their phase gate.

---

## Q1 — comparison product type is used but not declared (§6, §7)

**Status:** RESOLVED ~2026.8.1 — approved as proposed, applied to
`desk/sur/racoon.hoon`. §6's type block is amended to include `$ord`.

§7 pins `+pcmp`'s product type as `?(%lt %eq %gt)`, but the §6 `sur` block
declares no name for it. `hoon.hoon` has no such type: `++cmp:si` produces an
`@s` in `{-1, --0, --1}`, and `++aor`/`++dor` produce a `?`. Left as-is, the
literal `?(%lt %eq %gt)` is repeated in three `+pcmp` casts and in every
sorting helper.

**Proposed resolution:** add to `sur/racoon.hoon`:

```hoon
::    $ord:  result of a total-order comparison
+$  ord  ?(%lt %eq %gt)
```

This names an existing pinned type; it adds no new representation and changes
no arm signature. Not applied pending approval — §6 is pinned and silence is
not acceptance. Until then `/lib/racoon` will spell the union out inline.

---

## Q2 — `+cmp:qq` product type (§9 Phase 0)

**Status:** RESOLVED ~2026.8.1 — approved. `cmp:qq` produces `$ord`, and
`+pcmp` on `qol` delegates to it.

§9 lists `cmp` among the `qq` arms on `frac` but gives no product type. §7
defines `+pcmp` on `frac` coefficients by comparing `p1*q2` vs `p2*q1` via
`++cmp:si`, which implies the same three-valued result.

**Proposed resolution:** `cmp:qq` produces the same type as `+pcmp`
(`$ord` if Q1 is approved, else `?(%lt %eq %gt)`), and `+pcmp` on `qol`
delegates to it rather than reimplementing the cross-multiplication.

---

## Notes (delegated, recorded not escalated)

- **Spelling.** §3 spells every path `raccoon`; the repository directory and
  file names are `racoon` (single `c`), intentionally. Paths in this repo are
  `racoon/desk/sur/racoon.hoon` etc., and the library is imported as
  `/-  *racoon`. The prose name remains "Raccoon". §3 is outside the pinned
  §6–§10 range, so this is recorded here rather than escalated.
- **Toolchain.** §4.1's pinned environment is Vere **4.6** (the binary at
  `~/urbit/ships/emissary-dev/urbit`), fake `~zod` pier in that same
  directory, `%base` kelvin `[%zuse 409]`. `sur/racoon.hoon` builds clean
  there. `~nec` in the same directory is a live ship and is off limits.
- **`$ord` member order.** Hoon's fork bunt does not follow declaration
  order: `*?(%lt %eq %gt)` is `%gt`, whereas `*?(%lt %gt %eq)` is `%eq`.
  `$ord` is declared in the latter order so that a bunted comparison reads
  as "equal" rather than "greater than". Do not reorder the members.
