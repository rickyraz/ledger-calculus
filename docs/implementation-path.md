# Implementation path for ZBeam

Decision record, 2026-11-11. Status: accepted by the repository owner.

This file answers one question: once the logic in this repository says
something useful, how does it reach ZBeam code? It records the decision and the
conditions under which it would be revisited. It does not describe anything
that exists yet; this repository still contains no Zig code.

## Decision

Two steps, in this order:

1. **`comptime` wrappers in Zig.** Types such as `Owned(T)` and `InFlight(T)`,
   declared in user code without changing the language. The proposal already
   lists this in its table of Zig features.
2. **A separate checker.** A tool that reads Zig code and rejects programs that
   break the token protocol. This is phase 4 of the roadmap (README section 8).

Not chosen: a fork of the Zig compiler, and a new language with its own
compiler.

This confirms what the proposal already says in its section on Zig: `comptime`
cannot read the body of a function, so the checker cannot be an ordinary
library; the solution is an external checker with annotations as `comptime`
wrapper types, for a subset of Zig, and "the binary is still compiled by the
ordinary Zig compiler". The record exists because a custom compiler was
considered on 2026-11-11 and rejected.

## The options that were compared

| # | Option | What it can enforce | Cost |
|---|--------|---------------------|------|
| 1 | `comptime` wrappers | The shape of the protocol: which operations exist on which state. Not "exactly once". | Low |
| 2 | Separate checker | The full discipline, including linear use, as far as the checker is sound. | Medium |
| 3 | Fork of the Zig compiler with an extra pass | Same as 2. | High; must follow every Zig release |
| 4 | New language and compiler | Same as 2. | Highest; loses the Zig ecosystem |

## Why not a custom compiler on LLVM

The guarantees studied here are decided before code generation. "A token is
awaited exactly once" and "`free` is legal only after the await" are properties
of the program text. LLVM starts after that point and has no notion of
ownership. A new back end therefore adds cost without adding any guarantee.
What is needed is a checker in front of the existing Zig compiler.

Option 4 becomes reasonable only if some property of Zig makes the checking
impossible. No such property has been found.

## What each step needs from the logic

Step 1 needs only the state machine: Owned, InFlight, CancelRequested,
Completed, Cancelled. Candidate C in `experiments/` gives a candidate for it
(`Tok Fly`, `Tok Cnc`, `tok_await`, `tok_cancel`). Step 1 can start as a ZBeam
experiment before the logic is final, with the understanding that the wrappers
will change when the rules change.

Step 2 needs more than this repository has:

- A term language. A checker checks programs, and the logic currently has
  formulas and rules but no programs (README section 5, "Not yet done").
- A fixed set of rules. Candidate C is not final; its kernel is a hypothesis
  and the two-mode design it points to is untested (`experiments/README.md`).
- A statement of what the checker guarantees. That the checker is faithful to
  the rules is a theorem of its own. The proposal calls it adequacy and makes
  it the gate of phase 1. Without it the checker is still a useful bug finder,
  but "proved safe" does not transfer to ZBeam code.

## Consequence for the design of v2

"Can this be checked mechanically, on Zig code, without manual proofs?" is now
one of the criteria for choosing the rules of v2. A discipline of linear
resources plus a small state on each token is a good sign for that criterion;
a rule that needs a search or a global analysis would be a bad one.

## When to revisit

- Step 1 turns out unable to express even the state machine in Zig.
- A property of Zig is found that blocks step 2, for example a construct that
  hides ownership from any analysis and cannot be excluded from the checked
  subset.
- The term language, once designed, differs from Zig so much that checking Zig
  code against it is no longer meaningful.

## Not verified

These statements come from general knowledge and were not checked when this
record was written:

- How far `comptime` can enforce the protocol in current Zig.
- The stability of Zig's internal representations (ZIR, AIR) that phase 4
  plans to read.
- The current state of `std.Io` in Zig 0.17.
