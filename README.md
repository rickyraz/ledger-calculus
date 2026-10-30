# ledger-calculus

Research artifact for Ledger Calculus: a small sequent calculus for
*cancellable linear futures*, with proofs in Rocq. This repo contains the theory
and proofs, not tooling.

The source of truth for terms, notation, claims, and references is the proposal
[`docs/ledger-calculus.md`](docs/ledger-calculus.md). The inference rules that
are formalized live in [`docs/rules.md`](docs/rules.md).

## 1. What this is

From the proposal's summary: Ledger Calculus is a research program, not an
established theory. The idea: every program is treated as a ledger entry:
values, ownership, protocols, effects, and costs are recorded in a single
derivation, and every composition must "balance". This repo only works on one
small piece of that program, namely the fundamental direction in section 11:
a logic for cancellable linear futures that can be cancelled without releasing
their resources.

## 2. Core conjecture

Quoted from section 11 of the proposal:

> There is a graded adjoint logic with a loan modality ◇ₖ and a cancel rule on
> top of it, such that (1) cut elimination holds and corresponds to
> asynchronous I/O execution, (2) normalization length is bounded by the grade,
> and (3) freedom from deadlock, freedom from use-after-free, and a bound on
> retained memory are corollaries of cut elimination.

This repo does **not** prove that conjecture. It only proves cut
admissibility for a much smaller fragment (see sections 3 and 5).

## 3. What is formalized in this repo

The fragment of intuitionistic linear logic with 1, ⊗, ⊸, ⊕, plus the modality
◇ₖ (k : nat) with three rules:

| Rule in `rules.md` | Form |
|--------------------|------|
| `submit` (◇ₖ-right) | Δ ⊢ A ⟹ Δ ⊢ ◇ₖA |
| `await` (◇ₖ-left, graded lax) | A, Δ ⊢ ◇ⱼC ⟹ ◇ₖA, Δ ⊢ ◇₍ₖ₊ⱼ₎C |
| `cancel` | ◇ₖ(R ⊗ (X ⊕ 1)), Δ ⊢ C ⟹ ◇ₖ(R ⊗ X), Δ ⊢ C |

In the `v0-baseline` version, `await` is an ordinary left rule, so ◇ₖA is
equivalent to A and the modality has no content. Now `await` is lax: the
content of a future can only be used if the goal is also a future, so
◇ₖA ⊬ A for A without ◇ (`dia_not_elim`).

This system is a **simplification** of the adjoint logic of Pruiksma & Pfenning
([Back to Futures](https://arxiv.org/abs/2002.04607)), not an instance of it:

- There is only one mode (linear). There is no mode hierarchy, no ↑/↓ shifts,
  and no mode that permits weakening or contraction.
- ◇ₖ is a primitive lax modality with its own rules, not the result of
  composing shifts like the future in adjoint logic.
- There is no term assignment, no operational semantics, and no
  concurrency. Cut admissibility here is a theorem about derivability, not a
  correspondence with execution.
- The grade k has proof-theoretic content: `await` adds the grades, and
  `dia_mono` shows that it behaves as an upper bound. The grade has no cost
  semantics yet; that will come with the cost rules in the next stage.

The linear context is a `list form`, with an explicit `exchange` rule (based on
`Permutation` from the Rocq stdlib). The derivability relation is `seq Δ C`,
without parameters.

Pure Rocq: stdlib only, no Iris, no third-party libraries, no `Axiom`.

## 4. Status

All lemmas are proved. There is no `Admitted` and no `Axiom`;
`Print Assumptions` for each theorem below prints
`Closed under the global context`.

| Lemma | File | Status | Depends on |
|-------|------|--------|------------|
| `identity` : ∀A, `[A] ⊢ A` | `Identity.v` | proved | ◇ₖ case: `await k` over `submit 0` |
| `perm_cons_split`, `perm_app_split`, `perm_front`, `perm_to_front` | `CutElim.v` | proved | stdlib `Permutation` |
| `ext`, `ext_refl`, the inversion lemmas `ext_*_inv`, `ext_cancel_step` | `CutElim.v` | proved | - |
| `dia_mono` : `Δ ⊢ ◇ⱼC`, `j ≤ n` ⟹ `Δ ⊢ ◇ₙC` | `CutElim.v` | proved | - |
| `cut_E` (induction on the right derivation) | `CutElim.v` | proved | permutation lemmas, `ext`, `dia_mono` |
| `cut_aux` (induction on formula size and the left derivation) | `CutElim.v` | proved | `cut_E` |
| `cut_admissible` : ∀A, `cut_stmt A` | `CutElim.v` | proved | `cut_aux` |
| `cut` (cut formula at the head) | `CutElim.v` | proved | `cut_admissible`, `ext_refl` |
| `dia_free_inv` (inversion invariant) | `Examples.v` | proved | - |
| `dia_not_elim` : A without ◇ ⟹ `¬ ([◇ₖA] ⊢ A)` | `Examples.v` | proved | `dia_free_inv` |
| `dia0_dia` : `[◇₀(◇ⱼB)] ⊢ ◇ⱼB` | `Examples.v` | proved | `identity` |
| `cancel_admissible` | `Examples.v` | proved | `cut`, `identity` |
| `sanity_submit_cancel_await_free` (sanity check, not a result) | `Examples.v` | proved | `cut` |

**◇ₖA ⊬ A.** `dia_not_elim` is proved for the cut-free system via the invariant
`dia_free_inv`: if the goal has no ◇ and every context formula has no ◇ or is
◇ at the head, then the context has no ◇ at all. Only `submit` and `await`
produce a ◇ goal, and `cancel` preserves ◇ at the head. Because
`cut_admissible` is proved, this result also holds for the system with cut.
The restriction "A without ◇" is necessary: `dia0_dia` shows
◇₀(◇ⱼB) ⊢ ◇ⱼB.

**Is `cancel` admissible from `submit` + `await`?** Yes, with cut.
◇ₖ(R ⊗ X) ⊢ ◇ₖ(R ⊗ (X ⊕ 1)) is derived with `await k` over `submit 0`
(grade k + 0 = k), then cut with the premise of `cancel`
(`cancel_admissible`, without using the `cancel` constructor). So cancel does
not add logical strength: every sequent derived with cancel is also derived
from submit, await, and cut. An honest note: `cut_admissible` is proved for
the system containing `cancel`. The statement "the system without the `cancel`
constructor derives the same sequents" needs cut admissibility for the system
without cancel; the proof is the same (the `cancel` cases in `cut_E` and
`cut_aux` only commute an existing cancel), but it has not been formalized as a
separate system.

## 5. Open

There is no `Admitted`. Cut admissibility proof strategy:

- Outer induction on the size of the cut formula on the left (`size A`,
  `cut_aux`).
- Inside it, structural induction on the left derivation `Δ₁ ⊢ A`. Left rules
  other than `await`, `cancel`, and `exchange` on the left commute directly.
- If the left derivation ends with a right rule, `id_atom`, or `await`, its
  premises are recorded in `rinfo`, and then structural induction is performed
  on the right derivation (`cut_E`). Structural induction on derivations
  replaces induction on derivation height.
- `await` on the left cannot commute directly, because the rule needs a goal of
  future shape. It is handled when the right derivation is principal on the cut
  formula with `await`: the cut is moved into the premise of the left `await`,
  and then `await` is applied again with grade (k₁ + j₁) + j = k₁ + (j₁ + j).
- The `submit`-versus-`await` case produces ◇ⱼC when ◇₍ₖ₊ⱼ₎C is needed;
  `dia_mono` raises the grade.
- The near-stuck point: `cancel` on the right replaces the cut formula
  ◇ₖ(R ⊗ X) with ◇ₖ(R ⊗ (X ⊕ 1)), which is larger, so induction on formula
  size fails. The solution: the cut formula on the right may be A' with
  `ext A A'` (A with some positive subformula X replaced by X ⊕ 1), and the
  induction measure remains the size of A on the left. `ext` deliberately does
  not enter the antecedent of ⊸, so the size does not grow in negative
  positions.
- Cut is formulated for a right context that is a permutation of `A', Δ₂`,
  so the `exchange` case does not get stuck.

Not yet done:

- A system without `cancel` as a separate inductive, to state "cancel does not
  add logical strength" without going through cut in the system that contains
  cancel (see section 4).
- Cut elimination as execution (term assignment), cost semantics for grades,
  normalization-length bounds, and a categorical model (section 11, steps 2
  through 4).

## 6. Position

[Back to Futures](https://arxiv.org/abs/2002.04607) (Pruiksma & Pfenning,
JFP 2022) already gives linear futures via Curry-Howard for adjoint logic; the
proposal notes that the claim "that paper does not model cancellation" is still
a conjecture because its contents have not been read in full. ◇ as
"eventually" already appears in
[Fair Reactive Programming](https://www.cs.mcgill.ca/~acave1/papers/fair-reactive-long.pdf)
(Cave et al.) and Lively RaTT
([Bahr et al., POPL 2021](https://arxiv.org/abs/2003.03170)), but for values
that change over time, not resources.
[Curry-Howard for destructors](https://arxiv.org/abs/2510.23517) (Congard,
Munch-Maccagnoni, Douence, 2025) gives resource safety plus exceptions via
Curry-Howard and mentions borrowing as an open problem. This repo is **not** a
new logic on par with those works, **not** a proof of the section 11
conjecture, and does **not** claim novelty for the ILL fragment with 1, ⊗, ⊸, ⊕
or for its cut admissibility; its contribution is only a small and honest
mechanization of the submit, lax await, and cancel rules as a starting point.

## 7. Relation to ZBeam

[ZBeam](https://github.com/rickyraz/zbeam) is a native Erlang Distribution peer
in Zig with explicit ownership, currently at MVP status; io_uring and arena
ownership are still marked "research only". The proposal uses it as the first
user and feasibility proof: the io_uring buffer protocol (Owned → InFlight →
Completed/Cancelled) is where the cancel rules here will be tested. ZBeam is a
future case study; its model will later live in
`theories/case_studies/zbeam/`. That folder does not exist yet, and this repo
contains no Zig code.

## 8. Roadmap

Summary of section 10 of the proposal:

1. Phase 1: sequential λ-Ledger (ownership, effects, W and A costs) in Rocq on
   top of Iris and time credits. Gate: adequacy proved.
2. Phase 2: Actris-style protocols, concurrency, S, M, N costs, and the ZBeam
   model. Gate: demand-gated mailbox and at-most-once M2c protocol verified.
3. Phase 3: `Allocator` and `std.Io` contracts for one allocator (arena) and two
   Io backends. Gate: both backends behave equivalently, differing only in cost.
4. Phase 4: Zig checker over ZIR/AIR, level 0-1 inference. Gate: ZBeam
   mailbox/dispatcher modules pass without manual proofs, and leaks on
   `errdefer` paths in a synthetic test suite are all caught.
5. Phase 5: io_uring and arenas in ZBeam. Gate: cancellation-safe reads
   proved, and existing SIGKILL/nodedown tests still pass.

This repo sits before those phases, at step 1 of section 11 ("add cancel rules
to linear futures and prove cut elimination"), for the fragment without cost
semantics and without adjoint modes.

## 9. Build

Versions used (from the development machine, Rocq Platform 2026.07.0 on
Windows): Rocq 9.1.0 (`rocq --version`), dune 3.21.0 (`dune --version`),
rocq-stdlib 9.0.0 (Rocq Platform 9.1~2026.01 package pick). dune also needs an
OCaml compiler on PATH; the development machine uses OCaml 4.14.2 from opam
(the same version as the Rocq Platform build).

```bash
dune build
```

On Windows with Rocq Platform, `dune` needs the Rocq Platform `bin` and
`ocamlc` on PATH, plus `OCAMLPATH` pointing to the Rocq Platform `lib`, for
example (Git Bash):

```bash
PATH="$HOME/Rocq-platform-9.1/bin:$PATH:$LOCALAPPDATA/opam/ledger/bin" OCAMLPATH="$HOME/Rocq-platform-9.1/lib" dune build
```

Without dune, files can be checked directly with Rocq:

```bash
cd theories && for f in Syntax Sequent Identity CutElim Examples; do rocq compile -Q . LedgerCalculus $f.v; done
```

CI (`.github/workflows/ci.yml`) uses the official `rocq/rocq-prover:9.1` image
via `coq-community/docker-coq-action`. There is no image tagged 9.1.0, so
`ledger-calculus.opam` accepts the 9.1.x series (`rocq-core >= 9.1.0 < 9.2.0`,
`rocq-stdlib >= 9.0.0 < 9.2.0`), which covers both the development machine and
the CI image.
