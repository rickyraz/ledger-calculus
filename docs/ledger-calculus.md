# Ledger Calculus — Programs as a Resource Ledger

Oct 30, 2026 · @Ricky Raihan Azhari

## Summary

Ledger Calculus is a research program, not an established theory. The idea: every program is treated as a ledger entry. Values, ownership, protocols, effects, and costs are recorded in a single derivation, and every composition must "balance".

The name summarizes its moral axiom: no resource without origin, no effect without a record, no cost outside the books. Its core calculus is called λ-Ledger.

The intended contribution is not a new piece of theory. The pieces already exist in the Iris and resource-analysis ecosystems. The goal is to unite those pieces into a single judgment that can be inferred for Zig, a language with explicit allocation and I/O. ZBeam serves as the first user and feasibility proof.

## 1. Problem

Today every question about a program is answered by a different tool, even though the answers depend on each other.

| Tool | Question answered |
|------|-------------------|
| Type checker | Are the types correct? |
| Effect system | Does the program perform I/O, state, or throw? |
| Borrow checker | Who owns the resource? |
| Verifier | Is the algorithm correct? |
| Race detector / model checker | Is the concurrency safe? |
| Profiler | How expensive is execution? |

An example where all layers collide:

1. A task starts an async read and hands over a buffer.
2. The task is cancelled.
3. Cleanup frees the buffer.
4. The kernel is still writing to that buffer, and then a late completion arrives.

This is simultaneously a problem of correctness, ownership, concurrency, cancellation effects, temporal memory safety, and the cost of retaining resources. No single tool in the table can catch it alone. Ledger Calculus aims to give one specification for all of it.

## 2. Position relative to existing research

Most Ledger components have already been solved separately, and the Iris ecosystem already covers three of the five. The remaining gap is narrow but real.

| Component | Existing work | Already covered | Not yet covered |
|-----------|---------------|-----------------|-----------------|
| Concurrent state & ownership | Iris (Jung et al., ESOP 2017; JFP 2018) | Higher-order separation logic, invariants, ghost state | Interactive manual proofs in Rocq |
| Costs in separation logic | Time credits & time receipts in Iris (Mével, Jourdan, Pottier, ESOP 2019) | Upper bound on time as a logical resource | One dimension (time), still manual |
| Effect handlers | Hazel (de Vilhena & Pottier, POPL 2021) | Reasoning about handlers in Iris | One-shot continuations only, no costs |
| Message-passing protocols | Actris (Hinrichsen, Bengtson, Krebbers, POPL 2020) | Dependent separation protocols + functional correctness | No costs |
| Automatic resource bounds | AARA / RaML (Hoffmann et al.) | Polynomial bound inference via LP | Limited effects and concurrent state |
| Protocols + costs | Resource-aware session types (Das, Hoffmann, Pfenning, LICS 2018); Nomos (CSF 2021) | Work and span for message-passing processes | No shared memory and handlers |
| Quantitative grades | QTT (Atkey, LICS 2018), Idris 2, Granule (ICFP 2019) | Usage and grades in the type system | No program logic for concurrency |

The gap is threefold:

1. There is no single judgment that contains ownership, protocols, effects, correctness, and cost at once.
2. Multi-dimensional costs under concurrency (especially peak memory) do not yet have sound, scheduler-independent composition rules.
3. Automation vs expressiveness: Iris is expressive but manual, while AARA is automatic but narrow. There is no layered system connecting the two in a single semantic model.

Consequently, the most realistic strategy is to build on top of Iris (using time credits, Hazel, and Actris as foundations), rather than creating a new logic from scratch.

## 3. Shape of the judgment

One ledger entry records what goes in, what comes out, and how much it costs:

$$
\Gamma;\ \Delta \vdash e : A \dashv \Delta' \quad \{P\} \rightsquigarrow \{Q\} \quad !\,\varepsilon \quad @\,\kappa
$$

- Γ: ordinary context, may be used repeatedly.
- Δ and Δ': linear resources before and after execution.
- A: result type.
- P and Q: logical precondition and postcondition.
- ε: effects that may occur, as elements of an effect quantale (order matters).
- κ: cost upper-bound vector.

Example for a completion-queue-based async read:

```
read(fd, buf, n) : Result(usize)

Precondition:   fd is open; buf is owned by the task; len(buf) ≥ n
Ownership:      buf → InFlight(token)          (no longer owned by the task)
Effects:        KernelIO · MaySuspend · MayCancel
Cost:           W ≤ a·n + b
                SQE ≤ 1, CQE ≤ 2               (completion + cancel ack)
                M_retained ≤ n + c
Postcondition:  token completed → buf returns to the task
```

Costs are counted in submission/completion queue entries, not in syscalls, because submissions can be batched. The type `Result(usize)` alone does not say who owns the buffer, whether the operation can be cancelled, or when the buffer is safe to free.

## 4. Central hypothesis

> **Ledger Hypothesis.** For a subset of systems languages with explicit effects, structured concurrency, and linear resources, there is one semantic model in which four levels of checking are sound at once, and component specifications can be composed without opening their implementations.

A previous version claimed the whole system was decidable. That is impossible if functional correctness is also checked (Rice, 1953). So decidability is split by level:

| Level | What is checked | Status | Programmer burden |
|-------|-----------------|--------|-------------------|
| 0 | Types, linear ownership, protocol state, effect rows | Decidable, automatic | None |
| 1 | Cost bounds κ | Sound, incomplete; inference via LP à la AARA | Annotations for non-structural recursion |
| 2 | Functional correctness P ⇒ Q | Verification conditions to SMT; semi-decidable | Loop invariants, lemmas |
| 3 | Properties beyond automation | Interactive proofs in Rocq over the Iris model | Manual proofs |

What is promised is not "the system can always prove everything". What is promised: anything that passes at any level is genuinely valid against the same model, and higher levels can be used only for the parts of the code that need them.

## 5. Algebraic structure

Ledger uses four structures. Each already has mature theory, and what is new is only how the four are unified.

| Structure | Records | Form | Foundation |
|-----------|---------|------|------------|
| Refinement / dependent types | Value correctness | sort(xs) : { ys \| sorted(ys) ∧ perm(xs, ys) } | Liquid types, Iris |
| Separation algebra | Ownership | R ∗ S; no R ⊢ R ∗ R | Iris, QTT |
| Effect quantale | Sequential effects | Read(fd) · Write(log) · MayCancel | Gordon (ECOOP 2017), algebraic effects |
| Cost vector | Cost | κ = (W, S, M, A, N) | AARA, time credits |

Cost components: W total work, S span (critical path), M peak memory, A number of allocations, N number of messages or queue entries.

### Cost composition rules

W and S follow the standard rules:

$$
W(P;Q) = W(P) + W(Q) \qquad S(P;Q) = S(P) + S(Q)
$$

$$
W(P \parallel Q) = W(P) + W(Q) \qquad S(P \parallel Q) \le \max(S(P), S(Q)) + c_{\text{sync}}
$$

Peak memory was initially left open. The fix: also record R, the memory still retained after the program finishes. With that there is a rule sound for any scheduler:

$$
M(P;Q) \le \max\bigl(M(P),\ R(P) + M(Q)\bigr) \qquad M(P \parallel Q) \le M(P) + M(Q)
$$

That parallel rule is pessimistic, but it does not depend on the scheduler. Tighter bounds are allowed only when the schedule is restricted, for example κ(e, σ) for a particular scheduler class σ.

## 6. Basic laws

These are not "axioms of nature". They are laws the algebraic structure must satisfy, then proved as metatheorems. The last column records the parts fixed from the previous version.

| # | Law | Formula | Note |
|---|-----|---------|------|
| 1 | Identity | skip ; g = g ; skip = g | Cost of skip = 0 |
| 2 | Associativity | (g₁ ; g₂) ; g₃ = g₁ ; (g₂ ; g₃) | Compiler may regroup freely |
| 3 | Resource conservation | Δ = Δ₁ ⊎ Δ₂ for P ∥ Q | Resources are split, or shared through a proved invariant |
| 4 | Frame | {P} e {Q} ⟹ {P ∗ R} e {Q ∗ R} | Core of separation-logic modularity |
| 5 | Effect ordering | Lock · Write ≠ Write · Lock | Commute only with a proof of noninterference |
| 6 | Choice bound | ε(if) = ε_b · (ε₁ ⊔ ε₂); κ(if) ≤ κ_b + max(κ₁, κ₂) | Fixed: the cost and effect of evaluating condition b are counted too |
| 7 | Parallel noninterference | res(P) ∩ res(Q) = ∅, or shared access under an invariant | ∥ is commutative only up to observational equivalence |
| 8 | Handler homomorphism | H(e₁ ; e₂) = H(e₁) ; H(e₂); κ(H(e)) ≤ Φ_H(ε(e), κ(e)) | Fixed: only for deep handlers with one-shot (linear) continuations |
| 9 | Monotonic refinement | P ⇒ P′, Q′ ⇒ Q, ε′ ⪯ ε, κ′ ⪯ κ | An implementation may promise something stronger |

The restriction in law 8 is deliberate. Multi-shot continuations can duplicate linear resources and multiply costs. Following Hazel, λ-Ledger treats continuations as linear resources. Multi-shot is allowed only if the continuation captures no linear resource.

## 7. Metatheorems

Syntax and typing rules are not enough. This calculus is only worthwhile if the following results are proved and mechanized.

1. **Adequacy.** A derivation in the logic guarantees behavior in the operational semantics. This is the master theorem, and the others are derived from it, as in Iris.
2. **Preservation.** If e → e′, then Spec(e′) ⪯ Spec(e).
3. **Progress.** Programs do not get stuck, except on blocking or suspension declared in ε.
4. **Ownership safety.** Linear resources are not used after being moved or freed.
5. **Protocol fidelity.** Messages and operations follow the protocol state.
6. **Race freedom.** No illegal concurrent access to the same resource.
7. **Cost soundness.** If κ(e) ≤ f(n) is derived, then every execution in the model satisfies that bound.
8. **Contextual refinement.** No valid context can observe a specification violation.
9. **Compiler preservation.** Compilation preserves safety, observable effects, protocols, and the cost relation cost_machine ≤ a · cost_source + b.

## 8. Target: Zig, with ZBeam as feasibility proof

Ledger has the most impact when installed at the language level, not in a single program. The target is Zig: one contract in `Allocator` and `std.Io` applies to every program that uses it.

### Why Zig

Zig has no hidden control flow or allocation. As a result, most ledger entries are already visible directly in the code.

| Zig feature | Ledger component | Meaning |
|-------------|------------------|---------|
| `Allocator` as explicit parameter | Cost A, M + ownership | Every allocation has a clear origin |
| `std.Io` as explicit parameter | Effect handler | Threaded and evented backends are handlers; law 8 applies: same behavior, different cost |
| Error union + `try` | Exception effect | Error paths are visible in the type |
| `defer` / `errdefer` | Effect ordering and cleanup | Can prove every allocation is freed on all error paths |
| `comptime` | Specification as a type | Wrappers such as `Owned(T)` and `InFlight(T)` can be declared without changing the language |

### Gap: ownership is not in the type system

Zig has neither ownership nor linearity. Pointers are freely aliased, values can be copied, and safety checks run only at runtime in Debug/ReleaseSafe. `comptime` also cannot read the body of a function, so the checker cannot be an ordinary library.

The solution is an external checker that reads ZIR/AIR, with annotations as `comptime` wrapper types. The checker applies only to a subset of Zig: no unrestricted `@ptrCast`, no inline asm, and no `@intToPtr` in verified code. The binary is still compiled by the ordinary Zig compiler.

### Core contracts

1. **Allocator.** Memory may only be freed by the allocator that allocated it. `arena.reset()` invalidates all its descendant pointers.
2. **Futures from `std.Io`.** Every future must be awaited or cancelled exactly once (linear resource). A handed-over buffer only returns after the future completes.
3. **Leaks on error paths.** `errdefer` plus ownership rules prove that there are no leaks even when an error appears in the middle of a function. Today this is detected only at runtime by `std.testing.allocator`.
4. **Std cost contracts.** For example `ArrayList.append`: amortized O(1) work, allocations ≤ 1. User program bounds are assembled from these contracts.

### Position

Rust already has a formal foundation (RustBelt, on top of Iris) and several mature verifiers (Verus, Prusti, Creusot). Zig does not yet have a RustBelt counterpart, but that does not mean the space is empty:

- CLR (Checker for Lifetimes and other Refinement types) analyzes AIR to bring Rust-equivalent memory-safety guarantees to Zig. It uses a Zig compiler fork that forwards AIR to an external plugin.
- Zirakzigil adds contracts, refinement types, an ownership backstop, and an SMT verifier on top of the standard Zig compiler, without new syntax.
- zig-spec is the official effort for mechanized Zig specifications, but it has only just begun.

So the "external checker over AIR" approach already has prior art. Ledger's remaining contribution is threefold: (1) costs, effects, and protocols, not just lifetimes; (2) the `std.Io` contract and its futures; (3) soundness proved foundationally in Iris. CLR is a candidate basis for phase 4, not a competitor.

### Feasibility proof: ZBeam

ZBeam is used as the first user and feasibility proof because its invariants are already explicit in the design, though not yet formal. ZBeam is a native Erlang Distribution peer in Zig 0.17, without tracing GC, with explicit ownership. Its status is MVP: the I/O implementation is still blocking TCP framing, and io_uring plus arena ownership are still marked "research only".

The ZBeam README also notes that OS process boundaries do not isolate actors from each other inside ZBeam. That means ownership discipline is the only isolation. That is why Ledger is relevant here.

#### Existing invariants and their ledger form

| ZBeam invariant (now) | Ledger component | Specification form |
|-----------------------|------------------|--------------------|
| Mailbox bounded | Cost M, A | M_mailbox ≤ k · frame_max for capacity k |
| Demand-gated read: demand is reserved before read, without frame prefetch | Protocol + ownership | read : Demand ⊸ Frame; one demand token per frame |
| ETF decode produces an owned copy, with an aggregate allocation bound | Ownership + cost A | The decoded result term does not borrow the input buffer; A ≤ limit |
| M2c owner: one call per worker, uncertain work is never replayed | At-most-once protocol | Admitted → Sent → (Replied \| Uncertain); Uncertain is terminal, with no Retry transition |
| Connection table fixed at 64 slots | Resource conservation | 64 slot tokens in Δ; no slot without origin |
| Cooperative stop/join; CPU-bound handlers are not preempted | Effect + cost W | See below |

The last row gives a concrete insight. Because cancellation is cooperative, the W bound on a handler is also a stop-latency bound. Without κ, the specification can only say "stop will happen at the next yield point". With κ, it can say "stop happens within ≤ W_handler steps".

#### io_uring protocol + arena ownership

This is where Ledger is most useful, because io_uring cancellation bugs are not caught by ordinary types. Per-operation buffer protocol:

```
Owned ──submit──▶ InFlight ──CQE(result)──▶ Completed
                     │
                   cancel
                     ▼
              CancelRequested ──CQE(-ECANCELED)──▶ Cancelled
                     │
                     └──CQE(result) arrives first──▶ Completed
```

Rules that must be proved:

1. `free(buf)` is legal only in `Completed` or `Cancelled`, not when `cancel()` is called.
2. From `CancelRequested`, the operation can still complete successfully. Both branches must be handled.
3. Resetting an arena is legal only if there is no `InFlight` token originating from that arena. This is a new rule that appears because ZBeam plans to use arenas: one `reset()` can free many buffers at once.
4. Per-operation costs: SQE ≤ 1, CQE ≤ 2, M_retained ≤ n + c until the token completes.

From one derivation, ZBeam gets a guarantee of no use-after-free, cancellation that does not leak ownership, late completions that remain safe, and retained memory with a bound.

This buffer protocol is not specific to ZBeam. It is an instance of contract 2 (the `std.Io` future) for the `io_uring` backend, so the same proof can be reused by other Zig programs.

## 9. Hardest obstacles

These six obstacles determine whether Ledger can be used, not merely proved.

| Obstacle | Why it is hard | Solution direction |
|----------|----------------|--------------------|
| Effect interaction | state + exception ≠ exception + state; meaning depends on handler order | Non-commutative effect quantale; handler order goes into ε |
| Multi-shot continuations | Duplicate linear resources and costs | Linear continuations by default (law 8) |
| Scheduler-dependent costs | Peak memory, latency, and contention change per schedule | Pessimistic scheduler-independent bounds; κ(e, σ) when the schedule is restricted |
| Correctness vs performance | Locks and copies add both safety and cost | κ makes the price of safety visible, not hidden |
| Abstraction hides cost | Modular interfaces hide implementations | Cost contract: the interface exposes a symbolic cost function, not code |
| Target language without annotations | Zig has no ownership or linearity in types, and `comptime` cannot read function bodies | External checker over ZIR/AIR, annotations as `comptime` wrapper types, for the subset without unrestricted `@ptrCast` and inline asm |

There is one risk specific to the Zig target: the language is not yet 1.0, and ZIR/AIR change with every release. The checker must be pinned to one Zig version per release, and the `Allocator` / `std.Io` contracts must be written against their interfaces, not their internal details.

## 10. Success criteria and roadmap

Ledger is considered successful if there is a core calculus, semantics, a mechanized soundness proof, an automatic level 0–1 checker for a Zig subset, and ZBeam passes that checker. Each phase has a measurable gate.

1. **Phase 1 — sequential λ-Ledger.** Ownership, effects, and costs (W, A) mechanized in Rocq on top of Iris and time credits.
   Gate: adequacy theorem proved.
2. **Phase 2 — protocols, concurrency, and the ZBeam model.** Add Actris-style protocols and S, M, N costs.
   Gate: ZBeam's demand-gated mailbox model and at-most-once M2c protocol verified.
3. **Phase 3 — `Allocator` and `std.Io` contracts.** Contracts written and proved for one allocator (arena) and two Io backends.
   Gate: both Io backends proved behaviorally equivalent and differing only in cost.
4. **Phase 4 — Zig checker over ZIR/AIR.** Level 0–1 inference for a Zig subset.
   Gate: ZBeam mailbox/dispatcher modules pass without manual proofs, and leaks on `errdefer` paths in a synthetic test suite are all caught.
5. **Phase 5 — io_uring + arenas in ZBeam.** Buffer protocol and arena reset rules applied.
   Gate: cancellation-safe read proved, and existing ZBeam SIGKILL/nodedown tests still pass.

The final shape targeted for programmers:

```zig
// API sketch, not yet available. The specification is attached next to the
// function; signature and body of readFrame are unchanged.
pub const readFrame_spec = ledger.spec(readFrame, .{
    .ownership = .{ .buf = .moved_then_returned },
    .effects = .{ .kernel_io, .may_cancel },
    .work = ledger.linear("buf.len"),
    .alloc = 0,
    .cancel = .safe,
});
```

The checker then produces a proof certificate, effect manifest, and resource bound. The binary is still produced by the ordinary Zig compiler.

## 11. Fundamental direction: cancellable linear futures

To be on par with Curry–Howard, Ledger must start from logic, not from a specification system. The core candidate is **cancellable linear futures**: linear futures that can be cancelled without releasing their resources.

### Curry–Howard requirements

1. The logic stands on its own: a sequent calculus with rules that can be justified without mentioning programs.
2. Cut elimination equals execution.
3. Important properties (deadlock freedom, use-after-free freedom, resource bounds) are corollaries of cut elimination, not proved separately.
4. There is a categorical model.

Sections 3–10 do not yet satisfy all four. This section is the path to achieving them.

### Prior art

| Idea | Work | Status |
|------|------|--------|
| Linear futures from Curry–Howard adjoint logic | Back to Futures (Pruiksma & Pfenning, JFP 2022) | Exists; A ⊸ ◇A is essentially a linear future |
| ◇ as "eventually" | Fair Reactive Programming (Cave et al.); Lively RaTT (Bahr et al., POPL 2021) | Exists, for values that change over time, not resources |
| Resource safety + exceptions via Curry–Howard | Curry-Howard for destructors (Congard, Munch-Maccagnoni, Douence, 2025) | Exists; borrowing is mentioned as an open problem |
| Borrowing semantics | From Linearity to Borrowing (OOPSLA 2025) | Exists, for lexical lifetimes, without asynchronous third parties |
| Cancellable linear futures without releasing resources | — | Not found |

In practice, the problem is real and has not been solved at the logic level. uringscope (2026) names io_uring buffer-ownership contract checking as a gap that has not been filled. withoutboats concludes that the kernel must own the buffer. rustfs-uring enforces the same rules through an orphan table and acceptance tests, not through logic.

### Logical reading

| Rule | Reading |
|------|---------|
| submit : A ⊸ ◇ₖA | hand over a resource, receive a promise back in ≤ k steps |
| await : ◇ₖA ⊸ A | the only way to get the resource back |
| cancel : ◇ₖA ⊸ ◇ₖA | cancel is a protocol action, not a destruction |
| free : A ⊸ 1 | free only accepts A |

This logic has no rule ◇A ⊢ A other than through await. As a result, use-after-free on cancellation is not a bug the checker catches. It is a proof that cannot be derived.

### Conjecture

> There is a graded adjoint logic with a loan modality ◇ₖ and a cancel rule on top of it, such that (1) cut elimination holds and corresponds to asynchronous I/O execution, (2) normalization length is bounded by the grade, and (3) deadlock freedom, use-after-free freedom, and a bound on retained memory are corollaries of cut elimination.

### Basis and steps

The basis is the adjoint logic of Pruiksma & Pfenning. That logic already has Curry–Howard, concurrency, and linear futures, and cost grades come from the same research family (Rast).

1. **Logic.** Add cancel rules to linear futures and prove cut elimination.
2. **Grades.** Add ◇ₖ with Rast-style costs, then prove the normalization-length bound.
3. **Term assignment.** λ-Ledger is derived from proofs, not designed separately.
4. **Categorical model.** Find a structure that interprets ◇ₖ and cancel.
5. **Down to practice.** The `std.Io` contracts (section 8) and the ZBeam buffer protocol become instances of the term language, not axioms.

If successful, the result also answers part of the open problem of Congard et al. for the asynchronous borrowing case.

### Risks

- The full contents of Back to Futures have not been read. The claim that the paper does not model cancellation is still a conjecture.
- The cancellation literature in session types has not been re-reviewed. Some cancel rules may already exist there.
- This is pure logic research. Cut elimination with cancel rules may fail to hold, or may be too weak to capture real I/O cancellation.

## 12. Position map: Fil-C, Zig, and ZBeam

The three sit on different axes. Fil-C secures code through the runtime, Zig is where contracts live, and ZBeam is the first instance. Ledger targets the only quadrant that, from the search so far, is still empty: static proofs for protocols and costs.

*Figure: position map · assurance method × assurance coverage.* The horizontal axis is the assurance method, the vertical axis is assurance coverage. Dashed arrows show the movement of Zig and ZBeam if the conjecture in section 11 is proved. Fil-C stays where it is and becomes the trust boundary for C code.

### What is proved, and through what

| | Current guarantee | If the conjecture is proved | Proved through | Still unproved |
|-|-------------------|-----------------------------|----------------|----------------|
| Fil-C | Full memory safety for unmodified C/C++; bounds checks, InvisiCaps, and GC; violations become panics; roughly 4x overhead in the worst case | Fil-C itself is not proved by Ledger. C code compiled by Fil-C becomes a component with a runtime-guaranteed memory contract | Assumptions (axioms) at the FFI boundary: the memory contract is trusted from Fil-C, and protocol contracts at that boundary are written as assumptions | Protocols and costs of C code; correctness of the Fil-C runtime and GC |
| Zig (language) | Runtime safety checks in Debug/ReleaseSafe; no ownership in types; leaks detected by `std.testing.allocator` during tests | `Allocator` and `std.Io` contracts: free only from A; futures awaited or cancelled exactly once; buffers return only through await; Io backends behaviorally equivalent; cost bounds | Contracts derived as instances of the term language (section 11, step 5); user code checked by the checker over AIR (section 8, phase 4); checker soundness from adequacy (section 7) | Code outside the subset (unrestricted `@ptrCast`, inline asm); business logic |
| ZBeam | Design invariants (bounded mailbox, demand-gated read, at-most-once M2c, 64-slot table) maintained through code and SIGKILL/nodedown tests; io_uring not yet present | No frame prefetch; Uncertain terminal in M2c; no use-after-free on cancel; arena reset only without InFlight tokens; stop latency ≤ W handler | Mailbox and M2c protocols verified as models (phase 2); cancellation safety is a corollary of cut elimination, because ◇ₖA cannot become A without await; stop bound from cost grades | Remote Erlang peer behavior; cookie security and lack of TLS (noted in the README); CPU-bound handlers without a W bound |

Fil-C and Ledger do not compete. The proposed Fil-C ABI in Zig opens the possibility of two layers: linked C code is kept safe by Fil-C at runtime, while annotated Zig code is proved by Ledger at compile time.

## 13. Final formulation

> Can the values, state, ownership, concurrency, effects, protocols, and costs of a program be recorded as a single ledger entry whose composition follows simple laws?

The hypothesis: yes, for a controlled subset of systems languages, if correctness is viewed as state transition, ownership as linear resources, effects as grades, concurrency as partial-order interaction, and costs as quantities in the same algebra.

The paradigm shifts from programs as functions to programs as verified resource transformers. The correspondence below is a working analogy, not a theorem. It only deserves the name "Curry–Howard" if the conjecture in section 11 is proved.

| Program side | Logic side |
|--------------|------------|
| Program | Proof |
| Resource | Linear proposition |
| Protocol | Concurrent proof |
| Effect | Algebraic operation |
| Cost | Quantitative grade |
| Composition | Proof composition |

## References

Each reference links to the authors' PDF, arXiv, or the publisher's DOI.

- [ZBeam — README, MVP status and non-goals](https://github.com/rickyraz/zbeam)
- Krebbers et al. [The Essence of Higher-Order Concurrent Separation Logic](https://iris-project.org/pdfs/2017-esop-iris3-final.pdf), ESOP 2017
- [Lecture Notes on Iris](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)
- Jung et al. [Iris from the Ground Up](https://cs.au.dk/~birke/papers/iris-journal.pdf), JFP 2018
- Mével, Jourdan, Pottier. [Time Credits and Time Receipts in Iris](https://iris-project.org/pdfs/2019-esop-time.pdf), ESOP 2019
- de Vilhena, Pottier. [A Separation Logic for Effect Handlers](https://doi.org/10.1145/3434314), POPL 2021
- Hinrichsen, Bengtson, Krebbers. [Actris: Session-Type Based Reasoning in Separation Logic](https://doi.org/10.1145/3371074), POPL 2020
- Hoffmann, Hofmann. [Amortized Resource Analysis with Polynomial Potential](https://www.cs.cmu.edu/~janh/assets/pdf/HoffmannH10.pdf), ESOP 2010
- Hoffmann, Jost. [Two Decades of Automatic Amortized Resource Analysis](https://www.cs.cmu.edu/~janh/assets/pdf/HoffmannJ21.pdf), MSCS 2022
- Das, Hoffmann, Pfenning. [Work Analysis with Resource-Aware Session Types](https://arxiv.org/abs/1712.08310), LICS 2018
- Das et al. [Resource-Aware Session Types for Digital Contracts (Nomos)](https://arxiv.org/abs/1902.06056), CSF 2021
- Wadler. [Propositions as Sessions](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf), ICFP 2012
- Plotkin, Pretnar. [Handling Algebraic Effects](https://arxiv.org/abs/1312.1399), LMCS 2013
- Gordon. [A Generic Approach to Flow-Sensitive Polymorphic Effects (effect quantales)](https://doi.org/10.4230/LIPIcs.ECOOP.2017.13), ECOOP 2017
- Orchard, Wadler, Eades. [Unifying Graded and Parameterised Monads](https://arxiv.org/abs/2001.10274), MSFP 2020
- Atkey. [Syntax and Semantics of Quantitative Type Theory](https://doi.org/10.1145/3209108.3209189), LICS 2018
- Brady. [Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/abs/2104.00480), ECOOP 2021
- Orchard, Liepelt, Eades. [Quantitative Program Reasoning with Graded Modal Types (Granule)](https://doi.org/10.1145/3341714), ICFP 2019
- Rice. [Classes of Recursively Enumerable Sets and Their Decision Problems](https://doi.org/10.1090/S0002-9947-1953-0053041-6), Trans. AMS 1953

Comparisons and prior art (section 8):

- Jung et al. [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/), POPL 2018
- [Verus](https://github.com/verus-lang/verus)
- [Prusti](https://github.com/viperproject/prusti-dev)
- [Creusot](https://github.com/creusot-rs/creusot)
- [CLR: Checker for Lifetimes and other Refinement types for Zig](https://github.com/ityonemo/clr)
- [Zirakzigil](https://github.com/hotschmoe/zirakzigil)
- [zig-spec — Zig specification (informal and mechanized)](https://codeberg.org/ziglang/zig-spec)

Fundamental direction (section 11):

- Pruiksma, Pfenning. [Back to Futures](https://arxiv.org/abs/2002.04607), JFP 2022
- Cave, Ferreira, Panangaden, Pientka. [Fair Reactive Programming](https://www.cs.mcgill.ca/~acave1/papers/fair-reactive-long.pdf), POPL 2014
- Bahr, Graulund, Møgelberg. [Diamonds are not forever: Liveness in Reactive Programming with Guarded Recursion](https://arxiv.org/abs/2003.03170), POPL 2021
- Congard, Munch-Maccagnoni, Douence. [Linear Effects, Exceptions, and Resource Safety: a Curry-Howard Correspondence for Destructors](https://arxiv.org/abs/2510.23517), arXiv 2025
- Marshall, Wagner, Li, Gierczak, Ahmed. [From Linearity to Borrowing](https://2025.splashcon.org/details/OOPSLA/176/From-Linearity-to-Borrowing), OOPSLA 2025
- Das, Pfenning. [Rast: A Language for Resource-Aware Session Types](https://lmcs.episciences.org/7024/pdf), LMCS 2022
- [uringscope: Portable, Low-Overhead Observability for io_uring](https://arxiv.org/abs/2606.15137), arXiv 2026
- withoutboats. [Notes on io-uring](https://without.boats/blog/io-uring/)
- [rustfs-uring — cancel-safe io_uring read backend](https://docs.rs/rustfs-uring/)

Position map (section 12):

- [Fil-C — memory-safe C/C++](https://fil-c.org/)
- [InvisiCaps: The Fil-C Capability Model](https://fil-c.org/invisicaps)
- LWN. [Fil-C: A memory-safe C implementation](https://lwn.net/Articles/1042938/), October 2025
- [Fil-C ABI proposal — Zig issue tracker](https://codeberg.org/ziglang/zig/issues/36237)
