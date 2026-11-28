# ledger-calculus

Rocq proofs for a small sequent calculus of *cancellable linear futures*: futures you can cancel while their resources stay held. The repo has theory and proofs, no tooling.

Terms, claims, and references come from the proposal, [`docs/ledger-calculus.md`](docs/ledger-calculus.md). The formalized rules are in [`docs/rules.md`](docs/rules.md), and [`CLAIMS.md`](CLAIMS.md) maps proposal claims to lemmas.

## Status

We prove cut admissibility for a small fragment. We do **not** prove the proposal's conjecture (section 11):

> There is a graded adjoint logic with a loan modality ◇ₖ and a cancel rule on
> top of it, such that (1) cut elimination holds and corresponds to
> asynchronous I/O execution, (2) normalization length is bounded by the grade,
> and (3) freedom from deadlock, freedom from use-after-free, and a bound on
> retained memory are corollaries of cut elimination.

## The system

Intuitionistic linear logic with 1, ⊗, ⊸, ⊕, plus ◇ₖ (k : nat):

| Rule | Form |
|------|------|
| `submit` | Δ ⊢ A ⟹ Δ ⊢ ◇ₖA |
| `await` | A, Δ ⊢ ◇ⱼC ⟹ ◇ₖA, Δ ⊢ ◇₍ₖ₊ⱼ₎C |
| `cancel` | ◇ₖ(R ⊗ (X ⊕ 1)), Δ ⊢ C ⟹ ◇ₖ(R ⊗ X), Δ ⊢ C |

`await` is lax: you can use a future's content only to build another future. So ◇ₖA ⊬ A for A without ◇.

Limits:

- `cancel` is derivable from `submit`, `await`, and cut, so it adds no strength and does not yet model cancellation.
- We have no terms, operational semantics, or concurrency. Cut admissibility here concerns derivability, not execution.
- Grades add up and act as upper bounds. They have no cost semantics.
- This simplifies the adjoint logic of Pruiksma & Pfenning: one linear mode, no shifts, and ◇ₖ as a primitive.

## Main results

No `Admitted`, no `Axiom`. `Print Assumptions` reports `Closed under the global context`.

| Lemma | Statement | File |
|-------|-----------|------|
| `identity` | [A] ⊢ A for every A | `Identity.v` |
| `cut_admissible`, `cut` | cut is admissible | `CutElim.v` |
| `dia_mono` | a grade can be raised | `CutElim.v` |
| `dia_not_elim` | ◇ₖA ⊬ A for A without ◇ | `Examples.v` |
| `dia0_dia` | ◇₀(◇ⱼB) ⊢ ◇ⱼB, so the restriction above is needed | `Examples.v` |
| `cancel_admissible` | `cancel` follows from the other rules and cut | `Examples.v` |

To prove that the system *without* the `cancel` constructor derives the same sequents, we still need cut admissibility for that system as a separate definition.

The one unusual step in the cut proof: `cancel` makes the cut formula larger. The relation `ext` (some positive subformula X becomes X ⊕ 1) handles it. See the header of [`theories/CutElim.v`](theories/CutElim.v).

## Experiments

[`experiments/`](experiments/README.md) tries three cancel rules that are not derivable. Two break cut. The third, an in-flight token separate from ◇, keeps cut and passes a list of negative tests. None of it is part of `theories/`.

## Next

Not done: term assignment, cut elimination as execution, cost semantics, a normalization bound, and a categorical model.

The longer roadmap (proposal section 10) targets [ZBeam](https://github.com/rickyraz/zbeam), a Zig project, and its io_uring buffer protocol. This repo has no Zig code. [`docs/implementation-path.md`](docs/implementation-path.md) records how the logic would reach that code.

## Related work

We claim no novelty for the linear logic fragment, its cut admissibility, or the shape of ◇ₖ.

- ◇ₖ is a graded lax modality: [lax logic](https://doi.org/10.1006/inco.1997.2627) (Fairtlough & Mendler, 1997), [parametric effect monads](https://doi.org/10.1145/2535838.2535846) (Katsumata, 2014).
- [Back to Futures](https://arxiv.org/abs/2002.04607) (Pruiksma & Pfenning, JFP 2022) gives linear futures through Curry-Howard. We have not read it in full.
- The same authors treat [cancellation on affine channels](https://arxiv.org/abs/1904.01290) (PLACES 2019).
- ◇ as "eventually" appears in [Fair Reactive Programming](https://www.cs.mcgill.ca/~acave1/papers/fair-reactive-long.pdf) and [Lively RaTT](https://arxiv.org/abs/2003.03170), for values that change over time.
- [Congard, Munch-Maccagnoni & Douence](https://arxiv.org/abs/2510.23517) (2025) cover resource safety with exceptions and leave borrowing open.

## Build

Tested with Rocq 9.1.0, rocq-stdlib 9.0.0, dune 3.21.0, and OCaml 4.14.2.

```bash
dune build
```

On Windows with Rocq Platform, put its `bin` and `ocamlc` on PATH and point `OCAMLPATH` to its `lib` (Git Bash):

```bash
PATH="$HOME/Rocq-platform-9.1/bin:$PATH:$LOCALAPPDATA/opam/ledger/bin" OCAMLPATH="$HOME/Rocq-platform-9.1/lib" dune build
```

Without dune:

```bash
cd theories && for f in Syntax Sequent Identity CutElim Examples; do rocq compile -Q . LedgerCalculus $f.v; done
```

CI uses the `rocq/rocq-prover:9.1` image.
