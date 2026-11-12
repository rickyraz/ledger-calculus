# Experiments: candidate cancel rules

Work in progress, not part of the `LedgerCalculus` theory in `theories/`.
Each file is self-contained (Rocq stdlib only) and defines its own copy of the
formulas and rules, so candidates can be compared without touching v1.

The question: v1's `cancel` is admissible, so it models nothing. Which cancel
rules are *not* admissible and still keep cut admissible?

| File | Candidate | Cut | Main lemma |
|------|-----------|-----|------------|
| `CandA.v` | `cancel_down`: ◇ₖ(R ⊗ X) becomes ◇ⱼ(R ⊗ (X ⊕ 1)), j ≤ k | **fails** | `cut_fails` |
| `CandB.v` | `cancel_any`: every ◇ₖA becomes ◇ⱼ(A ⊕ 1), j ≤ k | **fails** | `cut_fails` |
| `CandC.v` | in-flight token `Tok s k R X`, separate from ◇, with `tok_await` and `tok_cancel` | holds | `cut_admissible`, `cut` |
| `CandC_Tests.v` | negative and positive tests for candidate C | | see the table at the top of the file |

Why A and B fail:

- **A.** A future built by `await` over another future cannot be cancelled
  faster than the future it waits for. Counterexample:
  `◇₁b, b ⊸ (r ⊗ x) ⊢ ◇₀(r ⊗ (x ⊕ 1))`.
- **B.** Letting cancel fire on every future pushes the cancel back to the
  source, but then the rest of the linear context is stranded in the
  "cancelled" branch. Counterexample: `◇₁b, c ⊢ ◇₀((b ⊗ c) ⊕ 1)`. A composable
  cancel needs an affine continuation.

Candidate C has two switches, `seq sp cn`:

- `cn`: is `tok_cancel` present?
- `sp`: is there a right rule `spawn` for tokens? With `sp = false` tokens are
  abstract and can only come from hypotheses that stand for the kernel
  interface, for example `read : buf ⊸ Tok Fly 5 buf nres`.

Cut admissibility is proved for all four settings. The tests are proved for
`sp = false`; with `sp = true` the "no forged token" tests fail
(`spawn_fake_inflight`, `spawn_fake_cancelled`).

Known limits of candidate C, not addressed here:

- The kernel is a hypothesis, not a rule. With `sp = false` a token is never
  the principal formula of a right rule, so cut against a token is always a
  commutation or an identity. This says nothing yet about "cut elimination as
  execution".
- `tok_cancel` may pick any `j ≤ k`, including 0.
- Awaits are sequential, so grades add up; there is no parallel composition.
- No adjoint modes. Candidate B suggests where an affine mode would enter.

## Build

`dune build` at the repository root builds these files too. Without dune:

```bash
cd experiments && for f in CandA CandB CandC CandC_Tests; do rocq compile -Q . LedgerExp $f.v; done
```

Every `Print Assumptions` line must print `Closed under the global context`.
