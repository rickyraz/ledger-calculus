# Claims

Only claims from the proposal (`docs/ledger-calculus.md`) have a counterpart in
this repo. All statuses below have been checked with `dune build`; there is no
`Admitted` or `Axiom`.

| Claim in the proposal | Rule (`rules.md`) or lemma | File | Status |
|-----------------------|----------------------------|------|--------|
| §11 Logical reading: `submit : A ⊸ ◇ₖA` | rule `submit` | `docs/rules.md`, `theories/Sequent.v` | present as a rule |
| §11 Logical reading: `await`, from A, Δ ⊢ ◇ⱼC infer ◇ₖA, Δ ⊢ ◇ₖ₊ⱼC | rule `await` | `docs/rules.md`, `theories/Sequent.v` | present as a rule (graded lax) |
| §11 Logical reading: `cancel`, from ◇ₖ(R ⊗ (X ⊕ 1)), Δ ⊢ C infer ◇ₖ(R ⊗ X), Δ ⊢ C | rule `cancel`, lemma `cancel_admissible` | `docs/rules.md`, `theories/Sequent.v`, `theories/Examples.v` | present as a rule; resource R stays inside the future; derivable from `submit`, `await`, and `cut` |
| §11 "In this logic ◇ₖA ⊢ A is not derivable"; §12 "◇ₖA cannot become A without await" | `dia_not_elim` | `theories/Examples.v` | proved for every A without ◇; the restriction is necessary (`dia0_dia`) |
| §11 Curry-Howard requirement 1: sequent calculus with rules that can be justified without mentioning programs | `docs/rules.md` | `docs/rules.md`, `theories/Sequent.v` | present, for the fragment 1, ⊗, ⊸, ⊕, ◇ₖ |
| §11 Basis and steps, step 1: "add cancel rules to linear futures and prove cut elimination" | `cut_admissible` | `theories/CutElim.v` | proved (cut admissibility, not cut elimination as execution), without cost semantics and without adjoint modes |
| §11 Conjecture (1): cut elimination holds | `cut_admissible` | `theories/CutElim.v` | only the "holds" part, for this fragment; "corresponds to asynchronous I/O execution" is not yet formalized |
| §11 Logical reading: `free : A ⊸ 1`, free only accepts A | hypothesis `free` in `sanity_submit_cancel_await_free` | `theories/Examples.v` | sanity check only, not a result; the goal is ◇ₖ1 because await is lax |
