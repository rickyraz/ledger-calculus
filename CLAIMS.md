# Claims

Only claims from the proposal (`docs/ledger-calculus.md`) have a counterpart in
this repo. All statuses below have been checked with `dune build`; there is no
`Admitted` or `Axiom`.

| Claim in the proposal | Rule (`rules.md`) or lemma | File | Status |
|-----------------------|----------------------------|------|--------|
| §11 Logical reading: `submit : A ⊸ ◇ₖA` | rule `submit` | `docs/rules.md`, `theories/Sequent.v` | present as a rule |
| §11 Logical reading: `await : ◇ₖA ⊸ A`, the only way to get the resource back | rule `await` | `docs/rules.md`, `theories/Sequent.v` | present as a rule, in graded lax form (A, Δ ⊢ ◇ⱼC ⟹ ◇ₖA, Δ ⊢ ◇₍ₖ₊ⱼ₎C), not ◇ₖA ⊸ A as stated; see README section 3 |
| §11 Logical reading: `cancel : ◇ₖA ⊸ ◇ₖA`, cancel is a protocol action, not a destruction | rule `cancel` | `docs/rules.md`, `theories/Sequent.v` | present as a rule, in the form ◇ₖ(R ⊗ (X ⊕ 1)), Δ ⊢ C ⟹ ◇ₖ(R ⊗ X), Δ ⊢ C; resource R stays inside the future |
| §11 "This logic has no rule ◇A ⊢ A other than through await"; §12 "◇ₖA cannot become A without await" | `dia_not_elim` | `theories/Examples.v` | proved for every A without ◇; the restriction is necessary (`dia0_dia`) |
| §11 Curry-Howard requirement 1: sequent calculus with rules that can be justified without mentioning programs | `docs/rules.md` | `docs/rules.md`, `theories/Sequent.v` | present, for the fragment 1, ⊗, ⊸, ⊕, ◇ₖ |
| §11 Basis and steps, step 1: "add cancel rules to linear futures and prove cut elimination" | `cut_admissible` | `theories/CutElim.v` | proved (cut admissibility, not cut elimination as execution), without cost semantics and without adjoint modes |
| §11 Conjecture (1): cut elimination holds | `cut_admissible` | `theories/CutElim.v` | only the "holds" part, for this fragment; "corresponds to asynchronous I/O execution" is not yet formalized |
| §11 Logical reading: `free : A ⊸ 1`, free only accepts A | hypothesis `free` in `sanity_submit_cancel_await_free` | `theories/Examples.v` | sanity check only, not a result; the goal is ◇ₖ1 because await is lax |
