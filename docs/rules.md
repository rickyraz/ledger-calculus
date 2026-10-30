# Inference rules

This file is the source of truth for `theories/Sequent.v`. Each rule below has
exactly one constructor with the same name in `Sequent.v`, and vice versa.

## Formulas

```
A, B ::= p | 1 | A ⊗ B | A ⊸ B | A ⊕ B | ◇ₖA        (p atom, k : nat)
```

## Sequents

```
Δ ⊢ C
```

`Δ` is the linear context, written as a list of formulas. The order in the list
has no logical meaning; exchange is given as one explicit rule (`exchange`).
Left rules always work on the formula at the head of the list. A context that
is split is written `Δ₁, Δ₂` (list concatenation).

There is no weakening and no contraction. There is no cut rule; cut is a
theorem (`cut_admissible` in `CutElim.v`).

## Rules

### Identity and structural

```
  ─────────── id_atom
    p ⊢ p


    Δ ⊢ C      Δ is a permutation of Δ'
  ───────────────────────────────────────── exchange
    Δ' ⊢ C
```

`id_atom` is only for atoms. `A ⊢ A` for an arbitrary formula is a theorem
(`identity` in `Identity.v`).

### Unit 1

```
  ─────── one_R
    ⊢ 1


    Δ ⊢ C
  ─────────── one_L
   1, Δ ⊢ C
```

### Tensor ⊗

```
   Δ₁ ⊢ A     Δ₂ ⊢ B
  ──────────────────── tensor_R
    Δ₁, Δ₂ ⊢ A ⊗ B


   A, B, Δ ⊢ C
  ────────────── tensor_L
   A ⊗ B, Δ ⊢ C
```

### Linear implication ⊸

```
   A, Δ ⊢ B
  ──────────── lolli_R
   Δ ⊢ A ⊸ B


   Δ₁ ⊢ A     B, Δ₂ ⊢ C
  ─────────────────────── lolli_L
   A ⊸ B, Δ₁, Δ₂ ⊢ C
```

### Plus ⊕

```
     Δ ⊢ A
  ─────────── plus_R1
   Δ ⊢ A ⊕ B


     Δ ⊢ B
  ─────────── plus_R2
   Δ ⊢ A ⊕ B


   A, Δ ⊢ C     B, Δ ⊢ C
  ─────────────────────── plus_L
       A ⊕ B, Δ ⊢ C
```

### Future ◇ₖ

```
    Δ ⊢ A
  ────────── submit          (◇ₖ-right, for every k)
   Δ ⊢ ◇ₖA


      A, Δ ⊢ ◇ⱼC
  ────────────────── await   (◇ₖ-left, graded lax)
   ◇ₖA, Δ ⊢ ◇₍ₖ₊ⱼ₎C


   ◇ₖ(R ⊗ (X ⊕ 1)), Δ ⊢ C
  ───────────────────────── cancel
     ◇ₖ(R ⊗ X), Δ ⊢ C
```

Notes:

- `submit` reads `submit : A ⊸ ◇ₖA`. The grade k is chosen freely.
- `await` is a lax rule: the content of the future (A) may only be used if the
  goal is also a future. Its grades are added: waiting for a future of grade k
  and then running the remainder of grade j gives a future of grade k + j. As a
  consequence, ◇ₖA is no longer equivalent to A.
- `cancel` works on a future carrying resource R and result X. After cancel,
  the result becomes X ⊕ 1 (finished, or cancelled without a result), while R
  remains inside the future: cancel never returns R or X out of ◇ₖ.
- `free : A ⊸ 1` is not a logical rule. In `Examples.v` it appears as the
  hypothesis `buf ⊸ 1` in the context.

## Theorems about the rules (not rules)

| Name | Statement | File |
|------|-----------|------|
| `identity` | `A ⊢ A` for every A | `Identity.v` |
| `dia_mono` | if `Δ ⊢ ◇ⱼC` and `j ≤ n`, then `Δ ⊢ ◇ₙC` | `CutElim.v` |
| `cut_admissible` | if `Δ₁ ⊢ A`, `Γ ⊢ C`, Γ is a permutation of `A', Δ₂`, and A' is A with some positive subformula X replaced by X ⊕ 1 (`ext A A'`), then `Δ₁, Δ₂ ⊢ C` | `CutElim.v` |
| `cut` | if `Δ₁ ⊢ A` and `A, Δ₂ ⊢ C`, then `Δ₁, Δ₂ ⊢ C` | `CutElim.v` |
| `cancel_admissible` | the `cancel` rule can be derived from `submit`, `await`, and `cut` | `Examples.v` |
