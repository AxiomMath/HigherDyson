
Please read the file `KeyFormulasDyson.tex` and `AxiomDysonSystems.tex`.

This is Batch 2. Formalize and prove ONLY the following (defect clearing, residues, kernel
cancellation): Key Formula~\ref{KF:defect}, Key Formula~\ref{KF:residues}, and
Key Formula~\ref{KF:kernelshift}.

Do not attempt the other Key Formulas in this run. You may take the results of run 1
(the recurrence, `R_{d,x}`, its degree bound and constant term) as GIVEN hypotheses here.

## CRITICAL — statement-level requirements (these must be baked into the theorem
## signatures, not patched during the proof search)

1. **`m ≥ 2` is a hypothesis on every signature.** Fix `def d := 2*m + 1` with a hypothesis
   `hm : 2 ≤ m` (equivalently `hd : 3 ≤ d`) carried by EVERY theorem and every helper lemma
   in this run — including `KF_defect`, its sub-lemmas, the residue lemmas, and the kernel
   lemmas. Do NOT place `hm` in a `section` variable and rely on auto-inclusion; either
   `include hm` explicitly, or thread `hm`/`hd` as an ordinary hypothesis in each signature.
   The proofs genuinely need `d ≥ 3` (indeed `d ≥ 5`): the `d - 3` exponents and the
   `∃ k, d = k + 3` step are only valid under `hm`, and at `d = 1` the defect identity is
   FALSE as a bare `ℂ(u)` equation. The theorem is not well-posed without this hypothesis.
   This is the root cause of the previous crash; it must be fixed at the statement level.

2. **`T_{d,x}` is a genuine polynomial; identities live in `RatFunc ℂ` / `ℂ(u)`.** Model
   `T_{d,x}`, `R_{d,x}`, `S_{d,x}` as `Polynomial ℂ` (with the degree bounds as hypotheses/
   conclusions), and state the partial-fraction and defect identities as equalities in
   `RatFunc ℂ` (equivalently, equalities of `Polynomial ℂ` numerators after clearing the
   common denominator `u(1-u^d)(1-xu)`). Do not state them as pointwise-away-from-poles
   identities with side conditions. (A previous Phase-B rejection hit exactly this.)

3. **Roots-of-unity factorization — Mathlib hint for the hardest lemma (`KF_residues`).**
   The per-pole residue extraction rests on `1 - u^d = ∏_{r<d}(1 - ω^r u)`, equivalently the
   monic factorization of `X^d - 1`. Mathlib provides this as:
   ```
   theorem Polynomial.X_pow_sub_one_eq_prod
     {R : Type*} [CommRing R] [IsDomain R] {ζ : R} {n : ℕ}
     (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
     X ^ n - 1 = ∏ ζ ∈ nthRootsFinset n 1, (X - C ζ)
   ```
   Use `Complex.isPrimitiveRoot_exp` (with `d ≠ 0`, available from `hm`) to obtain the
   primitive `d`-th root, and index the product over `nthRootsFinset d 1`. The distinctness
   of the `d` factors that the partial-fraction decomposition needs is exactly the
   distinctness of the elements of `nthRootsFinset d 1` (a primitive root gives `d` distinct
   `n`-th roots). Prefer this Mathlib-idiomatic indexing over a hand-rolled `∏_{r} (1-ω^r u)`.

## Formalization conventions (binding)

Follow (C1)-(C6) of `KeyFormulasDyson.tex` exactly. Most important for this run:

- **(C1) Opaque symbols, not series.** The kernels `Ψ`, `Ω_r`, `Ω_ext` and the products
  `M_d`, `J` are opaque parameters (`ℂ → ℂ`, or `ℂˣ → ℂ`). Do NOT define them via `tsum`,
  infinite sums, or infinite products. Their ONLY permitted properties are the shift laws:
  the `M_d` `q`-shift `M_d(qu) = u^{d-3}(1-u)/(1-u^d) · M_d(u)`, and the three kernel
  `q`-shift identities (eqs. 4.14-4.16). Introduce each as a theorem hypothesis. No
  summability or convergence claim is ever a goal. This was judge 1's #1 recurring objection
  in the failed run — the kernels must not be actual infinite sums.
- **(C6) Conclusions, not hypotheses.** Prove the stated identities; do not assume them.
  Ship NO `sorry`: every substantive residue / partial-fraction / kernel step must be closed
  in this run, not deferred with a "hand to next phase" comment.
- **(C2) Units.** `x : ℂˣ`, `u : ℂˣ`, `ω` a unit. Every negative power (`x⁻¹`, `x^{-d}`,
  `u^{-1}`, etc.) needs the unit hypothesis in scope; `x^d ≠ 1` alone does NOT justify `x⁻¹`.

## The residue regime split (Key Formula~\ref{KF:residues}) — two DISTINCT definitions

`D_{r,x}` must be defined by branching on whether `x^d = 1`. Do not derive one branch from
the other, and never reuse the `x^d ≠ 1` formula when `x^d = 1`.

- **General case, hypothesis `x^d ≠ 1`** (with `ω` a primitive `d`-th root, so the `d+2`
  factors `u`, `1 - ω^r u`, `1 - xu` are pairwise distinct):
  `D_{r,x} = ω^r / (d (1 - x ω^{-r})) · T_{d,x}(ω^{-r})`,
  `E_x = x/(1 - x^{-d}) · T_{d,x}(x^{-1})`,
  and the `1/u` coefficient is `-X₀ = T_{d,x}(0)`. Here `1 - x ω^{-r} ≠ 0` precisely because
  `x^d ≠ 1`.
- **Torsion case, hypothesis `x^d = 1`:** the `1 - x ω^{-r}` denominator VANISHES (e.g.
  `r = 0`, `x = 1`), so the general formula is undefined. Use instead:
  `D_{r,1} = ω^r/d · S_{d,1}(ω^{-r})` when `x = 1`, and
  `D_{r,x} = ω^r/d · (1 - ω^{-r}) · R_{d,x}(ω^{-r})` when `x ≠ 1`, `x^d = 1`;
  the `1-xu` factor coincides with one of the `1-ω^r u`, and the `E_x` term is absent.

## Given / Prove for this run

- **KF:defect.** Given `hm : 2 ≤ m`, the `M_d` shift law, and `R_{d,x}` from run 1 (as a
  `Polynomial ℂ` with `natDegree ≤ d-2`). Prove the homogeneous-coefficient collapse and the
  twisted defect equation (4.3) for `K_{d,x}` in `RatFunc ℂ`, with `T_{d,x}` as in the spec
  (`natDegree ≤ d`).
- **KF:residues.** Given `hm`, `x : ℂˣ`. In the general case add `x^d ≠ 1` and `ω` primitive;
  prove the partial-fraction identity in `RatFunc ℂ` with the explicit residues above, using
  `Polynomial.X_pow_sub_one_eq_prod` for the denominator factorization. Separately, under
  `x^d = 1`, prove the torsion-case partial fraction with the branched residues.
- **KF:kernelshift.** Given `hm` and the three kernel `q`-shift laws (C1). Prove they match
  the defect of KF:defect term by term, yielding the `K_{d,x}` kernel decomposition.

## Build hygiene (do not waste retries on lint — ~1/3 of the prior budget was lost here)

- Put `set_option linter.unusedVariables false` at the top of the target file.
- Prefix any intentionally-unused binder with `_`.
- Treat lint warnings as non-fatal; they are not validation failures.

The proofs must be fully sorry-free. No axioms, no stray sorrys. Relying on the designated
opaque-symbol shift laws (C1) and the run-1 results is not an axiom; introducing any new
unproved global assumption beyond those IS.
