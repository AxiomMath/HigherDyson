
Please read the file `KeyFormulasDyson.tex` and `AxiomDysonSystems.tex`.

This is Batch 4, the companion to Batch 3. Its ONLY purpose: derive the three normalized
kernel `τ`-shift laws of Prop. 4.5 — which Batch 3 takes as designated inputs `hBshift`,
`hArshift`, `hAextshift` — from honest series definitions of the kernels plus a summability
hypothesis. Batch 3 proves "kernel laws ⟹ elliptic correction structure"; Batch 4 proves
"series definitions + summability ⟹ kernel laws". Together they compose into the full
verification. Nothing else from the paper is in scope here.

## SCOPE — exactly three theorems

With `u := elv w` (`elv : ℂ → ℂˣ`), `d = 2m+1`, `hm : 2 ≤ m`, prove:

```
thm_Bshift    : ∀ w, B (w + τ) = x^2 * q^(-m : ℤ) * (elv w : ℂ)^(-(2*m) : ℤ) * B w
                          - q^(-m : ℤ) * (elv w : ℂ)^(-(2*m) : ℤ) * Pd (elv w)

thm_Arshift   : ∀ w, ∀ r < d, Ar r (w + τ) = x^2 * q^(-m : ℤ) * (elv w : ℂ)^(-(2*m) : ℤ) * Ar r w
                          - q^(-m : ℤ) * (elv w : ℂ)^(-(2*m) : ℤ) * (elv w : ℂ) * Pd (elv w) / (1 - ω^r * elv w)

thm_Aextshift : ∀ w, Aext (w + τ) = x^2 * q^(-m : ℤ) * (elv w : ℂ)^(-(2*m) : ℤ) * Aext w
                          - q^(-m : ℤ) * (elv w : ℂ)^(-(2*m) : ℤ) * (elv w : ℂ) * Pd (elv w) / (1 - x * elv w)
```

CRITICAL COMPOSITION REQUIREMENT: these statements must match Batch 3's accepted hypothesis
declarations VERBATIM — same types, same coercions, same prefactor form, same quantification.
If Batch 3 has already been accepted, COPY its `hBshift`/`hArshift`/`hAextshift` declarations
from the accepted `problem.lean` and use them as the theorem statements here, adjusting only
`hypothesis → theorem`. Any drift in statement form breaks the composition and defeats the
purpose of this run.

## MODELING — this batch deliberately OPENS the kernels (C1 is amended here, and only here)

Unlike Batches 1-3, the kernels in THIS batch are defined as genuine series:

```
B    w := ∑' (n : ℕ), x^(-(2*n)-2 : ℤ) * q^(m*n^2) * (elv w : ℂ)^(2*m*n) * Pd (q^n * elv w)
Ar r w := ∑' (n : ℕ), x^(-(2*n)-2 : ℤ) * q^(m*n^2+n) * (elv w : ℂ)^(2*m*n+1) * Pd (q^n * elv w) / (1 - ω^r * q^n * elv w)
Aext w := ∑' (n : ℕ), x^(-(2*n)-2 : ℤ) * q^(m*n^2+n) * (elv w : ℂ)^(2*m*n+1) * Pd (q^n * elv w) / (1 - x * q^n * elv w)
```

via `tsum` over `ℕ`. `Pd` remains an OPAQUE parameter (its only permitted property is
`hPshift : Pd (q*u) = q^{-m-1} u^{-2} (1-u)/(1-u^d) · Pd u` — do not open it). The theta
objects are not needed in this batch at all.

## Designated hypotheses (the ONLY permitted inputs)

- `hm : 2 ≤ m`, `d = 2*m+1`; units `x : ℂˣ`, `elv : ℂ → ℂˣ`, `q ≠ 0`, `ω` a unit;
  `hq : ‖q‖ < 1` if a norm is needed for summability bookkeeping.
- `helvτ : elv (w+τ) = q · elv w`      (the change-of-variable link; this is what makes
      `w ↦ w+τ` act as `u ↦ qu` inside the sum)
- `hPshift` as above (the opaque `Pd`'s defining law).
- SUMMABILITY, as explicit hypotheses — do NOT prove convergence, assume it:
  `hSummB    : ∀ w, Summable (fun n => ‖x^(-(2*n)-2 : ℤ) * q^(m*n^2) * (elv w : ℂ)^(2*m*n) * Pd (q^n * elv w)‖)`
  and the analogous `hSummAr r`, `hSummAext`, plus (if needed after the index shift) the same
  for the shifted summand. Absolute summability licenses the reindexing below. State these as
  hypotheses of the three theorems; proving them is OUT OF SCOPE (they are the classical
  convergence half of Prop. 4.5, `O(|q|^{(m-1)n²-…})`, and remain paper-level).
- Pole-avoidance at the point of use: `1 - ω^r * q^n * elv w ≠ 0`, `1 - x * q^n * elv w ≠ 0`
  (∀ n), as hypotheses.

No other hypotheses. In particular the CONCLUSIONS (the three normalized laws) must not appear
as inputs in any form.

## The derivation (this is the mathematical content — the paper's Prop. 4.5 index shift)

For each kernel the proof is the same three moves; here for `B`:

1. **Substitute** `w ↦ w+τ` using `helvτ`: the summand becomes
   `x^(-(2n)-2) * q^(mn²) * (q·u)^(2mn) * Pd (q^(n+1)·u)` with `u = elv w`.
2. **Square-complete the exponents** (prove as arithmetic lemmas, over ℤ or ℕ as appropriate):
   `m*n^2 + 2*m*n = m*(n+1)^2 - m`
   and for the `A`-kernels
   `m*n^2 + n + 2*m*n + 1 = m*(n+1)^2 + (n+1) - m`.
   These convert the shifted summand into `q^(-m) * u^(-2m) * x^2 ·` [the original summand at
   index `n+1`] — the `x^2` arising from `x^(-(2n)-2) = x^2 · x^(-(2(n+1))-2)`.
3. **Reindex the tsum** `n ↦ n+1`: use the Mathlib fact that a `tsum` over `ℕ` splits off its
   first term — locate the exact current name with `exact?`/`loogle` (candidates:
   `tsum_eq_zero_add`, `Summable.tsum_eq_zero_add`; do NOT trust a remembered name). This gives
   `∑'_{s≥1} (summand s) = B w /x^0-form minus the n=0 term`, and the peeled `n=0` term is
   exactly the defect: `-q^{-m} u^{-2m} · Pd u` for `B` (and the corresponding
   `-q^{-m}u^{-2m}·u·Pd(u)/(1-ω^r u)`, `/(1-xu)` terms for `Ar`, `Aext`, whose denominators at
   `n=0` read `1-ω^r u`, `1-xu` — note the `q^0` inside them).
   Summability hypotheses license every rearrangement; cite them, never prove them.

The three theorems then follow by finite algebra. This derivation is exactly the source's
Prop. 4.5 proof ("the shift identity … is obtained by the usual index shift"); the value of
this batch is that Lean checks the index shift — the step where a sign, an exponent, or the
peeled boundary term could silently go wrong.

## Conventions

- (F2) Units and pole-avoidance as above; every negative power carries its nonzero fact.
- (F4) No `noncomputable section` (individual `noncomputable def`s only where required); no
  hypotheses beyond the designated list.
- `m ≥ 2` explicit everywhere (`include hm`); exponents in the form `2*m - 2` where `d-3`
  would otherwise appear (it should barely appear in this batch).
- ℤ-valued exponents for anything that can go negative; ℕ only where nonnegativity is
  structural (e.g. `m*n^2`).

## Build hygiene

`set_option linter.unusedVariables false` at top; `_`-prefix unused binders; lint warnings
non-fatal.

The proofs must be fully sorry-free. No axioms, no stray sorrys. The summability and
pole-avoidance hypotheses are designated inputs of conditional theorems, NOT axioms;
introducing any hypothesis beyond the designated list IS a violation — in particular, any form
of the three normalized laws themselves.
