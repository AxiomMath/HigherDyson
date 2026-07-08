Please read the file `KeyFormulasDyson.tex` and `AxiomDysonSystems.tex`.

This is Batch 1 (rerun; Batches 2, 3, 4 are ACCEPTED and FROZEN). Formalize and prove ONLY
the following (the core q-series algebra): Key Formula~\ref{KF:collapse},
Key Formula~\ref{KF:recurrence}, Key Formula~\ref{KF:boundary}, Key Formula~\ref{KF:functional},
and Key Formula~\ref{KF:combi}. Do not attempt the other Key Formulas in this run.

## STRUCTURAL MODEL (final — read this before anything else)

**Work in the EVALUATED reading, at a fixed numeric nome.** The source licenses two readings
of every Key Formula (`KeyFormulasDyson.tex`, intro: "an equality in ℂ(u), in a Laurent ring
ℂ((q))[u], or — after evaluating the elliptic variable at a fixed τ — an equality of complex
numbers"). The accepted Batches 2, 3, 4 all use the evaluated reading: the nome is a numeric
unit `q : ℂˣ`, the values `X₀, G` are complex numbers, and `R_{d,x} : Polynomial ℂ`. This
batch MUST use the same reading, so that its conclusions are type-identical to the accepted
Batch 2's hypotheses (see the SEAM block). Do NOT build a `LaurentSeries ℂ`-in-`q` ambient,
do NOT type any `X_j` as `PowerSeries ℂ`, and do NOT introduce membership predicates like
`IsPowerSeries`/`IsPoleOrderOne` — at numeric `q` these are meaningless, and the formal
q-pole refinement is out of scope for this run (it is already closed by a separate accepted
formal-series run).

There is exactly ONE formal variable in this batch: the elliptic variable `u`. The generating
series `𝓕, 𝓖` are genuine formal power series in `u` with NUMERIC (complex) coefficients,
and the master functional equation lives in the Laurent-series field `K := LaurentSeries ℂ
= ℂ((u))`.

## C1 AMENDMENT — this batch OPENS the `X_j` (exactly as the accepted Batch 4 opened the kernels)

The accepted Batch 4 amended convention (C1) to define its kernels by genuine `tsum` series,
with summability supplied as designated hypotheses and the shift laws proven by an honest
index shift. This batch amends (C1) the same way, and ONLY for the family `X_j`:

- The building-block values `G_d(x q^n; q)` are an OPAQUE sequence `Gv : ℕ → ℂ` (so
  `Gval := Gv 0` is the value `G_d(x;q)`), subject ONLY to the `G_d`-shift law `GShift`
  below (Definition~\ref{def:G} specialized at the arguments `x q^n`). Do not open `Gv`.
- Each `X_j` is DEFINED by the genuine series `Xval q Gv j := ∑' n : ℕ, q^(n²+jn) · Gv n`
  (a `tsum` over `ℕ`; the exponent is a `zpow` since it can be negative for `j < 0`).
- Summability is a DESIGNATED HYPOTHESIS (`hSummX` below), never a proof obligation. Cite
  it; never prove it. It is the classical convergence half (|q| < 1), which stays paper-level.

WHY (root causes of the two prior dead runs — do not reproduce either):
1. A `FormalSum`/`Conv` closure-predicate interface (silver-tern) made the telescoping
   UNDERIVABLE (no closure axioms), with a genuine countermodel.
2. A total `SummationOp` structure with an unconditional reindex law
   `sum (fun n => f (n+1)) = sum f - f 0` is UNINHABITED: applied to `f ≡ 1` it yields
   `sum f = sum f - 1`, i.e. `0 = -1`, so every theorem assuming one is vacuous.
Both traps come from inventing a formal summation interface. The fix is Batch 4's: use the
real `tsum` with assumed summability. The recurrence is then proven by exactly the
index-shift technique the accepted Batch 4 already executed for `thm_Bshift` (peel the
`n = 0` term with `tsum_eq_zero_add'`, square-complete exponents, `tsum_mul_left`).
BANNED, in any form: `SummationOp`, `FormalSum`, `Conv`, or ANY bespoke opaque summation
operator or convergence predicate. The token `sorry` must not appear anywhere, including
comments.

## Exact definitions (produce these shapes; `noncomputable` where Lean requires)

```lean
open Finset

/-- `C_x = ∑_{r=0}^{d-1} x^r`. -/
noncomputable def Csum (d : ℕ) (x : ℂ) : ℂ := ∑ r ∈ Finset.range d, x ^ r

/-- The `G_d`-shift relation at the arguments `x q^n` (Definition def:G), as a predicate. -/
def GShift (d : ℕ) (x : ℂ) (q : ℂˣ) (Gv : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, Gv n = (∑ r ∈ Finset.range d, x ^ r * (q : ℂ) ^ (r * (n + 1))) * Gv (n + 1)

/-- `X_j := ∑_{n≥0} q^(n²+jn) · G_d(x q^n)`, opened as a genuine `tsum` (C1 amendment). -/
noncomputable def Xval (q : ℂˣ) (Gv : ℕ → ℂ) (j : ℤ) : ℂ :=
  ∑' n : ℕ, (q : ℂ) ^ ((n : ℤ) ^ 2 + j * (n : ℤ)) * Gv n

/-- `𝓕_x(t) = ∑_{j≥0} X_j t^j`: a genuine formal power series in the elliptic variable,
with numeric coefficients. -/
noncomputable def Fgen (X : ℤ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun j => X (j : ℤ)

/-- `𝓖_{d,x}(u) = x^{-2} · 𝓕_x(x u)`: scalar times dilation of the variable
(`PowerSeries.rescale`). -/
noncomputable def Ggen (x : ℂˣ) (X : ℤ → ℂ) : PowerSeries ℂ :=
  PowerSeries.C ℂ (((x : ℂ)⁻¹) ^ 2) * (PowerSeries.rescale (x : ℂ)) (Fgen X)

/-- `K = ℂ((u))`, the Laurent-series field in the elliptic variable. -/
abbrev K := LaurentSeries ℂ

/-- The formal elliptic variable `u`. -/
noncomputable def uVar : K := HahnSeries.single (1 : ℤ) (1 : ℂ)

/-- Embedding `ℂ[[u]] → ℂ((u))`. -/
noncomputable def toK : PowerSeries ℂ →+* K := HahnSeries.ofPowerSeries ℤ ℂ

/-- The `2×2` linear system for the combinatorial inversion. -/
def CombiSystem (d U D A B : ℂ) : Prop := U = A + (d - 1) * B ∧ D = A - B
```

## Exact theorem statements (produce these VERBATIM; only the proofs are open)

```lean
theorem KF_collapse (d : ℕ) (x : ℂ) (hx : x ^ d = 1) (hx1 : x ≠ 1) (Gval : ℂ) :
    Csum d x = (1 - x ^ d) / (1 - x) ∧ Csum d x = 0 ∧ Csum d x * Gval = 0

theorem exponent_identity (n j r : ℤ) :
    n ^ 2 + (j + r) * n + r = (n + 1) ^ 2 + (j + r - 2) * (n + 1) + (1 - j)

theorem KF_recurrence (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂ) (q : ℂˣ) (Gv : ℕ → ℂ)
    (hG : GShift d x q Gv)
    (hSummX : ∀ j : ℤ,
      Summable (fun n : ℕ => ‖(q : ℂ) ^ ((n : ℤ) ^ 2 + j * (n : ℤ)) * Gv n‖))
    (j : ℤ) :
    (∑ r ∈ Finset.range d, x ^ r * Xval q Gv (j + r - 2))
        - (q : ℂ) ^ (j - 1) * Xval q Gv j
      = Csum d x * Gv 0

theorem KF_boundary (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂ) (q : ℂˣ) (X : ℤ → ℂ) (Gval : ℂ)
    (hrec : ∀ j : ℤ,
      (∑ r ∈ Finset.range d, x ^ r * X (j + r - 2)) - (q : ℂ) ^ (j - 1) * X j
        = Csum d x * Gval) :
    (X (-1) = Csum d x * Gval - (∑ r ∈ Finset.Ico 1 d, x ^ r * X ((r : ℤ) - 1)) + X 1)
    ∧ (X (-2) = (q : ℂ)⁻¹ * X 0 - x * X 1 + x ^ d * X ((d : ℤ) - 2)
        + (1 - x) * Csum d x * Gval)

theorem rational_reduction_one (d : ℕ) (hd3 : 3 ≤ d) :
    (∑ r ∈ Finset.range d, uVar ^ ((2 : ℤ) - r))
      = (uVar ^ d - 1) / (uVar ^ (d - 3) * (uVar - 1))

theorem rational_reduction_two (x : ℂˣ) :
    (1 : K) + (algebraMap ℂ K (x : ℂ)) * uVar - 1 / (1 - (algebraMap ℂ K (x : ℂ)) * uVar)
      = - (algebraMap ℂ K ((x : ℂ) ^ 2)) * uVar ^ 2 / (1 - (algebraMap ℂ K (x : ℂ)) * uVar)

theorem KF_functional (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x q : ℂˣ) (X : ℤ → ℂ) (Gval : ℂ)
    (hrec : ∀ j : ℤ,
      (∑ r ∈ Finset.range d, (x : ℂ) ^ r * X (j + r - 2)) - (q : ℂ) ^ (j - 1) * X j
        = Csum d (x : ℂ) * Gval) :
    ∃ R : Polynomial ℂ,
      R.natDegree ≤ d - 2 ∧
      R.coeff 0 = - X 0 ∧
      toK ((PowerSeries.rescale (q : ℂ)) (Ggen x X))
        = algebraMap ℂ K ((x : ℂ) ^ 2 * (q : ℂ))
            * ((uVar ^ d - 1) / (uVar ^ (d - 3) * (uVar - 1))) * toK (Ggen x X)
          + algebraMap ℂ K (q : ℂ) * ((Polynomial.aeval uVar) R / uVar ^ (d - 3))
          - algebraMap ℂ K (Csum d (x : ℂ) * (q : ℂ) * Gval)
              * (uVar ^ 2 / (1 - algebraMap ℂ K (x : ℂ) * uVar))

theorem KF_combi_iff (d : ℂ) (hd : d ≠ 0) (U D A B : ℂ) :
    CombiSystem d U D A B ↔ (A = (U + (d - 1) * D) / d ∧ B = (U - D) / d)

theorem KF_combi_unique (d : ℂ) (hd : d ≠ 0) (U D : ℂ) :
    ∃! p : ℂ × ℂ, CombiSystem d U D p.1 p.2
```

## SEAM with the accepted Batch 2 (informational; nothing to import)

The accepted Batch 2 consumes, as hypotheses, exactly: `x q : ℂˣ`; `X0 Gval : ℂ`;
`R : Polynomial ℂ`; `hRdeg : R.natDegree ≤ d - 2`; `hR0 : R.coeff 0 = -X0`; and `hMaster`
(the master equation over `RatFunc ℂ` with opaque `Gg` and the `qShiftEquiv q` automorphism).
`KF_functional` above concludes objects of exactly those types, and its displayed equation
mirrors `hMaster` term for term — `σGg ↦ toK (rescale q 𝓖)`, `Gg ↦ toK 𝓖`,
`C(x²q)·((u^d−1)/(u^{d−3}(u−1)))·Gg`, `C q·(R(u)/u^{d−3})`, `−C(Cx·q·Gval)·(u²/(1−Cx·u))` —
with the one inherent difference that the concrete generating series lives in `ℂ((u))`
rather than `RatFunc ℂ`. Do not alter the conclusion shapes: `hR0` uses `R.coeff 0`
(NOT `R.eval 0`), the degree bound is `natDegree ≤ d - 2` (write `d - 2`, not `2*m - 1`),
and the inhomogeneity constant is `Csum d x * q * Gval` inside ONE `algebraMap`.

## Proof strategy (follow these; every named idiom compiles on this toolchain in the
## accepted batches)

- **KF_collapse / KF_combi.** Finite geometric series (`geom_sum_eq` or `geom_sum_mul`)
  plus field algebra (`field_simp`, `ring`, `linear_combination`); for `KF_combi_unique`,
  prove the `iff` first and instantiate.
- **KF_recurrence** (the Batch-4 index-shift pattern, verbatim). Set
  `F k : ℕ → ℂ := fun n => (q:ℂ)^((n:ℤ)^2 + k*(n:ℤ)) * Gv n`, so `Xval q Gv k = ∑' n, F k n`.
  (a) Pointwise: from `hG n` and `exponent_identity`,
      `(q:ℂ)^(j-1) * F j n = ∑ r ∈ Finset.range d, x^r * F (j+r-2) (n+1)`;
      combine `zpow` exponents with `zpow_add₀ (Units.ne_zero q ▸ …)` — note
      `(q:ℂ) ≠ 0` is `Units.ne_zero q` — and bridge ℕ-powers to ℤ-powers with
      `zpow_natCast` and `push_cast`, exactly as in Batch 4's `key` steps.
  (b) Summability: each `Summable (F k)` is `(hSummX k).of_norm`; the shifted family via
      `(summable_nat_add_iff 1).2`; scalar multiples via `Summable.mul_left`.
  (c) Sum: `tsum_congr` with (a); swap the finite `r`-sum out of the `tsum` (`tsum_sum`
      over `Finset.range d`, or `Finset.induction` with `Summable.tsum_add`); pull scalars
      with `tsum_mul_left`; peel `n = 0` with `tsum_eq_zero_add'` applied to the shifted
      summability. The `n = 0` term of `F k` is `(q:ℂ)^0 * Gv 0 = Gv 0` for every `k`, so
      the peeled boundary assembles to `Csum d x * Gv 0` (`Finset.sum_mul`). Rearrange
      (`linear_combination`).
- **KF_boundary.** Specialize `hrec` at `j = 1` and `j = 0`
  (`zpow_zero`, `zpow_neg`, `zpow_one` for `(q:ℂ)^(0:ℤ)` and `(q:ℂ)^(-1:ℤ)`); split the
  bottom terms off `range d` with `Finset.range_eq_Ico` +
  `Finset.sum_eq_sum_Ico_succ_bot`; for the second closure, reindex
  `x * ∑_{Ico 1 d} x^r X(r-1) = ∑_{Ico 2 d} x^r X(r-2) + x^d X(d-2)` via
  `Finset.sum_Ico_add'` and `Finset.sum_Ico_succ_top`; finish with `linear_combination`
  (first closure feeds the second).
- **rational_reduction_one/two.** `uVar_ne_zero`/`uVar ≠ 1` by coefficient inspection
  (`HahnSeries.single_eq_zero_iff`, coefficient at `0`); bridge
  `uVar ^ (n : ℤ) = HahnSeries.single n 1` (locate with `exact?`; on this toolchain the
  zpow bridge `RatFunc.single_zpow` applies to `LaurentSeries`); geometric series
  `geom_sum_eq` on `uVar⁻¹`; then a pure-field core lemma over an abstract field element
  (`field_simp` + `ring` on opaque atoms, with `v^d = v^(d-3) * v^3` from `omega`) to avoid
  expensive `whnf` on Laurent series. For reduction two, `1 - C x · u ≠ 0` by the
  coefficient-at-`0` argument.
- **KF_functional** (the substantive theorem; Thm 4.1 of the source, evaluated). The
  polynomial is EXPLICIT and `Gv`-free (the inhomogeneous `G`-contributions of the two
  boundary closures cancel in `R`). With `a := (x:ℂ)`, `ξ := (x:ℂ)⁻¹`:
  `Xm1 := -(∑ r ∈ Finset.Ico 1 d, a^r * X (r-1)) + X 1`,
  `Xm2 := (q:ℂ)⁻¹ * X 0 - a * X 1 + a^d * X (d-2)`,
  `Rc k := (if k = d-3 then ξ^2 * Xm2 else 0) + (if k = d-3 then ξ * Xm1 else 0)
           + (if k = d-2 then ξ * Xm1 else 0)
           - ∑ r ∈ Finset.Ico 2 d, ∑ n ∈ Finset.range (r-2),
               (if k + r = n + (d-1) then a^n * X n else 0)`,
  `R := ∑ k ∈ Finset.range (d-1), Polynomial.monomial k (Rc k)`.
  Then: degree bound by `Polynomial.natDegree_sum_le_of_forall_le` +
  `Polynomial.natDegree_monomial_le`; `R.coeff 0 = -X 0` because the three `if`-guards are
  false at `k = 0` (`d ≥ 5`) and the double sum collapses to the single cell
  `(r, n) = (d-1, 0)` (`Finset.sum_eq_single`), value `a^0 * X 0 = X 0`.
  For the equation: prove first the cleared power-series identity `hP` in `PowerSeries ℂ`
  (multiply through by `X^(d-3) * (X - 1) * (1 - C a * X)`), by `PowerSeries.ext` on the
  `u`-coefficient. Key ingredients: substitute `e := d - 3` (`obtain ⟨e, he⟩ : ∃ e, d = e+3`,
  `omega`); factor `X^(e+3) - 1 = (∑_{i<e+3} X^i) * (X - 1)` by `geom_sum_mul` and cancel
  the common `(X - 1)` via `linear_combination (X - 1) * hcore`; coefficient formulas
  `PowerSeries.coeff_rescale`, `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_mul_X_pow'`,
  `PowerSeries.coeff_succ_mul_X`, `PowerSeries.coeff_monomial`, `PowerSeries.coeff_mk`;
  the recurrence enters ONLY through the ℕ-shifted instances `hrec (s + 2)` (`s : ℕ`),
  giving `∑_{r<e+3} a^r X(s+r) = q^(s+1) X(s+2) + Csum·Gval`; the convolution
  `∑_{i<e+3} [i ≤ n] g(n-i)` is handled in two regimes — `n ≤ e+2` reindexes to the partial
  sums `SM k := ∑_{s<k+1} a^s X s` (`Finset.sum_range_reflect`, `Finset.sum_nbij'`), and
  `n ≥ e+3` drops all guards and reduces to the shifted recurrence (`hGE`); the unit facts
  `a * ξ = 1`, `a^2 * ξ^2 = 1` discharge the scalar bookkeeping; the double-sum part of
  `Rc` equals `SM k` for `k < e` and `0` for `e ≤ k ≤ e+2` (guard arithmetic by `omega`).
  Finally transport `hP` to `K` along the ring hom `toK` (`map_mul/map_sub/map_add/map_pow`,
  `HahnSeries.ofPowerSeries_X` for `toK PowerSeries.X = uVar`,
  `HahnSeries.ofPowerSeries_C` + `PowerSeries.algebraMap_apply` for
  `algebraMap ℂ K c = toK (PowerSeries.C ℂ c)`, and
  `Polynomial.aeval_monomial` + `PowerSeries.monomial_eq_C_mul_X_pow` for
  `aeval uVar R = toK (∑ monomial …)`), introduce opaque atoms with `set` +
  `clear_value` for `W := uVar^(d-3)`, `U := uVar`, etc. (so `field_simp`/`ring` never
  unfold Laurent series), record `U^d = W * U^3` and `U^(d-1) = W * U^2` (`pow_add`,
  `omega`), and finish with `field_simp` + `linear_combination`/`ring` against the
  nonzero-denominator facts (`uVar ≠ 0`, `uVar - 1 ≠ 0`, `1 - C x·uVar ≠ 0`,
  `uVar^(d-3) ≠ 0`).
  Set generous budgets on this theorem only:
  `set_option maxHeartbeats 3200000 in` and `set_option maxRecDepth 4000 in`.

## Conventions (binding)

- (C3) `hm : 2 ≤ m` and `hd : d = 2*m+1` are explicit hypotheses on `KF_recurrence`,
  `KF_boundary`, `KF_functional` (thread them; no section auto-inclusion). `KF_collapse`,
  the rational reductions, and `KF_combi` carry exactly the hypotheses shown.
- (C2) Units: `q : ℂˣ` everywhere the nome appears; `x : ℂ` where no inverse of `x` occurs
  (collapse, recurrence, boundary) and `x : ℂˣ` in `KF_functional` (where `x⁻¹` is real).
  Every inverse/negative power carries its nonzero fact (`Units.ne_zero`).
- (C6) Conclusions, not hypotheses: each statement above is to be PROVED as displayed.
  Chaining is permitted exactly as displayed: `KF_boundary` and `KF_functional` take the
  recurrence in equation form (`hrec`) — it is the conclusion of `KF_recurrence` — and
  nothing else about `X`. No hypothesis may restate any conclusion.
- (C5) The `KF_functional` equation is a single equality in the field `K = ℂ((u))`
  (equivalently of numerators after clearing `u^(d-3)(u-1)(1-xu)`), not a pointwise
  statement with side conditions.
- Sums are indexed `∑ r ∈ Finset.range d` / `Finset.Ico`, matching the accepted batches.

## Build hygiene (do not waste retries on lint)

- Put `set_option linter.unusedVariables false` at the top of the target file.
- Prefix any intentionally-unused binder with `_`.
- Treat lint warnings as non-fatal; they are not validation failures.

The proofs must be fully sorry-free. No axioms. The designated inputs (`hG`, `hSummX`,
`hrec` where displayed) are hypotheses of conditional theorems, not axioms; `tsum` and the
`PowerSeries`/`LaurentSeries` ring instances are Mathlib-provided. Introducing any
hypothesis beyond those displayed in the statements above — in particular any bespoke
summation structure or any form of a conclusion — is a violation.
