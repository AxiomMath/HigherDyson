import Mathlib

/-
# Problem Description

This corpus comes from Alfes-Ono, *Higher Dyson ranks and meromorphic elliptic
corrections*, restricted to the "core q-series algebra" (Batch 1).

All statements are read in the *evaluated* setting: the nome is a fixed numeric unit
`q : ℂˣ`, `x` is a complex number (or unit), and the deformed Dyson values are concrete
complex numbers. There is exactly one formal variable, the elliptic variable `u`; the
generating series are genuine formal power series in `u` with complex coefficients, and
the master functional equation lives in the Laurent-series field `K := ℂ((u))`.

Throughout, `m ≥ 2` is an integer and `d = 2m + 1` (so `d ≥ 5` is odd and
`d - 3 = 2m - 2 ≥ 2` is even) wherever those hypotheses are displayed.

## Scope

Only the five Key Formulas `KF:collapse`, `KF:recurrence`, `KF:boundary`,
`KF:functional`, `KF:combi` are in scope, plus the auxiliary lemmas
`exponent_identity`, `rational_reduction_one`, `rational_reduction_two`, and the split of
`KF:combi` into `KF_combi_iff` and `KF_combi_unique`.

## Modeling notes

- Evaluated reading: the nome `q` is a numeric unit `q : ℂˣ`, the values `X₀, G` are
  complex numbers, and the defect `R_{d,x}` is a `Polynomial ℂ`. The single formal
  variable is the elliptic variable `u`, living in `K = ℂ((u))`.
- Opaque building blocks (C1 amendment): the values `G_d(x q^n; q)` are an opaque
  sequence `Gv : ℕ → ℂ` (so `Gval := Gv 0` is `G_d(x; q)`), constrained only by the
  shift predicate `GShift`. Each `X_j` is the genuine convergent series `Xval`.
  Summability is a designated hypothesis (`hSummX`), representing the classical
  convergence `|q| < 1`; it is cited, never proven.
- Chaining (C6): `KF_boundary` and `KF_functional` take the recurrence in equation
  form as the hypothesis `hrec`; this is exactly the conclusion of `KF_recurrence`.
- Units convention (C2): `q : ℂˣ` everywhere the nome appears. `x : ℂ` where no inverse
  of `x` occurs, and `x : ℂˣ` in `KF_functional` (where `x⁻¹` genuinely appears).
-/

open Finset

-- Main Definition(s)

/-- The character sum `C_x = ∑_{r=0}^{d-1} x^r`. -/
noncomputable def Csum (d : ℕ) (x : ℂ) : ℂ := ∑ r ∈ Finset.range d, x ^ r

/-- The `G_d`-shift relation (Definition `def:G`), specialized at `x q^n`, taken as a
predicate on an opaque sequence `Gv : ℕ → ℂ` where `Gv n` plays the role of
`G_d(x q^n; q)`. This encodes
`G_d(x q^n; q) = (∑_{r=0}^{d-1} x^r q^{r(n+1)}) · G_d(x q^{n+1}; q)`. -/
def GShift (d : ℕ) (x : ℂ) (q : ℂˣ) (Gv : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, Gv n = (∑ r ∈ Finset.range d, x ^ r * (q : ℂ) ^ (r * (n + 1))) * Gv (n + 1)

/-- The deformed higher Dyson values `X_j` (Definition `def:X`), opened as a genuine
convergent series in `n` with numeric coefficients (the C1 amendment). This encodes
`X_j^{(m)}(x; q) = ∑_{n ≥ 0} q^{n² + j n} · G_d(x q^n; q)`. The exponent is a `zpow`
since `j` may be negative. -/
noncomputable def Xval (q : ℂˣ) (Gv : ℕ → ℂ) (j : ℤ) : ℂ :=
  ∑' n : ℕ, (q : ℂ) ^ ((n : ℤ) ^ 2 + j * (n : ℤ)) * Gv n

/-- The generating series `𝓕_x` in the elliptic variable, with numeric coefficients
(`eq:intro-F`). -/
noncomputable def Fgen (X : ℤ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun j => X (j : ℤ)

/-- The rescaled generating series `𝓖_{d,x}(u) = x^{-2} · 𝓕_x(x u)` (`eq:intro-G`), a
scalar times a dilation of the variable. -/
noncomputable def Ggen (x : ℂˣ) (X : ℤ → ℂ) : PowerSeries ℂ :=
  (PowerSeries.C (R := ℂ) (((x : ℂ)⁻¹) ^ 2)) * (PowerSeries.rescale (x : ℂ)) (Fgen X)

/-- The Laurent-series field `K = ℂ((u))`. -/
abbrev K := LaurentSeries ℂ

/-- The formal variable `u` in `K`. -/
noncomputable def uVar : K := HahnSeries.single (1 : ℤ) (1 : ℂ)

/-- The embedding `ℂ[[u]] → ℂ((u))`. -/
noncomputable def toK : PowerSeries ℂ →+* K := HahnSeries.ofPowerSeries ℤ ℂ

/-- The `2 × 2` linear system for the combinatorial inversion (`KF:combi`). -/
def CombiSystem (d U D A B : ℂ) : Prop := U = A + (d - 1) * B ∧ D = A - B

-- Main Statement(s)

/-- **Root-of-unity collapse of the inhomogeneity** (Key Formula `KF:collapse`).
For a nontrivial `d`-th root of unity, the character sum `C_x` collapses, and hence the
inhomogeneous term `C_x · G` of the recurrence vanishes. -/
theorem KF_collapse (d : ℕ) (x : ℂ) (hx : x ^ d = 1) (hx1 : x ≠ 1) (Gval : ℂ) :
    Csum d x = (1 - x ^ d) / (1 - x) ∧ Csum d x = 0 ∧ Csum d x * Gval = 0 := by
  sorry

/-- **The exponent identity** underlying the recurrence (source's shift arithmetic). -/
theorem exponent_identity (n j r : ℤ) :
    n ^ 2 + (j + r) * n + r = (n + 1) ^ 2 + (j + r - 2) * (n + 1) + (1 - j) := by
  sorry

/-- **The fundamental `(2m+1)`-term recurrence** (Key Formula `KF:recurrence`;
Prop. 2.2, eq. (2.1)). For every `j ∈ ℤ`,
`∑_{r=0}^{d-1} x^r X_{j+r-2} - q^{j-1} X_j = (∑_r x^r) G_d(x;q)` (with `G_d(x;q) = Gv 0`). -/
theorem KF_recurrence (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂ) (q : ℂˣ) (Gv : ℕ → ℂ)
    (hG : GShift d x q Gv)
    (hSummX : ∀ j : ℤ,
      Summable (fun n : ℕ => ‖(q : ℂ) ^ ((n : ℤ) ^ 2 + j * (n : ℤ)) * Gv n‖))
    (j : ℤ) :
    (∑ r ∈ Finset.range d, x ^ r * Xval q Gv (j + r - 2))
        - (q : ℂ) ^ (j - 1) * Xval q Gv j
      = Csum d x * Gv 0 := by
  sorry

/-- **The two negative-index boundary closures** (Key Formula `KF:boundary`;
eqs. (4.5),(4.6)). Given the recurrence in equation form `hrec`. -/
theorem KF_boundary (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂ) (q : ℂˣ) (X : ℤ → ℂ) (Gval : ℂ)
    (hrec : ∀ j : ℤ,
      (∑ r ∈ Finset.range d, x ^ r * X (j + r - 2)) - (q : ℂ) ^ (j - 1) * X j
        = Csum d x * Gval) :
    (X (-1) = Csum d x * Gval - (∑ r ∈ Finset.Ico 1 d, x ^ r * X ((r : ℤ) - 1)) + X 1)
    ∧ (X (-2) = (q : ℂ)⁻¹ * X 0 - x * X 1 + x ^ d * X ((d : ℤ) - 2)
        + (1 - x) * Csum d x * Gval) := by
  sorry

/-- **First rational-function reduction** (from Key Formula `KF:functional`), an
identity in `K = ℂ((u))`:
`∑_{r=0}^{d-1} u^{2-r} = (u^d - 1) / (u^{d-3}(u-1))`. -/
theorem rational_reduction_one (d : ℕ) (hd3 : 3 ≤ d) :
    (∑ r ∈ Finset.range d, uVar ^ ((2 : ℤ) - r))
      = (uVar ^ d - 1) / (uVar ^ (d - 3) * (uVar - 1)) := by
  sorry

/-- **Second rational-function reduction** (from Key Formula `KF:functional`), an
identity in `K`:
`1 + xu - 1/(1 - xu) = -x²u²/(1 - xu)`. -/
theorem rational_reduction_two (x : ℂˣ) :
    (1 : K) + (algebraMap ℂ K (x : ℂ)) * uVar - 1 / (1 - (algebraMap ℂ K (x : ℂ)) * uVar)
      = - (algebraMap ℂ K ((x : ℂ) ^ 2)) * uVar ^ 2 / (1 - (algebraMap ℂ K (x : ℂ)) * uVar) := by
  sorry

/-- **The master functional equation and the constant term of `R_{d,x}`**
(Key Formula `KF:functional`; Thm. 4.1, eqs. (1.8),(4.1)). Given the recurrence in
equation form `hrec`, there exists a defect polynomial `R` of degree `≤ d - 2` with
`R.coeff 0 = -X 0`, satisfying the displayed functional equation in `K`.

This mirrors the paper's
`𝓖_{d,x}(qu) = x²q · (u^d-1)/(u^{d-3}(u-1)) · 𝓖_{d,x}(u) + q/u^{d-3} · R_{d,x}(u)
- C_x q · u²/(1-xu) · G_d(x;q)`, with `R_{d,x}(0;q) = -X_0`. -/
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
              * (uVar ^ 2 / (1 - algebraMap ℂ K (x : ℂ) * uVar)) := by
  sorry

/-- **Combinatorial `2 × 2` inversion — solution formula** (Key Formula `KF:combi`;
Cor. A.6). For `d ≠ 0`, the linear system is equivalent to its explicit solution. -/
theorem KF_combi_iff (d : ℂ) (hd : d ≠ 0) (U D A B : ℂ) :
    CombiSystem d U D A B ↔ (A = (U + (d - 1) * D) / d ∧ B = (U - D) / d) := by
  sorry

/-- **Combinatorial `2 × 2` inversion — uniqueness** (Key Formula `KF:combi`).
For `d ≠ 0`, the system has a unique solution. -/
theorem KF_combi_unique (d : ℂ) (hd : d ≠ 0) (U D : ℂ) :
    ∃! p : ℂ × ℂ, CombiSystem d U D p.1 p.2 := by
  sorry
