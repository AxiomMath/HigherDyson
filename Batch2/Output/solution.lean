import Mathlib

/-
# Problem Description

We formalize three "Key Formulas" from the Dyson systems project (`KF:defect`,
`KF:residues`, `KF:kernelshift`), all stated as **equalities in the rational function
field `𝕂 := RatFunc ℂ`** in a single indeterminate whose image `RatFunc.X` we write `U`.

## Global setup and conventions (binding)

- an integer `m` with hypothesis `hm : 2 ≤ m`, and `d := 2*m + 1` (so `d ≥ 5` is odd and
  `d - 3 = 2*m - 2 ≥ 2` is even);
- a scalar `x : ℂˣ` (the marked twist), viewed as the nonzero constant `(x : ℂ)`;
- a scalar `q : ℂˣ` (the shift parameter), viewed as the nonzero constant `(q : ℂ)`;
- when a `d`-th root of unity is needed, `ω : ℂˣ` denotes a *primitive* `d`-th root of unity,
  carried as a hypothesis `IsPrimitiveRoot (ω : ℂ) d` (concretely `ω := Complex.exp (2πi/d)`,
  a unit since it is nonzero, with primitivity from `Complex.isPrimitiveRoot_exp d (by omega)`).

## The ambient field and the `q`-shift automorphism (the one modeling decision)

All Key Formulas are equalities in `𝕂 := RatFunc ℂ`. Working in the field `𝕂` (where a
nonzero element such as `1 - U^d` is invertible) removes every pole side-condition: the
displayed equalities hold verbatim as field equalities.

The substitution `u ↦ q·u` is modeled as the unique `ℂ`-algebra automorphism
`σ : 𝕂 ≃ₐ[ℂ] 𝕂` with `σ U = C q · U`. An algebra automorphism is determined by its value
on `U = RatFunc.X`, so this specifies `σ` uniquely; it exists and is bijective because
`(q : ℂ)` is a unit. We carry `σ` and its defining property as hypotheses.

## Opaque symbols (C1): elements of `𝕂`, never series

`M_d, 𝓖, K, Ψ, Ω_r (0 ≤ r ≤ d-1), Ω_ext` are opaque elements of `𝕂`. Their only permitted
properties are the finitely many algebraic shift relations, each introduced as a hypothesis.
No summability, convergence, or holomorphy claim is ever made.

The defect data `R_{d,x}`, `S_{d,x}`, `T_{d,x}` are genuine polynomials (`Polynomial ℂ`),
carried with their degree bounds; they enter the field identities via the algebra map
`Polynomial ℂ → RatFunc ℂ` (we write `T̂` for the image of a polynomial `T`).

## Units (C2)

Every symbol raised to a negative power (`x⁻¹`, `x^{-d}`, `ω^{-r}`, and the shift by `q⁻¹`)
is a unit; the unit hypotheses `x : ℂˣ`, `q : ℂˣ`, `ω : ℂˣ` are in scope wherever a negative
power occurs, so all inverses are of nonzero constants.

## Scope

This run formalizes and proves only the three Key Formulas `KF:defect`, `KF:residues`,
`KF:kernelshift` (Statements 1–3). The run‑1 results (the polynomial `R_{d,x}` with its
degree bound and constant term) and the designated opaque‑symbol shift laws are taken as
GIVEN hypotheses.
-/

open Polynomial

noncomputable section

/-! ## Abbreviations for the field and the indeterminate `U`. -/

/-- The ambient rational function field `𝕂 = ℂ(U)`. -/
abbrev Kf : Type := RatFunc ℂ

/-- The image of the indeterminate, written `U` in the informal text. -/
noncomputable def U : Kf := RatFunc.X

/-- Embedding of a polynomial `p ∈ ℂ[X]` into `𝕂 = ℂ(U)` (written `p̂`). -/
noncomputable def toField (p : Polynomial ℂ) : Kf :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) p

/-! ## Helper lemmas about `𝕂 = ℂ(U)`. -/

theorem toField_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) : toField p ≠ 0 := by
  intro h
  apply hp
  have hinj := RatFunc.algebraMap_injective (K := ℂ)
  apply hinj
  rw [map_zero]
  exact h

theorem toField_X : toField X = U := by
  simp [toField, U, RatFunc.algebraMap_X]

theorem toField_C (c : ℂ) : toField (C c) = RatFunc.C c := by
  simp [toField, RatFunc.algebraMap_C]

/-- `U ≠ 0` in `𝕂`. -/
theorem U_ne_zero : (U : Kf) ≠ 0 := by
  rw [U]; exact RatFunc.X_ne_zero

/-- `1 - U^d ≠ 0` in `𝕂` for `d ≥ 1`. -/
theorem one_sub_U_pow_ne_zero {d : ℕ} (hd : 1 ≤ d) : (1 : Kf) - U ^ d ≠ 0 := by
  have hpoly : (1 - X ^ d : Polynomial ℂ) ≠ 0 := by
    intro h
    have hc : (1 - X ^ d : Polynomial ℂ).coeff 0 = 0 := by rw [h]; simp
    rw [coeff_sub, coeff_one, coeff_X_pow] at hc
    have hd0 : ¬ ((0 : ℕ) = d) := by omega
    simp only [if_pos rfl, if_neg hd0, sub_zero] at hc
    exact one_ne_zero hc
  have hf : toField (1 - X ^ d) ≠ 0 := toField_ne_zero hpoly
  have he : toField (1 - X ^ d) = (1 : Kf) - U ^ d := by
    have : toField (1 - X ^ d) = toField 1 - (toField X) ^ d := by
      unfold toField; rw [map_sub, map_one, map_pow]
    rw [this, toField_X]; simp [toField]
  rw [he] at hf
  exact hf

/-- `1 - RatFunc.C c * U ≠ 0` in `𝕂` for `c ≠ 0`. -/
theorem one_sub_C_mul_U_ne_zero {c : ℂ} (hc : c ≠ 0) :
    (1 : Kf) - RatFunc.C c * U ≠ 0 := by
  have hpoly : (1 - C c * X : Polynomial ℂ) ≠ 0 := by
    intro h
    have h1 : (1 - C c * X : Polynomial ℂ).coeff 1 = 0 := by rw [h]; simp
    simp only [coeff_sub, coeff_one, coeff_C_mul, coeff_X, if_true, mul_one] at h1
    norm_num at h1
    exact hc h1
  have hf : toField (1 - C c * X) ≠ 0 := toField_ne_zero hpoly
  have he : toField (1 - C c * X) = (1 : Kf) - RatFunc.C c * U := by
    have : toField (1 - C c * X) = toField 1 - toField (C c) * toField X := by
      unfold toField; rw [map_sub, map_one, map_mul]
    rw [this, toField_C, toField_X]; simp [toField]
  rw [he] at hf
  exact hf

/-- Any `ℂ`-algebra automorphism of `RatFunc ℂ` fixes the constant `RatFunc.C c`. -/
theorem sigma_fix_C (σ : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ) (c : ℂ) :
    σ (RatFunc.C c) = RatFunc.C c := by
  have : σ (algebraMap ℂ (RatFunc ℂ) c) = algebraMap ℂ (RatFunc ℂ) c := σ.commutes c
  rwa [RatFunc.algebraMap_eq_C] at this

/-! ## Main Definition(s) -/

/-- **Definition 1 (The constant `C_x`).**
`C_x := ∑_{r=0}^{d-1} x^r ∈ ℂ`. For `x ≠ 1` one has `C_x = (1 - x^d)/(1 - x)`; if `x = 1`
then `C_x = d` (nonzero); if `x ≠ 1` and `x^d = 1` then `C_x = 0`. -/
def Cx (x : ℂ) (d : ℕ) : ℂ := ∑ r ∈ Finset.range d, x ^ r

/-- **Definition 5 (The defect polynomial `T_{d,x}`).**
In `ℂ[X]` (with `X` the indeterminate, `C` the constant embedding):
`T_{d,x} := (1 - C x · X)·(1 - X)·R - C (C_x)·X^{d-1}·(1 - X)·C G`. -/
def Tpoly (x G : ℂ) (d : ℕ) (R : Polynomial ℂ) : Polynomial ℂ :=
  (1 - C x * X) * (1 - X) * R - C (Cx x d) * X ^ (d - 1) * (1 - X) * C G

/-- **Definition (Subcase `x = 1`).**  `S_{d,1} := (1 - X)·R - C d · X^{d-1}·C G`. -/
def Spoly_one (G : ℂ) (d : ℕ) (R : Polynomial ℂ) : Polynomial ℂ :=
  (1 - X) * R - C (d : ℂ) * X ^ (d - 1) * C G

/-- **Definition (Subcase `x ≠ 1, x^d = 1`).**  `S_{d,x} := (1 - X)·R`. -/
def Spoly_tors (R : Polynomial ℂ) : Polynomial ℂ := (1 - X) * R

/-! ### Residue scalars (Definition of the partial-fraction data, Statement 2). -/

/-- General-case residue scalar `D_{r,x} = ω^r / (d·(1 - x·ω^{-r})) · T_{d,x}(ω^{-r})`. -/
def Dgen (x G : ℂ) (d : ℕ) (R : Polynomial ℂ) (ω : ℂ) (r : ℕ) : ℂ :=
  ω ^ r / ((d : ℂ) * (1 - x * ω⁻¹ ^ r)) * (Tpoly x G d R).eval (ω⁻¹ ^ r)

/-- General-case residue scalar `E_x = x / (1 - x^{-d}) · T_{d,x}(x^{-1})`. -/
def Ex (x G : ℂ) (d : ℕ) (R : Polynomial ℂ) : ℂ :=
  x / (1 - x⁻¹ ^ d) * (Tpoly x G d R).eval x⁻¹

/-- Torsion subcase `x = 1` residue scalar `D_{r,1} = ω^r / d · S_{d,1}(ω^{-r})`. -/
def Done (G : ℂ) (d : ℕ) (R : Polynomial ℂ) (ω : ℂ) (r : ℕ) : ℂ :=
  ω ^ r / (d : ℂ) * (Spoly_one G d R).eval (ω⁻¹ ^ r)

/-- Torsion subcase `x ≠ 1, x^d = 1` residue scalar
`D_{r,x} = ω^r / d · (1 - ω^{-r}) · R(ω^{-r})`. -/
def Dtors (d : ℕ) (R : Polynomial ℂ) (ω : ℂ) (r : ℕ) : ℂ :=
  ω ^ r / (d : ℂ) * (1 - ω⁻¹ ^ r) * R.eval (ω⁻¹ ^ r)

/-! ### Definition 5 characterization properties (`T_{d,x}` degree and constant term).

The problem records that `T_{d,x}` has `natDegree ≤ d` and constant term `-X₀`.  We state
these as the two lemmas below, part of the advertised formalization context.  Both carry
the binding global hypotheses `hm : 2 ≤ m`, `hd : d = 2*m+1`; these are genuinely used
(e.g. the constant-term claim needs `d - 1 ≠ 0`, which fails for small `d`). -/

/-- Definition 5 property: `T_{d,x}` has degree at most `d`, given `R` of degree `≤ d - 2`
and `2 ≤ m`, `d = 2*m+1`. -/
theorem Tpoly_natDegree_le
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x G : ℂ) (R : Polynomial ℂ) (hRdeg : R.natDegree ≤ d - 2) :
    (Tpoly x G d R).natDegree ≤ d := by
  unfold Tpoly
  have hd2 : d - 2 + 2 = d := by omega
  have hd1 : d - 1 + 1 = d := by omega
  have hb : (1 - X : ℂ[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_sub_le _ _) ?_
    simp
  have ha : (1 - C x * X).natDegree ≤ 1 := by
    refine le_trans (natDegree_sub_le _ _) ?_
    simp only [natDegree_one]
    exact max_le (by norm_num) (le_trans (natDegree_C_mul_le _ _) (by simp))
  refine le_trans (natDegree_sub_le _ _) ?_
  apply max_le
  · -- (1 - C x * X) * (1 - X) * R
    refine le_trans (natDegree_mul_le) ?_
    have h1 : ((1 - C x * X) * (1 - X)).natDegree ≤ 2 := by
      refine le_trans (natDegree_mul_le) ?_
      omega
    have := add_le_add h1 hRdeg
    omega
  · -- C (Cx x d) * X ^ (d - 1) * (1 - X) * C G
    refine le_trans (natDegree_mul_le) ?_
    have hCG : (C G).natDegree = 0 := natDegree_C _
    rw [hCG, add_zero]
    refine le_trans (natDegree_mul_le) ?_
    have hX : (C (Cx x d) * X ^ (d - 1)).natDegree ≤ d - 1 := by
      refine le_trans (natDegree_C_mul_le _ _) ?_
      simp
    omega

/-- Definition 5 property: the constant term of `T_{d,x}` equals `R(0) = -X₀`.
The global hypotheses `hm`, `hd` are required: they give `2 ≤ d`, hence `d - 1 ≠ 0`, so the
term `X^{d-1}` does not contribute to the constant term. -/
theorem Tpoly_coeff_zero
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x G : ℂ) (R : Polynomial ℂ) (X₀ : ℂ) (hR0 : R.coeff 0 = -X₀) :
    (Tpoly x G d R).coeff 0 = -X₀ := by
  have hd1 : d - 1 ≠ 0 := by omega
  rw [coeff_zero_eq_eval_zero] at hR0 ⊢
  unfold Tpoly
  simp only [eval_sub, eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_pow,
    zero_pow hd1]
  rw [hR0]
  ring

/-! ### Torsion factorization and constant-term characterizations of the `S`-polynomials.

These lemmas capture the relationships the problem states in the torsion subcases:
`C_x = d` and `T_{d,1} = (1 - X)·S_{d,1}` in the `x = 1` subcase, and `C_x = 0`,
`T_{d,x} = (1 - C x·X)·S_{d,x}` in the `x ≠ 1, x^d = 1` subcase, together with the
constant-term equalities `S_{d,1}(0) = R(0) = -X₀` and `S_{d,x}(0) = R(0) = -X₀`. They make
explicit that the torsion partial fractions (and the torsion form of the defect equation)
are obtained from the master `T_{d,x}` by cancelling the shared linear factor.  All carry
the binding hypotheses `hm`, `hd`. -/

/-- Torsion subcase `x = 1`: the constant `C_1 = d`. -/
theorem Cx_one (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1) :
    Cx (1 : ℂ) d = (d : ℂ) := by
  simp [Cx]

/-- Torsion subcase `x ≠ 1, x^d = 1`: the constant `C_x = 0`.  This uses `x^d = 1` and
`x ≠ 1`: `(1 - x)·C_x = 1 - x^d = 0`, and `1 - x ≠ 0`. -/
theorem Cx_torsion_ne (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂ) (hx1 : x ≠ 1) (hxd : x ^ d = 1) :
    Cx x d = 0 := by
  have hgeom : (x - 1) * Cx x d = x ^ d - 1 := by
    rw [Cx, mul_comm, geom_sum_mul]
  rw [hxd, sub_self] at hgeom
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  rcases mul_eq_zero.mp hgeom with h | h
  · exact absurd h hx1'
  · exact h

/-- Torsion subcase `x = 1`: `T_{d,1} = (1 - X)·S_{d,1}` as polynomials in `ℂ[X]`.
Since `C_1 = d`, `T_{d,1} = (1 - X)·(1 - X)·R - C d·X^{d-1}·(1 - X)·C G
= (1 - X)·S_{d,1}`. -/
theorem Tpoly_factor_one (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (G : ℂ) (R : Polynomial ℂ) :
    Tpoly (1 : ℂ) G d R = (1 - X) * Spoly_one G d R := by
  have hc : Cx (1 : ℂ) d = (d : ℂ) := Cx_one m hm d hd
  unfold Tpoly Spoly_one
  rw [hc]
  simp only [map_one, one_mul]
  ring

/-- Torsion subcase `x ≠ 1, x^d = 1`: `T_{d,x} = (1 - C x·X)·S_{d,x}` as polynomials in
`ℂ[X]`.  Since `C_x = 0`, `T_{d,x} = (1 - C x·X)·(1 - X)·R = (1 - C x·X)·S_{d,x}`. -/
theorem Tpoly_factor_torsion_ne (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x G : ℂ) (hx1 : x ≠ 1) (hxd : x ^ d = 1) (R : Polynomial ℂ) :
    Tpoly x G d R = (1 - C x * X) * Spoly_tors R := by
  have hc : Cx x d = 0 := Cx_torsion_ne m hm d hd x hx1 hxd
  unfold Tpoly Spoly_tors
  rw [hc]
  simp only [map_zero, zero_mul]
  ring

/-- Torsion subcase `x = 1`: the constant term of `S_{d,1}` equals `R(0) = -X₀`.
As with `Tpoly_coeff_zero`, the hypotheses `hm`, `hd` give `d - 1 ≠ 0`, so `X^{d-1}` does
not contribute to the constant term. -/
theorem Spoly_one_coeff_zero (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (G : ℂ) (R : Polynomial ℂ) (X₀ : ℂ) (hR0 : R.coeff 0 = -X₀) :
    (Spoly_one G d R).coeff 0 = -X₀ := by
  have hd1 : d - 1 ≠ 0 := by omega
  unfold Spoly_one
  rw [coeff_sub, coeff_mul]
  have h2 : (C (d : ℂ) * X ^ (d - 1) * C G).coeff 0 = 0 := by
    have : C (d : ℂ) * X ^ (d - 1) * C G = C ((d : ℂ) * G) * X ^ (d - 1) := by
      rw [C_mul]; ring
    rw [this, coeff_C_mul, coeff_X_pow, if_neg (by simpa [eq_comm] using hd1), mul_zero]
  rw [h2]
  simp [coeff_mul, hR0]

/-- Torsion subcase `x ≠ 1, x^d = 1`: the constant term of `S_{d,x} = (1 - X)·R` equals
`R(0) = -X₀`. -/
theorem Spoly_tors_coeff_zero (R : Polynomial ℂ) (X₀ : ℂ) (hR0 : R.coeff 0 = -X₀) :
    (Spoly_tors R).coeff 0 = -X₀ := by
  unfold Spoly_tors
  simp [coeff_mul, hR0]

/-! ## Main Statement(s)

All three statements are equalities in `𝕂 = RatFunc ℂ`.  The `q`-shift automorphism `σ`,
the opaque elements, and the run‑1 data all enter as hypotheses.
-/

/-! ### Sub-lemmas for the defect statement (Statement 1). -/

/-- **`KF:defect` (1a): homogeneous-coefficient collapse.**

`(σ M_d / (C q · U))·(x²·q·(U^d - 1)/(U^{d-3}·(U - 1))) = x²·M_d / U`.

Math argument.  Use the cleared shift law `(1 - U^d)·σ M_d = U^{d-3}·(1 - U)·M_d`.
Rewrite `U^d - 1 = -(1 - U^d)` and `U - 1 = -(1 - U)` so the two minus signs cancel; the
`q` in the numerator cancels the `1/(Cq·U)`.  Concretely
`σ M_d · (U^d - 1)/(U^{d-3}·(U-1)) = σ M_d · (1-U^d)/(U^{d-3}·(1-U))`
` = (U^{d-3}·(1-U)·M_d)/(U^{d-3}·(1-U)) = M_d` after cancelling `(1-U^d)` via the shift law,
leaving `x²·M_d/U` once the `q` cancels.  All denominators (`U`, `U^{d-3}`, `1-U`, `1-U^d`,
`Cq`) are nonzero in `𝕂`.

Formal-phase strategy: establish the nonvanishing facts (`U ≠ 0` via `U_ne_zero`;
`U^{d-3} ≠ 0` from `pow_ne_zero`; `1 - U ≠ 0` via `one_sub_U_pow_ne_zero` with exponent 1 —
i.e. `1 - U^1`; `1 - U^d ≠ 0`; `Cq ≠ 0` via `RatFunc.C` injectivity and `q.ne_zero`), then
`field_simp` and use `hMd` (rearranged) to cancel, finishing with `ring`.  The key rewrite:
from `hMd`, `σ Md = U^{d-3}·(1-U)·Md/(1-U^d)`; substitute and simplify. -/
theorem KF_defect_1a
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x q : ℂˣ)
    (σ : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ) (hσ : σ U = RatFunc.C (q : ℂ) * U)
    (Md : Kf)
    (hMd : (1 - U ^ d) * σ Md = U ^ (d - 3) * (1 - U) * Md) :
    (σ Md / (RatFunc.C (q : ℂ) * U))
        * (RatFunc.C ((x : ℂ) ^ 2 * (q : ℂ)) * (U ^ d - 1) / (U ^ (d - 3) * (U - 1)))
      = RatFunc.C ((x : ℂ) ^ 2) * Md / U := by
  have hUne : (U : Kf) ≠ 0 := U_ne_zero
  have hU3 : (U : Kf) ^ (d - 3) ≠ 0 := pow_ne_zero _ hUne
  have hUm1 : (1 : Kf) - U ≠ 0 := by
    have := one_sub_U_pow_ne_zero (d := 1) (by omega); simpa using this
  have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero (by omega)
  have hCq : (RatFunc.C (q : ℂ) : Kf) ≠ 0 := by
    intro h
    have h0 : (RatFunc.C (q : ℂ) : Kf) = RatFunc.C 0 := by rw [h, map_zero]
    exact q.ne_zero (RatFunc.C_injective (K := ℂ) h0)
  -- rewrite the sign-flipped factors
  have e1 : (U : Kf) ^ d - 1 = -(1 - U ^ d) := by ring
  have e2 : (U : Kf) - 1 = -(1 - U) := by ring
  -- σ Md solved from hMd
  have hσMd : σ Md = U ^ (d - 3) * (1 - U) * Md / (1 - U ^ d) := by
    rw [eq_div_iff hUd, mul_comm _ (1 - U ^ d)]; exact hMd
  rw [hσMd, e1, e2, map_mul]
  field_simp

/-- **`KF:defect` (1b), fractional form: the twisted defect equation.**

`σ K - x²·K = M_d / (U·(1 - U^d)·(1 - x·U))·T̂_{d,x}`.

Math argument (from `AxiomDysonSystems.tex` eqs (4.10),(4.3)).  `K = (M_d/U)·𝓖`, so
`σ K = (σ M_d / (Cq·U))·σ 𝓖` (using `σ U = Cq·U`).  Substitute the master functional
equation `hmaster` for `σ 𝓖`, whose three terms are: (i) the homogeneous term
`x²q(U^d-1)/(U^{d-3}(U-1))·𝓖`, which combined with `σ M_d/(Cq·U)` collapses (by 1a) to
`x²·(M_d/U)·𝓖 = x²·K`; (ii) the inhomogeneous run-1 term `(q/U^{d-3})·R̂`; and (iii) the
`-C_x·q·U²/(1-x·U)·G` term.  Subtracting `x²·K` cancels term (i), leaving
`σ K - x²·K = (σ M_d/(Cq·U))·[(q/U^{d-3})·R̂ - C_x·q·U²/(1-x·U)·G]`.  Using the shift law
`σ M_d = U^{d-3}(1-U)M_d/(1-U^d)`, this simplifies to
`M_d/(U(1-U^d)(1-x·U))·[(1-x·U)(1-U)R̂ - C_x·U^{d-1}·(1-U)·G·... ]`, and the bracket is
exactly `T̂_{d,x} = (1 - C x·X)·(1-X)·R - C(C_x)·X^{d-1}·(1-X)·C G` mapped into `𝕂` (recall
`X̂ = U`, `toField` is a ring hom, and `Tpoly` unfolds to precisely this combination).

Formal-phase strategy: `rw [hK]`, push `σ` through the product via `map_mul`, `hσ`,
`sigma_fix_C`; `rw [hmaster]`; use 1a (`KF_defect_1a`) to collapse the homogeneous term;
express `σ Md` from `hMd`; expand `toField (Tpoly …)` via `map_sub/map_mul/map_pow`,
`toField_C`, `toField_X`; establish all denominator ≠ 0 facts and finish with `field_simp`
+ `ring`.  This is the algebraic heart of Statement 1 and the main remaining work item. -/
theorem KF_defect_1b_frac
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x q : ℂˣ)
    (σ : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ) (hσ : σ U = RatFunc.C (q : ℂ) * U)
    (Md 𝓖 K : Kf)
    (hMd : (1 - U ^ d) * σ Md = U ^ (d - 3) * (1 - U) * Md)
    (hK : K = (Md / U) * 𝓖)
    (G : ℂ) (X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2) (hR0 : R.coeff 0 = -X₀)
    (hmaster : σ 𝓖 =
        RatFunc.C ((x : ℂ) ^ 2 * (q : ℂ)) * (U ^ d - 1) / (U ^ (d - 3) * (U - 1)) * 𝓖
        + RatFunc.C ((q : ℂ)) / U ^ (d - 3) * toField R
        - RatFunc.C (Cx (x : ℂ) d * (q : ℂ) * G) * U ^ 2 / (1 - RatFunc.C (x : ℂ) * U)) :
    σ K - RatFunc.C ((x : ℂ) ^ 2) * K
      = Md / (U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U)) * toField (Tpoly (x : ℂ) G d R) := by
  -- nonzero facts
  have hUne : (U : Kf) ≠ 0 := U_ne_zero
  have hU3 : (U : Kf) ^ (d - 3) ≠ 0 := pow_ne_zero _ hUne
  have hUm1 : (1 : Kf) - U ≠ 0 := by
    have := one_sub_U_pow_ne_zero (d := 1) (by omega); simpa using this
  have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero (by omega)
  have hxU : (1 : Kf) - RatFunc.C (x : ℂ) * U ≠ 0 := one_sub_C_mul_U_ne_zero x.ne_zero
  have hCq : (RatFunc.C (q : ℂ) : Kf) ≠ 0 := by
    intro h
    have h0 : (RatFunc.C (q : ℂ) : Kf) = RatFunc.C 0 := by rw [h, map_zero]
    exact q.ne_zero (RatFunc.C_injective (K := ℂ) h0)
  -- σ K in terms of σ Md and σ 𝓖
  have hσK : σ K = (σ Md / (RatFunc.C (q : ℂ) * U)) * σ 𝓖 := by
    rw [hK, map_mul, map_div₀, hσ]
  -- collapse homogeneous term via 1a
  have h1a := KF_defect_1a m hm d hd x q σ hσ Md hMd
  -- x² * K = (x² Md / U) * 𝓖
  have hx2K : RatFunc.C ((x : ℂ) ^ 2) * K = (RatFunc.C ((x : ℂ) ^ 2) * Md / U) * 𝓖 := by
    rw [hK]; ring
  -- σ Md solved from hMd
  have hσMd : σ Md = U ^ (d - 3) * (1 - U) * Md / (1 - U ^ d) := by
    rw [eq_div_iff hUd, mul_comm _ (1 - U ^ d)]; exact hMd
  -- expand toField (Tpoly …)
  have hT : toField (Tpoly (x : ℂ) G d R) =
      (1 - RatFunc.C (x : ℂ) * U) * (1 - U) * toField R
        - RatFunc.C (Cx (x : ℂ) d) * U ^ (d - 1) * (1 - U) * RatFunc.C G := by
    unfold Tpoly toField
    rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_mul, map_sub, map_sub,
        map_one, map_mul, map_pow]
    simp only [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rfl
  -- rewrite σ K, subtract, then substitute hmaster
  rw [hσK, hmaster]
  -- distribute the product over the three terms of hmaster
  have hdist : (σ Md / (RatFunc.C (q : ℂ) * U)) *
      (RatFunc.C ((x : ℂ) ^ 2 * (q : ℂ)) * (U ^ d - 1) / (U ^ (d - 3) * (U - 1)) * 𝓖
        + RatFunc.C ((q : ℂ)) / U ^ (d - 3) * toField R
        - RatFunc.C (Cx (x : ℂ) d * (q : ℂ) * G) * U ^ 2 / (1 - RatFunc.C (x : ℂ) * U))
      = (σ Md / (RatFunc.C (q : ℂ) * U)) *
          (RatFunc.C ((x : ℂ) ^ 2 * (q : ℂ)) * (U ^ d - 1) / (U ^ (d - 3) * (U - 1))) * 𝓖
        + (σ Md / (RatFunc.C (q : ℂ) * U)) * (RatFunc.C ((q : ℂ)) / U ^ (d - 3) * toField R)
        - (σ Md / (RatFunc.C (q : ℂ) * U)) *
            (RatFunc.C (Cx (x : ℂ) d * (q : ℂ) * G) * U ^ 2 / (1 - RatFunc.C (x : ℂ) * U)) := by
    ring
  rw [hdist, h1a, hx2K]
  -- now the first term matches x²K; cancel it
  rw [hT, hσMd]
  have hpow : (U : Kf) ^ (d - 1) = U ^ (d - 3) * U ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  have hxU' : (1 : Kf) - U * RatFunc.C (x : ℂ) ≠ 0 := by rw [mul_comm]; exact hxU
  simp only [map_mul]
  field_simp [hxU']
  ring

/-- **Statement 1 (Key Formula `KF:defect`).**

Assume `hm : 2 ≤ m`, `x q : ℂˣ`, the scaling automorphism `σ` with `σ U = C q · U`, the
`M_d` `q`-shift law (Definition 2), the definition `K = (M_d / U)·𝓖` (Definition 3), and the
master functional equation (Definition 4) for the run‑1 polynomial `R` of degree `≤ d - 2`
with `R(0) = - X₀`. Then, with `T_{d,x}` as in Definition 5, all three parts hold in `𝕂`.

**(1a)** Homogeneous‑coefficient collapse (no residual factor `q`):
`(σ M_d / (C q · U))·(x²·q·(U^d - 1)/(U^{d-3}·(U - 1))) = x²·M_d / U`.

**(1b)** Twisted defect equation, both in the fractional form
`σ K - x²·K = M_d / (U·(1 - U^d)·(1 - x·U))·T̂_{d,x}` and in the cleared
(inversion‑free) polynomial‑numerator form
`(U·(1 - U^d)·(1 - x·U))·(σ K - x²·K) = M_d · T̂_{d,x}`. -/
theorem KF_defect
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x q : ℂˣ)
    (σ : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ) (hσ : σ U = RatFunc.C (q : ℂ) * U)
    (Md 𝓖 K : Kf)
    -- Definition 2 : the `M_d` q-shift law (cleared form).
    (hMd : (1 - U ^ d) * σ Md = U ^ (d - 3) * (1 - U) * Md)
    -- Definition 3 : `K = (M_d / U)·𝓖`.
    (hK : K = (Md / U) * 𝓖)
    -- The run‑1 scalar `G`.
    (G : ℂ)
    -- Run‑1 data : the polynomial `R` with its degree bound and constant term.
    (X₀ : ℂ) (R : Polynomial ℂ) (hRdeg : R.natDegree ≤ d - 2) (hR0 : R.coeff 0 = -X₀)
    -- Definition 4 : the master functional equation (an equality in `𝕂`).
    -- (the last term carries the scalar coefficient `C_x · q · G`).
    (hmaster : σ 𝓖 =
        RatFunc.C ((x : ℂ) ^ 2 * (q : ℂ)) * (U ^ d - 1) / (U ^ (d - 3) * (U - 1)) * 𝓖
        + RatFunc.C ((q : ℂ)) / U ^ (d - 3) * toField R
        - RatFunc.C (Cx (x : ℂ) d * (q : ℂ) * G) * U ^ 2 / (1 - RatFunc.C (x : ℂ) * U)) :
    -- (1a)
    ((σ Md / (RatFunc.C (q : ℂ) * U))
        * (RatFunc.C ((x : ℂ) ^ 2 * (q : ℂ)) * (U ^ d - 1) / (U ^ (d - 3) * (U - 1)))
      = RatFunc.C ((x : ℂ) ^ 2) * Md / U)
    ∧
    -- (1b), fractional form
    (σ K - RatFunc.C ((x : ℂ) ^ 2) * K
      = Md / (U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U)) * toField (Tpoly (x : ℂ) G d R))
    ∧
    -- (1b), cleared form
    ((U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U)) * (σ K - RatFunc.C ((x : ℂ) ^ 2) * K)
      = Md * toField (Tpoly (x : ℂ) G d R)) := by
  -- Decompose into the three parts.  (1a) is the coefficient-collapse field identity;
  -- (1b)-fractional is the twisted defect equation; (1b)-cleared follows from
  -- (1b)-fractional by multiplying through the (nonzero) denominator.
  refine ⟨?_, ?_, ?_⟩
  · -- (1a) coefficient collapse
    exact KF_defect_1a m hm d hd x q σ hσ Md hMd
  · -- (1b) fractional form
    exact KF_defect_1b_frac m hm d hd x q σ hσ Md 𝓖 K hMd hK G X₀ R hRdeg hR0 hmaster
  · -- (1b) cleared form: multiply the fractional identity by the denominator.
    have hfrac := KF_defect_1b_frac m hm d hd x q σ hσ Md 𝓖 K hMd hK G X₀ R hRdeg hR0 hmaster
    have hUne : (U : Kf) ≠ 0 := U_ne_zero
    have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero (by omega)
    have hxU : (1 : Kf) - RatFunc.C (x : ℂ) * U ≠ 0 := one_sub_C_mul_U_ne_zero x.ne_zero
    have hdne : U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hUne hUd) hxU
    rw [hfrac, div_mul_eq_mul_div, mul_comm, div_mul_cancel₀ _ hdne]

/-! ### Sub-lemmas for the residues (partial-fraction) statements.

Each `KF_residues_*` theorem is a conjunction of "easy" facts (nonvanishing of scalars
and linear factors, factorizations) that follow from the already-proven helpers, and one
genuinely hard leaf: the partial-fraction identity in `𝕂 = RatFunc ℂ`.  We factor the
three PF-identity leaves out as the named sub-lemmas below so that the top-level theorems
reduce to `⟨easy₁, …, PF_lemma …⟩`.  The PF sub-lemmas are the real analytic/algebraic
work and carry a `sorry` for the next (formal) phase. -/

/-- Scalar nonvanishing: `1 - x·ω^{-r} ≠ 0` for `r < d`, when `ω` is a primitive `d`-th
root of unity and `x^d ≠ 1`.

Argument: if `1 - x·ω^{-r} = 0` then `x = ω^r` (since `ω^{-r}` is a unit), hence
`x^d = ω^{rd} = (ω^d)^r = 1` (as `ω^d = 1`), contradicting `x^d ≠ 1`. -/
theorem scalar_nonvanish_gen (d : ℕ) (x : ℂ) (hxd : x ^ d ≠ 1)
    (ω : ℂ) (hω : IsPrimitiveRoot ω d) :
    ∀ r < d, (1 : ℂ) - x * ω⁻¹ ^ r ≠ 0 := by
  intro r hr h
  have hd0 : d ≠ 0 := by omega
  have hωne : ω ≠ 0 := hω.ne_zero hd0
  have hωrne : ω ^ r ≠ 0 := pow_ne_zero r hωne
  -- from h: x * ω⁻¹^r = 1
  have h1 : x * ω⁻¹ ^ r = 1 := (sub_eq_zero.mp h).symm
  -- hence x = ω^r
  have hx : x = ω ^ r := by
    rw [inv_pow] at h1
    field_simp at h1
    linear_combination h1
  have hxd1 : x ^ d = 1 := by
    rw [hx, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  exact hxd hxd1

/-- Scalar nonvanishing: `1 - x^{-d} ≠ 0` when `x^d ≠ 1`.

Argument: `x^{-d} = (x^d)⁻¹`; if this equals `1` then `x^d = 1` (both sides are units),
contradicting `x^d ≠ 1`. -/
theorem scalar_nonvanish_Ex (d : ℕ) (x : ℂ) (hx : x ≠ 0) (hxd : x ^ d ≠ 1) :
    (1 : ℂ) - x⁻¹ ^ d ≠ 0 := by
  -- Hint (formal phase): rw [inv_pow]; intro h; from sub_eq_zero get (x^d)⁻¹ = 1,
  -- so x^d = 1 (inv_eq_one), contradiction. x^d ≠ 0 from pow_ne_zero hx.
  simp_all [inv_pow, sub_eq_zero, inv_eq_one]

/-- Linear-factor nonvanishing: `1 - ω^r·U ≠ 0` in `𝕂`, when `ω ≠ 0` (in particular for a
root of unity from a `ℂˣ`).  Directly from `one_sub_C_mul_U_ne_zero` with `c = ω^r ≠ 0`. -/
theorem lin_factor_ne (ω : ℂ) (hω : ω ≠ 0) (r : ℕ) :
    (1 : Kf) - RatFunc.C (ω ^ r) * U ≠ 0 :=
  one_sub_C_mul_U_ne_zero (pow_ne_zero r hω)

/-! ### Root-of-unity foundation lemmas for the partial-fraction identities. -/

/-- `r ↦ ω^r` is injective on `range d` when `ω` is a primitive `d`-th root of unity. -/
theorem omega_pow_inj (d : ℕ) (ω : ℂ) (hω : IsPrimitiveRoot ω d) :
    Set.InjOn (fun r => ω ^ r) (Finset.range d) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  exact hω.pow_inj ha hb hab

/-- `r ↦ ω⁻¹^r` is injective on `range d` when `ω` is a primitive `d`-th root of unity. -/
theorem omega_inv_pow_inj (d : ℕ) (ω : ℂ) (hω : IsPrimitiveRoot ω d) :
    Set.InjOn (fun r => ω⁻¹ ^ r) (Finset.range d) := by
  have hωinv : IsPrimitiveRoot ω⁻¹ d := (IsPrimitiveRoot.inv_iff).mpr hω
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  exact hωinv.pow_inj ha hb hab

/-- **(★) Root-of-unity factorization.** `1 - X^d = ∏_{r<d}(1 - C(ω^r)·X)` in `ℂ[X]`,
for `ω` a primitive `d`-th root of unity. -/
theorem star_factorization (d : ℕ) (hd : 0 < d) (ω : ℂ) (hω : IsPrimitiveRoot ω d) :
    (1 : Polynomial ℂ) - X ^ d = ∏ r ∈ Finset.range d, (1 - C (ω ^ r) * X) := by
  have hωne : ω ≠ 0 := hω.ne_zero (by omega)
  have hωinvne : ω⁻¹ ≠ 0 := inv_ne_zero hωne
  set P : Polynomial ℂ := (1 - X ^ d) - ∏ r ∈ Finset.range d, (1 - C (ω ^ r) * X) with hP
  rw [← sub_eq_zero]
  show P = 0
  set S : Finset ℂ := insert 0 ((Finset.range d).image (fun r => ω⁻¹ ^ r)) with hS
  have hdegLHS : (1 - X ^ d : Polynomial ℂ).natDegree ≤ d := by
    apply le_trans (natDegree_sub_le _ _)
    simp
  have hdegRHS : (∏ r ∈ Finset.range d, (1 - C (ω ^ r) * X) : Polynomial ℂ).natDegree ≤ d := by
    apply le_trans (natDegree_prod_le _ _)
    calc ∑ r ∈ Finset.range d, (1 - C (ω ^ r) * X : Polynomial ℂ).natDegree
        ≤ ∑ _r ∈ Finset.range d, 1 := by
          apply Finset.sum_le_sum
          intro r _
          apply le_trans (natDegree_sub_le _ _)
          apply max_le
          · simp
          · apply le_trans (natDegree_mul_le)
            simp
      _ = d := by simp
  have hdegP : P.natDegree ≤ d := by
    rw [hP]; exact le_trans (natDegree_sub_le _ _) (max_le hdegLHS hdegRHS)
  have hcardS : S.card = d + 1 := by
    rw [hS, Finset.card_insert_of_notMem]
    · rw [Finset.card_image_of_injOn (omega_inv_pow_inj d ω hω), Finset.card_range]
    · simp only [Finset.mem_image, Finset.mem_range, not_exists]
      rintro r ⟨_, hcontra⟩
      exact (pow_ne_zero r hωinvne) hcontra
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P S
  · intro c hc
    rw [hS] at hc
    rw [Finset.mem_insert] at hc
    rcases hc with hc0 | hcim
    · subst hc0
      rw [hP]
      simp only [eval_sub, eval_one, eval_pow, eval_X, eval_prod, eval_mul, eval_C]
      rw [zero_pow (by omega : d ≠ 0)]
      rw [Finset.prod_eq_one]
      · ring
      · intro r _; ring
    · rw [Finset.mem_image] at hcim
      obtain ⟨t, ht, rfl⟩ := hcim
      simp only [Finset.mem_range] at ht
      rw [hP]
      simp only [eval_sub, eval_one, eval_pow, eval_X, eval_prod, eval_mul, eval_C]
      have h1 : (ω⁻¹ ^ t) ^ d = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        rw [inv_pow, hω.pow_eq_one, inv_one, one_pow]
      rw [h1]
      have hprod0 : ∏ r ∈ Finset.range d, (1 - ω ^ r * ω⁻¹ ^ t) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_range.mpr ht)
        rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero t hωne), sub_self]
      rw [hprod0]
      ring
  · rw [hcardS]; omega

/-- **(†) The value `∏_{k=1}^{d-1}(1 - ω^k) = d`.** -/
theorem prod_one_sub_omega (d : ℕ) (hd : 0 < d) (ω : ℂ) (hω : IsPrimitiveRoot ω d) :
    ∏ k ∈ Finset.Ico 1 d, (1 - ω ^ k) = (d : ℂ) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have h := hω.prod_one_sub_pow_eq_order
  rw [Nat.cast_add, Nat.cast_one, ← h]
  rw [Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  congr 2
  omega

/-- Helper: `∏_{s ∈ (range d).erase t}(1 - ω^s·ω⁻¹^t) = d` for a primitive `d`-th root
of unity `ω` and `t < d`.  Reindex via `s ↦ (s + d - t) % d` onto `Ico 1 d` and use
`prod_one_sub_omega`. -/
theorem prod_erase_omega_eq_d (d : ℕ) (hd : 0 < d) (ω : ℂ) (hω : IsPrimitiveRoot ω d)
    (t : ℕ) (ht : t < d) :
    ∏ s ∈ (Finset.range d).erase t, (1 - ω ^ s * ω⁻¹ ^ t) = (d : ℂ) := by
  have hωne : ω ≠ 0 := hω.ne_zero (by omega)
  rw [← prod_one_sub_omega d hd ω hω]
  apply Finset.prod_nbij' (fun s => (s + d - t) % d) (fun k => (k + t) % d)
  · -- maps into Ico 1 d
    intro s hs
    rw [Finset.mem_erase, Finset.mem_range] at hs
    obtain ⟨hst, hsd⟩ := hs
    rw [Finset.mem_Ico]
    -- compute (s + d - t) % d explicitly by casing on s vs t
    rcases lt_or_ge s t with hlt | hge
    · have he : s + d - t = s + (d - t) := by omega
      rw [he, Nat.mod_eq_of_lt (by omega)]
      omega
    · have he : s + d - t = (s - t) + d := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  · -- maps into erase
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk1, hkd⟩ := hk
    rw [Finset.mem_erase, Finset.mem_range]
    rcases lt_or_ge (k + t) d with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have he : k + t = (k + t - d) + d := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  · -- left inverse: ((s + d - t) % d + t) % d = s
    intro s hs
    rw [Finset.mem_erase, Finset.mem_range] at hs
    obtain ⟨hst, hsd⟩ := hs
    -- first compute the inner mod value via a case split, stored as a plain value v
    rcases lt_or_ge s t with hlt | hge
    · have hinner : (s + d - t) % d = s + (d - t) := by
        have he : s + d - t = s + (d - t) := by omega
        rw [he, Nat.mod_eq_of_lt (by omega)]
      rw [hinner]
      have he2 : s + (d - t) + t = s + d := by omega
      rw [he2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hinner : (s + d - t) % d = s - t := by
        have he : s + d - t = (s - t) + d := by omega
        rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hinner]
      have he2 : s - t + t = s := by omega
      rw [he2, Nat.mod_eq_of_lt (by omega)]
  · -- right inverse: ((k + t) % d + d - t) % d = k
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk1, hkd⟩ := hk
    rcases lt_or_ge (k + t) d with hlt | hge
    · have hinner : (k + t) % d = k + t := Nat.mod_eq_of_lt hlt
      rw [hinner]
      have he : k + t + d - t = k + d := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hinner : (k + t) % d = k + t - d := by
        conv_lhs => rw [show k + t = (k + t - d) + d by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hinner]
      have he2 : k + t - d + d - t = k := by omega
      rw [he2, Nat.mod_eq_of_lt (by omega)]
  · -- values agree: 1 - ω^s * ω⁻¹^t = 1 - ω^((s+d-t)%d)
    intro s hs
    rw [Finset.mem_erase, Finset.mem_range] at hs
    obtain ⟨hst, hsd⟩ := hs
    congr 1
    -- ω^s * ω⁻¹^t = ω^((s + d - t) % d)
    set k := (s + d - t) % d with hk
    have hdiv : s + d - t = d * ((s + d - t) / d) + k := (Nat.div_add_mod (s + d - t) d).symm
    have hωpow : ω ^ (s + d - t) = ω ^ k := by
      rw [hdiv, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]
    have hst' : ω ^ s * ω⁻¹ ^ t = ω ^ (s + d - t) := by
      have hcancel : ω ^ (s + d - t) * ω ^ t = ω ^ s * ω⁻¹ ^ t * ω ^ t := by
        rw [inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero t hωne), mul_one,
          ← pow_add]
        have he : s + d - t + t = s + d := by omega
        rw [he, pow_add, hω.pow_eq_one, mul_one]
      exact (mul_right_cancel₀ (pow_ne_zero t hωne) hcancel.symm)
    rw [hst', hωpow]

/-- **Torsion PF core, polynomial form.**  For `S : ℂ[X]` with `natDegree S ≤ d` and
`S.coeff 0 = -X₀`, and `ω` a primitive `d`-th root of unity, the polynomial identity
`S = C(-X₀)·(1 - X^d) + ∑_r C(D_r)·X·∏_{s≠r}(1 - C(ω^s)·X)` holds in `ℂ[X]`, where
`D_r = ω^r/d·S(ω^{-r})`.  Proved by matching values at the `d+1` points `0, ω^{-t}`. -/
theorem PF_torsion_poly
    (d : ℕ) (hd : 0 < d)
    (ω : ℂ) (hω : IsPrimitiveRoot ω d)
    (X₀ : ℂ) (S : Polynomial ℂ)
    (hSdeg : S.natDegree ≤ d) (hS0 : S.coeff 0 = -X₀) :
    S = C (- X₀) * (1 - X ^ d)
        + ∑ r ∈ Finset.range d,
            C (ω ^ r / (d : ℂ) * S.eval (ω⁻¹ ^ r)) * X
              * ∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X) := by
  have hd0 : d ≠ 0 := by omega
  have hωne : ω ≠ 0 := hω.ne_zero hd0
  have hωinvne : ω⁻¹ ≠ 0 := inv_ne_zero hωne
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  -- name the RHS
  set RHS : Polynomial ℂ :=
    C (- X₀) * (1 - X ^ d)
      + ∑ r ∈ Finset.range d,
          C (ω ^ r / (d : ℂ) * S.eval (ω⁻¹ ^ r)) * X
            * ∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X) with hRHS
  set P : Polynomial ℂ := S - RHS with hP
  rw [← sub_eq_zero]
  show P = 0
  set T : Finset ℂ := insert 0 ((Finset.range d).image (fun r => ω⁻¹ ^ r)) with hT
  -- degree bound for RHS
  have hdegRHS : RHS.natDegree ≤ d := by
    rw [hRHS]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (natDegree_C_mul_le _ _) ?_
      refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_)
      simp
    · refine natDegree_sum_le_of_forall_le _ _ ?_
      intro r hr
      refine le_trans (natDegree_mul_le) ?_
      refine le_trans (add_le_add (natDegree_C_mul_le _ _) (le_refl _)) ?_
      rw [natDegree_X]
      have hprod : (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X)).natDegree
          ≤ d - 1 := by
        refine le_trans (natDegree_prod_le _ _) ?_
        calc ∑ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X).natDegree
            ≤ ∑ _s ∈ (Finset.range d).erase r, 1 := by
              apply Finset.sum_le_sum
              intro s _
              refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_)
              refine le_trans (natDegree_mul_le) (by simp)
          _ = ((Finset.range d).erase r).card := by simp
          _ ≤ d - 1 := by
              rw [Finset.card_erase_of_mem hr, Finset.card_range]
      omega
  have hdegP : P.natDegree ≤ d := by
    rw [hP]; exact le_trans (natDegree_sub_le _ _) (max_le hSdeg hdegRHS)
  have hcardT : T.card = d + 1 := by
    rw [hT, Finset.card_insert_of_notMem]
    · rw [Finset.card_image_of_injOn (omega_inv_pow_inj d ω hω), Finset.card_range]
    · simp only [Finset.mem_image, Finset.mem_range, not_exists]
      rintro r ⟨_, hcontra⟩
      exact (pow_ne_zero r hωinvne) hcontra
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P T
  · intro c hc
    rw [hT, Finset.mem_insert] at hc
    rw [hP, eval_sub, sub_eq_zero]
    rcases hc with hc0 | hcim
    · -- c = 0
      subst hc0
      -- LHS: S.eval 0 = -X₀
      have hSeval : S.eval 0 = -X₀ := by
        rw [← coeff_zero_eq_eval_zero]; exact hS0
      rw [hSeval, hRHS]
      rw [eval_add, eval_finset_sum]
      have hsum0 : (∑ r ∈ Finset.range d,
          (C (ω ^ r / (d : ℂ) * S.eval (ω⁻¹ ^ r)) * X
            * ∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X)).eval 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r _
        simp
      rw [hsum0]
      simp [zero_pow hd0]
    · -- c = ω⁻¹^t
      rw [Finset.mem_image] at hcim
      obtain ⟨t, ht, rfl⟩ := hcim
      simp only [Finset.mem_range] at ht
      rw [hRHS]
      rw [eval_add, eval_finset_sum]
      -- first term: eval at ω⁻¹^t of C(-X₀)*(1-X^d) = 0
      have hfirst : (C (- X₀) * (1 - X ^ d)).eval (ω⁻¹ ^ t) = 0 := by
        have h1 : (ω⁻¹ ^ t) ^ d = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, inv_pow, hω.pow_eq_one, inv_one, one_pow]
        rw [eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X, h1]
        ring
      rw [hfirst, zero_add]
      -- sum reduces to the r = t term
      rw [Finset.sum_eq_single t]
      · -- r = t term
        have hprodval :
            (∏ s ∈ (Finset.range d).erase t, (1 - ω ^ s * ω⁻¹ ^ t)) = (d : ℂ) :=
          prod_erase_omega_eq_d d hd ω hω t ht
        simp only [eval_mul, eval_C, eval_X, eval_prod, eval_sub, eval_one]
        rw [hprodval]
        -- ω^t * ω⁻¹^t = 1
        have hcancel : ω ^ t * ω⁻¹ ^ t = 1 := by
          rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero t hωne)]
        rw [show ω ^ t / (d : ℂ) * S.eval (ω⁻¹ ^ t) * ω⁻¹ ^ t * (d : ℂ)
              = S.eval (ω⁻¹ ^ t) * (ω ^ t * ω⁻¹ ^ t) * ((d : ℂ) / (d : ℂ)) by ring]
        rw [hcancel, div_self hdC]; ring
      · -- r ≠ t terms vanish
        intro r hr hrt
        have htmem : t ∈ (Finset.range d).erase r :=
          Finset.mem_erase.mpr ⟨Ne.symm hrt, Finset.mem_range.mpr ht⟩
        simp only [eval_mul, eval_C, eval_X, eval_prod, eval_sub, eval_one]
        have hprod0 : (∏ s ∈ (Finset.range d).erase r, (1 - ω ^ s * ω⁻¹ ^ t)) = 0 := by
          apply Finset.prod_eq_zero htmem
          rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero t hωne), sub_self]
        rw [hprod0]; ring
      · intro htcontra
        exact absurd (Finset.mem_range.mpr ht) htcontra
  · rw [hcardT]; omega

/-- Field version of `star_factorization`: `1 - U^d = ∏_{r<d}(1 - C(ω^r)·U)` in `𝕂`. -/
theorem star_factorization_field (d : ℕ) (hd : 0 < d) (ω : ℂ) (hω : IsPrimitiveRoot ω d) :
    (1 : Kf) - U ^ d = ∏ r ∈ Finset.range d, (1 - RatFunc.C (ω ^ r) * U) := by
  have hpoly := star_factorization d hd ω hω
  have h := congrArg toField hpoly
  have hlhs : toField (1 - X ^ d) = (1 : Kf) - U ^ d := by
    unfold toField
    rw [map_sub, map_one, map_pow, RatFunc.algebraMap_X]; rfl
  have hrhs : toField (∏ r ∈ Finset.range d, (1 - C (ω ^ r) * X))
      = ∏ r ∈ Finset.range d, (1 - RatFunc.C (ω ^ r) * U) := by
    unfold toField
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro r _
    rw [map_sub, map_one, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rfl
  rw [hlhs, hrhs] at h
  exact h

/-- **Torsion PF core, field form.**  For `S : ℂ[X]` with `natDegree S ≤ d` and
`S.coeff 0 = -X₀`, and `ω` a primitive `d`-th root of unity, the field identity
`toField S / (U·(1-U^d)) = C(-X₀)/U + ∑_r C(ω^r/d·S(ω^{-r}))/(1-C(ω^r)·U)` holds in `𝕂`. -/
theorem PF_torsion_field
    (d : ℕ) (hd : 0 < d)
    (ω : ℂ) (hω : IsPrimitiveRoot ω d)
    (X₀ : ℂ) (S : Polynomial ℂ)
    (hSdeg : S.natDegree ≤ d) (hS0 : S.coeff 0 = -X₀) :
    toField S / (U * (1 - U ^ d))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (ω ^ r / (d : ℂ) * S.eval (ω⁻¹ ^ r)) / (1 - RatFunc.C (ω ^ r) * U) := by
  have hd0 : d ≠ 0 := by omega
  have hωne : ω ≠ 0 := hω.ne_zero hd0
  have hUne : (U : Kf) ≠ 0 := U_ne_zero
  have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero hd
  have hpoly := PF_torsion_poly d hd ω hω X₀ S hSdeg hS0
  have hfield := congrArg toField hpoly
  have hpush : ∀ p : Polynomial ℂ, toField p = toField p := fun _ => rfl
  have hstarprod : ∀ r, toField (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X))
      = ∏ s ∈ (Finset.range d).erase r, (1 - RatFunc.C (ω ^ s) * U) := by
    intro r
    unfold toField
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro s _
    rw [map_sub, map_one, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rfl
  have hL : toField S =
      RatFunc.C (- X₀) * (1 - U ^ d)
        + ∑ r ∈ Finset.range d,
            RatFunc.C (ω ^ r / (d : ℂ) * S.eval (ω⁻¹ ^ r)) * U
              * ∏ s ∈ (Finset.range d).erase r, (1 - RatFunc.C (ω ^ s) * U) := by
    rw [hfield]
    unfold toField
    rw [map_add, map_mul, map_sub, map_one, map_pow, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [map_mul, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [show (algebraMap (Polynomial ℂ) (RatFunc ℂ))
          (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X))
        = ∏ s ∈ (Finset.range d).erase r, (1 - RatFunc.C (ω ^ s) * U) from hstarprod r]
    rfl
  have hsf := star_factorization_field d hd ω hω
  have hsplit : ∀ r ∈ Finset.range d,
      (1 : Kf) - U ^ d
        = (1 - RatFunc.C (ω ^ r) * U) * ∏ s ∈ (Finset.range d).erase r,
            (1 - RatFunc.C (ω ^ s) * U) := by
    intro r hr
    rw [hsf]
    exact (Finset.mul_prod_erase (Finset.range d) _ hr).symm
  have hlin : ∀ r ∈ Finset.range d, (1 : Kf) - RatFunc.C (ω ^ r) * U ≠ 0 := by
    intro r _; exact lin_factor_ne ω hωne r
  rw [hL, div_eq_iff (mul_ne_zero hUne hUd), add_mul]
  congr 1
  · field_simp
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hsplit r hr]
    have hne := hlin r hr
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hne]
    ring

/-- **General PF core, polynomial form.**  The polynomial identity underlying `PF_general`,
matched at the `d + 2` distinct points `0`, `ω⁻¹^t` (`t < d`), and `x⁻¹`. -/
theorem PF_general_poly
    (d : ℕ) (hd : 0 < d)
    (x : ℂ) (hx : x ≠ 0) (hxd : x ^ d ≠ 1)
    (ω : ℂ) (hω : IsPrimitiveRoot ω d)
    (G X₀ : ℂ) (R : Polynomial ℂ)
    (hTdeg : (Tpoly x G d R).natDegree ≤ d)
    (hT0 : (Tpoly x G d R).coeff 0 = -X₀) :
    Tpoly x G d R
      = C (- X₀) * (1 - X ^ d) * (1 - C x * X)
        + ∑ r ∈ Finset.range d,
            C (Dgen x G d R ω r) * X
              * (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X))
              * (1 - C x * X)
        + C (Ex x G d R) * X * (1 - X ^ d) := by
  have hd0 : d ≠ 0 := by omega
  have hωne : ω ≠ 0 := hω.ne_zero hd0
  have hωinvne : ω⁻¹ ≠ 0 := inv_ne_zero hωne
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hxinvne : x⁻¹ ≠ 0 := inv_ne_zero hx
  set RHS : Polynomial ℂ :=
    C (- X₀) * (1 - X ^ d) * (1 - C x * X)
      + ∑ r ∈ Finset.range d,
          C (Dgen x G d R ω r) * X
            * (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X))
            * (1 - C x * X)
      + C (Ex x G d R) * X * (1 - X ^ d) with hRHS
  set P : Polynomial ℂ := Tpoly x G d R - RHS with hP
  rw [← sub_eq_zero]
  show P = 0
  set T : Finset ℂ := insert 0 (insert x⁻¹ ((Finset.range d).image (fun r => ω⁻¹ ^ r))) with hT
  -- x⁻¹ is not a torsion point (else x^d = 1)
  have hxinv_notmem : x⁻¹ ∉ (Finset.range d).image (fun r => ω⁻¹ ^ r) := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists]
    rintro r ⟨hr, hcontra⟩
    apply hxd
    have hxeq : x = ω ^ r := by
      have hinv := congrArg (·⁻¹) hcontra
      simp only [inv_inv, inv_pow] at hinv
      rw [hinv]
    rw [hxeq, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have h0_notmem : (0 : ℂ) ∉ insert x⁻¹ ((Finset.range d).image (fun r => ω⁻¹ ^ r)) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or, not_exists]
    refine ⟨(Ne.symm hxinvne), ?_⟩
    rintro r ⟨_, hcontra⟩
    exact (pow_ne_zero r hωinvne) hcontra
  -- degree bound for RHS: ≤ d + 1
  have hdegRHS : RHS.natDegree ≤ d + 1 := by
    rw [hRHS]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · -- C(-X₀)*(1-X^d)*(1-C x*X)
      refine le_trans (natDegree_mul_le) ?_
      refine le_trans (add_le_add (natDegree_mul_le) (le_refl _)) ?_
      have h1 : (C (-X₀)).natDegree = 0 := natDegree_C _
      have h2 : (1 - X ^ d : Polynomial ℂ).natDegree ≤ d := by
        refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_); simp
      have h3 : (1 - C x * X : Polynomial ℂ).natDegree ≤ 1 := by
        refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_)
        refine le_trans (natDegree_C_mul_le _ _) (by simp)
      omega
    · -- sum term
      refine natDegree_sum_le_of_forall_le _ _ ?_
      intro r hr
      refine le_trans (natDegree_mul_le) ?_
      have hlast : (1 - C x * X : Polynomial ℂ).natDegree ≤ 1 := by
        refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_)
        refine le_trans (natDegree_C_mul_le _ _) (by simp)
      refine le_trans (add_le_add (le_refl _) hlast) ?_
      refine le_trans (add_le_add (natDegree_mul_le) (le_refl _)) ?_
      refine le_trans (add_le_add (add_le_add (natDegree_C_mul_le _ _) (le_refl _)) (le_refl _)) ?_
      rw [natDegree_X]
      have hprod : (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X)).natDegree
          ≤ d - 1 := by
        refine le_trans (natDegree_prod_le _ _) ?_
        calc ∑ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X).natDegree
            ≤ ∑ _s ∈ (Finset.range d).erase r, 1 := by
              apply Finset.sum_le_sum
              intro s _
              refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_)
              refine le_trans (natDegree_mul_le) (by simp)
          _ = ((Finset.range d).erase r).card := by simp
          _ ≤ d - 1 := by rw [Finset.card_erase_of_mem hr, Finset.card_range]
      omega
    · -- C(Ex)*X*(1-X^d)
      refine le_trans (natDegree_mul_le) ?_
      have h2 : (1 - X ^ d : Polynomial ℂ).natDegree ≤ d := by
        refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_); simp
      refine le_trans (add_le_add (natDegree_mul_le) h2) ?_
      have h1 : (C (Ex x G d R)).natDegree = 0 := natDegree_C _
      rw [h1, natDegree_X]; omega
  have hdegP : P.natDegree ≤ d + 1 := by
    rw [hP]; exact le_trans (natDegree_sub_le _ _) (max_le (le_trans hTdeg (by omega)) hdegRHS)
  have hcardT : T.card = d + 2 := by
    rw [hT, Finset.card_insert_of_notMem h0_notmem,
        Finset.card_insert_of_notMem hxinv_notmem,
        Finset.card_image_of_injOn (omega_inv_pow_inj d ω hω), Finset.card_range]
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P T
  · intro c hc
    rw [hT, Finset.mem_insert, Finset.mem_insert] at hc
    rw [hP, eval_sub, sub_eq_zero]
    rcases hc with hc0 | hcx | hcim
    · -- c = 0
      subst hc0
      have hTeval : (Tpoly x G d R).eval 0 = -X₀ := by
        rw [← coeff_zero_eq_eval_zero]; exact hT0
      rw [hTeval, hRHS]
      rw [eval_add, eval_add, eval_finset_sum]
      have hsum0 : (∑ r ∈ Finset.range d,
          (C (Dgen x G d R ω r) * X
            * (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X))
            * (1 - C x * X)).eval 0) = 0 := by
        apply Finset.sum_eq_zero; intro r _; simp
      rw [hsum0]
      simp [zero_pow hd0]
    · -- c = x⁻¹
      subst hcx
      rw [hRHS]
      rw [eval_add, eval_add, eval_finset_sum]
      have hxfac : (1 - C x * X : Polynomial ℂ).eval x⁻¹ = 0 := by
        rw [eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_inv_cancel₀ hx, sub_self]
      have hfirst : (C (- X₀) * (1 - X ^ d) * (1 - C x * X)).eval x⁻¹ = 0 := by
        rw [eval_mul, hxfac, mul_zero]
      have hsum0 : (∑ r ∈ Finset.range d,
          (C (Dgen x G d R ω r) * X
            * (∏ s ∈ (Finset.range d).erase r, (1 - C (ω ^ s) * X))
            * (1 - C x * X)).eval x⁻¹) = 0 := by
        apply Finset.sum_eq_zero; intro r _
        rw [eval_mul, hxfac, mul_zero]
      rw [hfirst, hsum0]
      simp only [zero_add, add_zero]
      have hExne : (1 : ℂ) - x⁻¹ ^ d ≠ 0 := scalar_nonvanish_Ex d x hx hxd
      simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_pow]
      unfold Ex
      rw [show x / (1 - x⁻¹ ^ d) * (Tpoly x G d R).eval x⁻¹ * x⁻¹ * (1 - x⁻¹ ^ d)
            = (Tpoly x G d R).eval x⁻¹ * (x * x⁻¹) * ((1 - x⁻¹ ^ d) / (1 - x⁻¹ ^ d)) by ring]
      rw [mul_inv_cancel₀ hx, div_self hExne, mul_one, mul_one]
    · -- c = ω⁻¹^t
      rw [Finset.mem_image] at hcim
      obtain ⟨t, ht, rfl⟩ := hcim
      simp only [Finset.mem_range] at ht
      rw [hRHS]
      rw [eval_add, eval_add, eval_finset_sum]
      have hpow1 : (ω⁻¹ ^ t) ^ d = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow, hω.pow_eq_one, inv_one, one_pow]
      have hxdfac : (1 - X ^ d : Polynomial ℂ).eval (ω⁻¹ ^ t) = 0 := by
        rw [eval_sub, eval_one, eval_pow, eval_X, hpow1, sub_self]
      have hfirst : (C (- X₀) * (1 - X ^ d) * (1 - C x * X)).eval (ω⁻¹ ^ t) = 0 := by
        rw [eval_mul, eval_mul, hxdfac, mul_zero, zero_mul]
      have hlastz : (C (Ex x G d R) * X * (1 - X ^ d)).eval (ω⁻¹ ^ t) = 0 := by
        rw [eval_mul, hxdfac, mul_zero]
      rw [hfirst, hlastz, zero_add, add_zero]
      rw [Finset.sum_eq_single t]
      · -- r = t term
        have hprodval :
            (∏ s ∈ (Finset.range d).erase t, (1 - ω ^ s * ω⁻¹ ^ t)) = (d : ℂ) :=
          prod_erase_omega_eq_d d hd ω hω t ht
        have hxne : (1 : ℂ) - x * ω⁻¹ ^ t ≠ 0 := scalar_nonvanish_gen d x hxd ω hω t ht
        simp only [eval_mul, eval_C, eval_X, eval_prod, eval_sub, eval_one]
        rw [hprodval]
        have hcancel : ω ^ t * ω⁻¹ ^ t = 1 := by
          rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero t hωne)]
        unfold Dgen
        rw [show ω ^ t / ((d : ℂ) * (1 - x * ω⁻¹ ^ t)) * (Tpoly x G d R).eval (ω⁻¹ ^ t)
              * ω⁻¹ ^ t * (d : ℂ) * (1 - x * ω⁻¹ ^ t)
            = (Tpoly x G d R).eval (ω⁻¹ ^ t) * (ω ^ t * ω⁻¹ ^ t)
              * ((d : ℂ) / (d : ℂ)) * ((1 - x * ω⁻¹ ^ t) / (1 - x * ω⁻¹ ^ t)) by
              field_simp]
        rw [hcancel, div_self hdC, div_self hxne]; ring
      · -- r ≠ t terms vanish
        intro r hr hrt
        have htmem : t ∈ (Finset.range d).erase r :=
          Finset.mem_erase.mpr ⟨Ne.symm hrt, Finset.mem_range.mpr ht⟩
        simp only [eval_mul, eval_C, eval_X, eval_prod, eval_sub, eval_one]
        have hprod0 : (∏ s ∈ (Finset.range d).erase r, (1 - ω ^ s * ω⁻¹ ^ t)) = 0 := by
          apply Finset.prod_eq_zero htmem
          rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero t hωne), sub_self]
        rw [hprod0]; ring
      · intro htcontra
        exact absurd (Finset.mem_range.mpr ht) htcontra
  · rw [hcardT]; omega

/-- **PF identity, general case (hard leaf).**

`T̂_{d,x} / (U·(1 - U^d)·(1 - x·U)) = C(-X₀)/U + ∑_r C(D_{r,x})/(1 - ω^r·U) + C(E_x)/(1-x·U)`.

Math argument.  `T_{d,x}` has `natDegree ≤ d` and the denominator `U·(1-U^d)·(1-x·U)` has
degree `d + 2` with `d + 2` distinct simple roots (`U = 0`; the `d` torsion points where
`ω^r·U = 1`, i.e. `U = ω^{-r}`, distinct since `ω` is a primitive `d`-th root of unity so
`1 - U^d = ∏_{r<d}(1 - ω^r·U)` via `Polynomial.X_pow_sub_one_eq_prod` / the
`nthRootsFinset` factorization; and the extra pole `U = x^{-1}`, distinct from the torsion
points because `x^d ≠ 1`).  Hence `T̂/den` admits a unique partial-fraction decomposition
into `d + 2` simple terms.  The residue at each simple pole is the standard Lagrange/Cauchy
residue: at `U = 0`, `res = T_{d,x}(0) / [(1-0)(1-0)] = T_{d,x}(0) = -X₀`, giving `C(-X₀)/U`;
at `U = ω^{-r}` (pole of `1 - ω^r·U`, whose derivative in `U` is `-ω^r`), the residue works
out to `ω^r/(d·(1 - x·ω^{-r}))·T_{d,x}(ω^{-r}) = D_{r,x}` (the `d` factor comes from
`d/dU(1-U^d)|_{U=ω^{-r}} = -d·U^{d-1} = -d·ω^{-r(d-1)} = -d·ω^r`, using `ω^{-rd}=1`); at
`U = x^{-1}`, the residue is `x/(1 - x^{-d})·T_{d,x}(x^{-1}) = E_x`.

Formal-phase strategy: this is best proved by clearing all denominators, i.e. multiply both
sides by `U·(1-U^d)·(1-x·U)` (all nonzero in `𝕂`) and reduce to the polynomial identity
`T̂ = C(-X₀)·(1-U^d)(1-x·U) + ∑_r C(D_{r,x})·U·(∏_{s≠r}(1-ω^s·U))·(1-x·U)
      + C(E_x)·U·(1-U^d)`, then verify it as an equality of polynomials of degree ≤ d+1 by
matching values at the `d+2` roots (each simple), or by injecting from `Polynomial ℂ` and
using the Lagrange interpolation / `Polynomial.eq_of_degree_lt_of_eval` machinery.  Consult
Mathlib partial-fraction API (`Polynomial.div_eq_...`, `nthRootsFinset`,
`X_pow_sub_one_eq_prod`). This is the principal remaining work item. -/
theorem PF_general
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂˣ) (hxd : (x : ℂ) ^ d ≠ 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (G : ℂ) (X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2) (hR0 : R.coeff 0 = -X₀) :
    toField (Tpoly (x : ℂ) G d R) / (U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U) := by
  have hd0 : 0 < d := by omega
  have hωne : (ω : ℂ) ≠ 0 := hω.ne_zero (by omega)
  have hUne : (U : Kf) ≠ 0 := U_ne_zero
  have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero hd0
  have hxU : (1 : Kf) - RatFunc.C (x : ℂ) * U ≠ 0 := one_sub_C_mul_U_ne_zero x.ne_zero
  have hden : U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hUne hUd) hxU
  -- the polynomial identity from PF_general_poly
  have hpoly := PF_general_poly d hd0 (x : ℂ) x.ne_zero hxd (ω : ℂ) hω G X₀ R
    (Tpoly_natDegree_le m hm d hd (x : ℂ) G R hRdeg)
    (Tpoly_coeff_zero m hm d hd (x : ℂ) G R X₀ hR0)
  have hfield := congrArg toField hpoly
  -- push toField over the erase-products
  have hstarprod : ∀ r, toField (∏ s ∈ (Finset.range d).erase r, (1 - C ((ω : ℂ) ^ s) * X))
      = ∏ s ∈ (Finset.range d).erase r, (1 - RatFunc.C ((ω : ℂ) ^ s) * U) := by
    intro r
    unfold toField
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro s _
    rw [map_sub, map_one, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rfl
  -- the field form of the polynomial RHS
  have hL : toField (Tpoly (x : ℂ) G d R) =
      RatFunc.C (- X₀) * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U)
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * U
              * (∏ s ∈ (Finset.range d).erase r, (1 - RatFunc.C ((ω : ℂ) ^ s) * U))
              * (1 - RatFunc.C (x : ℂ) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) * U * (1 - U ^ d) := by
    rw [hfield]
    unfold toField
    rw [map_add, map_add, map_sum]
    congr 1
    · congr 1
      · rw [map_mul, map_mul, map_sub, map_one, map_pow, map_sub, map_one, map_mul,
          RatFunc.algebraMap_C, RatFunc.algebraMap_X]
        rfl
      · apply Finset.sum_congr rfl
        intro r _
        have hsp := hstarprod r
        unfold toField at hsp
        rw [map_mul, map_mul, map_mul, map_sub, map_one, map_mul,
          RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_C, hsp]
        rfl
    · rw [map_mul, map_mul, map_sub, map_one, map_pow, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X]
      rfl
  -- factorization: 1 - U^d = (1 - C(ω^r)U) * ∏_{s≠r}
  have hsf := star_factorization_field d hd0 (ω : ℂ) hω
  have hsplit : ∀ r ∈ Finset.range d,
      (1 : Kf) - U ^ d
        = (1 - RatFunc.C ((ω : ℂ) ^ r) * U) * ∏ s ∈ (Finset.range d).erase r,
            (1 - RatFunc.C ((ω : ℂ) ^ s) * U) := by
    intro r hr
    rw [hsf]
    exact (Finset.mul_prod_erase (Finset.range d) _ hr).symm
  have hlin : ∀ r ∈ Finset.range d, (1 : Kf) - RatFunc.C ((ω : ℂ) ^ r) * U ≠ 0 := by
    intro r _; exact lin_factor_ne (ω : ℂ) hωne r
  rw [hL, div_eq_iff hden, add_mul, add_mul]
  congr 1
  · congr 1
    · -- C(-X₀) term
      rw [div_mul_eq_mul_div, eq_div_iff hUne]
      ring
    · -- sum term
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hsplit r hr]
      have hne := hlin r hr
      rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hne]
      ring
  · -- E_x term
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hxU]
    ring

/-- **PF identity, torsion subcase `x = 1` (hard leaf).**

`Ŝ_{d,1} / (U·(1 - U^d)) = C(-X₀)/U + ∑_r C(D_{r,1})/(1 - ω^r·U)`.

Math argument.  In this subcase `C_1 = d` and `T_{d,1} = (1-X)·S_{d,1}` (both proven), so
the shared factor `1 - U` cancels one torsion factor of `1 - U^d`, leaving numerator
`S_{d,1}` (`natDegree ≤ d - 1`) over `U·(1-U^d)` (degree `d+1`, `d+1` distinct simple poles:
`U=0` and the `d` torsion points `U=ω^{-r}`).  Partial fractions give residue `-X₀` at
`U=0` (constant term `S_{d,1}(0) = -X₀`, proven) and `ω^r/d·S_{d,1}(ω^{-r}) = D_{r,1}` at
`U=ω^{-r}` (again the `d` from `d/dU(1-U^d)|_{ω^{-r}} = -d·ω^r`).

Formal-phase strategy: same clearing-denominators approach as `PF_general`, but with the
smaller denominator `U·(1-U^d)`; polynomial identity
`Ŝ_{d,1} = C(-X₀)·(1-U^d) + ∑_r C(D_{r,1})·U·∏_{s≠r}(1-ω^s·U)`, matched at the `d+1` simple
roots. Reuse `X_pow_sub_one_eq_prod` for the factorization of `1-U^d`. -/
theorem PF_torsion_one
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (G : ℂ) (X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2) (hR0 : R.coeff 0 = -X₀) :
    toField (Spoly_one G d R) / (U * (1 - U ^ d))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U) := by
  have hd0 : 0 < d := by omega
  -- degree bound for Spoly_one
  have hSdeg : (Spoly_one G d R).natDegree ≤ d := by
    unfold Spoly_one
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (natDegree_mul_le) ?_
      have hb : (1 - X : ℂ[X]).natDegree ≤ 1 := by
        refine le_trans (natDegree_sub_le _ _) ?_; simp
      have := add_le_add hb hRdeg
      omega
    · refine le_trans (natDegree_mul_le) ?_
      have hCG : (C G).natDegree = 0 := natDegree_C _
      rw [hCG, add_zero]
      refine le_trans (natDegree_C_mul_le _ _) ?_
      rw [natDegree_X_pow]
      omega
  have hS0 : (Spoly_one G d R).coeff 0 = -X₀ := Spoly_one_coeff_zero m hm d hd G R X₀ hR0
  have hpf := PF_torsion_field d hd0 (ω : ℂ) hω X₀ (Spoly_one G d R) hSdeg hS0
  -- Done matches the summand coefficient definitionally
  rw [hpf]
  simp only [Done]

/-- **PF identity, torsion subcase `x ≠ 1, x^d = 1` (hard leaf).**

`Ŝ_{d,x} / (U·(1 - U^d)) = C(-X₀)/U + ∑_r C(D_{r,x})/(1 - ω^r·U)` with `S_{d,x} = (1-X)·R`.

Math argument.  Here `C_x = 0` and `T_{d,x} = (1 - C x·X)·S_{d,x}` (both proven), with
`S_{d,x} = (1-X)·R` (`natDegree ≤ d - 1`).  Since `x^d = 1` and `x ≠ 1`, `x = ω^{r_0}` for a
unique `r_0` with `0 < r_0 < d`, so the shared factor `1 - x·U` coincides with the torsion
factor `1 - ω^{r_0}·U`; the numerator `S_{d,x}` over `U·(1-U^d)` (degree `d+1`) again has
`d+1` distinct simple poles.  Residue `-X₀` at `U=0` (`S_{d,x}(0)=-X₀`, proven) and
`ω^r/d·(1-ω^{-r})·R(ω^{-r}) = D_{r,x}` at `U=ω^{-r}` (the `(1-ω^{-r})` factor is
`S_{d,x}(ω^{-r})/R(ω^{-r})` since `S_{d,x}=(1-X)·R`).

Formal-phase strategy: identical clearing-denominators approach as `PF_torsion_one`, with
`Ŝ_{d,x} = C(-X₀)·(1-U^d) + ∑_r C(D_{r,x})·U·∏_{s≠r}(1-ω^s·U)`. -/
theorem PF_torsion_ne
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂˣ) (hx1 : (x : ℂ) ≠ 1) (hxd : (x : ℂ) ^ d = 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (G : ℂ) (X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2) (hR0 : R.coeff 0 = -X₀) :
    toField (Spoly_tors R) / (U * (1 - U ^ d))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U) := by
  have hd0 : 0 < d := by omega
  have hSdeg : (Spoly_tors R).natDegree ≤ d := by
    unfold Spoly_tors
    refine le_trans (natDegree_mul_le) ?_
    have hb : (1 - X : ℂ[X]).natDegree ≤ 1 := by
      refine le_trans (natDegree_sub_le _ _) ?_; simp
    have := add_le_add hb hRdeg
    omega
  have hS0 : (Spoly_tors R).coeff 0 = -X₀ := Spoly_tors_coeff_zero R X₀ hR0
  have hpf := PF_torsion_field d hd0 (ω : ℂ) hω X₀ (Spoly_tors R) hSdeg hS0
  rw [hpf]
  apply congrArg
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  unfold Dtors Spoly_tors
  rw [eval_mul, eval_sub, eval_one, eval_X]
  ring

/-- **Statement 2 (Key Formula `KF:residues`), general case.**

Hypotheses `hm`, `x : ℂˣ`, `x^d ≠ 1`, `ω : ℂˣ` a primitive `d`-th root of unity, and the
run‑1 degree bound `R.natDegree ≤ d - 2`. Then, in `𝕂`:

1. the accompanying scalar nonvanishing facts hold — `1 - x·ω^{-r} ≠ 0` for each `r < d` and
   `1 - x^{-d} ≠ 0` (both consequences of `x^d ≠ 1` and primitivity, not extra hypotheses);
2. the `d + 2` linear factors `U`, `1 - ω^r·U` (`r < d`), `1 - x·U` are nonzero in `𝕂`;
3. the partial‑fraction identity
   `T̂_{d,x} / (U·(1 - U^d)·(1 - x·U)) = C(-X₀)/U + ∑_r C(D_{r,x})/(1 - ω^r·U) + C(E_x)/(1 - x·U)`
   with `-X₀ = T_{d,x}(0)`, and `D_{r,x}`, `E_x` the general‑case residue scalars. -/
theorem KF_residues_general
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂˣ) (hxd : (x : ℂ) ^ d ≠ 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (G : ℂ) (X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2)
    (hR0 : R.coeff 0 = -X₀) :
    -- (i) scalar nonvanishing conclusions
    (∀ r < d, (1 : ℂ) - (x : ℂ) * (ω : ℂ)⁻¹ ^ r ≠ 0)
    ∧ ((1 : ℂ) - (x : ℂ)⁻¹ ^ d ≠ 0)
    -- (ii) the `d + 2` linear factors are nonzero in `𝕂`
    ∧ (U ≠ 0)
    ∧ (∀ r < d, (1 : Kf) - RatFunc.C ((ω : ℂ) ^ r) * U ≠ 0)
    ∧ ((1 : Kf) - RatFunc.C (x : ℂ) * U ≠ 0)
    -- (iii) the partial-fraction identity
    ∧ (toField (Tpoly (x : ℂ) G d R) / (U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U)) := by
  -- Decompose the conjunction: the first two lines are scalar/linear-factor
  -- nonvanishing (proven by the dedicated sub-lemmas), the last is the PF identity.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact scalar_nonvanish_gen d (x : ℂ) hxd (ω : ℂ) hω
  · exact scalar_nonvanish_Ex d (x : ℂ) x.ne_zero hxd
  · exact U_ne_zero
  · intro r _; exact lin_factor_ne (ω : ℂ) ω.ne_zero r
  · exact one_sub_C_mul_U_ne_zero x.ne_zero
  · exact PF_general m hm d hd x hxd ω hω G X₀ R hRdeg hR0

/-- **Statement 2, torsion subcase `x = 1`.**  Here `C_x = d`, `T_{d,1} = (1 - X)·S_{d,1}`,
and the partial fraction runs over the `d` torsion poles only:
`Ŝ_{d,1} / (U·(1 - U^d)) = C(-X₀)/U + ∑_r C(D_{r,1})/(1 - ω^r·U)`,
with `-X₀ = S_{d,1}(0) = R(0)` and `D_{r,1} = ω^r/d · S_{d,1}(ω^{-r})`.

We additionally record: (a) `C_1 = d`; (b) the factorization `T_{d,1} = (1 - X)·S_{d,1}`
linking this subcase's numerator `S_{d,1}` to the master `T_{d,1}`; (c) the constant-term
equality `S_{d,1}(0) = -X₀`; (d) that the `d` torsion linear factors `1 - ω^r·U` and the
factor `U` are nonzero in `𝕂`. -/
theorem KF_residues_torsion_one
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (G : ℂ) (X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2)
    (hR0 : R.coeff 0 = -X₀) :
    -- (a) the constant `C_1 = d`
    (Cx (1 : ℂ) d = (d : ℂ))
    -- (b) factorization linking `T_{d,1}` and `S_{d,1}`
    ∧ (Tpoly (1 : ℂ) G d R = (1 - X) * Spoly_one G d R)
    -- (c) constant-term equality
    ∧ ((Spoly_one G d R).coeff 0 = -X₀)
    -- (d) nonvanishing linear factors
    ∧ (U ≠ 0)
    ∧ (∀ r < d, (1 : Kf) - RatFunc.C ((ω : ℂ) ^ r) * U ≠ 0)
    -- the partial fraction identity
    ∧ (toField (Spoly_one G d R) / (U * (1 - U ^ d))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Cx_one m hm d hd
  · exact Tpoly_factor_one m hm d hd G R
  · exact Spoly_one_coeff_zero m hm d hd G R X₀ hR0
  · exact U_ne_zero
  · intro r _; exact lin_factor_ne (ω : ℂ) ω.ne_zero r
  · exact PF_torsion_one m hm d hd ω hω G X₀ R hRdeg hR0

/-- **Statement 2, torsion subcase `x ≠ 1, x^d = 1`.**  Here `C_x = 0`,
`T_{d,x} = (1 - x·X)·S_{d,x}` with `S_{d,x} = (1 - X)·R`, and the shared factor `1 - x·U`
cancels a torsion factor:
`Ŝ_{d,x} / (U·(1 - U^d)) = C(-X₀)/U + ∑_r C(D_{r,x})/(1 - ω^r·U)`,
with `-X₀ = S_{d,x}(0) = R(0)` and `D_{r,x} = ω^r/d·(1 - ω^{-r})·R(ω^{-r})`.

We additionally record: (a) `C_x = 0`; (b) the factorization `T_{d,x} = (1 - C x·X)·S_{d,x}`
linking this subcase's numerator `S_{d,x}` to the master `T_{d,x}`; (c) the constant-term
equality `S_{d,x}(0) = -X₀`; (d) that the `d` torsion linear factors `1 - ω^r·U` and the
factor `U` are nonzero in `𝕂`. -/
theorem KF_residues_torsion_ne
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂˣ) (hx1 : (x : ℂ) ≠ 1) (hxd : (x : ℂ) ^ d = 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (G : ℂ) (X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2)
    (hR0 : R.coeff 0 = -X₀) :
    -- (a) the constant `C_x = 0`
    (Cx (x : ℂ) d = 0)
    -- (b) factorization linking `T_{d,x}` and `S_{d,x}`
    ∧ (Tpoly (x : ℂ) G d R = (1 - C (x : ℂ) * X) * Spoly_tors R)
    -- (c) constant-term equality
    ∧ ((Spoly_tors R).coeff 0 = -X₀)
    -- (d) nonvanishing linear factors
    ∧ (U ≠ 0)
    ∧ (∀ r < d, (1 : Kf) - RatFunc.C ((ω : ℂ) ^ r) * U ≠ 0)
    -- the partial fraction identity
    ∧ (toField (Spoly_tors R) / (U * (1 - U ^ d))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Cx_torsion_ne m hm d hd (x : ℂ) hx1 hxd
  · exact Tpoly_factor_torsion_ne m hm d hd (x : ℂ) G hx1 hxd R
  · exact Spoly_tors_coeff_zero R X₀ hR0
  · exact U_ne_zero
  · intro r _; exact lin_factor_ne (ω : ℂ) ω.ne_zero r
  · exact PF_torsion_ne m hm d hd x hx1 hxd ω hω G X₀ R hRdeg hR0

/-- **Statement 3 (Key Formula `KF:kernelshift`), general case.**

Hypotheses `hm`, `x q : ℂˣ`, `x^d ≠ 1`, `ω : ℂˣ` primitive, the three kernel `q`-shift laws
(Definition 6), the `M_d` shift (Definition 2), the defect equation Statement 1(1b), and the
partial fraction Statement 2 (general).  With
`Y := C(X₀)·Ψ - ∑_r C(D_{r,x})·Ω_r - C(E_x)·Ω_ext`, the `q`-shift defect of `Y` equals that
of `K`:  `σ Y - x²·Y = σ K - x²·K`  (equivalently `σ(K - Y) = x²·(K - Y)`). -/
theorem KF_kernelshift_general
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x q : ℂˣ) (hxd : (x : ℂ) ^ d ≠ 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (σ : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ) (hσ : σ U = RatFunc.C (q : ℂ) * U)
    (Md K Ψ Ωext : Kf) (Ω : ℕ → Kf)
    (G X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2)
    -- Definition 2 : the `M_d` q-shift law (cleared form).
    (hMd : (1 - U ^ d) * σ Md = U ^ (d - 3) * (1 - U) * Md)
    -- Definition 6 : the three kernel `q`-shift laws.
    (hΨ : σ Ψ - RatFunc.C ((x : ℂ) ^ 2) * Ψ = -Md / U)
    (hΩ : ∀ r < d,
        σ (Ω r) - RatFunc.C ((x : ℂ) ^ 2) * Ω r
          = -Md / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))
    (hΩext : σ Ωext - RatFunc.C ((x : ℂ) ^ 2) * Ωext = -Md / (1 - RatFunc.C (x : ℂ) * U))
    -- Statement 1(1b) : the twisted defect equation for `K`.
    (hdefect : (U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U))
        * (σ K - RatFunc.C ((x : ℂ) ^ 2) * K) = Md * toField (Tpoly (x : ℂ) G d R))
    -- Statement 2 (general) : the partial fraction.
    (hpf : toField (Tpoly (x : ℂ) G d R)
        / (U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U)) :
    let Y : Kf :=
      RatFunc.C X₀ * Ψ
        - ∑ r ∈ Finset.range d, RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * Ω r
        - RatFunc.C (Ex (x : ℂ) G d R) * Ωext
    σ Y - RatFunc.C ((x : ℂ) ^ 2) * Y = σ K - RatFunc.C ((x : ℂ) ^ 2) * K := by
  intro Y
  set c2 : Kf := RatFunc.C ((x : ℂ) ^ 2) with hc2
  -- shorthand for the shift operator sh a = σ a - c2 * a
  -- Compute σ Y.
  have hσY : σ Y =
      RatFunc.C X₀ * σ Ψ
        - ∑ r ∈ Finset.range d, RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * σ (Ω r)
        - RatFunc.C (Ex (x : ℂ) G d R) * σ Ωext := by
    simp only [Y, map_sub, map_mul, map_sum, sigma_fix_C]
  -- shift of Y in terms of shifts of the pieces
  have hshY : σ Y - c2 * Y =
      RatFunc.C X₀ * (σ Ψ - c2 * Ψ)
        - ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * (σ (Ω r) - c2 * Ω r)
        - RatFunc.C (Ex (x : ℂ) G d R) * (σ Ωext - c2 * Ωext) := by
    rw [hσY]
    conv_lhs => rw [show Y =
      RatFunc.C X₀ * Ψ
        - ∑ r ∈ Finset.range d, RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * Ω r
        - RatFunc.C (Ex (x : ℂ) G d R) * Ωext from rfl]
    have hsum : ∑ r ∈ Finset.range d,
          RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * (σ (Ω r) - c2 * Ω r)
        = (∑ r ∈ Finset.range d, RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * σ (Ω r))
          - c2 * ∑ r ∈ Finset.range d, RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * Ω r := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _; ring
    rw [hsum]
    ring
  -- substitute the shift laws
  have hCneg : RatFunc.C (- X₀) = - RatFunc.C X₀ := by rw [map_neg]
  have hshY2 : σ Y - c2 * Y =
      Md * (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U)) := by
    rw [hshY, hΨ, hΩext]
    rw [Finset.sum_congr rfl (fun r hr => by rw [hΩ r (Finset.mem_range.mp hr)])]
    have hsum2 : ∑ r ∈ Finset.range d,
          RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) * (-Md / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))
        = -Md * ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [hsum2, hCneg]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  -- Now compute σ K - c2 * K from hdefect and hpf.
  set denom : Kf := U * (1 - U ^ d) * (1 - RatFunc.C (x : ℂ) * U) with hden
  have hUne : (U : Kf) ≠ 0 := U_ne_zero
  have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero (by omega)
  have hxne : (x : ℂ) ≠ 0 := x.ne_zero
  have hxU : (1 : Kf) - RatFunc.C (x : ℂ) * U ≠ 0 := one_sub_C_mul_U_ne_zero hxne
  have hdne : denom ≠ 0 := by
    rw [hden]; exact mul_ne_zero (mul_ne_zero hUne hUd) hxU
  -- from hpf: Md * T̂ = Md * denom * P
  have hMdT : Md * toField (Tpoly (x : ℂ) G d R) = Md * denom *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U)) := by
    have hT : toField (Tpoly (x : ℂ) G d R) =
        (RatFunc.C (- X₀) / U
          + ∑ r ∈ Finset.range d,
              RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
          + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U)) * denom := by
      rw [← hpf, div_mul_cancel₀]
      exact hdne
    rw [hT]; ring
  -- hdefect says denom * (σ K - c2 K) = Md * T̂
  have hdefect' : denom * (σ K - c2 * K) = Md * toField (Tpoly (x : ℂ) G d R) := by
    rw [hden, hc2]; exact hdefect
  rw [hMdT] at hdefect'
  -- cancel denom
  have hK : σ K - c2 * K = Md *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U)) := by
    have h := hdefect'
    have : denom * (σ K - c2 * K) = denom * (Md *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dgen (x : ℂ) G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)
        + RatFunc.C (Ex (x : ℂ) G d R) / (1 - RatFunc.C (x : ℂ) * U))) := by
      rw [h]; ring
    exact mul_left_cancel₀ hdne this
  rw [hshY2, hK]

/-- **Statement 3, torsion subcase `x = 1`.**

Hypotheses `hm`, `x q : ℂˣ` with `x = 1` (hence `x^d = 1`), `ω : ℂˣ` primitive, the kernel
`q`-shift laws (Definition 6; the `Ω_ext` law is not used), the `M_d` shift (Definition 2),
the defect equation Statement 1(1b), and the torsion partial fraction Statement 2 (subcase
`x = 1`, residue data `D_{r,1} = Done`).

The torsion form of the defect equation (with numerator `Ŝ_{d,1}` and denominator
`U·(1 - U^d)`) is obtained from the master form via the factorization
`T_{d,1} = (1 - X)·S_{d,1}` (hypothesis `hfac`, provable by `Tpoly_factor_one`) which cancels
the shared factor `1 - x·U = 1 - U` against `1 - U^d`.  With
`Y := C(X₀)·Ψ - ∑_r C(D_{r,1})·Ω_r` (no `E_x·Ω_ext` term), the `q`-shift defect of `Y`
equals that of `K`. -/
theorem KF_kernelshift_torsion_one
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x q : ℂˣ) (hx1 : (x : ℂ) = 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (σ : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ) (hσ : σ U = RatFunc.C (q : ℂ) * U)
    (Md K Ψ : Kf) (Ω : ℕ → Kf)
    (G X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2)
    -- Definition 2 : the `M_d` q-shift law (cleared form).
    (hMd : (1 - U ^ d) * σ Md = U ^ (d - 3) * (1 - U) * Md)
    -- The factorization `T_{d,1} = (1 - X)·S_{d,1}` (provable by `Tpoly_factor_one`);
    -- it links the torsion numerator `S_{d,1}` to the master `T_{d,1}`.
    (hfac : Tpoly (x : ℂ) G d R = (1 - X) * Spoly_one G d R)
    -- Definition 6 (Ψ and Ω_r laws; the Ω_ext law is not used).
    (hΨ : σ Ψ - RatFunc.C ((x : ℂ) ^ 2) * Ψ = -Md / U)
    (hΩ : ∀ r < d,
        σ (Ω r) - RatFunc.C ((x : ℂ) ^ 2) * Ω r
          = -Md / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))
    -- Statement 1(1b), torsion form : defect equation for `K` with numerator `Ŝ_{d,1}`.
    (hdefect : (U * (1 - U ^ d)) * (σ K - RatFunc.C ((x : ℂ) ^ 2) * K)
        = Md * toField (Spoly_one G d R))
    -- Statement 2 (torsion, `x = 1`) : the partial fraction.
    (hpf : toField (Spoly_one G d R) / (U * (1 - U ^ d))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) :
    let Y : Kf :=
      RatFunc.C X₀ * Ψ - ∑ r ∈ Finset.range d, RatFunc.C (Done G d R (ω : ℂ) r) * Ω r
    σ Y - RatFunc.C ((x : ℂ) ^ 2) * Y = σ K - RatFunc.C ((x : ℂ) ^ 2) * K := by
  -- SANITY CHECK PASSED (mirrors the fully-proven KF_kernelshift_general; only
  -- structural difference: denom = U*(1-U^d) and Y has no E_x·Ω_ext term).
  -- Strategy (identical to the general proof): expand σ Y using sigma_fix_C, group
  -- into shift-defects of Ψ and Ω_r, substitute hΨ/hΩ to get σY-x²Y = Md * (RHS of
  -- hpf); then from hdefect (denom*(σK-x²K)=Md·Ŝ) and hpf (Ŝ = (RHS)·denom) derive
  -- σK-x²K = Md*(RHS) via mul_left_cancel₀ with denom = U*(1-U^d) ≠ 0; conclude.
  intro Y
  set c2 : Kf := RatFunc.C ((x : ℂ) ^ 2) with hc2
  have hσY : σ Y =
      RatFunc.C X₀ * σ Ψ
        - ∑ r ∈ Finset.range d, RatFunc.C (Done G d R (ω : ℂ) r) * σ (Ω r) := by
    simp only [Y, map_sub, map_mul, map_sum, sigma_fix_C]
  have hshY : σ Y - c2 * Y =
      RatFunc.C X₀ * (σ Ψ - c2 * Ψ)
        - ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) * (σ (Ω r) - c2 * Ω r) := by
    rw [hσY]
    conv_lhs => rw [show Y =
      RatFunc.C X₀ * Ψ
        - ∑ r ∈ Finset.range d, RatFunc.C (Done G d R (ω : ℂ) r) * Ω r from rfl]
    have hsum : ∑ r ∈ Finset.range d,
          RatFunc.C (Done G d R (ω : ℂ) r) * (σ (Ω r) - c2 * Ω r)
        = (∑ r ∈ Finset.range d, RatFunc.C (Done G d R (ω : ℂ) r) * σ (Ω r))
          - c2 * ∑ r ∈ Finset.range d, RatFunc.C (Done G d R (ω : ℂ) r) * Ω r := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _; ring
    rw [hsum]; ring
  have hCneg : RatFunc.C (- X₀) = - RatFunc.C X₀ := by rw [map_neg]
  have hshY2 : σ Y - c2 * Y =
      Md * (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
    rw [hshY, hΨ]
    rw [Finset.sum_congr rfl (fun r hr => by rw [hΩ r (Finset.mem_range.mp hr)])]
    have hsum2 : ∑ r ∈ Finset.range d,
          RatFunc.C (Done G d R (ω : ℂ) r) * (-Md / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))
        = -Md * ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [hsum2, hCneg]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  set denom : Kf := U * (1 - U ^ d) with hden
  have hUne : (U : Kf) ≠ 0 := U_ne_zero
  have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero (by omega)
  have hdne : denom ≠ 0 := by rw [hden]; exact mul_ne_zero hUne hUd
  have hMdT : Md * toField (Spoly_one G d R) = Md * denom *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
    have hT : toField (Spoly_one G d R) =
        (RatFunc.C (- X₀) / U
          + ∑ r ∈ Finset.range d,
              RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) * denom := by
      rw [← hpf, div_mul_cancel₀]
      exact hdne
    rw [hT]; ring
  have hdefect' : denom * (σ K - c2 * K) = Md * toField (Spoly_one G d R) := by
    rw [hden, hc2]; exact hdefect
  rw [hMdT] at hdefect'
  have hK : σ K - c2 * K = Md *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
    have h := hdefect'
    have : denom * (σ K - c2 * K) = denom * (Md *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Done G d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))) := by
      rw [h]; ring
    exact mul_left_cancel₀ hdne this
  rw [hshY2, hK]

/-- **Statement 3, torsion subcase `x ≠ 1, x^d = 1`.**

Hypotheses `hm`, `x q : ℂˣ` with `x ≠ 1` and `x^d = 1`, `ω : ℂˣ` primitive, the kernel
`q`-shift laws (Definition 6; the `Ω_ext` law is not used), the `M_d` shift (Definition 2),
the defect equation Statement 1(1b), and the torsion partial fraction Statement 2 (subcase
`x ≠ 1`, residue data `D_{r,x} = Dtors`).

The torsion form of the defect equation (with numerator `Ŝ_{d,x} = (1-X)·R` and denominator
`U·(1 - U^d)`) is obtained from the master form via the factorization
`T_{d,x} = (1 - C x·X)·S_{d,x}` (hypothesis `hfac`, provable by `Tpoly_factor_torsion_ne`)
which cancels the shared factor `1 - x·U` against a torsion factor of `1 - U^d`.  With
`Y := C(X₀)·Ψ - ∑_r C(D_{r,x})·Ω_r` (no `E_x·Ω_ext` term), the `q`-shift defect of `Y`
equals that of `K`. -/
theorem KF_kernelshift_torsion_ne
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x q : ℂˣ) (hx1 : (x : ℂ) ≠ 1) (hxd : (x : ℂ) ^ d = 1)
    (ω : ℂˣ) (hω : IsPrimitiveRoot (ω : ℂ) d)
    (σ : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ) (hσ : σ U = RatFunc.C (q : ℂ) * U)
    (Md K Ψ : Kf) (Ω : ℕ → Kf)
    (G X₀ : ℂ) (R : Polynomial ℂ)
    (hRdeg : R.natDegree ≤ d - 2)
    -- Definition 2 : the `M_d` q-shift law (cleared form).
    (hMd : (1 - U ^ d) * σ Md = U ^ (d - 3) * (1 - U) * Md)
    -- The factorization `T_{d,x} = (1 - C x·X)·S_{d,x}` (provable by
    -- `Tpoly_factor_torsion_ne`); it links the torsion numerator `S_{d,x}` to the master.
    (hfac : Tpoly (x : ℂ) G d R = (1 - C (x : ℂ) * X) * Spoly_tors R)
    -- Definition 6 (Ψ and Ω_r laws; the Ω_ext law is not used).
    (hΨ : σ Ψ - RatFunc.C ((x : ℂ) ^ 2) * Ψ = -Md / U)
    (hΩ : ∀ r < d,
        σ (Ω r) - RatFunc.C ((x : ℂ) ^ 2) * Ω r
          = -Md / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))
    -- Statement 1(1b), torsion form : defect equation for `K` with numerator `Ŝ_{d,x}`.
    (hdefect : (U * (1 - U ^ d)) * (σ K - RatFunc.C ((x : ℂ) ^ 2) * K)
        = Md * toField (Spoly_tors R))
    -- Statement 2 (torsion, `x ≠ 1`) : the partial fraction.
    (hpf : toField (Spoly_tors R) / (U * (1 - U ^ d))
      = RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) :
    let Y : Kf :=
      RatFunc.C X₀ * Ψ - ∑ r ∈ Finset.range d, RatFunc.C (Dtors d R (ω : ℂ) r) * Ω r
    σ Y - RatFunc.C ((x : ℂ) ^ 2) * Y = σ K - RatFunc.C ((x : ℂ) ^ 2) * K := by
  -- SANITY CHECK PASSED (mirrors KF_kernelshift_general / torsion_one; denom =
  -- U*(1-U^d), residue data Dtors, numerator Spoly_tors, no E_x·Ω_ext term).
  intro Y
  set c2 : Kf := RatFunc.C ((x : ℂ) ^ 2) with hc2
  have hσY : σ Y =
      RatFunc.C X₀ * σ Ψ
        - ∑ r ∈ Finset.range d, RatFunc.C (Dtors d R (ω : ℂ) r) * σ (Ω r) := by
    simp only [Y, map_sub, map_mul, map_sum, sigma_fix_C]
  have hshY : σ Y - c2 * Y =
      RatFunc.C X₀ * (σ Ψ - c2 * Ψ)
        - ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) * (σ (Ω r) - c2 * Ω r) := by
    rw [hσY]
    conv_lhs => rw [show Y =
      RatFunc.C X₀ * Ψ
        - ∑ r ∈ Finset.range d, RatFunc.C (Dtors d R (ω : ℂ) r) * Ω r from rfl]
    have hsum : ∑ r ∈ Finset.range d,
          RatFunc.C (Dtors d R (ω : ℂ) r) * (σ (Ω r) - c2 * Ω r)
        = (∑ r ∈ Finset.range d, RatFunc.C (Dtors d R (ω : ℂ) r) * σ (Ω r))
          - c2 * ∑ r ∈ Finset.range d, RatFunc.C (Dtors d R (ω : ℂ) r) * Ω r := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _; ring
    rw [hsum]; ring
  have hCneg : RatFunc.C (- X₀) = - RatFunc.C X₀ := by rw [map_neg]
  have hshY2 : σ Y - c2 * Y =
      Md * (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
    rw [hshY, hΨ]
    rw [Finset.sum_congr rfl (fun r hr => by rw [hΩ r (Finset.mem_range.mp hr)])]
    have hsum2 : ∑ r ∈ Finset.range d,
          RatFunc.C (Dtors d R (ω : ℂ) r) * (-Md / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))
        = -Md * ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [hsum2, hCneg]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  set denom : Kf := U * (1 - U ^ d) with hden
  have hUne : (U : Kf) ≠ 0 := U_ne_zero
  have hUd : (1 : Kf) - U ^ d ≠ 0 := one_sub_U_pow_ne_zero (by omega)
  have hdne : denom ≠ 0 := by rw [hden]; exact mul_ne_zero hUne hUd
  have hMdT : Md * toField (Spoly_tors R) = Md * denom *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
    have hT : toField (Spoly_tors R) =
        (RatFunc.C (- X₀) / U
          + ∑ r ∈ Finset.range d,
              RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) * denom := by
      rw [← hpf, div_mul_cancel₀]
      exact hdne
    rw [hT]; ring
  have hdefect' : denom * (σ K - c2 * K) = Md * toField (Spoly_tors R) := by
    rw [hden, hc2]; exact hdefect
  rw [hMdT] at hdefect'
  have hK : σ K - c2 * K = Md *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U)) := by
    have h := hdefect'
    have : denom * (σ K - c2 * K) = denom * (Md *
      (RatFunc.C (- X₀) / U
        + ∑ r ∈ Finset.range d,
            RatFunc.C (Dtors d R (ω : ℂ) r) / (1 - RatFunc.C ((ω : ℂ) ^ r) * U))) := by
      rw [h]; ring
    exact mul_left_cancel₀ hdne this
  rw [hshY2, hK]

end
