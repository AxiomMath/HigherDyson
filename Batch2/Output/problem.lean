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
  sorry

/-- Definition 5 property: the constant term of `T_{d,x}` equals `R(0) = -X₀`.
The global hypotheses `hm`, `hd` are required: they give `2 ≤ d`, hence `d - 1 ≠ 0`, so the
term `X^{d-1}` does not contribute to the constant term. -/
theorem Tpoly_coeff_zero
    (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x G : ℂ) (R : Polynomial ℂ) (X₀ : ℂ) (hR0 : R.coeff 0 = -X₀) :
    (Tpoly x G d R).coeff 0 = -X₀ := by
  sorry

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
  sorry

/-- Torsion subcase `x ≠ 1, x^d = 1`: the constant `C_x = 0`.  This uses `x^d = 1` and
`x ≠ 1`: `(1 - x)·C_x = 1 - x^d = 0`, and `1 - x ≠ 0`. -/
theorem Cx_torsion_ne (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x : ℂ) (hx1 : x ≠ 1) (hxd : x ^ d = 1) :
    Cx x d = 0 := by
  sorry

/-- Torsion subcase `x = 1`: `T_{d,1} = (1 - X)·S_{d,1}` as polynomials in `ℂ[X]`.
Since `C_1 = d`, `T_{d,1} = (1 - X)·(1 - X)·R - C d·X^{d-1}·(1 - X)·C G
= (1 - X)·S_{d,1}`. -/
theorem Tpoly_factor_one (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (G : ℂ) (R : Polynomial ℂ) :
    Tpoly (1 : ℂ) G d R = (1 - X) * Spoly_one G d R := by
  sorry

/-- Torsion subcase `x ≠ 1, x^d = 1`: `T_{d,x} = (1 - C x·X)·S_{d,x}` as polynomials in
`ℂ[X]`.  Since `C_x = 0`, `T_{d,x} = (1 - C x·X)·(1 - X)·R = (1 - C x·X)·S_{d,x}`. -/
theorem Tpoly_factor_torsion_ne (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (x G : ℂ) (hx1 : x ≠ 1) (hxd : x ^ d = 1) (R : Polynomial ℂ) :
    Tpoly x G d R = (1 - C x * X) * Spoly_tors R := by
  sorry

/-- Torsion subcase `x = 1`: the constant term of `S_{d,1}` equals `R(0) = -X₀`.
As with `Tpoly_coeff_zero`, the hypotheses `hm`, `hd` give `d - 1 ≠ 0`, so `X^{d-1}` does
not contribute to the constant term. -/
theorem Spoly_one_coeff_zero (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : d = 2 * m + 1)
    (G : ℂ) (R : Polynomial ℂ) (X₀ : ℂ) (hR0 : R.coeff 0 = -X₀) :
    (Spoly_one G d R).coeff 0 = -X₀ := by
  sorry

/-- Torsion subcase `x ≠ 1, x^d = 1`: the constant term of `S_{d,x} = (1 - X)·R` equals
`R(0) = -X₀`. -/
theorem Spoly_tors_coeff_zero (R : Polynomial ℂ) (X₀ : ℂ) (hR0 : R.coeff 0 = -X₀) :
    (Spoly_tors R).coeff 0 = -X₀ := by
  sorry

/-! ## Main Statement(s)

All three statements are equalities in `𝕂 = RatFunc ℂ`.  The `q`-shift automorphism `σ`,
the opaque elements, and the run‑1 data all enter as hypotheses.
-/

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end
