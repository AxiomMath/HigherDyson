import Mathlib

/-
# Problem Description

Higher Dyson ranks and meromorphic elliptic corrections (Alfes-Ono), companion
`KeyFormulasDyson.tex`.  We prove Batch 3 Key Formulas `KF:Pshift`, `KF:appellshift`,
`KF:corrected`, `KF:untwist`, `KF:carrier`, `KF:level5`.

Throughout, `m : ℕ` is fixed with `hm : 2 ≤ m`, and `d := 2*m + 1` (so `d ≥ 5` is odd
and `d - 3 = 2*m - 2 ≥ 2` is even).  All objects live over `ℂ`.  We fix a unit `x : ℂˣ`,
a parameter `τ : ℂ`, `ω : ℂ` (a primitive fifth root of unity at level 5), and nonzero
`Q U : ℂ` pinning fractional powers as integer monomials.

Each Key Formula is a finite algebraic identity among opaque `q`-series / rational
function symbols subject to finitely many designated shift laws (the "designated
inputs").  The definitions fix exactly how the objects are modeled.
-/

namespace HigherDyson

-- Fixed data (Definitions 1, 3, 7).
variable (m : ℕ) (x : ℂˣ) (τ : ℂ) (ω : ℂ)

/-- The level, `d := 2*m + 1`. -/
def d (m : ℕ) : ℕ := 2 * m + 1

/- ## Definition 1 (concrete elliptic variable and nome). -/

/-- The elliptic variable `elvC w = exp(2πi w)`. -/
noncomputable def elvC (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)

/-- The nome `qC = exp(2πi τ)`. -/
noncomputable def qC (τ : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ)

/-- Nonvanishing of the elliptic variable. -/
lemma helvC0 (w : ℂ) : elvC w ≠ 0 := Complex.exp_ne_zero _

/-- Nonvanishing of the nome. -/
lemma hqC0 : qC τ ≠ 0 := Complex.exp_ne_zero _

/- ## Definition 2 (concrete translation lemmas — proved, never assumed). -/

/-- Translation by `τ` multiplies by the nome. -/
lemma lem_elv_tau (w : ℂ) : elvC (w + τ) = qC τ * elvC w := by
  unfold elvC qC
  rw [← Complex.exp_add]
  ring_nf

/-- Translation by `1` is invariant. -/
lemma lem_elv_one (w : ℂ) : elvC (w + 1) = elvC w := by
  unfold elvC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (w + 1))
        = (2 * (Real.pi : ℂ) * Complex.I * w) + (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- General `λ`-translation law. -/
lemma lem_elv_lam (w lam : ℂ) :
    elvC (w + lam) = Complex.exp (2 * Real.pi * Complex.I * lam) * elvC w := by
  unfold elvC
  rw [← Complex.exp_add]
  ring_nf

/- ## Definition 3 (opaque `u`-level symbols; assembled objects by composition).

The `q`-series / product data are opaque parameters, constrained only by the designated
relations of Definitions 4-8. -/

section OpaqueData

-- opaque `u`-level symbols
variable (Pd Md Gu Bu Aextu : ℂ → ℂ) (Aru : ℕ → ℂ → ℂ)
variable (X₀ : ℂ) (D : ℕ → ℂ) (E : ℂ)

/-- `Φ` at the `u`-level: `Phiu t = Pd t · Gu t`. -/
def Phiu (t : ℂ) : ℂ := Pd t * Gu t

/-- `K` at the `u`-level: `Ku t = Md t / t · Gu t`. -/
noncomputable def Ku (t : ℂ) : ℂ := Md t / t * Gu t

/-- `𝓗` at the `u`-level. -/
noncomputable def Hu (t : ℂ) : ℂ :=
  Phiu Pd Gu t - X₀ * Bu t
    + (∑ r ∈ Finset.range (d m), D r * Aru r t)
    + E * Aextu t

/- The `w`-level ("elliptic-variable") functions are compositions with `elvC`. -/

/-- `B w = Bu (elvC w)`. -/
noncomputable def B (w : ℂ) : ℂ := Bu (elvC w)

/-- `Ar r w = Aru r (elvC w)`. -/
noncomputable def Ar (r : ℕ) (w : ℂ) : ℂ := Aru r (elvC w)

/-- `Aext w = Aextu (elvC w)`. -/
noncomputable def Aext (w : ℂ) : ℂ := Aextu (elvC w)

/-- `Φ w = Phiu (elvC w)`. -/
noncomputable def Φ (w : ℂ) : ℂ := Phiu Pd Gu (elvC w)

/-- `𝓗 w = Hu (elvC w)`. -/
noncomputable def 𝓗 (w : ℂ) : ℂ := Hu m Pd Gu Bu Aextu Aru X₀ D E (elvC w)

/- ## Definition 5 (the prefactor-free master package — `hpack`). -/

/-- The scalar residue package (partial-fraction RHS, no factor of `Pd`). -/
noncomputable def Residues (u : ℂ) : ℂ :=
  - X₀ + (∑ r ∈ Finset.range (d m), D r * u / (1 - ω^r * u)) + E * u / (1 - x * u)

/-- The master defect: normalized raw defect of the master functional equation. -/
noncomputable def MasterDefect (u : ℂ) : ℂ :=
  (qC τ)^(-1 : ℤ) * u^(2*m - 2 : ℤ) * (1 - u) / (1 - u^(d m))
    * ( Gu (qC τ * u)
          - (x:ℂ)^2 * qC τ * (u^(d m) - 1) / (u^(2*m - 2 : ℤ) * (u - 1)) * Gu u )

end OpaqueData

/- ## Definition 7 (theta / carrier data — `Q,U` monomial language). -/

section Theta

variable (Q U : ℂ)
-- opaque theta / product symbols
variable (ϑη : ℂ) (ϑ₁ : ℂ → ℂ → ℂ) (qpoch : ℂ) (Jprod Jprodd : ℂ → ℂ)

/-- The Jacobi carrier `𝓙`. -/
noncomputable def 𝓙 (z : ℂ) : ℂ :=
  ϑη^(2 - 4*(m:ℤ)) * (ϑ₁ τ z)^(4*m + 1) / (ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z))

end Theta

/- ## Definition 8 (level-5 specialized data; `x = 1`, `m = 2`, `d = 5`). -/

section Level5

variable (Md G51 T51 : ℂ → ℂ)
variable (X₀ X₁ X₂ X₃ P5P1 : ℂ)

/-- Level-5 raw defect expression `R_{5,1}`. -/
noncomputable def R51 (u : ℂ) : ℂ :=
  ((qC τ)^(-1 : ℤ) * u^2 - u^3 - u^2 - u - 1) * X₀
    - (u^2 + u) * X₁ - (u^3 + u^2) * X₂ - u^3 * X₃

/-- Level-5 clearing expression `S_{5,1}`. -/
noncomputable def S51 (u : ℂ) : ℂ :=
  (1 - u) * R51 τ X₀ X₁ X₂ X₃ u - 5 * u^4 * P5P1

/-- Level-5 `K`-form. -/
noncomputable def K51 (u : ℂ) : ℂ := Md u / u * G51 u

/-- Level-5 residue coefficients, defined explicitly by the closed form. -/
noncomputable def D51 (r : ℕ) : ℂ := (ω^r / 5) * S51 τ X₀ X₁ X₂ X₃ P5P1 (ω^(-(r : ℤ)))

end Level5

/- ############################################################################
   # Main Statement(s)
   ############################################################################ -/

/- ## Statement 1 (`KF:Pshift`). -/

/-- Statement 1(i): Multiplier collapse.
As a pointwise identity for `u ≠ 0`, `u ≠ 1`, `u^d ≠ 1`. -/
theorem stmt1_i (Pd : ℂ → ℂ) (u : ℂ) (hm : 2 ≤ m)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hud : u^(d m) ≠ 1)
    (hPshift : Pd (qC τ * u)
      = (qC τ)^(-(m:ℤ) - 1) * u^(-2 : ℤ) * (1 - u) / (1 - u^(d m)) * Pd u) :
    Pd (qC τ * u) * ((x:ℂ)^2 * qC τ * (u^(d m) - 1) / (u^(2*m - 2 : ℤ) * (u - 1)))
      = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * u^(-(2*(m:ℤ))) * Pd u := by
  -- SANITY CHECK PASSED (a pure algebraic identity: substitute hPshift and
  -- collect zpow/Nat-pow monomials; no numerical instance can violate it).
  -- STRATEGY (leaf, directly closable): `rw [hPshift]`, then establish the
  -- nonzero bases: qC τ ≠ 0 (hqC0 τ), u ≠ 0 (hu0), 1-u ≠ 0 (from hu1),
  -- 1 - u^(d m) ≠ 0 (from hud).  Note (u^(d m) - 1) = -(1 - u^(d m)) and
  -- (u-1) = -(1-u) so the two minus signs cancel.  Convert the Nat power
  -- u^(d m) is opaque and cancels literally against the (1 - u^(d m)) in the
  -- denominator; the qC exponents combine (-m-1)+1 = -m and the u exponents
  -- combine (-2) - (2*m-2) = -(2*m) via `zpow_add₀`/`zpow_sub₀` (base ≠ 0).
  -- Then `field_simp [hqC0, hu0, sub_ne_zero.mpr, ...]; ring` should finish;
  -- if ring stalls on mixed zpow/Nat-pow, rewrite u^(d m) as a fresh variable
  -- `set U5 := u^(d m)` first so only zpow/z-exponent arithmetic remains.
  rw [hPshift]
  have hq0 : qC τ ≠ 0 := hqC0 τ
  have h1u : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (fun h => hu1 h.symm)
  have h1ud : (1 : ℂ) - u ^ (d m) ≠ 0 := sub_ne_zero.mpr (fun h => hud h.symm)
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  rw [show (-(m:ℤ) - 1) = (-(m:ℤ)) + (-1) by ring, zpow_add₀ hq0]
  rw [show (-(2*(m:ℤ))) = (-2) + (-(2*(m:ℤ) - 2)) by ring, zpow_add₀ hu0]
  rw [show (2*(m:ℤ) - 2) = -(-(2*(m:ℤ) - 2)) by ring, zpow_neg]
  have hz : u ^ (-(2*(m:ℤ) - 2)) ≠ 0 := zpow_ne_zero _ hu0
  field_simp
  have hcancel : u ^ (- -(2*(m:ℤ) - 2)) * u ^ (- - -(2*(m:ℤ) - 2)) = 1 := by
    rw [← zpow_add₀ hu0]; norm_num
  rw [show (1 - u ^ (d m)) * Pd u * u ^ (- -(2*(m:ℤ) - 2)) * (u - 1) * u ^ (- - -(2*(m:ℤ) - 2))
        = (1 - u ^ (d m)) * Pd u * (u - 1)
            * (u ^ (- -(2*(m:ℤ) - 2)) * u ^ (- - -(2*(m:ℤ) - 2))) by ring]
  rw [hcancel]
  ring

/-- Statement 1(ii): The `Φ` `w+τ` law (paper eq. (4.21)). -/
theorem stmt1_ii (Pd Gu Bu Aextu : ℂ → ℂ) (Aru : ℕ → ℂ → ℂ)
    (X₀ : ℂ) (D : ℕ → ℂ) (E : ℂ) (w : ℂ) (hm : 2 ≤ m)
    (hu0 : elvC w ≠ 0) (hu1 : elvC w ≠ 1) (hud : (elvC w)^(d m) ≠ 1)
    (hxu : 1 - x * elvC w ≠ 0) (hωu : ∀ r < d m, 1 - ω^r * elvC w ≠ 0)
    (hPshift : Pd (qC τ * elvC w)
      = (qC τ)^(-(m:ℤ) - 1) * (elvC w)^(-2 : ℤ) * (1 - elvC w) / (1 - (elvC w)^(d m)) * Pd (elvC w))
    (hpack : Pd (elvC w) * MasterDefect m x τ Gu (elvC w)
      = Pd (elvC w) * Residues m x ω X₀ D E (elvC w)) :
    Φ Pd Gu (w + τ)
      = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Φ Pd Gu w
        + (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Pd (elvC w)
            * ( - X₀ + (∑ r ∈ Finset.range (d m), D r * elvC w / (1 - ω^r * elvC w))
                     + E * elvC w / (1 - x * elvC w) ) := by
  -- SANITY CHECK PASSED (identity conditioned on hpack, hPshift; sub-lemma).
  -- STRATEGY: Unfold `Φ`, `Phiu`.  Φ(w+τ) = Pd(elvC(w+τ))·Gu(elvC(w+τ)).
  -- By lem_elv_tau, elvC(w+τ) = qC τ · elvC w, so Φ(w+τ) =
  --   Pd(qC τ · elvC w) · Gu(qC τ · elvC w).
  -- Rewrite Pd(qC τ · elvC w) with hPshift.  The Gu(qC τ · elvC w) term is
  -- supplied by `hpack`: MasterDefect (Definition 5) is exactly
  --   (qC)^-1·u^(2m-2)·(1-u)/(1-u^d)·(Gu(qC u) - x²·qC·(u^d-1)/(u^(2m-2)(u-1))·Gu u),
  -- and hpack : Pd u · MasterDefect = Pd u · Residues.  So multiply the
  -- Pd(qC u)·Gu(qC u) product out, use stmt1_i to rewrite the
  -- Pd(qC u)·[x²·qC·(u^d-1)/(u^(2m-2)(u-1))] factor into x²·qC^-m·u^-2m·Pd u,
  -- and hpack to replace the residual Gu(qC u) combination by the Residues
  -- bracket.  Collect: the first summand becomes x²·qC^-m·u^-2m·Φ w (since
  -- Φ w = Pd u·Gu u), and the second is qC^-m·u^-2m·Pd u·Residues.  Then the
  -- RHS matches after unfolding `Residues`.  Nonzero side conditions hu0,hu1,
  -- hud,hxu,hωu are used to justify the field cancellations.
  unfold Φ Phiu
  rw [lem_elv_tau]
  set u := elvC w with hu_def
  set q := qC τ with hq_def
  have hq0 : q ≠ 0 := hqC0 τ
  have h1u : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (fun h => hu1 h.symm)
  have h1ud : (1 : ℂ) - u ^ (d m) ≠ 0 := sub_ne_zero.mpr (fun h => hud h.symm)
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have hz2m2 : u ^ (2*(m:ℤ) - 2) ≠ 0 := zpow_ne_zero _ hu0
  -- opaque abbreviations
  set g1 := Gu (q * u) with hg1_def
  set g0 := Gu u with hg0_def
  set p := Pd u with hp_def
  -- unfold hpack (MasterDefect, Residues)
  unfold MasterDefect Residues at hpack
  -- residue bracket abbreviation
  set Res := -X₀ + (∑ r ∈ Finset.range (d m), D r * u / (1 - ω ^ r * u)) + E * u / (1 - x * u)
    with hRes_def
  -- master prefactor and correction
  set M := q ^ (-1 : ℤ) * u ^ (2*(m:ℤ) - 2) * (1 - u) / (1 - u ^ (d m)) with hM_def
  set C := (x:ℂ)^2 * q * (u ^ (d m) - 1) / (u ^ (2*(m:ℤ) - 2) * (u - 1)) with hC_def
  -- note: the exponent `2*m - 2 : ℤ` in the definitions equals `2*(m:ℤ) - 2`
  -- M * C = x²
  have hMC : M * C = (x:ℂ)^2 := by
    rw [hM_def, hC_def, zpow_neg, zpow_one]
    field_simp
    ring
  -- from hpack:  p * M * g1 = p * Res + x² * (p * g0)
  have hkey : p * M * g1 = p * Res + (x:ℂ)^2 * (p * g0) := by
    have hp2 : p * (M * (g1 - C * g0)) = p * Res := hpack
    linear_combination hp2 + (p * g0) * hMC
  -- prefactor relation M' = A * M with A = q^-m * u^-2m
  have hMeq : q ^ (-(m:ℤ) - 1) * u ^ (-2 : ℤ) * (1 - u) / (1 - u ^ (d m))
      = (q ^ (-(m:ℤ)) * u ^ (-(2*(m:ℤ)))) * M := by
    rw [hM_def]
    rw [show (-(m:ℤ) - 1) = (-(m:ℤ)) + (-1) by ring, zpow_add₀ hq0]
    rw [show (-(2*(m:ℤ))) = (-(2*(m:ℤ) - 2)) + (-2) by ring, zpow_add₀ hu0]
    have hv0 : u ^ (2*(m:ℤ) - 2) ≠ 0 := hz2m2
    rw [show u ^ (-(2*(m:ℤ) - 2)) = (u ^ (2*(m:ℤ) - 2))⁻¹ from by rw [zpow_neg]]
    field_simp
  -- rewrite goal LHS via hPshift, then the prefactor relation
  rw [hPshift, hMeq]
  -- goal: (A * M * p) * g1 = x²*A*(p*g0) + A*p*Res
  linear_combination (q ^ (-(m:ℤ)) * u ^ (-(2*(m:ℤ)))) * hkey

/- ## Statement 2 (`KF:appellshift`). -/

/-- Statement 2(a): Term-by-term defect match.
The linear combination of kernel defects is the negative of the `Φ`-defect of 1(ii). -/
theorem stmt2_a (Pd : ℂ → ℂ) (X₀ : ℂ) (D : ℕ → ℂ) (E : ℂ) (w : ℂ) (hm : 2 ≤ m) :
    - X₀ * ( - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Pd (elvC w) )
      + (∑ r ∈ Finset.range (d m),
           D r * ( - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * elvC w * Pd (elvC w)
                      / (1 - ω^r * elvC w) ))
      + E * ( - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * elvC w * Pd (elvC w)
                 / (1 - x * elvC w) )
        = - ( (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Pd (elvC w)
                * ( - X₀ + (∑ r ∈ Finset.range (d m), D r * elvC w / (1 - ω^r * elvC w))
                         + E * elvC w / (1 - x * elvC w) ) ) := by
  -- Distribute -(qC^-m u^-2m Pd u) over the residue bracket; the sum matches
  -- term-by-term after pulling the constant into the Finset.sum.
  -- Both sides share the same Finset.sum after we rewrite each side's sum into
  -- the common summand `-(A · D r · u/(1-ω^r u))`, then `ring` on the scalars.
  have key : ∑ r ∈ Finset.range (d m),
        D r * (-qC τ ^ (-(m:ℤ)) * elvC w ^ (-(2*(m:ℤ))) * elvC w * Pd (elvC w)
                / (1 - ω ^ r * elvC w))
      = qC τ ^ (-(m:ℤ)) * elvC w ^ (-(2*(m:ℤ))) * Pd (elvC w)
          * (- ∑ r ∈ Finset.range (d m), D r * elvC w / (1 - ω ^ r * elvC w)) := by
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [key]
  ring

/-- Statement 2(b): Square-completion identities (standalone arithmetic).
Stated over `ℤ` (via casts) to avoid truncated natural subtraction. -/
theorem stmt2_b_left (n : ℕ) (hm : 2 ≤ m) :
    (m : ℤ) * n^2 + 2*m*n = m*(n+1)^2 - m := by
  ring

theorem stmt2_b_right (n : ℕ) (hm : 2 ≤ m) :
    (m : ℤ) * n^2 + n + 2*m*n + 1 = m*(n+1)^2 + (n+1) - m := by
  ring

/- ## Statement 3 (`KF:corrected`). -/

/-- Statement 3(i): 1-periodicity of `𝓗`. -/
theorem stmt3_i (Pd Gu Bu Aextu : ℂ → ℂ) (Aru : ℕ → ℂ → ℂ)
    (X₀ : ℂ) (D : ℕ → ℂ) (E : ℂ) (w : ℂ) (hm : 2 ≤ m) :
    𝓗 m Pd Gu Bu Aextu Aru X₀ D E (w + 1) = 𝓗 m Pd Gu Bu Aextu Aru X₀ D E w := by
  -- 𝓗 factors through elvC, and elvC (w+1) = elvC w (lem_elv_one).
  simp only [𝓗, lem_elv_one]

/-- Statement 3(ii): Index-`m` twist (paper eq. (4.27)).
The kernel `τ`-shift laws are taken as the designated globally-quantified hypotheses
`hBshift`, `hArshift`, `hAextshift` (Definition 6), specialized inside the proof. -/
theorem stmt3_ii (Pd Gu Bu Aextu : ℂ → ℂ) (Aru : ℕ → ℂ → ℂ)
    (X₀ : ℂ) (D : ℕ → ℂ) (E : ℂ) (w : ℂ) (hm : 2 ≤ m)
    (hu0 : elvC w ≠ 0) (hu1 : elvC w ≠ 1) (hud : (elvC w)^(d m) ≠ 1)
    (hxu : 1 - x * elvC w ≠ 0) (hωu : ∀ r < d m, 1 - ω^r * elvC w ≠ 0)
    (hPshift : Pd (qC τ * elvC w)
      = (qC τ)^(-(m:ℤ) - 1) * (elvC w)^(-2 : ℤ) * (1 - elvC w) / (1 - (elvC w)^(d m)) * Pd (elvC w))
    (hpack : Pd (elvC w) * MasterDefect m x τ Gu (elvC w)
      = Pd (elvC w) * Residues m x ω X₀ D E (elvC w))
    (hBshift : ∀ w : ℂ,
        B Bu (w + τ) = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * B Bu w
                        - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Pd (elvC w))
    (hArshift : ∀ w : ℂ, ∀ r < d m,
        Ar Aru r (w + τ) = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Ar Aru r w
                        - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ)))
                             * elvC w * Pd (elvC w) / (1 - ω^r * elvC w))
    (hAextshift : ∀ w : ℂ,
        Aext Aextu (w + τ)
        = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Aext Aextu w
                        - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ)))
                             * elvC w * Pd (elvC w) / (1 - x * elvC w)) :
    𝓗 m Pd Gu Bu Aextu Aru X₀ D E (w + τ)
      = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * 𝓗 m Pd Gu Bu Aextu Aru X₀ D E w := by
  -- SANITY CHECK PASSED (identity conditioned on the designated shift laws).
  -- STRATEGY: Unfold `𝓗`, `Hu`.  𝓗 = Φ - X₀·B + ∑ D r·Ar r + E·Aext.
  -- Compute 𝓗(w+τ) termwise:
  --  • Φ(w+τ) via stmt1_ii = x²·A·Φ w + A·Pd u·(Residues bracket),  where
  --    A := qC^-m·u^-2m and u := elvC w.
  --  • X₀·B(w+τ) via hBshift = x²·A·X₀·B w - A·X₀·Pd u.
  --  • ∑ D r·Ar r(w+τ) via hArshift (specialize `hArshift w r hr` for each
  --    r < d m inside a Finset.sum_congr) = x²·A·∑ D r·Ar r w
  --      - A·Pd u·∑ D r·u/(1-ω^r u).
  --  • E·Aext(w+τ) via hAextshift = x²·A·E·Aext w - A·Pd u·E·u/(1-x u).
  -- Substitute all four.  The x²·A·(…) parts assemble to x²·A·𝓗 w exactly.
  -- The remaining defect terms are  A·Pd u·(Residues bracket) from Φ, plus the
  -- negatives  +A·X₀·Pd u - A·Pd u·∑ D r u/(1-ω^r u) - A·Pd u·E u/(1-x u),
  -- which is precisely the content of stmt2_a (term-by-term the Φ-defect is the
  -- negative of the kernel defects), so they cancel to 0.  Conclude 𝓗(w+τ)=x²·A·𝓗 w.
  -- Uses hu*, hxu, hωu only through stmt1_ii; the cancellation itself is stmt2_a.
  -- Abbreviations.
  set u := elvC w with hu_def
  set A := (qC τ)^(-(m:ℤ)) * u^(-(2*(m:ℤ))) with hA_def
  -- Express 𝓗 in terms of Φ, B, Ar, Aext at any point.
  have hHexpand : ∀ v : ℂ,
      𝓗 m Pd Gu Bu Aextu Aru X₀ D E v
        = Φ Pd Gu v - X₀ * B Bu v
            + (∑ r ∈ Finset.range (d m), D r * Ar Aru r v) + E * Aext Aextu v := by
    intro v
    simp only [𝓗, Hu, Φ, B, Ar, Aext]
  -- The Φ shift law (Statement 1(ii)).
  have hΦ := stmt1_ii m x τ ω Pd Gu Bu Aextu Aru X₀ D E w hm hu0 hu1 hud hxu hωu hPshift hpack
  -- The kernel shift laws specialized at w.
  have hB := hBshift w
  have hAe := hAextshift w
  -- Canonical residue sum atom.
  set Ssum := ∑ r ∈ Finset.range (d m), D r * u / (1 - ω^r * u) with hSsum_def
  -- Sum shift law: rewrite the sum of Ar(w+τ) termwise, producing Pd u * Ssum.
  have hArsum : ∑ r ∈ Finset.range (d m), D r * Ar Aru r (w + τ)
      = (x:ℂ)^2 * A * (∑ r ∈ Finset.range (d m), D r * Ar Aru r w)
        - A * (Pd u * Ssum) := by
    have hstep : ∑ r ∈ Finset.range (d m), D r * Ar Aru r (w + τ)
        = ∑ r ∈ Finset.range (d m),
            ((x:ℂ)^2 * A * (D r * Ar Aru r w) - A * (Pd u * (D r * u / (1 - ω^r * u)))) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      rw [hArshift w r hr]
      rw [hA_def, hu_def]
      ring
    rw [hstep, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hPS : ∑ r ∈ Finset.range (d m), Pd u * (D r * u / (1 - ω^r * u)) = Pd u * Ssum := by
      rw [hSsum_def, Finset.mul_sum]
    rw [hPS]
  -- The Φ shift law's bracket, rewritten via Ssum.
  have hΦ' : Φ Pd Gu (w + τ)
      = (x:ℂ)^2 * A * Φ Pd Gu w
        + A * Pd u * ( - X₀ + Ssum + E * u / (1 - x * u) ) := by
    rw [hΦ, hA_def, hu_def, hSsum_def]
    ring
  -- Expand both sides.
  rw [hHexpand (w + τ), hHexpand w]
  rw [hΦ', hB, hAe, hArsum]
  rw [hA_def, hu_def]
  ring

/- ## Statement 4 (`KF:untwist`). -/

/-- The untwisted correction `𝓗trans w := 𝓗 (w + lam)`. -/
noncomputable def 𝓗trans (Pd Gu Bu Aextu : ℂ → ℂ) (Aru : ℕ → ℂ → ℂ)
    (X₀ : ℂ) (D : ℕ → ℂ) (E : ℂ) (lam : ℂ) (w : ℂ) : ℂ :=
  𝓗 m Pd Gu Bu Aextu Aru X₀ D E (w + lam)

/-- Statement 4(i): Twist trivialization. -/
theorem stmt4_i (α lam : ℂ) (hm : 2 ≤ m)
    (hx : (x : ℂ) = Complex.exp (2*Real.pi*Complex.I*α))
    (hlam : (m : ℂ) * lam = α) :
    (x : ℂ)^2 * Complex.exp (-(4 : ℂ) * Real.pi * Complex.I * (m : ℂ) * lam) = 1 := by
  -- x = exp(2πiα), α = m·lam, so x^2 = exp(4πi·m·lam); multiply by exp(-4πi·m·lam).
  rw [hx, ← Complex.exp_nat_mul, ← Complex.exp_add]
  rw [show (2 : ℕ) * (2*Real.pi*Complex.I*α) + (-(4:ℂ)*Real.pi*Complex.I*(m:ℂ)*lam)
        = 0 by rw [← hlam]; push_cast; ring]
  exact Complex.exp_zero

/-- Statement 4(ii): Untwisted law (paper eq. (1.17)).

With `𝓗trans w := 𝓗 (w + lam)`.  Derived from Statement 3 (1-periodicity and the
index-`m` twist), the twist trivialization of part (i), and `lem_elv_lam`.  The
side conditions of Statement 3(ii) are imposed at the relevant shifted point
`w + lam` (for the `τ`-law) via `h3ii`, whose hypotheses are the side conditions
at `w + lam`.  The `w+1` case only needs Statement 3(i) (`stmt3_i`), applied at
`w + lam`, so it carries no side conditions. -/
theorem stmt4_ii (Pd Gu Bu Aextu : ℂ → ℂ) (Aru : ℕ → ℂ → ℂ)
    (X₀ : ℂ) (D : ℕ → ℂ) (E : ℂ) (α lam w : ℂ) (hm : 2 ≤ m)
    (hx : (x : ℂ) = Complex.exp (2*Real.pi*Complex.I*α))
    (hlam : (m : ℂ) * lam = α)
    -- side conditions of Statement 3(ii), imposed at the shifted point `w + lam`:
    (hu0 : elvC (w + lam) ≠ 0) (hu1 : elvC (w + lam) ≠ 1)
    (hud : (elvC (w + lam))^(d m) ≠ 1)
    (hxu : 1 - x * elvC (w + lam) ≠ 0)
    (hωu : ∀ r < d m, 1 - ω^r * elvC (w + lam) ≠ 0)
    (hPshift : Pd (qC τ * elvC (w + lam))
      = (qC τ)^(-(m:ℤ) - 1) * (elvC (w + lam))^(-2 : ℤ) * (1 - elvC (w + lam))
          / (1 - (elvC (w + lam))^(d m)) * Pd (elvC (w + lam)))
    (hpack : Pd (elvC (w + lam)) * MasterDefect m x τ Gu (elvC (w + lam))
      = Pd (elvC (w + lam)) * Residues m x ω X₀ D E (elvC (w + lam)))
    (hBshift : ∀ w : ℂ,
        B Bu (w + τ) = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * B Bu w
                        - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Pd (elvC w))
    (hArshift : ∀ w : ℂ, ∀ r < d m,
        Ar Aru r (w + τ) = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Ar Aru r w
                        - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ)))
                             * elvC w * Pd (elvC w) / (1 - ω^r * elvC w))
    (hAextshift : ∀ w : ℂ,
        Aext Aextu (w + τ)
        = (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ))) * Aext Aextu w
                        - (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ)))
                             * elvC w * Pd (elvC w) / (1 - x * elvC w)) :
    (𝓗trans m Pd Gu Bu Aextu Aru X₀ D E lam (w + 1)
        = 𝓗trans m Pd Gu Bu Aextu Aru X₀ D E lam w)
    ∧ (𝓗trans m Pd Gu Bu Aextu Aru X₀ D E lam (w + τ)
        = (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ)))
            * 𝓗trans m Pd Gu Bu Aextu Aru X₀ D E lam w) := by
  -- SANITY CHECK PASSED (derived from stmt3_i, stmt3_ii, stmt4_i, lem_elv_lam).
  -- STRATEGY: constructor (prove the two conjuncts).
  --  • w+1 case: 𝓗trans (w+1) = 𝓗 ((w+1)+lam) = 𝓗 ((w+lam)+1).  Rearrange the
  --    argument with `show`/`ring_nf`/`add_right_comm`, then apply stmt3_i at
  --    the point (w+lam): 𝓗 ((w+lam)+1) = 𝓗 (w+lam) = 𝓗trans w.  No side
  --    conditions needed (stmt3_i is unconditional).
  --  • w+τ case: 𝓗trans (w+τ) = 𝓗 ((w+lam)+τ).  Apply stmt3_ii at the point
  --    (w+lam) — this is exactly why every side condition (hu0..hωu, hPshift,
  --    hpack) is stated at `w+lam` and hBshift/hArshift/hAextshift are global.
  --    That gives 𝓗 ((w+lam)+τ) = x²·(qC)^-m·(elvC(w+lam))^-2m·𝓗 (w+lam).
  --    Now use stmt4_i to kill the twist: x²·exp(-4πi·m·lam) = 1, and
  --    lem_elv_lam gives elvC(w+lam) = exp(2πi lam)·elvC w so
  --    (elvC(w+lam))^-2m = exp(-4πi m lam)·(elvC w)^-2m (via zpow_add₀ /
  --    Complex.exp splitting, base ≠ 0).  Hence x²·(elvC(w+lam))^-2m =
  --    (elvC w)^-2m, leaving (qC)^-m·(elvC w)^-2m·𝓗 (w+lam) = the RHS.
  constructor
  · -- w+1 case
    simp only [𝓗trans]
    rw [show w + 1 + lam = (w + lam) + 1 by ring]
    exact stmt3_i m Pd Gu Bu Aextu Aru X₀ D E (w + lam) hm
  · -- w+τ case
    simp only [𝓗trans]
    rw [show w + τ + lam = (w + lam) + τ by ring]
    have h3 := stmt3_ii m x τ ω Pd Gu Bu Aextu Aru X₀ D E (w + lam) hm
      hu0 hu1 hud hxu hωu hPshift hpack hBshift hArshift hAextshift
    rw [h3]
    -- twist reduction
    have htriv := stmt4_i m x α lam hm hx hlam
    have hlaw := lem_elv_lam w lam
    set e := Complex.exp (2 * Real.pi * Complex.I * lam) with he_def
    have he0 : e ≠ 0 := Complex.exp_ne_zero _
    have hew0 : elvC w ≠ 0 := helvC0 w
    have hsplit : (elvC (w + lam))^(-(2*(m:ℤ))) = e^(-(2*(m:ℤ))) * (elvC w)^(-(2*(m:ℤ))) := by
      rw [hlaw, mul_zpow]
    have hexp : e^(-(2*(m:ℤ))) = Complex.exp (-(4:ℂ) * Real.pi * Complex.I * (m:ℂ) * lam) := by
      rw [he_def, ← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    have hkey : (x:ℂ)^2 * (elvC (w + lam))^(-(2*(m:ℤ))) = (elvC w)^(-(2*(m:ℤ))) := by
      rw [hsplit, hexp]
      have hstep : (x:ℂ)^2 * (Complex.exp (-(4:ℂ) * Real.pi * Complex.I * (m:ℂ) * lam)
              * (elvC w)^(-(2*(m:ℤ))))
            = ((x:ℂ)^2 * Complex.exp (-(4:ℂ) * Real.pi * Complex.I * (m:ℂ) * lam))
              * (elvC w)^(-(2*(m:ℤ))) := by ring
      rw [hstep, htriv, one_mul]
    calc (x:ℂ)^2 * (qC τ)^(-(m:ℤ)) * (elvC (w + lam))^(-(2*(m:ℤ)))
            * 𝓗 m Pd Gu Bu Aextu Aru X₀ D E (w + lam)
        = (qC τ)^(-(m:ℤ)) * ((x:ℂ)^2 * (elvC (w + lam))^(-(2*(m:ℤ))))
            * 𝓗 m Pd Gu Bu Aextu Aru X₀ D E (w + lam) := by ring
      _ = (qC τ)^(-(m:ℤ)) * (elvC w)^(-(2*(m:ℤ)))
            * 𝓗 m Pd Gu Bu Aextu Aru X₀ D E (w + lam) := by rw [hkey]

/- ## Statement 5 (`KF:carrier`), general `m ≥ 2`. -/

/-- Statement 5(i): Covering formula (paper eq. (3.9)), general `m`, in `Q,U` monomials. -/
theorem stmt5_i (Q U : ℂ) (ϑη : ℂ) (ϑ₁ : ℂ → ℂ → ℂ) (qpoch : ℂ)
    (Jprod Jprodd : ℂ → ℂ) (z : ℂ) (hm : 2 ≤ m)
    (hQ0 : Q ≠ 0) (hU0 : U ≠ 0)
    (hQ : Q^24 = qC τ) (hU : U^2 = elvC z)
    (hη : ϑη = Q * qpoch)
    (hϑ₁_tp : ϑ₁ τ z = Complex.I * Q^3 * U^(-1 : ℤ) * Jprod (elvC z))
    (hϑ₁_tpd : ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z)
      = Complex.I * Q^(3*(d m : ℤ)) * U^(-(d m : ℤ)) * Jprodd (elvC z)) :
    𝓙 m τ ϑη ϑ₁ (z) = Q^(2*((m:ℤ) + 1)) * qpoch^(2 - 4*(m:ℤ)) * U^(-(2*(m:ℤ)))
           * (Jprod (elvC z))^(4*m + 1) / Jprodd (elvC z) := by
  -- SANITY CHECK PASSED (algebraic substitution; conditioned on hϑ₁_tp,tpd,hη).
  -- STRATEGY (leaf, directly closable): unfold `𝓙`; substitute hη, hϑ₁_tp,
  -- hϑ₁_tpd.  Numerator: ϑη^(2-4m)·(ϑ₁ τ z)^(4m+1) with
  --   ϑη = Q·qpoch  ⇒  ϑη^(2-4m) = Q^(2-4m)·qpoch^(2-4m),
  --   ϑ₁ τ z = I·Q^3·U^-1·Jprod  ⇒ (ϑ₁ τ z)^(4m+1)
  --       = I^(4m+1)·Q^(3(4m+1))·U^-(4m+1)·(Jprod)^(4m+1).
  -- Denominator: ϑ₁(dτ)(dz) = I·Q^(3d)·U^-d·Jprodd.
  -- Divide: the I-powers give I^(4m+1)/I = I^(4m) = (I^4)^m = 1 (m ℕ), the
  -- Q-powers combine to Q^(2-4m + 3(4m+1) - 3d) = Q^(2·(m+1)) using d=2m+1
  --   [2-4m + 12m+3 - 3(2m+1) = 2-4m+12m+3-6m-3 = 2+2m = 2(m+1)], the U-powers
  -- give U^(-(4m+1)+d) = U^0·... actually -(4m+1) - (-d) = -(4m+1)+(2m+1) =
  --   -2m ⇒ U^-2m, the qpoch keeps qpoch^(2-4m), and Jprod^(4m+1)/Jprodd.
  -- Close via `simp only [𝓙, hη, hϑ₁_tp, hϑ₁_tpd, d]` then push_cast and
  -- `field_simp`/`ring` with Q≠0 (hQ0), U≠0 (hU0); reduce I^(4m) with
  -- Complex.I_pow_four / pow_mul; the zpow arithmetic uses zpow_add₀/zpow_sub₀.
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  set J := Jprod (elvC z) with hJ
  set Jd := Jprodd (elvC z) with hJd
  -- Expand the numerator theta power as a clean monomial in Q, U, I, J.
  have hnum : (Complex.I * Q^3 * U^(-1 : ℤ) * J)^(4*m+1)
      = Complex.I * Q^(3*(4*(m:ℤ)+1)) * U^(-(4*(m:ℤ)+1)) * J^(4*m+1) := by
    rw [mul_pow, mul_pow, mul_pow]
    have hIp : Complex.I ^ (4*m+1) = Complex.I := by
      rw [pow_succ, pow_mul, Complex.I_pow_four, one_pow, one_mul]
    have hQp : (Q^3) ^ (4*m+1) = Q^(3*(4*(m:ℤ)+1)) := by
      rw [← zpow_natCast (Q^3) (4*m+1), ← zpow_natCast Q 3, ← zpow_mul]
      push_cast; ring_nf
    have hUp : (U^(-1:ℤ)) ^ (4*m+1) = U^(-(4*(m:ℤ)+1)) := by
      rw [← zpow_natCast (U^(-1:ℤ)) (4*m+1), ← zpow_mul]
      push_cast; ring_nf
    rw [hIp, hQp, hUp]
  unfold 𝓙
  rw [hη, hϑ₁_tp, hϑ₁_tpd, hnum]
  -- combine ϑη^(2-4m) = Q^(2-4m) * qpoch^(2-4m)
  rw [mul_zpow]
  push_cast [d]
  have hA : Complex.I * Q ^ (3 * (2 * (m:ℤ) + 1)) * U ^ (-(2 * (m:ℤ) + 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hI0 (zpow_ne_zero _ hQ0)) (zpow_ne_zero _ hU0)
  rw [show (Complex.I * Q ^ (3 * (2 * (m:ℤ) + 1)) * U ^ (-(2 * (m:ℤ) + 1)) * Jd)
        = (Complex.I * Q ^ (3 * (2 * (m:ℤ) + 1)) * U ^ (-(2 * (m:ℤ) + 1))) * Jd by ring,
      div_mul_eq_div_div]
  congr 1
  rw [div_eq_iff hA]
  rw [show Q ^ (2 * ((m:ℤ) + 1)) * qpoch ^ (2 - 4 * (m:ℤ)) * U ^ (-(2 * (m:ℤ))) * J ^ (4 * m + 1) *
        (Complex.I * Q ^ (3 * (2 * (m:ℤ) + 1)) * U ^ (-(2 * (m:ℤ) + 1)))
        = Complex.I * (Q ^ (2 * ((m:ℤ) + 1)) * Q ^ (3 * (2 * (m:ℤ) + 1)))
            * (U ^ (-(2 * (m:ℤ))) * U ^ (-(2 * (m:ℤ) + 1)))
            * qpoch ^ (2 - 4 * (m:ℤ)) * J ^ (4 * m + 1) by ring]
  rw [show Q ^ (2 - 4 * (m:ℤ)) * qpoch ^ (2 - 4 * (m:ℤ)) *
        (Complex.I * Q ^ (3 * (4 * (m:ℤ) + 1)) * U ^ (-(4 * (m:ℤ) + 1)) * J ^ (4 * m + 1))
        = Complex.I * (Q ^ (2 - 4 * (m:ℤ)) * Q ^ (3 * (4 * (m:ℤ) + 1)))
            * U ^ (-(4 * (m:ℤ) + 1))
            * qpoch ^ (2 - 4 * (m:ℤ)) * J ^ (4 * m + 1) by ring]
  rw [← zpow_add₀ hQ0, ← zpow_add₀ hQ0, ← zpow_add₀ hU0]
  ring_nf

/-- Statement 5(ii): Index-`m` elliptic law. -/
theorem stmt5_ii (Q U : ℂ) (ϑη : ℂ) (ϑ₁ : ℂ → ℂ → ℂ) (z : ℂ) (hm : 2 ≤ m)
    (hϑ₁_per1 : ϑ₁ τ (z + 1) = - ϑ₁ τ z)
    (hϑ₁_perτ : ϑ₁ τ (z + τ) = - Q^(-12 : ℤ) * U^(-2 : ℤ) * ϑ₁ τ z)
    (hϑ₁_dper1 : ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z + (d m : ℂ)) = - ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z))
    (hϑ₁_dperτ : ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z + (d m : ℂ)*τ)
      = - Q^(-12*(d m : ℤ)) * U^(-2*(d m : ℤ)) * ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z))
    (hQ : Q^24 = qC τ) (hU : U^2 = elvC z) (hQ0 : Q ≠ 0) (hU0 : U ≠ 0) :
    (𝓙 m τ ϑη ϑ₁ (z + 1) = 𝓙 m τ ϑη ϑ₁ z)
    ∧ (𝓙 m τ ϑη ϑ₁ (z + τ) = (qC τ)^(-(m:ℤ)) * (elvC z)^(-(2*(m:ℤ))) * 𝓙 m τ ϑη ϑ₁ z) := by
  -- SANITY CHECK PASSED (conditioned on the four quasi-periodicity hyps).
  -- STRATEGY: constructor.  Unfold `𝓙 = ϑη^(2-4m)·(ϑ₁ τ z)^(4m+1)/ϑ₁(dτ)(dz)`.
  --  • z+1 case: numerator uses hϑ₁_per1: ϑ₁ τ (z+1) = -ϑ₁ τ z, so
  --      (ϑ₁ τ (z+1))^(4m+1) = (-1)^(4m+1)·(ϑ₁ τ z)^(4m+1) = -(…) (odd exponent).
  --    Denominator: ϑ₁(dτ)(d(z+1)) — rewrite d(z+1) = d·z + d (push_cast/ring),
  --    then hϑ₁_dper1: ϑ₁(dτ)(dz + d) = -ϑ₁(dτ)(dz).  The two (-1)'s cancel
  --    ((4m+1) odd and one factor of -1 downstairs), leaving 𝓙 z.  (ϑη factor
  --    unchanged.)  Close with `ring` after the two rewrites.
  --  • z+τ case: numerator uses hϑ₁_perτ: ϑ₁ τ (z+τ) = -Q^-12·U^-2·ϑ₁ τ z ⇒
  --      raised to (4m+1): (-1)^(4m+1)·Q^(-12(4m+1))·U^(-2(4m+1))·(ϑ₁ τ z)^(4m+1).
  --    Denominator: d(z+τ) = d·z + d·τ (push_cast/ring), hϑ₁_dperτ gives
  --      -Q^(-12d)·U^(-2d)·ϑ₁(dτ)(dz).  Ratio of the extra factors:
  --      (-1)/(-1)=1, Q^(-12(4m+1)+12d) and U^(-2(4m+1)+2d).  With d=2m+1:
  --      -12(4m+1)+12(2m+1) = -24m, and -2(4m+1)+2(2m+1) = -4m.  So the prefactor
  --      is Q^-24m·U^-4m = (Q^24)^-m·(U^2)^-2m = (qC τ)^-m·(elvC z)^-2m using
  --      hQ (Q^24=qC τ) and hU (U^2=elvC z).  This matches the RHS times 𝓙 z.
  --    Close via the rewrites + zpow_add₀/zpow_sub₀/mul_zpow with Q≠0,U≠0,
  --    then hQ,hU substitution and `ring`.
  have hQ0' : Q ≠ 0 := hQ0
  have hU0' : U ≠ 0 := hU0
  constructor
  · -- z + 1 case
    unfold 𝓙
    have hd1 : (d m : ℂ) * (z + 1) = (d m : ℂ) * z + (d m : ℂ) := by ring
    rw [hd1, hϑ₁_per1, hϑ₁_dper1]
    have hodd : ((- ϑ₁ τ z) : ℂ) ^ (4*m+1) = - (ϑ₁ τ z) ^ (4*m+1) := by
      rw [neg_pow]
      have : (-1 : ℂ) ^ (4*m+1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [this]; ring
    rw [hodd, mul_neg, neg_div_neg_eq]
  · -- z + τ case
    unfold 𝓙
    have hdτ : (d m : ℂ) * (z + τ) = (d m : ℂ) * z + (d m : ℂ) * τ := by ring
    rw [hdτ, hϑ₁_perτ, hϑ₁_dperτ]
    -- numerator power
    have hnum : (- Q^(-12 : ℤ) * U^(-2 : ℤ) * ϑ₁ τ z) ^ (4*m+1)
        = - Q^(-12*(4*(m:ℤ)+1)) * U^(-2*(4*(m:ℤ)+1)) * (ϑ₁ τ z)^(4*m+1) := by
      rw [show (- Q^(-12 : ℤ) * U^(-2 : ℤ) * ϑ₁ τ z)
            = (-1 : ℂ) * (Q^(-12 : ℤ)) * (U^(-2 : ℤ)) * ϑ₁ τ z by ring,
          mul_pow, mul_pow, mul_pow]
      have hm1 : ((-1 : ℂ)) ^ (4*m+1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      have hQp : (Q^(-12 : ℤ)) ^ (4*m+1) = Q^(-12*(4*(m:ℤ)+1)) := by
        rw [← zpow_natCast (Q^(-12:ℤ)) (4*m+1), ← zpow_mul]; push_cast; ring_nf
      have hUp : (U^(-2 : ℤ)) ^ (4*m+1) = U^(-2*(4*(m:ℤ)+1)) := by
        rw [← zpow_natCast (U^(-2:ℤ)) (4*m+1), ← zpow_mul]; push_cast; ring_nf
      rw [hm1, hQp, hUp]; ring
    rw [hnum]
    set N := (ϑ₁ τ z)^(4*m+1) with hN
    set Dn := ϑ₁ ((d m:ℂ)*τ) ((d m:ℂ)*z) with hDn
    push_cast [d]
    -- Denominator is (- Q^c * U^e) * Dn ; pull Dn out on both sides.
    have hden : (-Q ^ (-12 * (2 * (m:ℤ) + 1)) * U ^ (-2 * (2 * (m:ℤ) + 1)) * Dn)
        = (-Q ^ (-12 * (2 * (m:ℤ) + 1)) * U ^ (-2 * (2 * (m:ℤ) + 1))) * Dn := by ring
    rw [hden, div_mul_eq_div_div]
    rw [show HigherDyson.qC τ ^ (-(m:ℤ)) * HigherDyson.elvC z ^ (-(2 * (m:ℤ))) *
          (ϑη ^ (2 - 4 * (m:ℤ)) * N / Dn)
        = (HigherDyson.qC τ ^ (-(m:ℤ)) * HigherDyson.elvC z ^ (-(2 * (m:ℤ))) *
            (ϑη ^ (2 - 4 * (m:ℤ)) * N)) / Dn by ring]
    congr 1
    have hC : (-Q ^ (-12 * (2 * (m:ℤ) + 1)) * U ^ (-2 * (2 * (m:ℤ) + 1))) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (zpow_ne_zero _ hQ0')) (zpow_ne_zero _ hU0')
    rw [div_eq_iff hC]
    have hq24 : HigherDyson.qC τ ^ (-(m:ℤ)) = Q ^ (-24 * (m:ℤ)) := by
      rw [← hQ, ← zpow_natCast Q 24, ← zpow_mul]; congr 1; push_cast; ring
    have hu2 : HigherDyson.elvC z ^ (-(2 * (m:ℤ))) = U ^ (-4 * (m:ℤ)) := by
      rw [← hU, ← zpow_natCast U 2, ← zpow_mul]; congr 1; push_cast; ring
    rw [hq24, hu2]
    rw [show ϑη ^ (2 - 4 * (m:ℤ)) * (-Q ^ (-12 * (4 * (m:ℤ) + 1)) * U ^ (-2 * (4 * (m:ℤ) + 1)) * N)
          = (-1 : ℂ) * (Q ^ (-12 * (4 * (m:ℤ) + 1))) * (U ^ (-2 * (4 * (m:ℤ) + 1)))
              * (ϑη ^ (2 - 4 * (m:ℤ)) * N) by ring,
        show Q ^ (-24 * (m:ℤ)) * U ^ (-4 * (m:ℤ)) * (ϑη ^ (2 - 4 * (m:ℤ)) * N) *
              (-Q ^ (-12 * (2 * (m:ℤ) + 1)) * U ^ (-2 * (2 * (m:ℤ) + 1)))
          = (-1 : ℂ) * (Q ^ (-24 * (m:ℤ)) * Q ^ (-12 * (2 * (m:ℤ) + 1)))
              * (U ^ (-4 * (m:ℤ)) * U ^ (-2 * (2 * (m:ℤ) + 1)))
              * (ϑη ^ (2 - 4 * (m:ℤ)) * N) by ring]
    rw [← zpow_add₀ hQ0', ← zpow_add₀ hU0']
    congr 2
    · congr 1; ring
    · congr 1; ring

/-- Statement 5(iii): Weight datum.  Stated over `ℤ` to avoid natural subtraction. -/
theorem stmt5_iii (hm : 2 ≤ m) : (4*(m:ℤ) + 1) - (d m : ℤ) = 2*m := by
  simp only [d]; push_cast; ring

/- ## Statement 6 (`KF:level5`). Level `m = 2`, `d = 5`, `IsPrimitiveRoot ω 5`, `x = 1`. -/

/-- Statement 6(a): Collapsed level-5 defect identity.
Pointwise for `u ≠ 0`, `1 - u^5 ≠ 0`, `1 - u ≠ 0`. -/
theorem stmt6_a (Md G51 T51 : ℂ → ℂ) (X₀ X₁ X₂ X₃ P5P1 : ℂ) (u : ℂ)
    (hx1 : (x : ℂ) = 1) (hω : IsPrimitiveRoot ω 5) (hm : m = 2)
    (hu0 : u ≠ 0) (hu5 : 1 - u^5 ≠ 0) (hu1 : 1 - u ≠ 0)
    (hMshift : Md (qC τ * u)
      = u^(2*(m:ℤ) - 2) * (1 - u) / (1 - u^(d m)) * Md u)
    (hTc : T51 u = (1 - u) * S51 τ X₀ X₁ X₂ X₃ P5P1 u)
    (hKdefect : K51 Md G51 (qC τ * u) - (1:ℂ) * K51 Md G51 u
      = Md u / (u * (1 - u^5) * (1 - u)) * T51 u) :
    K51 Md G51 (qC τ * u) - K51 Md G51 u
      = Md u / (u * (1 - u^5)) * S51 τ X₀ X₁ X₂ X₃ P5P1 u := by
  -- SANITY CHECK PASSED (conditioned on hKdefect, hTc; pure field algebra).
  -- STRATEGY (leaf, directly closable): rewrite the LHS with hKdefect (drop the
  -- `1 *` via `one_mul`):  LHS = Md u/(u·(1-u^5)·(1-u))·T51 u.  Substitute hTc:
  --   T51 u = (1-u)·S51 …, so  LHS = Md u/(u·(1-u^5)·(1-u))·(1-u)·S51 …
  --   = Md u·(1-u)/(u·(1-u^5)·(1-u))·S51 = Md u/(u·(1-u^5))·S51 …
  -- after cancelling the (1-u) factor (needs 1-u ≠ 0 = hu1; also u≠0=hu0,
  -- 1-u^5≠0=hu5 to keep denominators nonzero).  Close with
  -- `rw [hKdefect, one_mul, hTc]; field_simp; ring` (the S51/K51/Md are opaque
  -- and pass through untouched).
  rw [one_mul] at hKdefect
  rw [hKdefect, hTc]
  have hne : (1 : ℂ) - u ≠ 0 := hu1
  field_simp

/-- Statement 6(b): Level-5 residue partial fraction.
Pointwise for `u ≠ 0`, `1 - ω^r u ≠ 0` for `0 ≤ r < 5`, `1 - u^5 ≠ 0`. -/
theorem stmt6_b (X₀ X₁ X₂ X₃ P5P1 : ℂ) (u : ℂ) (hm : m = 2)
    (hω : IsPrimitiveRoot ω 5)
    (hu0 : u ≠ 0) (hu5 : 1 - u^5 ≠ 0)
    (hωu : ∀ r < 5, 1 - ω^r * u ≠ 0) :
    S51 τ X₀ X₁ X₂ X₃ P5P1 u / (u * (1 - u^5))
      = - X₀ / u + (∑ r ∈ Finset.range 5, D51 τ ω X₀ X₁ X₂ X₃ P5P1 r / (1 - ω^r * u)) := by
  -- SANITY CHECK PASSED (a genuine partial-fraction identity; the RHS
  -- coefficients D51 r are DEFINED as (ω^r/5)·S51(ω^{-r}), so this is a real
  -- root-of-unity conclusion, not a definitional restatement).
  -- =========================  RIGOROUS ARGUMENT  =========================
  -- Multiply both sides by u·(1-u^5) (both denominators nonzero: hu0, hu5, and
  -- 1-ω^r u ≠ 0 by hωu; also 1-u^5 = ∏_{r<5}(1-ω^r u) since ω is a primitive
  -- 5th root — see below).  The claim becomes the POLYNOMIAL identity
  --    S51 u  =  -X₀·(1-u^5)  +  ∑_{r<5} D51 r · u·(1-u^5)/(1-ω^r u).       (★)
  -- Two ingredients:
  --  (1) Factorization of 1-u^5.  Since IsPrimitiveRoot ω 5, {ω^0,…,ω^4} are
  --      the five distinct 5th roots of unity, so
  --         1 - u^5 = ∏_{r<5} (1 - ω^r·u)                                    (F)
  --      (Mathlib: `IsPrimitiveRoot` API — `IsPrimitiveRoot.prod_one_sub`-style
  --      / `X^n - C 1 = ∏ (X - C ζ^i)`; concretely one can expand the RHS of
  --      (F) with Finset.range 5 = {0,1,2,3,4}, use ω^5 = 1 (hω.pow_eq_one) and
  --      the elementary-symmetric vanishing e_1=…=e_4 = 0, e_5 = -1 for 5th
  --      roots, then `ring`.  Equivalently reduce (F) to the Vandermonde/geom
  --      fact ∑_{r<5} ω^{rk} = 0 for 1≤k≤4, ω^{r·0}=5, i.e. `hω.geom_sum_eq_zero`.)
  --      Hence u·(1-u^5)/(1-ω^r u) = u·∏_{s≠r}(1-ω^s u), a polynomial.
  --  (2) Residue evaluation.  Because D51 r := (ω^r/5)·S51(ω^{-r}) and (★) is a
  --      polynomial identity of degree ≤5 (LHS S51 has degree 4; RHS degree 5
  --      but the u^5-coefficients cancel — see check below), it suffices to
  --      verify (★) at the 6 points u ∈ {0, ω^0,…,ω^{-4}}=6 distinct values, OR
  --      to expand both sides symbolically.  At u = ω^{-r₀} (a pole of the r₀
  --      term, killed elsewhere by the (1-ω^{r₀}u) factor in (F)) the surviving
  --      residue reads:  the r₀-term contributes D51 r₀·ω^{-r₀}·∏_{s≠r₀}(1-ω^{s-r₀})
  --      and ∏_{s≠r₀}(1-ω^{s-r₀}) = ∏_{k=1}^{4}(1-ω^k) = 5  (standard:
  --      ∏_{k=1}^{n-1}(1-ω^k) = n for a primitive n-th root; Mathlib around
  --      `IsPrimitiveRoot` / cyclotomic `Polynomial.cyclotomic_eval_one`).
  --      Thus the residue is D51 r₀·ω^{-r₀}·5 = (ω^{r₀}/5)·S51(ω^{-r₀})·ω^{-r₀}·5
  --      = S51(ω^{-r₀}), matching the LHS residue at that pole. The 1/u term
  --      residue at u=0 is S51 0 = (1-0)·R51 0 - 0 = R51 0 = -X₀ (from the R51
  --      definition: constant term of R51 is ((qC)^-1·0 - 0 -0 -0 -1)·X₀ ... 
  --      careful: R51 0 = (0-0-0-0-1)·X₀ - 0 - 0 - 0 = -X₀), matching -X₀/u.
  --  Matching all 6 residues (5 finite poles + the u=0 pole) of the two rational
  --  functions, which have the SAME denominator u·(1-u^5) with only simple poles,
  --  forces equality (a rational function with prescribed simple-pole residues and
  --  no polynomial part — degree S51 = 4 < 5 = deg(u(1-u^5)) — is unique).
  -- =======================================================================
  -- FORMALIZATION PLAN (next phase): prove (F) as a helper `have hfac`, then
  -- prove ∏_{k=1}^4 (1-ω^k) = 5 as `have hprod5` (cyclotomic_eval_one 5 or direct
  -- expansion of Finset with hω.pow_eq_one + hω.ne_one powers), unfold S51/R51/D51,
  -- clear denominators with field_simp [hu0,hu5,hωu,...], expand Finset.range 5,
  -- and close the resulting polynomial identity in u,ω with `ring_nf` + the two
  -- ω-relations (ω^5=1 and the symmetric-function/residue evaluations).  This is
  -- the sole genuinely number-theoretic subgoal; per problem.md it must be closed
  -- honestly (no smuggled per-residue hypothesis) or reported "not closed".
  have hw5 : ω^5 = 1 := hω.pow_eq_one
  have hgeom0 : ∑ i ∈ Finset.range 5, ω^i = 0 := hω.geom_sum_eq_zero (by norm_num)
  have hgeom : 1 + ω + ω^2 + ω^3 + ω^4 = 0 := by
    have := hgeom0
    simp [Finset.sum_range_succ] at this
    linear_combination this
  -- nonzero denominators
  have h0 := hωu 0 (by norm_num)
  have h1 := hωu 1 (by norm_num)
  have h2 := hωu 2 (by norm_num)
  have h3 := hωu 3 (by norm_num)
  have h4 := hωu 4 (by norm_num)
  simp only [pow_zero, one_mul] at h0
  -- unfold D51, S51, R51 and expand the sum
  simp only [D51, S51, R51, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- reduce negative zpow of ω to nat powers using ω^5=1
  have e0 : ω^(-(0:ℤ)) = 1 := by norm_num
  have e1 : ω^(-(1:ℤ)) = ω^4 := by
    rw [zpow_neg, zpow_one]; rw [inv_eq_of_mul_eq_one_left]; linear_combination hw5
  have e2 : ω^(-(2:ℤ)) = ω^3 := by
    rw [show (-(2:ℤ)) = -(2:ℕ) by norm_num, zpow_neg, zpow_natCast]
    rw [inv_eq_of_mul_eq_one_left]; linear_combination hw5
  have e3 : ω^(-(3:ℤ)) = ω^2 := by
    rw [show (-(3:ℤ)) = -(3:ℕ) by norm_num, zpow_neg, zpow_natCast]
    rw [inv_eq_of_mul_eq_one_left]; linear_combination hw5
  have e4 : ω^(-(4:ℤ)) = ω := by
    rw [show (-(4:ℤ)) = -(4:ℕ) by norm_num, zpow_neg, zpow_natCast]
    rw [inv_eq_of_mul_eq_one_left]; linear_combination hw5
  push_cast [e0, e1, e2, e3, e4]
  -- Factorization (F): 1 - u^5 = ∏_{r<5}(1-ω^r u), expanded to 5 explicit factors.
  -- Proof: (1-u^5) - ∏(1-ω^r u) = P(u,ω)·(1+ω+ω²+ω³+ω⁴), which vanishes by hgeom
  -- (the cofactor P was computed by polynomial division; see sympy check).
  have hfac : (1:ℂ) - u^5
      = (1 - u) * (1 - ω*u) * (1 - ω^2*u) * (1 - ω^3*u) * (1 - ω^4*u) := by
    linear_combination
      (u^5*ω^6 - u^5*ω^5 + u^5*ω - u^5 - u^4*ω^6 + u^3*ω^5 + u^3*ω^3
        - u^2*ω^3 - u^2*ω + u) * hgeom
  -- ω-power reductions mod 5 (for cleaning up (ω^k)^j after expansion).
  have p6 : ω^6 = ω := by rw [show (6:ℕ)=5+1 by rfl, pow_add, hw5, one_mul, pow_one]
  have p7 : ω^7 = ω^2 := by rw [show (7:ℕ)=5+2 by rfl, pow_add, hw5, one_mul]
  have p8 : ω^8 = ω^3 := by rw [show (8:ℕ)=5+3 by rfl, pow_add, hw5, one_mul]
  have p9 : ω^9 = ω^4 := by rw [show (9:ℕ)=5+4 by rfl, pow_add, hw5, one_mul]
  have p10 : ω^10 = 1 := by rw [show (10:ℕ)=5+5 by rfl, pow_add, hw5, one_mul]
  have p12 : ω^12 = ω^2 := by rw [show (12:ℕ)=5+5+2 by rfl, pow_add, pow_add, hw5, one_mul, one_mul]
  -- Nonzero denominators.
  have hp1 : (1:ℂ) - ω * u ≠ 0 := by simpa using h1
  have hp2 : (1:ℂ) - ω^2 * u ≠ 0 := h2
  have hp3 : (1:ℂ) - ω^3 * u ≠ 0 := h3
  have hp4 : (1:ℂ) - ω^4 * u ≠ 0 := h4
  -- Clear all denominators (u, 1-u^5, and 1-ω^r u for r=1..4; the r=0 factor is
  -- 1-u=h0) to a common polynomial identity, then close it as a ℚ[u,ω]-multiple of
  -- the cyclotomic relation hgeom (cofactor computed by polynomial division after
  -- reducing ω-powers mod 5; see sympy).  hfac (1-u^5 = ∏(1-ω^r u)) supplies the
  -- link between the two denominator families used inside the final ring reasoning.
  simp only [pow_zero, one_mul]
  -- Turn every RHS fraction into one over the common denominator (1-u^5) using hfac,
  -- so combining collapses the whole equality into a single polynomial identity.
  -- Products of the "other four" pole factors:
  set P0 := (1 - ω*u) * (1 - ω^2*u) * (1 - ω^3*u) * (1 - ω^4*u) with hP0
  set P1 := (1 - u) * (1 - ω^2*u) * (1 - ω^3*u) * (1 - ω^4*u) with hP1
  set P2 := (1 - u) * (1 - ω*u) * (1 - ω^3*u) * (1 - ω^4*u) with hP2
  set P3 := (1 - u) * (1 - ω*u) * (1 - ω^2*u) * (1 - ω^4*u) with hP3
  set P4 := (1 - u) * (1 - ω*u) * (1 - ω^2*u) * (1 - ω^3*u) with hP4
  -- Each pole factor times its complementary product equals 1-u^5 (hfac, reordered).
  have hf0 : (1 - u) * P0 = 1 - u^5 := by rw [hP0, hfac]; ring
  have hf1 : (1 - ω*u) * P1 = 1 - u^5 := by rw [hP1, hfac]; ring
  have hf2 : (1 - ω^2*u) * P2 = 1 - u^5 := by rw [hP2, hfac]; ring
  have hf3 : (1 - ω^3*u) * P3 = 1 - u^5 := by rw [hP3, hfac]; ring
  have hf4 : (1 - ω^4*u) * P4 = 1 - u^5 := by rw [hP4, hfac]; ring
  -- P_r ≠ 0 (since (1-ω^r u)*P_r = 1-u^5 ≠ 0).
  have hP0ne : P0 ≠ 0 := by intro h; apply hu5; rw [← hf0, h, mul_zero]
  have hP1ne : P1 ≠ 0 := by intro h; apply hu5; rw [← hf1, h, mul_zero]
  have hP2ne : P2 ≠ 0 := by intro h; apply hu5; rw [← hf2, h, mul_zero]
  have hP3ne : P3 ≠ 0 := by intro h; apply hu5; rw [← hf3, h, mul_zero]
  have hP4ne : P4 ≠ 0 := by intro h; apply hu5; rw [← hf4, h, mul_zero]
  -- Convert each finite pole term to denominator (1-u^5):  x/(1-ω^r u) = x*P_r/(1-u^5).
  have conv0 : ∀ x : ℂ, x / (1 - u) = x * P0 / (1 - u^5) := by
    intro x; rw [← hf0, mul_comm (1-u) P0, ← div_div, mul_div_assoc,
      div_self hP0ne, mul_one]
  have conv1 : ∀ x : ℂ, x / (1 - ω*u) = x * P1 / (1 - u^5) := by
    intro x; rw [← hf1, mul_comm (1-ω*u) P1, ← div_div, mul_div_assoc,
      div_self hP1ne, mul_one]
  have conv2 : ∀ x : ℂ, x / (1 - ω^2*u) = x * P2 / (1 - u^5) := by
    intro x; rw [← hf2, mul_comm (1-ω^2*u) P2, ← div_div, mul_div_assoc,
      div_self hP2ne, mul_one]
  have conv3 : ∀ x : ℂ, x / (1 - ω^3*u) = x * P3 / (1 - u^5) := by
    intro x; rw [← hf3, mul_comm (1-ω^3*u) P3, ← div_div, mul_div_assoc,
      div_self hP3ne, mul_one]
  have conv4 : ∀ x : ℂ, x / (1 - ω^4*u) = x * P4 / (1 - u^5) := by
    intro x; rw [← hf4, mul_comm (1-ω^4*u) P4, ← div_div, mul_div_assoc,
      div_self hP4ne, mul_one]
  -- Normalize ω^1 to ω, then rewrite each finite pole to denominator (1-u^5).
  simp only [pow_one]
  rw [conv0, conv1, conv2, conv3, conv4]
  -- Combine the five (1-u^5) fractions into one, and -X₀/u over u.
  rw [div_add_div_same, div_add_div_same, div_add_div_same, div_add_div_same,
      div_add_div _ _ hu0 hu5]
  -- Both single fractions share the SAME denominator u*(1-u^5); reduce to equal numerators.
  congr 1
  -- Expand P_r; now a pure polynomial identity (★) in u,ω,q:=(qC τ)⁻¹,X_i,P5P1.
  rw [hP0, hP1, hP2, hP3, hP4]
  linear_combination ((P5P1*u^5*ω^22) + (-1*P5P1*u^5*ω^21) + (P5P1*u^5*ω^18) + (-1*P5P1*u^5*ω^16) + (P5P1*u^5*ω^14) + (-1*P5P1*u^5*ω^11) + (P5P1*u^5*ω^10) + (-1*P5P1*u^4*ω^22) + (P5P1*u^4*ω^21) + (-1*P5P1*u^4*ω^20) + (-1*P5P1*u^4*ω^18) + (2*P5P1*u^4*ω^16) + (-2*P5P1*u^4*ω^15) + (-1*P5P1*u^4*ω^14) + (3*P5P1*u^4*ω^11) + (-4*P5P1*u^4*ω^10) + (4*P5P1*u^4*ω^6) + (-5*P5P1*u^4*ω^5) + (5*P5P1*ω*u^4) + (-5*P5P1*u^4) + (P5P1*u^3*ω^20) + (P5P1*u^3*ω^17) + (-1*P5P1*u^3*ω^16) + (2*P5P1*u^3*ω^15) + (P5P1*u^3*ω^10) + (P5P1*u^3*ω^9) + (-1*P5P1*u^3*ω^6) + (P5P1*u^3*ω^5) + (P5P1*u^3*ω^3) + (-1*P5P1*u^2*ω^17) + (-1*P5P1*u^2*ω^13) + (P5P1*u^2*ω^12) + (-2*P5P1*u^2*ω^11) + (P5P1*u^2*ω^10) + (-1*P5P1*u^2*ω^8) + (-1*P5P1*u^2*ω^6) + (P5P1*u^2*ω^5) + (-1*P5P1*ω*u^2) + (P5P1*u*ω^13) + (-1*P5P1*u*ω^12) + (P5P1*u*ω^10) + (-1*P5P1*u*ω^9) + (P5P1*u*ω^8) + (-1*P5P1*u*ω^6) + (P5P1*u*ω^5) + (-1*P5P1*u*ω) + (P5P1*u) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^5*ω^18) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^5*ω^17) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^5*ω^15) + ((-2/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^5*ω^14) + ((2/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^5*ω^13) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^5*ω^12) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^18) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^17) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^16) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^15) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^14) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^12) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^11) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^4*ω^9) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^16) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^14) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^13) + ((2/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^11) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^10) + ((-2/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^9) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^7) + (X₀*(qC τ ^ (-1:ℤ))*u^3*ω^6) + (-1*X₀*(qC τ ^ (-1:ℤ))*u^3*ω^5) + (X₀*(qC τ ^ (-1:ℤ))*ω*u^3) + (-1*X₀*(qC τ ^ (-1:ℤ))*u^3) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^2*ω^13) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^2*ω^11) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^2*ω^10) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^2*ω^8) + ((-4/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u^2*ω^6) + (X₀*(qC τ ^ (-1:ℤ))*u^2*ω^5) + (-1*X₀*(qC τ ^ (-1:ℤ))*ω*u^2) + (X₀*(qC τ ^ (-1:ℤ))*u^2) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u*ω^9) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u*ω^8) + ((1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u*ω^7) + ((-1/5 : ℂ)*X₀*(qC τ ^ (-1:ℤ))*u*ω^6) + ((-1/5 : ℂ)*X₀*u^5*ω^22) + ((1/5 : ℂ)*X₀*u^5*ω^21) + ((-1/5 : ℂ)*X₀*u^5*ω^18) + ((1/5 : ℂ)*X₀*u^5*ω^16) + ((-1/5 : ℂ)*X₀*u^5*ω^14) + ((1/5 : ℂ)*X₀*u^5*ω^11) + ((-1/5 : ℂ)*X₀*u^5*ω^10) + (X₀*u^5*ω^6) + (-1*X₀*u^5*ω^5) + (X₀*ω*u^5) + (-1*X₀*u^5) + ((1/5 : ℂ)*X₀*u^4*ω^22) + ((-1/5 : ℂ)*X₀*u^4*ω^21) + ((1/5 : ℂ)*X₀*u^4*ω^20) + ((1/5 : ℂ)*X₀*u^4*ω^18) + ((-2/5 : ℂ)*X₀*u^4*ω^16) + ((2/5 : ℂ)*X₀*u^4*ω^15) + ((1/5 : ℂ)*X₀*u^4*ω^14) + ((-3/5 : ℂ)*X₀*u^4*ω^11) + ((4/5 : ℂ)*X₀*u^4*ω^10) + ((-8/5 : ℂ)*X₀*u^4*ω^6) + (X₀*u^4*ω^5) + (-1*X₀*ω*u^4) + (X₀*u^4) + ((-1/5 : ℂ)*X₀*u^3*ω^20) + ((-1/5 : ℂ)*X₀*u^3*ω^17) + ((1/5 : ℂ)*X₀*u^3*ω^16) + ((-2/5 : ℂ)*X₀*u^3*ω^15) + ((-1/5 : ℂ)*X₀*u^3*ω^10) + ((-1/5 : ℂ)*X₀*u^3*ω^9) + ((1/5 : ℂ)*X₀*u^3*ω^6) + ((2/5 : ℂ)*X₀*u^3*ω^5) + ((2/5 : ℂ)*X₀*u^3*ω^3) + ((1/5 : ℂ)*X₀*u^2*ω^17) + ((1/5 : ℂ)*X₀*u^2*ω^13) + ((-1/5 : ℂ)*X₀*u^2*ω^12) + ((2/5 : ℂ)*X₀*u^2*ω^11) + ((-1/5 : ℂ)*X₀*u^2*ω^10) + ((1/5 : ℂ)*X₀*u^2*ω^8) + ((1/5 : ℂ)*X₀*u^2*ω^6) + ((-1/5 : ℂ)*X₀*u^2*ω^5) + ((-2/5 : ℂ)*X₀*u^2*ω^3) + ((-1/5 : ℂ)*X₀*ω*u^2) + ((-1/5 : ℂ)*X₀*u*ω^13) + ((1/5 : ℂ)*X₀*u*ω^12) + ((-1/5 : ℂ)*X₀*u*ω^10) + ((1/5 : ℂ)*X₀*u*ω^9) + ((-1/5 : ℂ)*X₀*u*ω^8) + ((1/5 : ℂ)*X₀*u*ω^6) + ((-1/5 : ℂ)*X₀*u*ω^5) + ((1/5 : ℂ)*X₀*u*ω) + ((-1/5 : ℂ)*X₁*u^5*ω^18) + ((1/5 : ℂ)*X₁*u^5*ω^17) + ((-1/5 : ℂ)*X₁*u^5*ω^15) + ((1/5 : ℂ)*X₁*u^5*ω^14) + ((-1/5 : ℂ)*X₁*u^5*ω^13) + ((1/5 : ℂ)*X₁*u^5*ω^11) + ((1/5 : ℂ)*X₁*u^4*ω^18) + ((-1/5 : ℂ)*X₁*u^4*ω^17) + ((1/5 : ℂ)*X₁*u^4*ω^16) + ((1/5 : ℂ)*X₁*u^4*ω^15) + ((-1/5 : ℂ)*X₁*u^4*ω^13) + ((1/5 : ℂ)*X₁*u^4*ω^12) + ((1/5 : ℂ)*X₁*u^4*ω^11) + ((-1/5 : ℂ)*X₁*u^4*ω^10) + ((-2/5 : ℂ)*X₁*u^4*ω^8) + ((-1/5 : ℂ)*X₁*u^3*ω^16) + ((-1/5 : ℂ)*X₁*u^3*ω^14) + ((1/5 : ℂ)*X₁*u^3*ω^13) + ((-1/5 : ℂ)*X₁*u^3*ω^12) + ((-3/5 : ℂ)*X₁*u^3*ω^11) + ((2/5 : ℂ)*X₁*u^3*ω^10) + ((1/5 : ℂ)*X₁*u^3*ω^8) + ((-2/5 : ℂ)*X₁*u^3*ω^6) + (X₁*u^3*ω^5) + (-1*X₁*ω*u^3) + (X₁*u^3) + ((1/5 : ℂ)*X₁*u^2*ω^13) + ((1/5 : ℂ)*X₁*u^2*ω^11) + ((-1/5 : ℂ)*X₁*u^2*ω^10) + ((1/5 : ℂ)*X₁*u^2*ω^9) + ((1/5 : ℂ)*X₁*u^2*ω^7) + ((1/5 : ℂ)*X₁*u^2*ω^6) + ((-4/5 : ℂ)*X₁*u^2*ω^5) + ((-1/5 : ℂ)*X₁*u*ω^9) + ((1/5 : ℂ)*X₁*u*ω^8) + ((-1/5 : ℂ)*X₁*u*ω^7) + ((1/5 : ℂ)*X₁*u*ω^6) + ((-1/5 : ℂ)*X₁*u*ω^5) + (X₁*u*ω) + (-1*X₁*u) + ((-1/5 : ℂ)*X₂*u^5*ω^22) + ((1/5 : ℂ)*X₂*u^5*ω^21) + ((-1/5 : ℂ)*X₂*u^5*ω^18) + ((1/5 : ℂ)*X₂*u^5*ω^16) + ((-1/5 : ℂ)*X₂*u^5*ω^13) + ((1/5 : ℂ)*X₂*u^5*ω^12) + ((1/5 : ℂ)*X₂*u^4*ω^22) + ((-1/5 : ℂ)*X₂*u^4*ω^21) + ((1/5 : ℂ)*X₂*u^4*ω^20) + ((1/5 : ℂ)*X₂*u^4*ω^18) + ((-2/5 : ℂ)*X₂*u^4*ω^16) + ((2/5 : ℂ)*X₂*u^4*ω^15) + ((1/5 : ℂ)*X₂*u^4*ω^13) + ((-2/5 : ℂ)*X₂*u^4*ω^12) + ((-3/5 : ℂ)*X₂*u^4*ω^11) + ((4/5 : ℂ)*X₂*u^4*ω^10) + ((-1/5 : ℂ)*X₂*u^4*ω^9) + (-1*X₂*u^4*ω^6) + (X₂*u^4*ω^5) + (-1*X₂*ω*u^4) + (X₂*u^4) + ((-1/5 : ℂ)*X₂*u^3*ω^20) + ((-1/5 : ℂ)*X₂*u^3*ω^17) + ((1/5 : ℂ)*X₂*u^3*ω^16) + ((-2/5 : ℂ)*X₂*u^3*ω^15) + ((1/5 : ℂ)*X₂*u^3*ω^12) + ((1/5 : ℂ)*X₂*u^3*ω^11) + ((-2/5 : ℂ)*X₂*u^3*ω^10) + ((1/5 : ℂ)*X₂*u^3*ω^9) + ((1/5 : ℂ)*X₂*u^3*ω^8) + ((1/5 : ℂ)*X₂*u^3*ω^7) + ((1/5 : ℂ)*X₂*u^2*ω^17) + ((1/5 : ℂ)*X₂*u^2*ω^13) + ((-1/5 : ℂ)*X₂*u^2*ω^12) + ((2/5 : ℂ)*X₂*u^2*ω^11) + ((-1/5 : ℂ)*X₂*u^2*ω^10) + ((-1/5 : ℂ)*X₂*u^2*ω^9) + ((-1/5 : ℂ)*X₂*u^2*ω^7) + ((4/5 : ℂ)*X₂*u^2*ω^6) + (-1*X₂*u^2*ω^5) + (X₂*ω*u^2) + (-1*X₂*u^2) + ((-1/5 : ℂ)*X₂*u*ω^13) + ((1/5 : ℂ)*X₂*u*ω^12) + ((-1/5 : ℂ)*X₂*u*ω^10) + ((1/5 : ℂ)*X₂*u*ω^9) + ((-1/5 : ℂ)*X₂*u*ω^8) + ((1/5 : ℂ)*X₂*u*ω^6) + ((-1/5 : ℂ)*X₃*u^5*ω^22) + ((1/5 : ℂ)*X₃*u^5*ω^21) + ((-1/5 : ℂ)*X₃*u^5*ω^17) + ((1/5 : ℂ)*X₃*u^5*ω^16) + ((1/5 : ℂ)*X₃*u^5*ω^15) + ((-2/5 : ℂ)*X₃*u^5*ω^14) + ((1/5 : ℂ)*X₃*u^5*ω^13) + ((1/5 : ℂ)*X₃*u^4*ω^22) + ((-1/5 : ℂ)*X₃*u^4*ω^21) + ((1/5 : ℂ)*X₃*u^4*ω^20) + ((1/5 : ℂ)*X₃*u^4*ω^17) + ((-3/5 : ℂ)*X₃*u^4*ω^16) + ((1/5 : ℂ)*X₃*u^4*ω^15) + ((1/5 : ℂ)*X₃*u^4*ω^14) + ((1/5 : ℂ)*X₃*u^4*ω^13) + ((-1/5 : ℂ)*X₃*u^4*ω^12) + ((-4/5 : ℂ)*X₃*u^4*ω^11) + ((4/5 : ℂ)*X₃*u^4*ω^10) + (-1*X₃*u^4*ω^6) + (X₃*u^4*ω^5) + (-1*X₃*ω*u^4) + (X₃*u^4) + ((-1/5 : ℂ)*X₃*u^3*ω^20) + ((-1/5 : ℂ)*X₃*u^3*ω^17) + ((2/5 : ℂ)*X₃*u^3*ω^16) + ((-2/5 : ℂ)*X₃*u^3*ω^15) + ((1/5 : ℂ)*X₃*u^3*ω^14) + ((-1/5 : ℂ)*X₃*u^3*ω^13) + ((1/5 : ℂ)*X₃*u^3*ω^12) + ((3/5 : ℂ)*X₃*u^3*ω^11) + ((-3/5 : ℂ)*X₃*u^3*ω^10) + ((-1/5 : ℂ)*X₃*u^3*ω^9) + ((1/5 : ℂ)*X₃*u^3*ω^8) + (X₃*u^3*ω^6) + (-1*X₃*u^3*ω^5) + (X₃*ω*u^3) + (-1*X₃*u^3) + ((1/5 : ℂ)*X₃*u^2*ω^17) + ((-1/5 : ℂ)*X₃*u^2*ω^12) + ((1/5 : ℂ)*X₃*u^2*ω^11) + ((-1/5 : ℂ)*X₃*u^2*ω^9) + ((1/5 : ℂ)*X₃*u^2*ω^8) + ((-1/5 : ℂ)*X₃*u^2*ω^7) + ((-1/5 : ℂ)*X₃*u*ω^13) + ((1/5 : ℂ)*X₃*u*ω^12) + ((-1/5 : ℂ)*X₃*u*ω^10) + ((2/5 : ℂ)*X₃*u*ω^9) + ((-2/5 : ℂ)*X₃*u*ω^8) + ((1/5 : ℂ)*X₃*u*ω^7)) * hgeom

/-- Statement 6(c): Level-5 carrier — specialized index-2 elliptic law and covering formula. -/
theorem stmt6_c (Q U : ℂ) (ϑη : ℂ) (ϑ₁ : ℂ → ℂ → ℂ) (qpoch : ℂ)
    (Jprod Jprodd : ℂ → ℂ) (z : ℂ) (hm : m = 2)
    (hx1 : (x : ℂ) = 1) (hω : IsPrimitiveRoot ω 5)
    (hQ0 : Q ≠ 0) (hU0 : U ≠ 0)
    (hQ : Q^24 = qC τ) (hU : U^2 = elvC z)
    (hη : ϑη = Q * qpoch)
    (hϑ₁_tp : ϑ₁ τ z = Complex.I * Q^3 * U^(-1 : ℤ) * Jprod (elvC z))
    (hϑ₁_tpd : ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z)
      = Complex.I * Q^(3*(d m : ℤ)) * U^(-(d m : ℤ)) * Jprodd (elvC z))
    (hϑ₁_per1 : ϑ₁ τ (z + 1) = - ϑ₁ τ z)
    (hϑ₁_perτ : ϑ₁ τ (z + τ) = - Q^(-12 : ℤ) * U^(-2 : ℤ) * ϑ₁ τ z)
    (hϑ₁_dper1 : ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z + (d m : ℂ)) = - ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z))
    (hϑ₁_dperτ : ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z + (d m : ℂ)*τ)
      = - Q^(-12*(d m : ℤ)) * U^(-2*(d m : ℤ)) * ϑ₁ ((d m : ℂ)*τ) ((d m : ℂ)*z)) :
    (𝓙 m τ ϑη ϑ₁ (z + 1) = 𝓙 m τ ϑη ϑ₁ z)
    ∧ (𝓙 m τ ϑη ϑ₁ (z + τ) = (qC τ)^(-2 : ℤ) * (elvC z)^(-4 : ℤ) * 𝓙 m τ ϑη ϑ₁ z)
    ∧ (𝓙 m τ ϑη ϑ₁ z = Q^6 * qpoch^(-6 : ℤ) * U^(-4 : ℤ) * (Jprod (elvC z))^9 / Jprodd (elvC z))
    ∧ (24 * 5^2 = 600) := by
  -- SANITY CHECK PASSED (specialization of stmt5_ii and stmt5_i at m=2 plus
  -- arithmetic).
  -- STRATEGY: `refine ⟨?_, ?_, ?_, ?_⟩`.
  --  • Parts 1,2 (z+1 and z+τ laws): apply stmt5_ii m τ ω Q U ϑη ϑ₁ z with the
  --    quasi-periodicity hyps.  stmt5_ii needs `hm : 2 ≤ m`; here hm : m = 2 so
  --    `have hm' : 2 ≤ m := by omega`.  stmt5_ii's z+τ multiplier is
  --    (qC)^-m·(elvC z)^-2m; with m=2 (rw hm / simp) that is (qC)^-2·(elvC z)^-4,
  --    matching part 2's exponents.  Extract .1 and .2 of the stmt5_ii conjunction.
  --  • Part 3 (covering formula): apply stmt5_i m τ Q U ϑη ϑ₁ qpoch Jprod Jprodd z
  --    with hm', hQ0,hU0,hQ,hU,hη,hϑ₁_tp,hϑ₁_tpd.  stmt5_i gives
  --    𝓙 = Q^(2(m+1))·qpoch^(2-4m)·U^-2m·(Jprod)^(4m+1)/Jprodd; substitute m=2
  --    (rw hm; norm_num): 2(m+1)=6, 2-4m=-6, -2m=-4, 4m+1=9.  Matches part 3.
  --  • Part 4: `24 * 5^2 = 600` by `norm_num` (or `decide`).
  subst hm
  have hm' : 2 ≤ 2 := le_refl 2
  obtain ⟨h1, h2⟩ := stmt5_ii 2 τ Q U ϑη ϑ₁ z hm'
    hϑ₁_per1 hϑ₁_perτ hϑ₁_dper1 hϑ₁_dperτ hQ hU hQ0 hU0
  have h3 := stmt5_i 2 τ Q U ϑη ϑ₁ qpoch Jprod Jprodd z hm'
    hQ0 hU0 hQ hU hη hϑ₁_tp hϑ₁_tpd
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h2]; norm_num
  · rw [h3]
    norm_num
    rfl
  · norm_num

end HigherDyson
