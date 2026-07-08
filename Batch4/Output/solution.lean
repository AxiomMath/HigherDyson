import Mathlib

/-
# Problem Description

We work over the complex numbers `ℂ`. Fix the following global data (carried everywhere):

- an integer `m : ℕ` with `2 ≤ m`, and `d := 2*m + 1`;
- a unit `x : ℂˣ` (so `x ≠ 0`);
- a function `elv : ℂ → ℂˣ` sending each `w : ℂ` to a unit `elv w` (the elliptic
  variable, written `u := elv w`, with `u = e^{2πi w}`);
- a nonzero scalar `q : ℂ`, `q ≠ 0` (the nome), with a complex number `τ` (the period);
- a unit `ω : ℂˣ` (a `d`-th root of unity in the paper; only its unit status is used);
- an *opaque* function `Pd : ℂˣ → ℂ` (the normalizing product `P_d(·;q)`).

Throughout, for a base `z : ℂˣ` and an integer exponent `k : ℤ`, the power `z^k` is the
integer (zpow) power. Coercions `(y : ℂ)` of a unit `y : ℂˣ` to `ℂ` are the canonical ones.

## Main Definition(s)

Definition 1 (three correction kernels as honest series), defined as `tsum` over `n : ℕ`:

- `B w := ∑' n, x^(-(2*n)-2) * q^(m*n^2) * (elv w)^(2*m*n) * Pd (q^n * elv w)`
- `Ar r w := ∑' n, x^(-(2*n)-2) * q^(m*n^2+n) * (elv w)^(2*m*n+1)
                     * Pd (q^n * elv w) / (1 - ω^r * q^n * elv w)`
- `Aext w := ∑' n, x^(-(2*n)-2) * q^(m*n^2+n) * (elv w)^(2*m*n+1)
                     * Pd (q^n * elv w) / (1 - x * q^n * elv w)`

The argument `q^n * elv w` fed to `Pd` is regarded as a unit in `ℂˣ` (built from the units
`q` (via `q ≠ 0`), and `elv w`). The exponents on `x` are `ℤ`-valued (may be negative); the
exponents on `q` and on `elv w` inside the summand are `ℕ`-valued.

Definition 2 (designated hypotheses): see the `variable`s and hypotheses of each theorem.

## Main Statement(s)

Three normalized kernel `τ`-shift laws (Prop. 4.5, "Appell-kernel τ-shift laws").
-/

namespace AppellKernelShift

/- We record the unit `qᵤ : ℂˣ` corresponding to the nonzero scalar `q`, so that the
argument `q^n * elv w` to `Pd` is an honest unit. -/

variable (m : ℕ)

/-- `d := 2*m + 1`. -/
def d (m : ℕ) : ℕ := 2 * m + 1

section Setup

variable (x : ℂˣ) (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (τ : ℂ) (ω : ℂˣ) (Pd : ℂˣ → ℂ)

/-- The nonzero scalar `q` regarded as a unit of `ℂ`. -/
noncomputable def qUnit (q : ℂ) (hq : q ≠ 0) : ℂˣ := Units.mk0 q hq

/-- The unit argument `q^n * elv w ∈ ℂˣ` fed to `Pd`. -/
noncomputable def parg (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (n : ℕ) (w : ℂ) : ℂˣ :=
  (qUnit q hq) ^ n * elv w

/-- The `B`-kernel `B : ℂ → ℂ`. -/
noncomputable def B (x : ℂˣ) (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (Pd : ℂˣ → ℂ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2)
    * (elv w : ℂ) ^ (2 * m * n) * Pd (parg elv q hq n w)

/-- The `Ar`-kernels `Ar : ℕ → ℂ → ℂ`, one for each residue index `r`. -/
noncomputable def Ar (x : ℂˣ) (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (ω : ℂˣ) (Pd : ℂˣ → ℂ)
    (r : ℕ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
    * (elv w : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n w)
      / (1 - (ω : ℂ) ^ r * q ^ n * (elv w : ℂ))

/-- The extended kernel `Aext : ℂ → ℂ`. -/
noncomputable def Aext (x : ℂˣ) (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (Pd : ℂˣ → ℂ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
    * (elv w : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n w)
      / (1 - (x : ℂ) * q ^ n * (elv w : ℂ))

end Setup

/-!
## Designated hypotheses (Definition 2)

The three theorems take exactly:
- `helvτ : ∀ w, elv (w + τ) = q * elv w` (as an equation of units, with `q` the unit `qUnit`);
- `hPshift`, the `q`-shift law of the opaque `Pd`;
- absolute summability of the defining summands and of the shifted (index `n ↦ n+1`) summands;
- pole-avoidance hypotheses.
-/

/-- **Theorem 1 (`thm_Bshift`).** -/
theorem thm_Bshift
    (m : ℕ) (hm : 2 ≤ m) (x : ℂˣ) (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (τ : ℂ)
    (ω : ℂˣ) (Pd : ℂˣ → ℂ)
    (helvτ : ∀ w, elv (w + τ) = qUnit q hq * elv w)
    (hPshift : ∀ u : ℂˣ, Pd (qUnit q hq * u)
      = q ^ (-(m : ℤ) - 1) * (u : ℂ) ^ (-2 : ℤ) * (1 - (u : ℂ))
        / (1 - (u : ℂ) ^ (d m)) * Pd u)
    (hSummB : ∀ w, Summable (fun n : ℕ =>
      ‖(x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2)
        * (elv w : ℂ) ^ (2 * m * n) * Pd (parg elv q hq n w)‖))
    (hSummBshift : ∀ w, Summable (fun n : ℕ =>
      ‖(x : ℂ) ^ (-(2 * ((n : ℤ) + 1)) - 2) * q ^ (m * (n + 1) ^ 2)
        * (elv w : ℂ) ^ (2 * m * (n + 1)) * Pd (parg elv q hq (n + 1) w)‖)) :
    ∀ w, B m x elv q hq Pd (w + τ)
      = (x : ℂ) ^ 2 * q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ))) * B m x elv q hq Pd w
        - q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ))) * Pd (elv w) := by
  intro w
  have hxne : (x : ℂ) ≠ 0 := x.ne_zero
  have hune : (elv w : ℂ) ≠ 0 := (elv w).ne_zero
  -- the summand of `B w`
  set c : ℕ → ℂ := fun n => (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2)
    * (elv w : ℂ) ^ (2 * m * n) * Pd (parg elv q hq n w) with hc
  -- key: parg at `w+τ`, index `n`, equals parg at `w`, index `n+1`.
  have hparg : ∀ n : ℕ, parg elv q hq n (w + τ) = parg elv q hq (n + 1) w := by
    intro n
    simp only [parg, helvτ w, pow_succ]
    rw [mul_assoc]
  have hev : (elv (w + τ) : ℂ) = q * (elv w : ℂ) := by
    rw [helvτ w]; simp [qUnit]
  -- The scaling factor.
  set A : ℂ := (x : ℂ) ^ 2 * q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ))) with hA
  -- pointwise: summand of `B (w+τ)` at n equals `A * c (n+1)`.
  have hpt : ∀ n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2)
      * (elv (w + τ) : ℂ) ^ (2 * m * n) * Pd (parg elv q hq n (w + τ))
      = A * c (n + 1) := by
    intro n
    rw [hparg n, hev, hA, hc]
    simp only []
    -- Convert every nat-power to a zpow with integer exponent.
    rw [mul_pow,
        show (q ^ (m * n ^ 2) : ℂ) = q ^ ((m * n ^ 2 : ℕ) : ℤ) by rw [zpow_natCast],
        show (q ^ (2 * m * n) : ℂ) = q ^ ((2 * m * n : ℕ) : ℤ) by rw [zpow_natCast],
        show ((elv w : ℂ) ^ (2 * m * n)) = (elv w : ℂ) ^ ((2 * m * n : ℕ) : ℤ) by rw [zpow_natCast],
        show ((x : ℂ) ^ 2) = (x : ℂ) ^ (2 : ℤ) by rw [zpow_two, sq],
        show (q ^ (m * (n + 1) ^ 2) : ℂ) = q ^ ((m * (n + 1) ^ 2 : ℕ) : ℤ) by rw [zpow_natCast],
        show ((elv w : ℂ) ^ (2 * m * (n + 1))) = (elv w : ℂ) ^ ((2 * m * (n + 1) : ℕ) : ℤ) by
          rw [zpow_natCast]]
    -- combine zpows on the RHS
    rw [show (x : ℂ) ^ (2:ℤ) * q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ)))
          * ((x:ℂ)^(-(2*(((n:ℕ)+1 :ℕ):ℤ)) - 2) * q ^ ((m * (n + 1) ^ 2 : ℕ) : ℤ)
             * (elv w : ℂ)^((2 * m * (n + 1) : ℕ) : ℤ) * Pd (parg elv q hq (n + 1) w))
        = ((x:ℂ)^(2:ℤ) * (x:ℂ)^(-(2*(((n:ℕ)+1 :ℕ):ℤ)) - 2))
          * (q ^ (-(m:ℤ)) * q ^ ((m * (n + 1) ^ 2 : ℕ) : ℤ))
          * ((elv w : ℂ) ^ (-(2 * (m:ℤ))) * (elv w : ℂ)^((2 * m * (n + 1) : ℕ) : ℤ))
          * Pd (parg elv q hq (n + 1) w) by ring]
    rw [← zpow_add₀ hxne, ← zpow_add₀ hq, ← zpow_add₀ hune]
    -- combine zpows on the LHS
    rw [show (x : ℂ) ^ (-(2 * (n:ℤ)) - 2) * q ^ ((m * n ^ 2 : ℕ):ℤ)
          * (q ^ ((2 * m * n : ℕ):ℤ) * (elv w : ℂ) ^ ((2 * m * n : ℕ):ℤ))
          * Pd (parg elv q hq (n + 1) w)
        = (x : ℂ) ^ (-(2 * (n:ℤ)) - 2)
          * (q ^ ((m * n ^ 2 : ℕ):ℤ) * q ^ ((2 * m * n : ℕ):ℤ))
          * (elv w : ℂ) ^ ((2 * m * n : ℕ):ℤ)
          * Pd (parg elv q hq (n + 1) w) by ring]
    rw [← zpow_add₀ hq]
    -- now match exponents
    rw [show (-(2 * (n:ℤ)) - 2) = (2:ℤ) + (-(2*(((n:ℕ)+1 :ℕ):ℤ)) - 2) by push_cast; ring,
        show ((m * n ^ 2 : ℕ):ℤ) + ((2 * m * n : ℕ):ℤ)
          = -(m:ℤ) + ((m * (n + 1) ^ 2 : ℕ) : ℤ) by push_cast; ring,
        show ((2 * m * n : ℕ):ℤ) = -(2 * (m:ℤ)) + ((2 * m * (n + 1) : ℕ) : ℤ) by push_cast; ring]
  -- Now sum.
  have hBwτ : B m x elv q hq Pd (w + τ) = ∑' n : ℕ, A * c (n + 1) := by
    rw [B]
    exact tsum_congr hpt
  have hsummShift : Summable (fun n : ℕ => c (n + 1)) := by
    apply Summable.of_norm
    apply (hSummBshift w).congr
    intro n
    rw [hc]
    simp only []
    push_cast
    ring_nf
  rw [hBwτ, tsum_mul_left]
  have hsplit : ∑' n : ℕ, c n = c 0 + ∑' n : ℕ, c (n + 1) :=
    tsum_eq_zero_add' hsummShift
  have hBw : B m x elv q hq Pd w = ∑' n : ℕ, c n := by rw [B]
  have hshift : (∑' n : ℕ, c (n + 1)) = B m x elv q hq Pd w - c 0 := by
    rw [hBw, hsplit]; ring
  rw [hshift]
  -- c 0
  have hc0 : c 0 = (x : ℂ) ^ (-2 : ℤ) * Pd (elv w) := by
    rw [hc]
    simp only [Nat.cast_zero, mul_zero, pow_zero, mul_one]
    rw [show parg elv q hq 0 w = elv w by simp [parg]]
    norm_num
  rw [hc0, hA]
  -- final algebra
  have hxsq : (x : ℂ) ^ 2 * (x : ℂ) ^ (-2 : ℤ) = 1 := by
    rw [show ((x:ℂ)^2) = (x:ℂ)^(2:ℤ) by rw [zpow_two, sq], ← zpow_add₀ hxne]
    norm_num
  have expand : ((x : ℂ) ^ 2 * q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ))))
      * ((x:ℂ)^(-2:ℤ) * Pd (elv w))
      = q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ))) * Pd (elv w) := by
    calc ((x : ℂ) ^ 2 * q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ))))
          * ((x:ℂ)^(-2:ℤ) * Pd (elv w))
        = ((x : ℂ) ^ 2 * (x:ℂ)^(-2:ℤ)) * (q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ))) * Pd (elv w)) := by ring
      _ = q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ))) * Pd (elv w) := by rw [hxsq, one_mul]
  rw [mul_sub, expand]

/-- **Theorem 2 (`thm_Arshift`).** -/
theorem thm_Arshift
    (m : ℕ) (hm : 2 ≤ m) (x : ℂˣ) (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (τ : ℂ)
    (ω : ℂˣ) (Pd : ℂˣ → ℂ)
    (helvτ : ∀ w, elv (w + τ) = qUnit q hq * elv w)
    (hPshift : ∀ u : ℂˣ, Pd (qUnit q hq * u)
      = q ^ (-(m : ℤ) - 1) * (u : ℂ) ^ (-2 : ℤ) * (1 - (u : ℂ))
        / (1 - (u : ℂ) ^ (d m)) * Pd u)
    (hSummAr : ∀ (r : ℕ) (w : ℂ), Summable (fun n : ℕ =>
      ‖(x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
        * (elv w : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n w)
          / (1 - (ω : ℂ) ^ r * q ^ n * (elv w : ℂ))‖))
    (hSummArshift : ∀ (r : ℕ) (w : ℂ), Summable (fun n : ℕ =>
      ‖(x : ℂ) ^ (-(2 * ((n : ℤ) + 1)) - 2) * q ^ (m * (n + 1) ^ 2 + (n + 1))
        * (elv w : ℂ) ^ (2 * m * (n + 1) + 1) * Pd (parg elv q hq (n + 1) w)
          / (1 - (ω : ℂ) ^ r * q ^ (n + 1) * (elv w : ℂ))‖))
    (hPoleAr : ∀ (r : ℕ) (n : ℕ) (w : ℂ), 1 - (ω : ℂ) ^ r * q ^ n * (elv w : ℂ) ≠ 0) :
    ∀ w, ∀ r < d m, Ar m x elv q hq ω Pd r (w + τ)
      = (x : ℂ) ^ 2 * q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ)))
          * Ar m x elv q hq ω Pd r w
        - q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ))) * (elv w : ℂ) * Pd (elv w)
          / (1 - (ω : ℂ) ^ r * (elv w : ℂ)) := by
  intro w r _
  have hxne : (x : ℂ) ≠ 0 := x.ne_zero
  have hune : (elv w : ℂ) ≠ 0 := (elv w).ne_zero
  set a : ℕ → ℂ := fun n => (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
    * (elv w : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n w)
      / (1 - (ω : ℂ) ^ r * q ^ n * (elv w : ℂ)) with ha
  have hparg : ∀ n : ℕ, parg elv q hq n (w + τ) = parg elv q hq (n + 1) w := by
    intro n
    simp only [parg, helvτ w, pow_succ]
    rw [mul_assoc]
  have hev : (elv (w + τ) : ℂ) = q * (elv w : ℂ) := by
    rw [helvτ w]; simp [qUnit]
  set A : ℂ := (x : ℂ) ^ 2 * q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ))) with hA
  -- denominators match
  have hden : ∀ n : ℕ, (1 - (ω : ℂ) ^ r * q ^ n * (elv (w + τ) : ℂ))
      = (1 - (ω : ℂ) ^ r * q ^ (n + 1) * (elv w : ℂ)) := by
    intro n
    rw [hev, pow_succ]; ring
  -- numerators scale by A
  have hnum : ∀ n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
      * (elv (w + τ) : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n (w + τ))
      = A * ((x : ℂ) ^ (-(2 * ((n : ℤ) + 1)) - 2) * q ^ (m * (n + 1) ^ 2 + (n + 1))
        * (elv w : ℂ) ^ (2 * m * (n + 1) + 1) * Pd (parg elv q hq (n + 1) w)) := by
    intro n
    rw [hparg n, hev, hA]
    rw [mul_pow,
        show (q ^ (m * n ^ 2 + n) : ℂ) = q ^ ((m * n ^ 2 + n : ℕ) : ℤ) by rw [zpow_natCast],
        show (q ^ (2 * m * n + 1) : ℂ) = q ^ ((2 * m * n + 1 : ℕ) : ℤ) by rw [zpow_natCast],
        show ((elv w : ℂ) ^ (2 * m * n + 1)) = (elv w : ℂ) ^ ((2 * m * n + 1 : ℕ) : ℤ) by
          rw [zpow_natCast],
        show ((x : ℂ) ^ 2) = (x : ℂ) ^ (2 : ℤ) by rw [zpow_two, sq],
        show (q ^ (m * (n + 1) ^ 2 + (n + 1)) : ℂ) = q ^ ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ) by
          rw [zpow_natCast],
        show ((elv w : ℂ) ^ (2 * m * (n + 1) + 1)) = (elv w : ℂ) ^ ((2 * m * (n + 1) + 1 : ℕ) : ℤ) by
          rw [zpow_natCast]]
    rw [show (x : ℂ) ^ (2:ℤ) * q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ)))
          * ((x:ℂ)^(-(2*(((n:ℤ)+1)) ) - 2) * q ^ ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ)
             * (elv w : ℂ)^((2 * m * (n + 1) + 1 : ℕ) : ℤ) * Pd (parg elv q hq (n + 1) w))
        = ((x:ℂ)^(2:ℤ) * (x:ℂ)^(-(2*(((n:ℤ)+1)) ) - 2))
          * (q ^ (-(m:ℤ)) * q ^ ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ))
          * ((elv w : ℂ) ^ (-(2 * (m:ℤ))) * (elv w : ℂ)^((2 * m * (n + 1) + 1 : ℕ) : ℤ))
          * Pd (parg elv q hq (n + 1) w) by ring]
    rw [← zpow_add₀ hxne, ← zpow_add₀ hq, ← zpow_add₀ hune]
    rw [show (x : ℂ) ^ (-(2 * (n:ℤ)) - 2) * q ^ ((m * n ^ 2 + n : ℕ):ℤ)
          * (q ^ ((2 * m * n + 1 : ℕ):ℤ) * (elv w : ℂ) ^ ((2 * m * n + 1 : ℕ):ℤ))
          * Pd (parg elv q hq (n + 1) w)
        = (x : ℂ) ^ (-(2 * (n:ℤ)) - 2)
          * (q ^ ((m * n ^ 2 + n : ℕ):ℤ) * q ^ ((2 * m * n + 1 : ℕ):ℤ))
          * (elv w : ℂ) ^ ((2 * m * n + 1 : ℕ):ℤ)
          * Pd (parg elv q hq (n + 1) w) by ring]
    rw [← zpow_add₀ hq]
    rw [show (-(2 * (n:ℤ)) - 2) = (2:ℤ) + (-(2*((n:ℤ)+1)) - 2) by ring,
        show ((m * n ^ 2 + n : ℕ):ℤ) + ((2 * m * n + 1 : ℕ):ℤ)
          = -(m:ℤ) + ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ) by push_cast; ring,
        show ((2 * m * n + 1 : ℕ):ℤ) = -(2 * (m:ℤ)) + ((2 * m * (n + 1) + 1 : ℕ) : ℤ) by
          push_cast; ring]
  -- pointwise summand identity
  have hpt : ∀ n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
      * (elv (w + τ) : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n (w + τ))
        / (1 - (ω : ℂ) ^ r * q ^ n * (elv (w + τ) : ℂ))
      = A * a (n + 1) := by
    intro n
    rw [ha]
    simp only []
    rw [hden n, hnum n, mul_div_assoc]
    push_cast
    ring_nf
  have hArwτ : Ar m x elv q hq ω Pd r (w + τ) = ∑' n : ℕ, A * a (n + 1) := by
    rw [Ar]
    exact tsum_congr hpt
  have hsummShift : Summable (fun n : ℕ => a (n + 1)) := by
    apply Summable.of_norm
    apply (hSummArshift r w).congr
    intro n
    rw [ha]
    simp only []
    push_cast
    ring_nf
  rw [hArwτ, tsum_mul_left]
  have hsplit : ∑' n : ℕ, a n = a 0 + ∑' n : ℕ, a (n + 1) :=
    tsum_eq_zero_add' hsummShift
  have hArw : Ar m x elv q hq ω Pd r w = ∑' n : ℕ, a n := by rw [Ar]
  have hshift : (∑' n : ℕ, a (n + 1)) = Ar m x elv q hq ω Pd r w - a 0 := by
    rw [hArw, hsplit]; ring
  rw [hshift]
  have ha0 : a 0 = (x : ℂ) ^ (-2 : ℤ) * (elv w : ℂ) * Pd (elv w) / (1 - (ω : ℂ) ^ r * (elv w : ℂ)) := by
    rw [ha]
    simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, mul_one, pow_one]
    rw [show parg elv q hq 0 w = elv w by simp [parg]]
    norm_num
  rw [ha0, hA]
  have hxsq : (x : ℂ) ^ 2 * (x : ℂ) ^ (-2 : ℤ) = 1 := by
    rw [show ((x:ℂ)^2) = (x:ℂ)^(2:ℤ) by rw [zpow_two, sq], ← zpow_add₀ hxne]
    norm_num
  rw [mul_sub]
  congr 1
  rw [mul_div_assoc']
  rw [show (x : ℂ) ^ 2 * q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ)))
        * ((x:ℂ)^(-2:ℤ) * (elv w : ℂ) * Pd (elv w))
      = ((x:ℂ)^2 * (x:ℂ)^(-2:ℤ)) * (q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ)))
        * (elv w : ℂ) * Pd (elv w)) by ring]
  rw [hxsq, one_mul]

/-- **Theorem 3 (`thm_Aextshift`).** -/
theorem thm_Aextshift
    (m : ℕ) (hm : 2 ≤ m) (x : ℂˣ) (elv : ℂ → ℂˣ) (q : ℂ) (hq : q ≠ 0) (τ : ℂ)
    (ω : ℂˣ) (Pd : ℂˣ → ℂ)
    (helvτ : ∀ w, elv (w + τ) = qUnit q hq * elv w)
    (hPshift : ∀ u : ℂˣ, Pd (qUnit q hq * u)
      = q ^ (-(m : ℤ) - 1) * (u : ℂ) ^ (-2 : ℤ) * (1 - (u : ℂ))
        / (1 - (u : ℂ) ^ (d m)) * Pd u)
    (hSummAext : ∀ w, Summable (fun n : ℕ =>
      ‖(x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
        * (elv w : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n w)
          / (1 - (x : ℂ) * q ^ n * (elv w : ℂ))‖))
    (hSummAextshift : ∀ w, Summable (fun n : ℕ =>
      ‖(x : ℂ) ^ (-(2 * ((n : ℤ) + 1)) - 2) * q ^ (m * (n + 1) ^ 2 + (n + 1))
        * (elv w : ℂ) ^ (2 * m * (n + 1) + 1) * Pd (parg elv q hq (n + 1) w)
          / (1 - (x : ℂ) * q ^ (n + 1) * (elv w : ℂ))‖))
    (hPoleAext : ∀ (n : ℕ) (w : ℂ), 1 - (x : ℂ) * q ^ n * (elv w : ℂ) ≠ 0) :
    ∀ w, Aext m x elv q hq Pd (w + τ)
      = (x : ℂ) ^ 2 * q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ)))
          * Aext m x elv q hq Pd w
        - q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ))) * (elv w : ℂ) * Pd (elv w)
          / (1 - (x : ℂ) * (elv w : ℂ)) := by
  intro w
  have hxne : (x : ℂ) ≠ 0 := x.ne_zero
  have hune : (elv w : ℂ) ≠ 0 := (elv w).ne_zero
  set a : ℕ → ℂ := fun n => (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
    * (elv w : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n w)
      / (1 - (x : ℂ) * q ^ n * (elv w : ℂ)) with ha
  have hparg : ∀ n : ℕ, parg elv q hq n (w + τ) = parg elv q hq (n + 1) w := by
    intro n
    simp only [parg, helvτ w, pow_succ]
    rw [mul_assoc]
  have hev : (elv (w + τ) : ℂ) = q * (elv w : ℂ) := by
    rw [helvτ w]; simp [qUnit]
  set A : ℂ := (x : ℂ) ^ 2 * q ^ (-(m : ℤ)) * (elv w : ℂ) ^ (-(2 * (m : ℤ))) with hA
  have hden : ∀ n : ℕ, (1 - (x : ℂ) * q ^ n * (elv (w + τ) : ℂ))
      = (1 - (x : ℂ) * q ^ (n + 1) * (elv w : ℂ)) := by
    intro n
    rw [hev, pow_succ]; ring
  have hnum : ∀ n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
      * (elv (w + τ) : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n (w + τ))
      = A * ((x : ℂ) ^ (-(2 * ((n : ℤ) + 1)) - 2) * q ^ (m * (n + 1) ^ 2 + (n + 1))
        * (elv w : ℂ) ^ (2 * m * (n + 1) + 1) * Pd (parg elv q hq (n + 1) w)) := by
    intro n
    rw [hparg n, hev, hA]
    rw [mul_pow,
        show (q ^ (m * n ^ 2 + n) : ℂ) = q ^ ((m * n ^ 2 + n : ℕ) : ℤ) by rw [zpow_natCast],
        show (q ^ (2 * m * n + 1) : ℂ) = q ^ ((2 * m * n + 1 : ℕ) : ℤ) by rw [zpow_natCast],
        show ((elv w : ℂ) ^ (2 * m * n + 1)) = (elv w : ℂ) ^ ((2 * m * n + 1 : ℕ) : ℤ) by
          rw [zpow_natCast],
        show ((x : ℂ) ^ 2) = (x : ℂ) ^ (2 : ℤ) by rw [zpow_two, sq],
        show (q ^ (m * (n + 1) ^ 2 + (n + 1)) : ℂ) = q ^ ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ) by
          rw [zpow_natCast],
        show ((elv w : ℂ) ^ (2 * m * (n + 1) + 1)) = (elv w : ℂ) ^ ((2 * m * (n + 1) + 1 : ℕ) : ℤ) by
          rw [zpow_natCast]]
    rw [show (x : ℂ) ^ (2:ℤ) * q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ)))
          * ((x:ℂ)^(-(2*(((n:ℤ)+1)) ) - 2) * q ^ ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ)
             * (elv w : ℂ)^((2 * m * (n + 1) + 1 : ℕ) : ℤ) * Pd (parg elv q hq (n + 1) w))
        = ((x:ℂ)^(2:ℤ) * (x:ℂ)^(-(2*(((n:ℤ)+1)) ) - 2))
          * (q ^ (-(m:ℤ)) * q ^ ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ))
          * ((elv w : ℂ) ^ (-(2 * (m:ℤ))) * (elv w : ℂ)^((2 * m * (n + 1) + 1 : ℕ) : ℤ))
          * Pd (parg elv q hq (n + 1) w) by ring]
    rw [← zpow_add₀ hxne, ← zpow_add₀ hq, ← zpow_add₀ hune]
    rw [show (x : ℂ) ^ (-(2 * (n:ℤ)) - 2) * q ^ ((m * n ^ 2 + n : ℕ):ℤ)
          * (q ^ ((2 * m * n + 1 : ℕ):ℤ) * (elv w : ℂ) ^ ((2 * m * n + 1 : ℕ):ℤ))
          * Pd (parg elv q hq (n + 1) w)
        = (x : ℂ) ^ (-(2 * (n:ℤ)) - 2)
          * (q ^ ((m * n ^ 2 + n : ℕ):ℤ) * q ^ ((2 * m * n + 1 : ℕ):ℤ))
          * (elv w : ℂ) ^ ((2 * m * n + 1 : ℕ):ℤ)
          * Pd (parg elv q hq (n + 1) w) by ring]
    rw [← zpow_add₀ hq]
    rw [show (-(2 * (n:ℤ)) - 2) = (2:ℤ) + (-(2*((n:ℤ)+1)) - 2) by ring,
        show ((m * n ^ 2 + n : ℕ):ℤ) + ((2 * m * n + 1 : ℕ):ℤ)
          = -(m:ℤ) + ((m * (n + 1) ^ 2 + (n + 1) : ℕ) : ℤ) by push_cast; ring,
        show ((2 * m * n + 1 : ℕ):ℤ) = -(2 * (m:ℤ)) + ((2 * m * (n + 1) + 1 : ℕ) : ℤ) by
          push_cast; ring]
  have hpt : ∀ n : ℕ, (x : ℂ) ^ (-(2 * (n : ℤ)) - 2) * q ^ (m * n ^ 2 + n)
      * (elv (w + τ) : ℂ) ^ (2 * m * n + 1) * Pd (parg elv q hq n (w + τ))
        / (1 - (x : ℂ) * q ^ n * (elv (w + τ) : ℂ))
      = A * a (n + 1) := by
    intro n
    rw [ha]
    simp only []
    rw [hden n, hnum n, mul_div_assoc]
    push_cast
    ring_nf
  have hAextwτ : Aext m x elv q hq Pd (w + τ) = ∑' n : ℕ, A * a (n + 1) := by
    rw [Aext]
    exact tsum_congr hpt
  have hsummShift : Summable (fun n : ℕ => a (n + 1)) := by
    apply Summable.of_norm
    apply (hSummAextshift w).congr
    intro n
    rw [ha]
    simp only []
    push_cast
    ring_nf
  rw [hAextwτ, tsum_mul_left]
  have hsplit : ∑' n : ℕ, a n = a 0 + ∑' n : ℕ, a (n + 1) :=
    tsum_eq_zero_add' hsummShift
  have hAextw : Aext m x elv q hq Pd w = ∑' n : ℕ, a n := by rw [Aext]
  have hshift : (∑' n : ℕ, a (n + 1)) = Aext m x elv q hq Pd w - a 0 := by
    rw [hAextw, hsplit]; ring
  rw [hshift]
  have ha0 : a 0 = (x : ℂ) ^ (-2 : ℤ) * (elv w : ℂ) * Pd (elv w) / (1 - (x : ℂ) * (elv w : ℂ)) := by
    rw [ha]
    simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, mul_one, pow_one]
    rw [show parg elv q hq 0 w = elv w by simp [parg]]
    norm_num
  rw [ha0, hA]
  have hxsq : (x : ℂ) ^ 2 * (x : ℂ) ^ (-2 : ℤ) = 1 := by
    rw [show ((x:ℂ)^2) = (x:ℂ)^(2:ℤ) by rw [zpow_two, sq], ← zpow_add₀ hxne]
    norm_num
  rw [mul_sub]
  congr 1
  rw [mul_div_assoc']
  rw [show (x : ℂ) ^ 2 * q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ)))
        * ((x:ℂ)^(-2:ℤ) * (elv w : ℂ) * Pd (elv w))
      = ((x:ℂ)^2 * (x:ℂ)^(-2:ℤ)) * (q ^ (-(m:ℤ)) * (elv w : ℂ) ^ (-(2 * (m:ℤ)))
        * (elv w : ℂ) * Pd (elv w)) by ring]
  rw [hxsq, one_mul]

end AppellKernelShift
