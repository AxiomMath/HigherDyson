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
  sorry

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
  sorry

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
  sorry

end AppellKernelShift
