
Please read the file `KeyFormulasDyson.tex` and `AxiomDysonSystems.tex`.

This is Batch 3, the last open batch (Batches 1, 2, 4 are accepted). Formalize and prove ONLY:
Key Formula~\ref{KF:Pshift}, Key Formula~\ref{KF:appellshift}, Key Formula~\ref{KF:corrected},
Key Formula~\ref{KF:untwist}, Key Formula~\ref{KF:carrier}, and Key Formula~\ref{KF:level5}.

## STRUCTURAL MODEL (final — this fixes the inconsistency that sank the last run)

The previous task was internally inconsistent: it demanded `w+1`-periodicity and `w+λ`
untwisting as conclusions about opaque functions of `w`, while banning every hypothesis from
which such facts could follow. For an opaque `f : ℂ → ℂ`, `f(w+1) = f(w)` is underivable from
anything. The fix is structural, and it is FAITHFUL — both pieces are the source's own
definitions, not modeling inventions:

**(S1) The elliptic variable is CONCRETE.** The paper defines `u = e^{2πiw}` and `q = e^{2πiτ}`
verbatim. So define:
```
def elvC (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)
def qC          : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ)     -- τ a parameter
```
with `elvC w ≠ 0` and `qC ≠ 0` by `Complex.exp_ne_zero` (bundle to `ℂˣ` via `Units.mk0` where
a `ℂˣ` is needed). The three translation facts are now THEOREMS, to be proved as named lemmas
(locate exact Mathlib names with `exact?`/`loogle` — candidates `Complex.exp_add`,
`Complex.exp_int_mul_two_pi_mul_I` / `Complex.exp_two_pi_mul_I`; do NOT trust remembered names):
```
lem_elv_tau  : elvC (w + τ) = qC * elvC w                    -- from exp_add
lem_elv_one  : elvC (w + 1) = elvC w                          -- from exp(2πi) = 1
lem_elv_lam  : elvC (w + λ) = Complex.exp (2*π*I*λ) * elvC w  -- from exp_add
```
These REPLACE the former hypotheses `helvτ`/`helv1per` (now derived, not designated) and make
the formerly-banned-and-needed λ-translation available legitimately.

**(S2) Kernels and assembled objects FACTOR THROUGH the elliptic variable.** The accepted
Batch 4 defines `B, Ar, Aext` as sums whose terms depend on `w` only via `elv w`; the paper's
`Φ, 𝓗` are likewise functions of `(τ, u)`. So declare opaque `u`-level symbols and compose:
```
Bu Aextu Φu 𝓗u : ℂ → ℂ        Aru : ℕ → ℂ → ℂ        (opaque)
B    w := Bu   (elvC w)         Ar r w := Aru r (elvC w)
Aext w := Aextu (elvC w)        Φ w    := Φu (elvC w)         𝓗 w := 𝓗u (elvC w)
```
Consequently `w+1`-periodicity of every assembled object is a THEOREM (via `lem_elv_one`), and
the untwist reduces to `lem_elv_lam` + the scalar identity. The former bans on
`hBper/hArper/hAextper/helvLam/htwistLam` REMAIN as hypothesis-bans — those facts are now
lemmas you must DERIVE, never assume.

**Seam with the accepted Batch 4 (by instantiation).** Batch 4's `thm_Bshift`/`thm_Arshift`/
`thm_Aextshift` are parametric in `elv, q` with hypothesis `helvτ`. Instantiate
`elv := Units.mk0 ∘ elvC`, `q := qC`, discharge `helvτ` by `lem_elv_tau`: the results are
exactly this batch's designated inputs `hBshift/hArshift/hAextshift` below. State those inputs
in the SAME form as Batch 4's theorems (same prefactor `x² q^{-m} u^{-2m}`, same defect terms,
same `∀ r < d` quantification), with `u = elvC w`.

## Designated inputs (closed list — the ONLY permitted hypotheses)

- `hBshift, hArshift, hAextshift` : the three kernel `τ`-shift laws, displayed in full —
  these are EXACTLY the accepted Batch 4's `thm_Bshift/thm_Arshift/thm_Aextshift`
  instantiated at `elv := Units.mk0 ∘ elvC`, `q := qC` (so `(elv w : ℂ)` becomes `elvC w`):
```
hBshift    : ∀ w, B (w + τ) = x^2 * qC^(-m : ℤ) * (elvC w)^(-(2*m) : ℤ) * B w
                       - qC^(-m : ℤ) * (elvC w)^(-(2*m) : ℤ) * Pd (elvC w)

hArshift   : ∀ w, ∀ r < d, Ar r (w + τ) = x^2 * qC^(-m : ℤ) * (elvC w)^(-(2*m) : ℤ) * Ar r w
                       - qC^(-m : ℤ) * (elvC w)^(-(2*m) : ℤ) * (elvC w) * Pd (elvC w) / (1 - ω^r * elvC w)

hAextshift : ∀ w, Aext (w + τ) = x^2 * qC^(-m : ℤ) * (elvC w)^(-(2*m) : ℤ) * Aext w
                       - qC^(-m : ℤ) * (elvC w)^(-(2*m) : ℤ) * (elvC w) * Pd (elvC w) / (1 - x * elvC w)
```
  Do not alter the prefactor form, the defect terms, or the `∀ w`, `∀ r < d` quantification.
  (Via S2 these are equivalently `u`-level facts about `Bu, Aru, Aextu` at `u = elvC w`; keep
  the `w`-level display to preserve the Batch-4 match.)
- `hpack    : Pd u * MasterDefect u = Pd u * Residues u`   (prefactor-FREE — the
  `q^{-m}u^{-2m}` enters (4.21) only via `hPshift`; stating it inside `hpack` double-counts
  and produces the `q^{-2m}u^{-4m}` defect both judges flagged)
- `hKdefect : K_{d,x}(qu) - x²·K_{d,x}(u) = M_d(u)/(u(1-u^d)(1-xu)) · T_{d,x}(u)`  (RatFunc ℂ;
  the `K`-level bridge for 6(a); at `x=1` combine with `hTc`)
- `hMshift  : M_d(qu) = u^(2*m-2)·(1-u)/(1-u^d) · M_d(u)`
- `hPshift  : Pd(qu)  = q^{-m-1}·u^{-2}·(1-u)/(1-u^d) · Pd(u)`
- `hR0 : R_{d,x}.eval 0 = -X₀`;  `hdegR : R_{d,x}.natDegree ≤ 2*m - 1`
- For `x=1` only: `hEcancel : E_1 = 0`;  `hTc : T_{d,1}(u) = (1-u)·S_{d,1}(u)`
- For KF:untwist only: `hx : (x:ℂ) = Complex.exp (2*π*I*α)`;  `hlam : (m:ℂ) * λ = α`
- Theta defining laws (as `Q,U` monomials, below); `IsPrimitiveRoot ω 5` for level-5.
NOTE: `helvτ`, `helv1per`, and any λ-translation law are NOT on this list — they are now
LEMMAS of the concrete `elvC` (S1). Derive them; do not designate them.

BANNED HYPOTHESES (every one previously smuggled and rejected; the list is closed — nothing
off the designated list is permitted): `hGmaster`, `hGfunc`, `hBper`, `hArper`, `hAextper`,
`hΦraw`, `hΦraw_prod`, `hpackK`, `helvLam`, `htwistLam`, `helvλ`, `helv1`, `h𝓖per`, `hEps`,
`hResidues`, `hcov`, `hPFnum`, and any retyped `u`-level kernel law beyond the three
designated ones. Where a banned name corresponds to a true fact (`hBper`-style periodicity,
λ-translation), that fact is now DERIVABLE from (S1)/(S2) — prove it as a lemma.

## Units — exact signatures (matching accepted Batches; do not retype)

`x : ℂˣ`; `elvC : ℂ → ℂ` with `helvC0 : ∀ w, elvC w ≠ 0` (lemma); `qC : ℂ` with
`hqC0 : qC ≠ 0` (lemma); `ω : ℂ` a unit via primitivity; `Q U : ℂ` nonzero. `Pd Md : ℂ → ℂ`;
`Bu Aextu Φu 𝓗u : ℂ → ℂ`; `Aru : ℕ → ℂ → ℂ`. Every negative power/division carries its
nonzero fact at the point of use.

## Fractional powers — (Q,U) pinning (unchanged; per-point for U)

`(hQ : Q^24 = qC) (hU : U^2 = u)` with `u = elvC w` at the point of use; all fractional powers
as integer monomials (`q^{1/8}=Q^3`, `u^{-1/2}=U^{-1}`, `q^{-1/2}=Q^{-12}`, `q^{1/4}=Q^6`,
`u^{-2}=U^{-4}`, `q^{-d/2}=Q^{-12d}`, `u^{-d}=U^{-2d}`). BANNED: any additional formal root
(`qh` with `qh^2=q`, etc.) — `Q` provides every needed power; a second unrelated root is a
soundness hazard. No `rpow`/`cpow`.

## `m ≥ 2` everywhere; exponents as `2*m - 2`

`hm : 2 ≤ m` explicit on every definition and theorem (`include hm`); write `2*m - 2`, never
`d - 3`.

## Given / Prove

- **KF:Pshift.** GIVEN `hPshift, hpack, hm`, units. PROVE the multiplier collapse
  `Pd(qu)·x²q(u^d-1)/(u^(2m-2)(u-1)) = x²q^{-m}u^{-2m}·Pd(u)` and the `Φ` `w+τ` law (4.21)
  (via `lem_elv_tau` + `hpack` + `hPshift` — finite algebra; the prefactor arises HERE from
  `hPshift`, which is why `hpack` is prefactor-free). No `hΦraw`/`hΦraw_prod`/`hGfunc`.
- **KF:appellshift.** GIVEN `hBshift, hArshift, hAextshift`. PROVE their defect terms match
  the `Φ`-defect of (4.21) TERM BY TERM. Also prove, as standalone arithmetic lemmas, the
  square-completion identities `m·n²+2·m·n = m·(n+1)²-m` and
  `m·n²+n+2·m·n+1 = m·(n+1)²+(n+1)-m` (they document the designated laws, which Batch 4 has
  PROVED from `tsum` definitions).
- **KF:corrected.** GIVEN KF:Pshift + the kernel laws. PROVE (i) `𝓗` is 1-periodic — via the
  factorization (S2) and `lem_elv_one`; this is now a genuine derivation, not an assumption —
  and (ii) the `x²q^{-m}u^{-2m}` twist (4.27): the defects cancel.
- **KF:untwist.** GIVEN `hx, hlam`. Define `𝓗trans w := 𝓗 (w + λ)`. PROVE
  `x² · Complex.exp(-(4:ℂ)*π*I*(m:ℂ)*λ) = 1` (from `hx`, `hlam`, `exp_add`/`exp_int_mul...`),
  then the untwisted law (1.17) via `lem_elv_lam` + KF:corrected. INLINE BAN: no
  `helvLam`/`htwistLam`/`helvλ` hypothesis — `lem_elv_lam` is the derived replacement.
- **KF:carrier.** GIVEN the `ϑ₁` quasi-periodicities + triple-product normalization as `Q,U`
  monomials. PROVE the covering formula (3.9), the index-`m` elliptic law for `𝓙_{m,d}`, and
  `(4m+1)-d = 2m`. Level-5: `𝓙_{2,5} = Q^6 (q;q)_∞^{-6} U^{-4} J(u)^9/J(u^5)` on `Γ(600)`
  (`2-4m=-6`, `4m+1=9`, `24·5²=600`).
- **KF:level5.**
  6(a): the collapsed identity — CONCLUSION, denominator `u(1-u^5)`, in `RatFunc ℂ` (or
    pointwise with `u ≠ 0`, `1-u^5 ≠ 0`); inputs `hKdefect` (at `x=1`), `hMshift`, `hTc`. The
    `(1-u)` lives ONLY inside `S_{5,1}(u) = (1-u)R_{5,1}(u) - 5u^4(P5/P1)` — never the
    denominator (settled against the source). Not `hpack`; no `hpackK`.
  6(b): `D_{r,1} = (ω^r/5)·S_{5,1}(ω^{-r})` as a CONCLUSION from a genuine partial-fraction +
    root-of-unity argument (`IsPrimitiveRoot ω 5`, `Polynomial.X_pow_sub_one_eq_prod` over
    `nthRootsFinset 5 1`, evaluation at poles). No `hPFnum`-style per-residue identity; no
    cleared all-`v` PF identity (circular). Index range `0 ≤ r < 5`, never `∀ r : ℕ`. If 6(b)
    cannot be honestly closed, report it NOT CLOSED — never a `sorry`, never a smuggled
    hypothesis; a sorry-free file of the rest is worth more.
  6(c): the SPECIALIZED index-2 elliptic law for `𝓙_{2,5}` (multiplier `q^{-2}u^{-4}`) plus
    the datum `24·5² = 600`, both explicit.

## Build hygiene

`set_option linter.unusedVariables false` at top; `_`-prefix unused binders; lint warnings
non-fatal. The token `sorry` must never appear anywhere in the file — including comments and
docstrings (a commented `sorry` tripped the validator before); write "not closed" in prose.

## PRE-SUBMIT SELF-CHECK (verify before handing to the judges)

1. `elvC`, `qC` are DEFINED (S1); `lem_elv_tau/one/lam` are proved lemmas, not hypotheses.
2. `B, Ar, Aext, Φ, 𝓗` are compositions through `elvC` of opaque `u`-level symbols (S2).
3. Every hypothesis in every signature is on the designated list; no banned name appears; no
   hypothesis is a restatement/specialization of any conclusion in this batch.
4. `hpack` is prefactor-free.
5. Units/signatures exactly as specified; every fractional power is a `Q`/`U` monomial; no
   second root.
6. All `r`-indexed statements quantified `0 ≤ r < d` (level-5: `< 5`).
7. The token `sorry` appears nowhere, including comments.
8. 6(b) honestly closed, or absent and reported NOT CLOSED.

The proofs must be fully sorry-free. No axioms. The designated inputs (including the three
kernel laws, PROVED by the accepted Batch 4 and consumed here by instantiation) are hypotheses
of conditional theorems, not axioms; any hypothesis beyond the designated list is a violation.
