module

public import Lib.Analytic.PrimeNumberTheorem.ZeroFreeRegion

/-!
# Primes congruent to `1` modulo `M ^ k` with logarithm in a prescribed window

Let `4 ∣ M` and let `A` be fixed. For large `W` there is a prime `p ≡ 1` modulo `M ^ k` with `log p`
in `[U, U + W]`, uniformly for `1 < k`, `M ^ k ≤ W ^ A` and `W ≤ U ≤ W ^ A`
(`New.exists_prime_modEq_one_log_mem`).

The characters modulo `M ^ k` with trivial square come from the fixed modulus `M ^ 2`, so the
zero-free region gives a disc about `1` without zeros, uniformly in `k`. Newman's contour argument
on its boundary yields the prime.

Independently, the first section proves `n ≤ φ n * (2 * log n + 1)` (`New.le_totient_mul_log`).

Notions from other files:
* `entireL χ` is `L(s, χ)`, times `s - 1` if `χ` is principal;
* `regularL χ` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal.

## Relation to the literature

Known result: primes congruent to `1` modulo `M ^ k` with logarithm in a prescribed window. It is a
consequence of the Siegel–Walfisz theorem. Only one prime is found, in a long window, and only for
moduli that are powers of a fixed multiple of `4`. Source: Montgomery and Vaughan, Multiplicative
Number Theory I, 2007, Cor. 11.19.
-/

@[expose] public section

/-! ## A lower bound for Euler's totient -/

section TotientBound

open Finset Real Nat Prime

/-- If every element of a finite set `S` of natural numbers exceeds `a`, then
`∏ p ∈ S, (1 - p⁻¹) ≥ a / (a + #S)`. -/
lemma New.div_add_card_le_prod_one_sub_inv (S : Finset ℕ) (a : ℕ) (ha : ∀ p ∈ S, a < p) :
    (a : ℚ) / (a + #S) ≤ ∏ p ∈ S, (1 - (p : ℚ)⁻¹) := by
  -- Remove the least element `b` of `S`: by induction the product is at least
  -- `(1 - b⁻¹) * b / (b + #S - 1) = (b - 1) / (b + #S - 1)`, and `a ≤ b - 1`.
  induction S using Finset.induction_on_min generalizing a with
  | empty => simp [div_self_le_one]
  | insert b S b_min ih =>
    have hab : (a : ℚ) + 1 ≤ b := mod_cast ha b (mem_insert_self b S)
    have hb : 0 < (b : ℚ) := lt_of_lt_of_le (by positivity) hab
    have hb_notMem : b ∉ S := fun h ↦ (b_min b h).false
    rw [prod_insert hb_notMem, card_insert_of_notMem hb_notMem, Nat.cast_succ]
    calc
      (a : ℚ) / (a + (#S + 1)) ≤ (b - 1) / (b + #S) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      _ = (1 - (b : ℚ)⁻¹) * (b / (b + #S)) := by field_simp
      _ ≤ (1 - (b : ℚ)⁻¹) * ∏ p ∈ S, (1 - (p : ℚ)⁻¹) :=
        mul_le_mul_of_nonneg_left (ih b b_min) (sub_nonneg.2 (cast_inv_le_one b))

/-- Every positive integer satisfies `n ≤ φ n * (2 * log n + 1)`. -/
lemma New.le_totient_mul_log {n : ℕ} (hn : 0 < n) : n ≤ φ n * (2 * Real.log n + 1) := by
  -- If `n` has `j` distinct prime factors, then `2 ^ j ≤ n`, so `j ≤ 2 * log n`, and
  -- `φ n / n = ∏ (1 - p⁻¹) ≥ 1 / (1 + j)`.
  set j : ℕ := #n.primeFactors
  have two_pow_le : 2 ^ j ≤ n :=
    (pow_card_le_prod _ _ 2 fun _ hp ↦ (prime_of_mem_primeFactors hp).two_le).trans
      (le_of_dvd hn n.prod_primeFactors_dvd)
  have card_le : j * Real.log 2 ≤ Real.log n := by grw [← two_pow_le]; simp
  have totient_ge : (n : ℝ) ≤ φ n * (1 + j) := by
    have h_prod : ((1 : ℕ) : ℚ) / ((1 : ℕ) + j) ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
      div_add_card_le_prod_one_sub_inv _ 1 fun _ hp ↦ (prime_of_mem_primeFactors hp).one_lt
    suffices h_rat : (n : ℚ) ≤ φ n * (1 + j) from mod_cast h_rat
    rw [totient_eq_mul_prod_factors, mul_assoc]
    exact le_mul_of_one_le_right (by positivity)
      ((div_le_iff₀ (by positivity)).1 (mod_cast h_prod))
  refine totient_ge.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  nlinarith [log_two_gt_d9]

end TotientBound

/-!
## Primes congruent to 1 mod M^k in a logarithmic window via Newman's method
-/

section AuxiliaryPrimes

open ArithmeticFunction DirichletCharacter Complex Set Filter LSeries Finset Real
  Topology vonMangoldt Chebyshev Polynomial ZMod MulChar

/-- If `4 ∣ M` and `2 ≤ k`, a character mod `M ^ k` whose square is trivial factors through modulus
`M ^ 2`, since every unit congruent to `1` mod `M ^ 2` is a square. -/
lemma New.factorsThrough_sq_of_sq_eq_one {M k : ℕ} [NeZero M] (hM : 4 ∣ M) (hk : 2 ≤ k)
    {χ : DirichletCharacter ℂ (M ^ k)} (hχ : χ ^ 2 = 1) :
    χ.FactorsThrough (M ^ 2) := by
  refine (χ.factorsThrough_iff_ker_unitsMap (pow_dvd_pow M hk)).mpr fun u hu ↦ ?_
  obtain ⟨m, hm⟩ := hM
  obtain ⟨t, ht⟩ : (↑(M ^ 2) : ℤ) ∣ 1 - (u : ZMod (M ^ k)).cast :=
    (intCast_eq_intCast_iff_dvd_sub u.val.cast 1 (M ^ 2)).mp
      (by simpa [unitsMap_def] using congrArg Units.val (MonoidHom.mem_ker.1 hu))
  have u_lin : 1 - (u : ZMod (M ^ k)) = M ^ 2 * t := by
    simpa using congrArg (Int.cast : ℤ → ZMod (M ^ k)) ht
  -- Newton's iteration from `0` solves `c ^ 2 + c = -M * m * t`, as the right side is nilpotent;
  -- then `(1 + 2 * c) ^ 2 = 1 - 4 * M * m * t = u`
  obtain ⟨c, hc⟩ : ∃ c : ZMod (M ^ k), M * m * t + c ^ 2 + c = 0 := by
    have h_nil : IsNilpotent ((M : ZMod (M ^ k)) * m * t) :=
      ⟨k, by simp [mul_pow, natCast_pow_eq_zero_of_le]⟩
    obtain ⟨c, ⟨-, hc⟩, -⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero (x := (0 : ZMod (M ^ k)))
      (P := C ((M : ZMod (M ^ k)) * m * t) + X ^ 2 + X) (by simpa using h_nil) (by simp)
    exact ⟨c, by simpa using hc⟩
  have hM_cast : (M : ZMod (M ^ k)) = 4 * m := by simp [hm]
  have u_eq : u = (1 + 2 * c) ^ 2 := by linear_combination -u_lin - 4 * hc - M * t * hM_cast
  refine Units.ext ?_
  simpa [u_eq, ← pow_apply', hχ] using one_apply_coe u

/-- If `4 ∣ M` and `2 ≤ k`, then for a character `χ` mod `M ^ k` with trivial square there is a
character `χ₀` mod `M ^ 2` with `regularL χ = regularL χ₀`, as the two moduli have the same prime
factors. Here `regularL χ` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal. -/
lemma New.exists_regularL_eq_of_sq_eq_one {M k : ℕ} [NeZero M] (hM : 4 ∣ M) (hk : 2 ≤ k)
    {χ : DirichletCharacter ℂ (M ^ k)} (hχ : χ ^ 2 = 1) :
    ∃ χ₀ : DirichletCharacter ℂ (M ^ 2), regularL χ = regularL χ₀ := by
  obtain ⟨h_dvd, χ₀, hχ₀⟩ := factorsThrough_sq_of_sq_eq_one hM hk hχ
  have h_one : χ = 1 ↔ χ₀ = 1 := by rw [hχ₀, changeLevel_eq_one_iff]
  have h_primes : (M ^ k).primeFactors = (M ^ 2).primeFactors := by
    simp [Nat.primeFactors_pow M (show k ≠ 0 by lia), Nat.primeFactors_pow M two_ne_zero]
  -- Changing the level multiplies by Euler factors at new primes, and there are none.
  have h_LFunction {z : ℂ} (h : χ₀ ≠ 1 ∨ z ≠ 1) : χ.LFunction z = χ₀.LFunction z := by
    rw [hχ₀, LFunction_changeLevel h_dvd χ₀ h, h_primes, Finset.prod_eq_one, mul_one]
    simp +contextual [ZMod.isUnit_prime_iff_not_dvd]
  have h_entire (z : ℂ) : entireL χ₀ z = entireL χ z := by
    by_cases hχ₀_one : χ₀ = 1
    · subst χ₀
      by_cases hz : z = 1 <;>
        simp [entireL, LFunctionTrivChar₁, LFunctionTrivChar, h_one.2 rfl, hz, h_primes,
          ← h_LFunction]
    · simp [entireL, hχ₀_one, mt h_one.1 hχ₀_one, h_LFunction (.inl hχ₀_one)]
  exact ⟨χ₀, funext fun z ↦ by by_cases h : χ₀ = 1 <;> simp [regularL, ← h_entire, h_one, h]⟩

/-- For `4 ∣ M` and `A` fixed, for all large `X` the following holds for every `k > 1`, every
Dirichlet character `χ` mod `M ^ k` with `M ^ k ≤ X ^ A`, and every `s` with `|s - 1| ≤ 1 / X`:
`entireL χ s ≠ 0` and `|logDeriv (entireL χ) s| ≤ X`. Here `entireL χ` is the entire function equal
to `L(s, χ)` for non-principal `χ`, and to the continuation of `(s - 1) L(s, χ)` for principal `χ`.
No exceptional zero can occur, because the real characters come from the fixed modulus `M ^ 2`. -/
lemma New.eventually_norm_logDeriv_entireL_le_near_one (A : ℕ) {M : ℕ} [NeZero M] (hM : 4 ∣ M) :
    ∀ᶠ X : ℝ in atTop, ∀ k : ℕ, 1 < k → ∀ (χ : DirichletCharacter ℂ (M ^ k)) (s : ℂ),
      (M : ℝ) ^ k ≤ X ^ A → ‖s - 1‖ ≤ X⁻¹ → entireL χ s ≠ 0 ∧ ‖logDeriv (entireL χ) s‖ ≤ X := by
  -- Apply the zero-free region with `l = (A + 1) log X`, for which `e ^ l = X ^ (A + 1)`.
  have h_log : Tendsto (fun X : ℝ ↦ (A + 1 : ℕ) * X.log) atTop atTop :=
    tendsto_log_atTop.const_mul_atTop (by positivity)
  have h_inv : Tendsto (fun X : ℝ ↦ 1 / ((A + 1 : ℕ) * X.log)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h_log
  have h_small : (fun X : ℝ ↦ 2 * ((A + 1 : ℕ) * X.log) ^ 25) =o[atTop] id := by
    simpa only [mul_pow, ← mul_assoc] using
      (isLittleO_pow_log_id_atTop (n := 25)).const_mul_left (2 * ((A + 1 : ℕ) : ℝ) ^ 25)
  filter_upwards [h_log.eventually_ge_atTop (10 ^ 10), h_small.eventuallyLE, eventually_ge_atTop 2,
    h_inv.eventually (eventually_all.2 fun χ₀ : DirichletCharacter ℂ (M ^ 2) ↦
      eventually_le_norm_regularL χ₀)] with X hl h_pow hX h_near k hk χ s hq hs
  set l : ℝ := (A + 1 : ℕ) * X.log with l_def
  have hX_pos : 0 < X := by linarith
  have hl_pow : 0 < l ^ 25 := pow_pos (by linarith) 25
  replace h_pow : 2 * l ^ 25 ≤ X := (le_abs_self _).trans (h_pow.trans_eq (abs_of_pos hX_pos))
  have h_exp : rexp l = X ^ A * X := by
    rw [l_def, Real.exp_natCast_mul, Real.exp_log hX_pos, pow_succ]
  have h_one : 1 ≤ X ^ A := one_le_pow₀ (by linarith)
  have h_re_lower : 1 - 1 / l ^ 25 ≤ s.re := by
    have h_inv_le : X⁻¹ ≤ 1 / l ^ 25 := by
      simpa using inv_anti₀ hl_pow (show l ^ 25 ≤ X by linarith)
    have h_re : |s.re - 1| ≤ X⁻¹ := by simpa using (abs_re_le_norm (s - 1)).trans hs
    linarith [abs_le.1 h_re]
  have h_norm : ‖s‖ ≤ 2 := by
    linarith [norm_le_norm_sub_add s 1, norm_one (α := ℂ),
      inv_le_one_of_one_le₀ (show 1 ≤ X by linarith)]
  have h_level : ((M ^ k : ℕ) : ℝ) ≤ rexp l := by push_cast; nlinarith
  have h_not_small : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖ := fun hχ ↦ by
    obtain ⟨χ₀, h_eq⟩ := exists_regularL_eq_of_sq_eq_one hM hk hχ
    simpa only [h_eq] using h_near χ₀
  exact (norm_logDeriv_entireL_le χ hl h_level h_not_small h_re_lower (by nlinarith)).imp_right
    fun h_le ↦ h_le.trans h_pow

/-- If `log n * (σ - re z) ≤ E`, then moving the `n`-th term of the Dirichlet series of `a` from
`1 + z` to the real point `1 + σ` costs at most the factor `exp E`. -/
lemma New.norm_term_le_exp_mul (a : ℕ → ℂ) {z : ℂ} (σ E : ℝ) {n : ℕ}
    (h_le : Real.log n * (σ - z.re) ≤ E) :
    ‖term a (1 + z) n‖ ≤ Real.exp E * ‖term a (1 + σ) n‖ := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  -- `↓cpow_add` must fire before simp rewrites the exponent.
  have h_eq : ‖term a (1 + z) n‖ = Real.exp (Real.log n * (σ - z.re)) * ‖term a (1 + σ) n‖ := by
    simp [hn, ↓cpow_add, cpow_def, norm_exp, field, mul_sub, Real.exp_sub, ← natCast_log]
  grw [h_eq, h_le]

open scoped ComplexOrder in
/-- Let `4 ∣ M` and let `A` be fixed. For all large `W` there is a prime `p ≡ 1` mod `M ^ k` with
`U ≤ log p ≤ U + W`, whenever `1 < k`, `M ^ k ≤ W ^ A` and `W ≤ U ≤ W ^ A`. This is a consequence
of the Siegel–Walfisz theorem, proved here directly by Newman's contour method. -/
theorem New.exists_prime_modEq_one_log_mem (M A : ℕ) [NeZero M] (hM : 4 ∣ M) :
    ∀ᶠ W : ℝ in atTop, ∀ k : ℕ, 1 < k → (M : ℝ) ^ k ≤ W ^ A → ∀ U : ℝ, U ∈ Set.Icc W (W ^ A) →
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD M ^ k] ∧ Real.log p ∈ Set.Icc U (U + W) := by
  -- Write `W = X ^ 2`, `q = M ^ k`. Let `F z / z` be the Dirichlet series of `Λ` on `1 mod q` at
  -- `1 + z`, and `P` its part with `n < e ^ U`. If the window has no prime, `F z - z P z` over
  -- `exp (2 - U z - X (1 + X z)² / 4)` is at most `3 U` on `‖z‖ = 1 / X`, yet of size
  -- `e ^ (X / 4 - 2) / φ(q)` at `0`.
  let b (n : ℕ) : ℂ := ↑(if n.Prime then 0 else vonMangoldt n : ℝ)
  obtain ⟨C, hC⟩ : Summable fun n ↦ ‖term b (1 + -4⁻¹) n‖ := by
    have h_bigO : (fun n : ℕ ↦ ∑ m ∈ Finset.Icc 1 n, if m.Prime then 0 else vonMangoldt m) =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ (2⁻¹ : ℝ) := by
      simpa [Function.comp_def, psi_sub_theta_eq_sum_not_prime, sum_filter, sqrt_eq_rpow,
        ← Finset.Icc_add_one_left_eq_Ioc] using isBigO_psi_sub_theta_sqrt.natCast_atTop
    exact (LSeriesSummable_of_sum_norm_bigO_and_nonneg h_bigO
      (fun m ↦ by split_ifs <;> simp [vonMangoldt_nonneg]) (by simp) (by norm_num)).norm
  -- Take `X = √W` large: `q, U ≤ X ^ (2 * A)`, so `3 * U * q < e ^ (X / 4 - 2)`.
  rw [← comap_sqrt_atTop, eventually_comap]
  filter_upwards [eventually_norm_logDeriv_entireL_le_near_one (2 * A) hM,
    (tendsto_exp_mul_div_rpow_atTop ↑(4 * A) 4⁻¹ (by simp)).eventually_gt_atTop (.exp 2 * 3),
    eventually_ge_atTop 200, eventually_ge_atTop C] with
    X h_free h_exp hX200 hXC W hW k hk hq U ⟨hWU, hU⟩
  have hX : 0 < X := by linarith
  obtain rfl : W = X ^ 2 := by rw [← hW, sq_sqrt (sqrt_pos.1 (hX.trans_eq hW.symm)).le]
  have hU_pos : 0 < U := (pow_pos hX 2).trans_le hWU
  have hXU : X ≤ U := by nlinarith
  set q : ℕ := M ^ k
  simp only [← pow_mul, rpow_natCast, ← natCast_eq_natCast_iff, Nat.cast_one,
    Set.mem_Icc] at hq hU h_exp ⊢
  have hq_cast : (q : ℝ) ≤ X ^ (2 * A) := by simpa [q] using hq
  have hq_tot : (1 : ℝ) ≤ q.totient := mod_cast Nat.totient_pos.2 (NeZero.pos q)
  let a (n : ℕ) : ℂ := residueClass (1 : ZMod q) n
  let F (z : ℂ) : ℂ :=
    (1 - z * ∑ χ : DirichletCharacter ℂ q, logDeriv (entireL χ) (1 + z)) / q.totient
  have h_series (z : ℂ) (hz : 0 < z.re) : LSeriesHasSum a (1 + z) (F z / z) := by
    have h_coeff : a = (q.totient : ℂ)⁻¹ •
        ∑ χ : DirichletCharacter ℂ q, fun n : ℕ ↦ χ n * vonMangoldt n := by
      ext n; simp [a, residueClass_apply]
    have h_val : F z / z = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ((if χ = 1 then 1 else 0) / (1 + z - 1) - logDeriv (entireL χ) (1 + z)) := by
      simp [F, ite_div]
      field_simp [ne_zero_of_re_pos hz]
    rw [h_coeff, h_val]
    exact (LSeriesHasSum.sum fun χ _ ↦ LSeriesHasSum_mul_vonMangoldt χ (by simpa using hz)).smul _
  -- For `‖z‖ ≤ 1 / X` each `z * logDeriv (entireL χ)` has norm at most `1`, so `‖F z‖ ≤ 2`.
  have h_disc {z : ℂ} (hz : ‖z‖ ≤ X⁻¹) (χ : DirichletCharacter ℂ q) :
      entireL χ (1 + z) ≠ 0 ∧ ‖logDeriv (entireL χ) (1 + z)‖ ≤ X :=
    h_free k hk χ (1 + z) hq (by simpa)
  have hF {z : ℂ} (hz : ‖z‖ ≤ X⁻¹) : ‖F z‖ ≤ 2 := by
    have h_sum : ∑ χ : DirichletCharacter ℂ q, ‖z * logDeriv (entireL χ) (1 + z)‖ ≤ q.totient := by
      grw [sum_le_card_nsmul _ _ 1 fun χ _ ↦ ?_]
      · simp [← card_eq_totient_of_hasEnoughRootsOfUnity ℂ]
      · grw [norm_mul, hz, (h_disc hz χ).2, inv_mul_cancel₀ hX.ne']
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith), mul_sum]
    grw [norm_sub_le, norm_sum_le, norm_one]
    linarith
  by_contra h_none
  let P (z : ℂ) : ℂ := ∑ n ∈ .range ⌈U.exp⌉₊, term a (1 + z) n
  let G (z : ℂ) : ℂ := (F z - z * P z) / (2 - U * z - 4⁻¹ * X * (1 + X * z) ^ 2).exp
  -- A bound on the circle bounds `G 0` by Cauchy's estimate, which is too large.
  suffices h_circle : ∀ z : ℂ, ‖z‖ = X⁻¹ → ‖G z‖ ≤ 3 * U by
    have h_term (n : ℕ) (w : ℂ) : DifferentiableAt ℂ (term a · n) w :=
      (hasDerivAt_term a n w).differentiableAt
    have hG : DiffContOnCl ℂ G (Metric.ball 0 X⁻¹) :=
      DifferentiableOn.diffContOnCl_ball (fun s hs ↦ by
        have hs_ne (χ : DirichletCharacter ℂ q) : entireL χ (1 + s) ≠ 0 :=
          (h_disc (by simpa using hs) χ).1
        exact DifferentiableAt.differentiableWithinAt (by fun_prop (disch := simp_all) [logDeriv]))
        le_rfl
    have h_zero : ‖G 0‖ ≤ 3 * U := by
      simpa using norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0 (inv_pos.2 hX) hG
        (by simpa using h_circle)
    have h_value : ‖G 0‖ = rexp (4⁻¹ * X) / rexp 2 / q.totient := by
      simp [G, F, norm_exp, Real.exp_sub, field]
    have h_large : 3 * U < rexp (4⁻¹ * X) / rexp 2 / q.totient := by
      rw [lt_div_iff₀ (by linarith), lt_div_iff₀ (exp_pos 2)]
      calc
        3 * U * q.totient * rexp 2 ≤ 3 * X ^ (2 * A) * X ^ (2 * A) * rexp 2 := by
          grw [Nat.totient_le, hq_cast, hU]
        _ = rexp 2 * 3 * X ^ (4 * A) := by ring
        _ < rexp (4⁻¹ * X) := (lt_div_iff₀ (by positivity)).1 h_exp
    linarith
  intro z hz
  rw [norm_div, norm_exp, div_le_iff₀' (by positivity)]
  have hz_small : ‖z‖ ≤ 200⁻¹ := hz.trans_le (inv_anti₀ (by positivity) hX200)
  set E : ℝ := (2 - U * z - 4⁻¹ * X * (1 + X * z) ^ 2 : ℂ).re
  -- On `‖z‖ = 1 / X` the Gaussian term shifts `U` to `U + t` with `t ∈ [0, X ^ 2]`.
  set t : ℝ := X ^ 2 / 2 * (1 + X * z.re)
  obtain ⟨hz_lo, hz_hi⟩ : -1 ≤ X * z.re ∧ X * z.re ≤ 1 := by
    rw [← abs_le, abs_mul, abs_of_pos hX]
    grw [z.abs_re_le_norm, hz, mul_inv_cancel₀ hX.ne']
  have ht_nonneg : 0 ≤ t := mul_nonneg (by positivity) (by linarith)
  have ht_le : t ≤ X ^ 2 := calc
    t ≤ X ^ 2 / 2 * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = X ^ 2 := by ring
  have hE : E = 2 - (U + t) * z.re := by
    have h_im : X ^ 2 * z.im ^ 2 = 1 - (X * z.re) ^ 2 := by
      rw [← z.sq_norm_sub_sq_re, hz]; field_simp
    have h_re : E = 2 - U * z.re - X / 4 * ((1 + X * z.re) ^ 2 - X ^ 2 * z.im ^ 2) := by
      simp [E, sq]; ring
    linear_combination h_re + X / 4 * h_im
  -- At `1 + 1 / U` the nonnegative Dirichlet series of `a` has sum at most `2 U`.
  have h_norm : HasSum (fun n : ℕ ↦ ‖term a (1 + (U⁻¹ : ℝ)) n‖) (F (U⁻¹ : ℝ) / (U⁻¹ : ℝ)).re := by
    have hc : HasSum (fun n : ℕ ↦ (‖term a (1 + (U⁻¹ : ℝ)) n‖ : ℂ)) (F (U⁻¹ : ℝ) / (U⁻¹ : ℝ)) :=
      (h_series _ (by simpa using hU_pos)).congr_fun fun n ↦ by
        have ha : 0 ≤ a n := Complex.zero_le_real.2 (residueClass_nonneg (1 : ZMod q) n)
        have hterm : 0 ≤ term a (1 + (U⁻¹ : ℝ)) n := by
          simpa only [Complex.ofReal_add, Complex.ofReal_one] using term_nonneg ha (1 + U⁻¹)
        exact norm_of_nonneg' hterm
    simpa using hasSum_re hc
  have h_total : (F (U⁻¹ : ℝ) / (U⁻¹ : ℝ)).re ≤ 2 * U := by
    have h_abs : ‖((U⁻¹ : ℝ) : ℂ)‖ = U⁻¹ := by simp [hU_pos.le]
    grw [re_le_norm, norm_div, hF (h_abs.trans_le (inv_anti₀ hX hXU)), h_abs, div_inv_eq_mul]
  have h_unit : U * U⁻¹ = 1 := mul_inv_cancel₀ hU_pos.ne'
  have h_shift : t * U⁻¹ ≤ 1 := (div_le_one hU_pos).2 (ht_le.trans hWU)
  rcases le_total z.re U⁻¹ with h_left | h_right
  · -- If `re z ≤ 1 / U`, then `E ≥ 0`, and we bound `F` and the finite sum `P` separately.
    have hU_re : U * z.re ≤ 1 := (mul_le_mul_of_nonneg_left h_left hU_pos.le).trans_eq h_unit
    have ht_re : t * z.re ≤ 1 := (mul_le_mul_of_nonneg_left h_left ht_nonneg).trans h_shift
    have hP : ‖P z‖ ≤ rexp E * (2 * U) := by
      have h_le (n : ℕ) (hn : n ∈ Finset.range ⌈U.exp⌉₊) :
          ‖term a (1 + z) n‖ ≤ rexp E * ‖term a (1 + (U⁻¹ : ℝ)) n‖ := by
        have h_log : Real.log n ≤ U := by
          obtain rfl | hn_pos := n.eq_zero_or_pos
          · simpa using hU_pos.le
          · exact ((log_lt_iff_lt_exp (mod_cast hn_pos)).2 (Nat.lt_ceil.1 (mem_range.1 hn))).le
        exact norm_term_le_exp_mul a U⁻¹ E
          (by linarith [mul_le_mul_of_nonneg_right h_log (sub_nonneg.2 h_left)])
      calc
        ‖P z‖ ≤ ∑ n ∈ .range ⌈U.exp⌉₊, rexp E * ‖term a (1 + (U⁻¹ : ℝ)) n‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum h_le)
        _ = rexp E * ∑ n ∈ .range ⌈U.exp⌉₊, ‖term a (1 + (U⁻¹ : ℝ)) n‖ := (mul_sum ..).symm
        _ ≤ rexp E * (2 * U) := by
          gcongr
          exact (sum_le_hasSum _ (fun _ _ ↦ norm_nonneg _) h_norm).trans h_total
    calc
      ‖F z - z * P z‖ ≤ 2 + 200⁻¹ * (rexp E * (2 * U)) := by
        grw [norm_sub_le, norm_mul, hF hz.le, hz_small, hP]
      _ ≤ rexp E * (3 * U) := by nlinarith only [E.one_le_exp (show 0 ≤ E by linarith), hWU, hX200]
  · -- If `re z ≥ 1 / U`, then `F z - z P z` is `z` times the tail `n ≥ e ^ U` of the series.
    have h_pos : 0 < z.re := (inv_pos.2 hU_pos).trans_le h_right
    have hP_sum : HasSum (fun n : ℕ ↦ if n < ⌈U.exp⌉₊ then term a (1 + z) n else 0) (P z) := by
      have h_eq :
          (∑ n ∈ Finset.range ⌈U.exp⌉₊, if n < ⌈U.exp⌉₊ then term a (1 + z) n else 0) =
            P z :=
        Finset.sum_congr rfl fun _ hn ↦ by simp [Finset.mem_range.mp hn]
      rw [← h_eq]
      refine hasSum_sum_of_ne_finset_zero (s := .range ⌈U.exp⌉₊) fun n hn ↦ ?_
      have h : ¬n < ⌈U.exp⌉₊ := fun hn' ↦ hn (Finset.mem_range.mpr hn')
      simp [h]
    have h_full : HasSum (fun n : ℕ ↦ term a (1 + z) n) (F z / z) := h_series z h_pos
    have h_tail_sum : HasSum (fun n : ℕ ↦ if n < ⌈U.exp⌉₊ then 0 else term a (1 + z) n)
        (F z / z - P z) :=
      (h_full.sub hP_sum).congr_fun fun n ↦ by split_ifs <;> simp
    have h_tail : ‖F z / z - P z‖ ≤ rexp E * (3 * U) := by
      refine (h_tail_sum.norm_le_of_bounded ((h_norm.add hC).mul_left (rexp E)) fun n ↦ ?_).trans
        (by gcongr; linarith)
      split_ifs with hn
      · simp; positivity
      · have hn_ge : U.exp ≤ n := Nat.ceil_le.1 (not_lt.1 hn)
        have h_log : U ≤ Real.log n := (le_log_iff_exp_le (U.exp_pos.trans_le hn_ge)).2 hn_ge
        rcases le_total (Real.log n) (U + X ^ 2) with h_in | h_out
        · -- In the window no `n ≡ 1` is prime, so compare with `b` at `3 / 4`.
          have hab : ‖a n‖ ≤ ‖b n‖ := by
            by_cases hp : n.Prime
            · have h_ne : (n : ZMod q) ≠ 1 := fun h ↦ h_none ⟨n, hp, h, h_log, h_in⟩
              simp [a, residueClass, h_ne]
            · simpa [a, b, hp, abs_of_nonneg, residueClass_nonneg] using
                residueClass_le (1 : ZMod q) n
          have ht_re : t * z.re ≤ U * 200⁻¹ :=
            mul_le_mul (ht_le.trans hWU) (z.re_le_norm.trans hz_small) h_pos.le hU_pos.le
          have h_exp_le : Real.log n * (-4⁻¹ - z.re) ≤ E := by
            linarith [mul_le_mul_of_nonpos_right h_log (show -4⁻¹ - z.re ≤ 0 by linarith)]
          exact (norm_term_le _ hab).trans
            ((norm_term_le_exp_mul b (-4⁻¹) E h_exp_le).trans (by gcongr; simp))
        · -- Beyond the window we have `log n ≥ U + X² ≥ U + t`.
          have h_exp_le : Real.log n * (U⁻¹ - z.re) ≤ E := by
            linarith [mul_le_mul_of_nonpos_right (show U + t ≤ Real.log n by linarith)
              (sub_nonpos.2 h_right)]
          exact (norm_term_le_exp_mul a U⁻¹ E h_exp_le).trans (by gcongr; simp)
    calc
      ‖F z - z * P z‖ = ‖z * (F z / z - P z)‖ := by
        rw [mul_sub, mul_div_cancel₀ _ (ne_zero_of_re_pos h_pos)]
      _ ≤ rexp E * (3 * U) := by grw [norm_mul, h_tail, show ‖z‖ ≤ 1 by linarith, one_mul]

end AuxiliaryPrimes
