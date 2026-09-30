/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Foundations.OrthProj

/-!
# Maximizing projections commute

Let `A` be a Hermitian matrix. If `Q` maximizes `P ↦ Re tr(A P)` among the orthogonal projections
of rank `m`, then `AQ = QA` (`commute_of_isMaxOn`). This is the matrix version of the first
order condition on the Grassmannian (cf. [Basso, *Almost minimal orthogonal projections*,
Lemma 3.1]; the real case is `Amop.commute_of_opt`).

Proof: if `(1 - Q) A Q ≠ 0`, pick unit vectors `x ∈ range Q`, `y ⊥ range Q` with
`Re ⟨y, A x⟩ > 0` and rotate `x` towards `y`: with `c² + d² = 1` the matrix
`Q - x xᴴ + v vᴴ`, `v = c x + d y`, is again an orthogonal projection of rank `m`, and for small
`d > 0` it has a larger value. The rotation uses the rational parametrization
`c = (1 - s²)/(1 + s²)`, `d = 2s/(1 + s²)` of the circle, so no square roots are needed.
-/

open Matrix

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-! ### Rank-one matrices -/

omit [Fintype ι] in

/-- The rank-one matrix `x xᴴ`. -/
def rk1 (x : ι → 𝕜) : Matrix ι ι 𝕜 := vecMulVec x (star x)

omit [Fintype ι] in
lemma rk1_conjTranspose (x : ι → 𝕜) : (rk1 x)ᴴ = rk1 x := by
  simp [rk1, conjTranspose_vecMulVec]

lemma mul_rk1 (M : Matrix ι ι 𝕜) (x : ι → 𝕜) : M * rk1 x = vecMulVec (M *ᵥ x) (star x) :=
  mul_vecMulVec _ _ _

lemma rk1_mul_of_herm {M : Matrix ι ι 𝕜} (hM : Mᴴ = M) (x : ι → 𝕜) :
    rk1 x * M = vecMulVec x (star (M *ᵥ x)) := by
  rw [rk1, vecMulVec_mul, star_mulVec, hM]

lemma rk1_mul_rk1 (x y : ι → 𝕜) : rk1 x * rk1 y = (star x ⬝ᵥ y) • vecMulVec x (star y) := by
  rw [rk1, rk1, vecMulVec_mul_vecMulVec]
  ext i j
  simp [vecMulVec_apply, mul_left_comm]

lemma trace_mul_rk1 (A : Matrix ι ι 𝕜) (x : ι → 𝕜) :
    (A * rk1 x).trace = star x ⬝ᵥ (A *ᵥ x) := by
  rw [mul_rk1, trace_vecMulVec, dotProduct_comm]

lemma trace_rk1 (x : ι → 𝕜) : (rk1 x).trace = star x ⬝ᵥ x := by
  rw [rk1, trace_vecMulVec, dotProduct_comm]

/-! ### Building orthogonal projections -/

lemma isOrthProj_rk1 {v : ι → 𝕜} (hv : star v ⬝ᵥ v = 1) : IsOrthProj (rk1 v) :=
  ⟨rk1_conjTranspose v, by rw [rk1_mul_rk1, hv, one_smul]; rfl⟩

/-- Removing a unit vector `x` of the range: `Q - x xᴴ` is again an orthogonal projection. -/
lemma isOrthProj_sub_rk1 {Q : Matrix ι ι 𝕜} (hQ : IsOrthProj Q) {x : ι → 𝕜} (hx : Q *ᵥ x = x)
    (hxx : star x ⬝ᵥ x = 1) : IsOrthProj (Q - rk1 x) := by
  refine ⟨by rw [conjTranspose_sub, hQ.herm, rk1_conjTranspose], ?_⟩
  have h1 : Q * rk1 x = rk1 x := by rw [mul_rk1, hx]; rfl
  have h2 : rk1 x * Q = rk1 x := by rw [rk1_mul_of_herm hQ.herm, hx]; rfl
  have h3 : rk1 x * rk1 x = rk1 x := by rw [rk1_mul_rk1, hxx, one_smul]; rfl
  rw [sub_mul, mul_sub, mul_sub, hQ.idem, h1, h2, h3]
  abel

/-- The sum of two orthogonal projections with `E F = 0` is an orthogonal projection. -/
lemma IsOrthProj.add {E F : Matrix ι ι 𝕜} (hE : IsOrthProj E) (hF : IsOrthProj F)
    (hEF : E * F = 0) : IsOrthProj (E + F) := by
  have hFE : F * E = 0 := by
    have := congrArg conjTranspose hEF
    rwa [conjTranspose_mul, hE.herm, hF.herm, conjTranspose_zero] at this
  refine ⟨by rw [conjTranspose_add, hE.herm, hF.herm], ?_⟩
  rw [add_mul, mul_add, mul_add, hE.idem, hF.idem, hEF, hFE]
  abel

/-! ### Sesquilinear bookkeeping -/

/-- `⟨u, M v⟩ = ⟨Mᴴ u, v⟩`. -/
lemma dotProduct_mulVec_star (M : Matrix ι ι 𝕜) (u v : ι → 𝕜) :
    star u ⬝ᵥ (M *ᵥ v) = star (Mᴴ *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

/-- For Hermitian `A`, `⟨x, A y⟩ = conj ⟨y, A x⟩`. -/
lemma dotProduct_mulVec_herm {A : Matrix ι ι 𝕜} (hA : Aᴴ = A) (x y : ι → 𝕜) :
    star x ⬝ᵥ (A *ᵥ y) = star (star y ⬝ᵥ (A *ᵥ x)) := by
  rw [dotProduct_mulVec_star, hA, star_dotProduct]

lemma re_dotProduct_mulVec_herm {A : Matrix ι ι 𝕜} (hA : Aᴴ = A) (x y : ι → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ y)) = RCLike.re (star y ⬝ᵥ (A *ᵥ x)) := by
  rw [dotProduct_mulVec_herm hA, RCLike.star_def, RCLike.conj_re]

/-- Expansion of `⟨v, A v⟩` for `v = c x + d y` with real `c, d`. -/
lemma re_quad_add {A : Matrix ι ι 𝕜} (hA : Aᴴ = A) (x y : ι → 𝕜) (c d : ℝ) :
    RCLike.re (star ((c : 𝕜) • x + (d : 𝕜) • y) ⬝ᵥ (A *ᵥ ((c : 𝕜) • x + (d : 𝕜) • y))) =
      c ^ 2 * RCLike.re (star x ⬝ᵥ (A *ᵥ x)) +
        2 * c * d * RCLike.re (star y ⬝ᵥ (A *ᵥ x)) +
        d ^ 2 * RCLike.re (star y ⬝ᵥ (A *ᵥ y)) := by
  have hxy := re_dotProduct_mulVec_herm hA x y
  simp only [star_add, star_smul, RCLike.star_def, RCLike.conj_ofReal, mulVec_add,
    mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, map_add, RCLike.re_ofReal_mul]
  rw [hxy]
  ring

lemma dotProduct_add_smul (x y : ι → 𝕜) (c d : ℝ) :
    star ((c : 𝕜) • x + (d : 𝕜) • y) ⬝ᵥ ((c : 𝕜) • x + (d : 𝕜) • y) =
      (c ^ 2 : ℝ) * (star x ⬝ᵥ x) + (c * d : ℝ) * (star x ⬝ᵥ y + star y ⬝ᵥ x) +
        (d ^ 2 : ℝ) * (star y ⬝ᵥ y) := by
  simp only [star_add, star_smul, RCLike.star_def, RCLike.conj_ofReal, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  push_cast
  ring

/-- Every nonzero vector has a positive real multiple of norm one. -/
lemma exists_normalize {v : ι → 𝕜} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ star ((c : 𝕜) • v) ⬝ᵥ ((c : 𝕜) • v) = 1 := by
  have hpos : 0 < RCLike.re (star v ⬝ᵥ v) := by
    have h1 : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
      push_cast; rfl
    rw [h1, RCLike.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ i))
  have hre : star v ⬝ᵥ v = (RCLike.re (star v ⬝ᵥ v) : 𝕜) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, map_sum]
    simp
  refine ⟨1 / √(RCLike.re (star v ⬝ᵥ v)), by positivity, ?_⟩
  simp only [star_smul, RCLike.star_def, RCLike.conj_ofReal, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [hre, ← mul_assoc]
  norm_cast
  field_simp
  rw [Real.sq_sqrt hpos.le]

/-! ### The commutation lemma -/

variable [DecidableEq ι]

/-- **The rotation step.** Let `Q` be an orthogonal projection of rank `m`, let `x` be a unit
vector in its range and `y` a unit vector in its kernel with `Re ⟨y, A x⟩ > 0`. Rotating `x`
slightly towards `y` produces an orthogonal projection of rank `m` with a larger value of
`Re tr(A ·)`. -/
theorem exists_rotation_gt {m : ℕ} {A Q : Matrix ι ι 𝕜} (hA : Aᴴ = A)
    (hQ : Q ∈ orthProjs 𝕜 ι m) {x y : ι → 𝕜} (hQx : Q *ᵥ x = x) (hQy : Q *ᵥ y = 0)
    (hxx : star x ⬝ᵥ x = 1) (hyy : star y ⬝ᵥ y = 1) (hxy : star x ⬝ᵥ y = 0)
    (hβ : 0 < RCLike.re (star y ⬝ᵥ (A *ᵥ x))) :
    ∃ Q' ∈ orthProjs 𝕜 ι m, RCLike.re (A * Q).trace < RCLike.re (A * Q').trace := by
  have hyx : star y ⬝ᵥ x = 0 := by rw [star_dotProduct, hxy, star_zero]
  set a := RCLike.re (star x ⬝ᵥ (A *ᵥ x))
  set b := RCLike.re (star y ⬝ᵥ (A *ᵥ y))
  set β := RCLike.re (star y ⬝ᵥ (A *ᵥ x))
  set s : ℝ := min (1 / 2) (β / (2 * (|b - a| + 1))) with hs_def
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hs2 : s * |b - a| ≤ β / 2 := by
    have h := min_le_right (1 / 2 : ℝ) (β / (2 * (|b - a| + 1)))
    rw [← hs_def] at h
    calc s * |b - a| ≤ β / (2 * (|b - a| + 1)) * |b - a| :=
          mul_le_mul_of_nonneg_right h (abs_nonneg _)
      _ ≤ β / (2 * (|b - a| + 1)) * (|b - a| + 1) := by
          gcongr; linarith
      _ = β / 2 := by field_simp
  set c : ℝ := (1 - s ^ 2) / (1 + s ^ 2) with hc_def
  set d : ℝ := 2 * s / (1 + s ^ 2) with hd_def
  have hsq : 0 < 1 + s ^ 2 := by positivity
  have hcd : c ^ 2 + d ^ 2 = 1 := by
    rw [hc_def, hd_def]
    field_simp
    ring
  set v := (c : 𝕜) • x + (d : 𝕜) • y with hv_def
  have hvv : star v ⬝ᵥ v = 1 := by
    rw [hv_def, dotProduct_add_smul, hxx, hyy, hxy, hyx]
    simp only [add_zero, mul_one, mul_zero]
    exact_mod_cast hcd
  -- the new projection `(Q - x xᴴ) + v vᴴ`
  have hE : IsOrthProj (Q - rk1 x) := isOrthProj_sub_rk1 hQ.1 hQx hxx
  have hEv : (Q - rk1 x) *ᵥ v = 0 := by
    rw [sub_mulVec, rk1, vecMulVec_mulVec, hv_def, mulVec_add, mulVec_smul,
      mulVec_smul, hQx, hQy, dotProduct_add, dotProduct_smul, dotProduct_smul, hxx, hxy]
    ext i
    simp
  have hQ' : (Q - rk1 x) + rk1 v ∈ orthProjs 𝕜 ι m := by
    refine ⟨hE.add (isOrthProj_rk1 hvv) (by rw [mul_rk1, hEv, zero_vecMulVec]), ?_⟩
    rw [trace_add, trace_sub, trace_rk1, trace_rk1, hxx, hvv, hQ.2]
    ring
  refine ⟨_, hQ', ?_⟩
  have hval : RCLike.re (A * ((Q - rk1 x) + rk1 v)).trace =
      RCLike.re (A * Q).trace - a + (c ^ 2 * a + 2 * c * d * β + d ^ 2 * b) := by
    rw [mul_add, mul_sub, trace_add, trace_sub, trace_mul_rk1, trace_mul_rk1,
      map_add, map_sub, hv_def, re_quad_add hA]
  rw [hval]
  have hc2 : c ^ 2 = 1 - d ^ 2 := by linarith
  have hd0 : 0 < d := by rw [hd_def]; positivity
  have hinner : 0 < d * (b - a) + 2 * c * β := by
    have hba : -(s * |b - a|) ≤ s * (b - a) := by
      have h1 := neg_abs_le (b - a)
      nlinarith
    have h34 : (3 : ℝ) / 4 ≤ 1 - s ^ 2 := by nlinarith
    have e : d * (b - a) + 2 * c * β = (2 * (s * (b - a)) + 2 * ((1 - s ^ 2) * β)) / (1 + s ^ 2) := by
      rw [hc_def, hd_def]
      field_simp
    rw [e]
    apply div_pos _ hsq
    nlinarith
  have : 0 < c ^ 2 * a + 2 * c * d * β + d ^ 2 * b - a := by
    have e : c ^ 2 * a + 2 * c * d * β + d ^ 2 * b - a = d * (d * (b - a) + 2 * c * β) := by
      rw [hc2]; ring
    rw [e]
    exact mul_pos hd0 hinner
  linarith

/-- **Maximizing projections commute.** If `Q` maximizes `Re tr(A P)` over the orthogonal
projections `P` of rank `m` and `A` is Hermitian, then `A Q = Q A`. -/
theorem commute_of_isMaxOn {m : ℕ} {A Q : Matrix ι ι 𝕜} (hA : Aᴴ = A)
    (hQ : Q ∈ orthProjs 𝕜 ι m)
    (hmax : ∀ Q' ∈ orthProjs 𝕜 ι m, RCLike.re (A * Q').trace ≤ RCLike.re (A * Q).trace) :
    A * Q = Q * A := by
  have hQh := hQ.1.herm
  have hQi := hQ.1.idem
  -- `1 - Q` is an orthogonal projection as well
  have hRh : (1 - Q)ᴴ = 1 - Q := by rw [conjTranspose_sub, conjTranspose_one, hQh]
  have hQR : Q * (1 - Q) = 0 := by rw [mul_sub, mul_one, hQi, sub_self]
  have hRR : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [sub_mul, one_mul, hQR, sub_zero]
  have key : (1 - Q) * A * Q = 0 := by
    by_contra hne
    obtain ⟨z, hz⟩ : ∃ z, ((1 - Q) * A * Q) *ᵥ z ≠ 0 := by
      by_contra! h
      refine hne (Matrix.toLin'.injective (LinearMap.ext fun z => ?_))
      simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
      exact h z
    -- the unit vector `x ∈ range Q`
    have hx0 : Q *ᵥ z ≠ 0 := by
      intro h0
      apply hz
      rw [← mulVec_mulVec, h0, mulVec_zero]
    obtain ⟨c₀, hc₀, hxx⟩ := exists_normalize hx0
    set x := (c₀ : 𝕜) • (Q *ᵥ z) with hx_def
    have hQx : Q *ᵥ x = x := by rw [hx_def, mulVec_smul, mulVec_mulVec, hQi]
    -- the unit vector `y ⊥ range Q`
    set y₀ := (1 - Q) *ᵥ (A *ᵥ x) with hy₀_def
    have hy₀ : y₀ ≠ 0 := by
      rw [hy₀_def, hx_def, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec]
      exact smul_ne_zero (by exact_mod_cast hc₀.ne') hz
    obtain ⟨c₁, hc₁, hyy⟩ := exists_normalize hy₀
    set y := (c₁ : 𝕜) • y₀ with hy_def
    have hQy : Q *ᵥ y = 0 := by
      rw [hy_def, hy₀_def, mulVec_smul, mulVec_mulVec, hQR, zero_mulVec, smul_zero]
    have hxy : star x ⬝ᵥ y = 0 := by
      rw [hy_def, hy₀_def, dotProduct_smul, dotProduct_mulVec_star, hRh]
      have : (1 - Q) *ᵥ x = 0 := by rw [sub_mulVec, one_mulVec, hQx, sub_self]
      rw [this, star_zero, zero_dotProduct, smul_zero]
    -- `Re ⟨y, A x⟩ > 0`
    have hβ : 0 < RCLike.re (star y ⬝ᵥ (A *ᵥ x)) := by
      have e1 : star y₀ ⬝ᵥ (A *ᵥ x) = star y₀ ⬝ᵥ y₀ := by
        rw [hy₀_def]
        symm
        rw [dotProduct_mulVec_star (1 - Q) ((1 - Q) *ᵥ (A *ᵥ x)) (A *ᵥ x), hRh, mulVec_mulVec,
          hRR]
      have e2 : star y ⬝ᵥ (A *ᵥ x) = (c₁ : 𝕜) * (star y₀ ⬝ᵥ y₀) := by
        rw [hy_def, star_smul, RCLike.star_def, RCLike.conj_ofReal, smul_dotProduct, e1,
          smul_eq_mul]
      have e3 : star y ⬝ᵥ y = (c₁ : 𝕜) ^ 2 * (star y₀ ⬝ᵥ y₀) := by
        rw [hy_def, star_smul, RCLike.star_def, RCLike.conj_ofReal, smul_dotProduct,
          dotProduct_smul, smul_eq_mul, smul_eq_mul]
        ring
      have e4 : RCLike.re (star y₀ ⬝ᵥ y₀) = 1 / c₁ ^ 2 := by
        have := congrArg RCLike.re (e3.symm.trans hyy)
        rw [RCLike.one_re] at this
        have h' : RCLike.re ((c₁ : 𝕜) ^ 2 * (star y₀ ⬝ᵥ y₀)) =
            c₁ ^ 2 * RCLike.re (star y₀ ⬝ᵥ y₀) := by
          rw [← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
        rw [h'] at this
        field_simp
        linarith
      rw [e2, RCLike.re_ofReal_mul, e4]
      positivity
    clear_value x y y₀
    obtain ⟨Q', hQ', hlt⟩ := exists_rotation_gt hA hQ hQx hQy hxx hyy hxy hβ
    exact absurd (hmax Q' hQ') (not_le.2 hlt)
  -- conclude from `(1 - Q) A Q = 0`
  have h1 : A * Q = Q * A * Q := by
    have : A * Q - Q * A * Q = 0 := by
      rw [← key, sub_mul, sub_mul, one_mul]
    exact sub_eq_zero.1 this
  have h2 : Q * A = Q * A * Q := by
    have := congrArg conjTranspose h1
    simp only [conjTranspose_mul, hA, hQh] at this
    rw [Matrix.mul_assoc]
    exact this
  rw [h1, ← h2]

end ProjectionConstants
