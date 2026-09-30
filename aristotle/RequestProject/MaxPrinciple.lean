import RequestProject.LengthArea

/-!
# A maximum principle for the chord length under curve shortening flow

Auxiliary results for Theorem 3.0.1 of the notes: at a pair of parameters `(x, y)` at which the
squared chord length `‖γ(y, t) - γ(x, t)‖²` is locally minimal (and non-zero), the chord length is
non-decreasing in time.
-/

open scoped ContDiff Real Topology
open Complex Set Filter

noncomputable section

namespace CSF

/-- Necessary second order condition at a local minimum of a real function of one variable. Auxiliary for the proof of Theorem 3.0.1 of the notes. -/
lemma second_deriv_nonneg_of_isLocalMin {f f' : ℝ → ℝ} {a f'' : ℝ} (hmin : IsLocalMin f a)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : HasDerivAt f' f'' a) : 0 ≤ f'' := by
  have h0 : f' a = 0 := hmin.hasDerivAt_eq_zero (hf a)
  by_contra hneg
  push_neg at hneg
  have hsl := hf'.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f' (a + t) - f' a) < 0 :=
    hsl.eventually (gt_mem_nhds hneg)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (a) ≤ f (a + t) := by
    have : Tendsto (fun t : ℝ => a + t) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      have h := (continuous_add_left a).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    exact this.eventually hmin
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hev.and hev2)
  have hu0 : 0 < u := hu
  set b := u / 2 with hbdef
  have hb : 0 < b := by positivity
  obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f f' (show a < a + b by linarith)
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
  have hξmem : ξ - a ∈ Ioo 0 u := ⟨by linarith [hξ.1], by linarith [hξ.2, hbdef]⟩
  have h1 := (hsub hξmem).1
  have h2 := (hsub (show b ∈ Ioo 0 u from ⟨hb, by simp only [b]; linarith⟩)).2
  simp only [h0, sub_zero, smul_eq_mul, add_sub_cancel] at h1
  have hpos : 0 < (ξ - a)⁻¹ := inv_pos.mpr hξmem.1
  have hneg' : f' ξ < 0 := by
    by_contra hc; push_neg at hc; nlinarith
  rw [hξ', add_sub_cancel_left, div_lt_iff₀ hb] at hneg'
  linarith

/-- Two unit vectors orthogonal to the same non-zero vector of the plane are parallel. Auxiliary for the proof of Theorem 3.0.1 of the notes. -/
lemma parallel_of_orthogonal {z a b : ℂ} (hz : z ≠ 0) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hza : inner ℝ z a = 0) (hzb : inner ℝ z b = 0) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ b = (σ : ℂ) * a := by
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hza hzb
  have ha2 : a.re * a.re + a.im * a.im = 1 := by
    have := Complex.normSq_eq_norm_sq a
    rw [ha, Complex.normSq_apply] at this; linarith
  have hb2 : b.re * b.re + b.im * b.im = 1 := by
    have := Complex.normSq_eq_norm_sq b
    rw [hb, Complex.normSq_apply] at this; linarith
  have hcross : a.re * b.im - a.im * b.re = 0 := by
    have h1 : z.re * (a.re * b.im - a.im * b.re) = 0 := by linear_combination b.im * hza - a.im * hzb
    have h2 : z.im * (a.re * b.im - a.im * b.re) = 0 := by linear_combination (-b.re) * hza + a.re * hzb
    by_contra hc
    apply hz
    apply Complex.ext
    · simpa using (mul_eq_zero.mp h1).resolve_right hc
    · simpa using (mul_eq_zero.mp h2).resolve_right hc
  refine ⟨a.re * b.re + a.im * b.im, ?_, ?_⟩
  · linear_combination (b.re * b.re + b.im * b.im) * ha2 + hb2
      - (a.re * b.im - a.im * b.re) * hcross
  · apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    · linear_combination (-b.re) * ha2 - a.im * hcross
    · linear_combination (-b.im) * ha2 + a.re * hcross

/-- Inner products with real multiples (auxiliary for Theorem 3.0.1 of the notes). -/
lemma inner_ofReal_mul (z w : ℂ) (r : ℝ) : inner ℝ z ((r : ℂ) * w) = r * inner ℝ z w := by
  rw [← Complex.real_smul, inner_smul_right]

variable {γ : ℝ × ℝ → ℂ} {a b : ℝ}

/-- `∂²γ/∂u²` paired with a vector orthogonal to the tangent. Uses the Serret–Frenet equations from the proof of Lemma 2 of the notes; auxiliary for Theorem 3.0.1. -/
lemma inner_pu_pu_of_orthogonal (h : IsCSF γ (univ ×ˢ Ioo a b)) {p : ℝ × ℝ}
    (hp : p ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ))) {z : ℂ} (hz : inner ℝ z (tangent γ p) = 0) :
    inner ℝ z (pu (pu γ) p) = speed γ p ^ 2 * curvature γ p * inner ℝ z (normal γ p) := by
  have hR := h.toRegular
  have hev : pu γ =ᶠ[𝓝 p] fun q => (speed γ q : ℂ) * tangent γ q := by
    filter_upwards [h.isOpen.mem_nhds hp] with q hq
    exact hR.pu_eq_speed_mul_tangent hq
  have e : pu (pu γ) p = pu (fun q => (speed γ q : ℂ) * tangent γ q) p :=
    Filter.EventuallyEq.lineDeriv_eq hev
  have hv := hR.diff hR.smooth_speed hp
  have hv' : DifferentiableAt ℝ (fun q => (speed γ q : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hv
  rw [e]
  simp only [pu]
  rw [ld_mul hv' (hR.diff hR.smooth_tangent hp), ld_ofReal hv]
  have hsf := hR.serret_frenet_tangent_u hp
  simp only [pu] at hsf
  rw [hsf, inner_add_right, inner_ofReal_mul, hz, mul_zero, zero_add,
    show (speed γ p : ℂ) * ((speed γ p : ℂ) * (curvature γ p : ℂ) * normal γ p) =
      ((speed γ p * speed γ p * curvature γ p : ℝ) : ℂ) * normal γ p by push_cast; ring,
    inner_ofReal_mul]
  ring

/-- **Maximum principle** for the chord: if the chord length `‖γ(y, t) - γ(x, t)‖` is non-zero
and locally minimal among pairs of parameters near `(x, y)`, then
`⟨γ(y) - γ(x), ∂γ/∂t(y) - ∂γ/∂t(x)⟩ ≥ 0`. This is the key step of the proof of Theorem 3.0.1 of the notes. -/
lemma chord_max_principle (h : IsCSF γ (univ ×ˢ Ioo a b)) {x y t : ℝ} (ht : t ∈ Ioo a b)
    (hne : γ (y, t) ≠ γ (x, t))
    (hmin : ∀ᶠ q in 𝓝 (x, y), ‖γ (y, t) - γ (x, t)‖ ≤ ‖γ (q.2, t) - γ (q.1, t)‖) :
    0 ≤ inner ℝ (γ (y, t) - γ (x, t)) (pt γ (y, t) - pt γ (x, t)) := by
  have hR := h.toRegular
  set z := γ (y, t) - γ (x, t) with hzdef
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  -- derivative facts along the lines
  have dγ : ∀ s, HasDerivAt (fun u => γ (u, t)) (pu γ (s, t)) s := fun s =>
    hasDerivAt_line_u (hR.diff hR.smooth (mem_strip ht))
  have dw : ∀ s, HasDerivAt (fun u => pu γ (u, t)) (pu (pu γ) (s, t)) s := fun s =>
    hasDerivAt_line_u (hR.diff hR.smooth_pu (mem_strip ht))
  -- the key one-dimensional computation along the direction `(α, β)`
  have key : ∀ α β : ℝ,
      inner ℝ z ((β : ℂ) * pu γ (y, t) - (α : ℂ) * pu γ (x, t)) = 0 ∧
      0 ≤ inner ℝ ((β : ℂ) * pu γ (y, t) - (α : ℂ) * pu γ (x, t))
            ((β : ℂ) * pu γ (y, t) - (α : ℂ) * pu γ (x, t)) +
          inner ℝ z ((β ^ 2 : ℝ) * pu (pu γ) (y, t) - (α ^ 2 : ℝ) * pu (pu γ) (x, t)) := by
    intro α β
    let c : ℝ → ℂ := fun τ => γ (y + β * τ, t) - γ (x + α * τ, t)
    let c' : ℝ → ℂ := fun τ => (β : ℂ) * pu γ (y + β * τ, t) - (α : ℂ) * pu γ (x + α * τ, t)
    let c'' : ℝ → ℂ := fun τ =>
      ((β ^ 2 : ℝ) : ℂ) * pu (pu γ) (y + β * τ, t) - ((α ^ 2 : ℝ) : ℂ) * pu (pu γ) (x + α * τ, t)
    have aff : ∀ (x₀ α₀ τ : ℝ), HasDerivAt (fun τ => x₀ + α₀ * τ) α₀ τ := fun x₀ α₀ τ => by
      simpa using ((hasDerivAt_id τ).const_mul α₀).const_add x₀
    have hc : ∀ τ, HasDerivAt c (c' τ) τ := by
      intro τ
      have h1 := (dγ (y + β * τ)).scomp τ (aff y β τ)
      have h2 := (dγ (x + α * τ)).scomp τ (aff x α τ)
      have := h1.sub h2
      simp only [Complex.real_smul] at this
      exact this
    have hc' : HasDerivAt c' (c'' 0) 0 := by
      have h1 := ((dw (y + β * 0)).scomp 0 (aff y β 0)).const_mul (β : ℂ)
      have h2 := ((dw (x + α * 0)).scomp 0 (aff x α 0)).const_mul (α : ℂ)
      have := h1.sub h2
      simp only [Complex.real_smul] at this
      convert this using 1
      simp only [c'', mul_zero, add_zero]
      push_cast; ring
    let φ : ℝ → ℝ := fun τ => inner ℝ (c τ) (c τ)
    let φ' : ℝ → ℝ := fun τ => inner ℝ (c τ) (c' τ) + inner ℝ (c' τ) (c τ)
    have hφ : ∀ τ, HasDerivAt φ (φ' τ) τ := fun τ => (hc τ).inner ℝ (hc τ)
    have hφ' : HasDerivAt φ' (inner ℝ (c 0) (c'' 0) + inner ℝ (c' 0) (c' 0) +
        (inner ℝ (c' 0) (c' 0) + inner ℝ (c'' 0) (c 0))) 0 := by
      have h1 := (hc 0).inner ℝ hc'
      have h2 := hc'.inner ℝ (hc 0)
      exact h1.add h2
    have hmin' : IsLocalMin φ 0 := by
      have htend : Tendsto (fun τ : ℝ => (x + α * τ, y + β * τ)) (𝓝 0) (𝓝 (x, y)) := by
        have : Continuous (fun τ : ℝ => (x + α * τ, y + β * τ)) := by fun_prop
        simpa using this.tendsto 0
      filter_upwards [htend.eventually hmin] with τ hτ
      simp only [φ, c, real_inner_self_eq_norm_sq, mul_zero, add_zero]
      exact pow_le_pow_left₀ (norm_nonneg _) hτ 2
    have h0 : c 0 = z := by simp [c, z]
    have hfirst : φ' 0 = 0 := hmin'.hasDerivAt_eq_zero (hφ 0)
    have hsecond := second_deriv_nonneg_of_isLocalMin hmin' hφ hφ'
    have ec' : c' 0 = (β : ℂ) * pu γ (y, t) - (α : ℂ) * pu γ (x, t) := by simp [c']
    have ec'' : c'' 0 = ((β ^ 2 : ℝ) : ℂ) * pu (pu γ) (y, t) - ((α ^ 2 : ℝ) : ℂ) * pu (pu γ) (x, t) := by
      simp [c'']
    have hf1 : inner ℝ (c 0) (c' 0) + inner ℝ (c' 0) (c 0) = 0 := hfirst
    have hs2 : 0 ≤ inner ℝ (c 0) (c'' 0) + inner ℝ (c' 0) (c' 0) +
        (inner ℝ (c' 0) (c' 0) + inner ℝ (c'' 0) (c 0)) := hsecond
    rw [h0, ec'] at hf1
    rw [h0, ec', ec''] at hs2
    rw [real_inner_comm z] at hf1
    rw [real_inner_comm z] at hs2
    constructor
    · linarith
    · linarith
  -- first order conditions: the chord is orthogonal to both tangents
  have hTx : inner ℝ z (tangent γ (x, t)) = 0 := by
    have := (key 1 0).1
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, zero_sub,
      inner_neg_right, neg_eq_zero] at this
    rw [hR.pu_eq_speed_mul_tangent (mem_strip ht), ← Complex.real_smul,
      inner_smul_right] at this
    exact (mul_eq_zero.mp this).resolve_left (hR.speed_ne (mem_strip ht))
  have hTy : inner ℝ z (tangent γ (y, t)) = 0 := by
    have := (key 0 1).1
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, sub_zero] at this
    rw [hR.pu_eq_speed_mul_tangent (mem_strip ht), ← Complex.real_smul,
      inner_smul_right] at this
    exact (mul_eq_zero.mp this).resolve_left (hR.speed_ne (mem_strip ht))
  obtain ⟨σ, hσ, hTyx⟩ := parallel_of_orthogonal hz (hR.norm_tangent (mem_strip ht))
    (hR.norm_tangent (mem_strip ht)) hTx hTy
  -- second order condition in the direction aligning the tangents
  have hvx := hR.speed_ne (mem_strip (u := x) ht)
  have hvy := hR.speed_ne (mem_strip (u := y) ht)
  have h2 := (key (speed γ (x, t))⁻¹ (σ / speed γ (y, t))).2
  have hc0 : (((σ / speed γ (y, t) : ℝ)) : ℂ) * pu γ (y, t) -
      (((speed γ (x, t))⁻¹ : ℝ) : ℂ) * pu γ (x, t) = 0 := by
    rw [hR.pu_eq_speed_mul_tangent (mem_strip ht), hR.pu_eq_speed_mul_tangent (mem_strip ht),
      hTyx]
    have hvx' : (speed γ (x, t) : ℂ) ≠ 0 := by exact_mod_cast hvx
    have hvy' : (speed γ (y, t) : ℂ) ≠ 0 := by exact_mod_cast hvy
    have hσ' : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
    push_cast
    field_simp
    linear_combination tangent γ (x, t) * hσ'
  rw [hc0, inner_zero_left, zero_add, inner_sub_right, ← Complex.real_smul,
    ← Complex.real_smul, inner_smul_right, inner_smul_right,
    inner_pu_pu_of_orthogonal h (mem_strip ht) hTx,
    inner_pu_pu_of_orthogonal h (mem_strip ht) hTy] at h2
  rw [h.flow _ (mem_strip ht), h.flow _ (mem_strip ht), inner_sub_right,
    ← Complex.real_smul, ← Complex.real_smul, inner_smul_right, inner_smul_right]
  have e1 : (σ / speed γ (y, t)) ^ 2 * (speed γ (y, t) ^ 2 * curvature γ (y, t) *
      inner ℝ z (normal γ (y, t))) = curvature γ (y, t) * inner ℝ z (normal γ (y, t)) := by
    field_simp; rw [hσ]; ring
  have e2 : (speed γ (x, t))⁻¹ ^ 2 * (speed γ (x, t) ^ 2 * curvature γ (x, t) *
      inner ℝ z (normal γ (x, t))) = curvature γ (x, t) * inner ℝ z (normal γ (x, t)) := by
    field_simp
  rw [e1, e2] at h2
  linarith

end CSF

end
