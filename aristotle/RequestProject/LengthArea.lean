import RequestProject.Evolution

/-!
# Chapter 3: Lemma 6 of the notes (evolution of length and enclosed area)
-/

open scoped ContDiff Real Topology
open Complex Set

noncomputable section

namespace CSF

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section lines

variable {a b : ℝ}

/-- Points of the time strip `ℝ × (a, b)` (auxiliary for Lemma 6 of the notes). -/
lemma mem_strip {u t : ℝ} (ht : t ∈ Ioo a b) : (u, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
  ⟨mem_univ _, ht⟩

/-- The time strip `ℝ × (a, b)` is open (auxiliary for Lemma 6 of the notes). -/
lemma isOpen_strip : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
  isOpen_univ.prod isOpen_Ioo

omit [NormedSpace ℝ E] in
/-- Continuity along the lines `t = const` (auxiliary for Lemma 6 of the notes). -/
lemma continuous_line_u {F : ℝ × ℝ → E} (hF : ContinuousOn F (univ ×ˢ Ioo a b)) {t : ℝ}
    (ht : t ∈ Ioo a b) : Continuous fun u => F (u, t) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact ((hF.continuousAt (isOpen_strip.mem_nhds (mem_strip ht))).comp
    (f := fun u : ℝ => (u, t)) (by fun_prop))

/-- `∂F/∂u` is the derivative of `u ↦ F(u, t)` at points of differentiability (auxiliary for Lemma 6 of the notes). -/
lemma hasDerivAt_line_u {F : ℝ × ℝ → E} {u t : ℝ} (hF : DifferentiableAt ℝ F (u, t)) :
    HasDerivAt (fun u => F (u, t)) (pu F (u, t)) u := by
  have hd : DifferentiableAt ℝ (fun u => F (u, t)) u :=
    hF.comp u ((differentiableAt_id).prodMk (differentiableAt_const t))
  rw [pu_eq_deriv]
  exact hd.hasDerivAt

/-- `∂F/∂t` is the derivative of `t ↦ F(u, t)` at points of differentiability (auxiliary for Lemma 6 of the notes). -/
lemma hasDerivAt_line_t {F : ℝ × ℝ → E} {u t : ℝ} (hF : DifferentiableAt ℝ F (u, t)) :
    HasDerivAt (fun t => F (u, t)) (pt F (u, t)) t := by
  have hd : DifferentiableAt ℝ (fun t => F (u, t)) t :=
    hF.comp t ((differentiableAt_const u).prodMk differentiableAt_id)
  rw [pt_eq_deriv]
  exact hd.hasDerivAt

/-- Differentiation under the integral sign. Used for `dL/dt = ∫ ∂v/∂t du` and for `dA/dt` in the proof of Lemma 6 of the notes. -/
lemma hasDerivAt_integral_pt {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (c d : ℝ) :
    HasDerivAt (fun t => ∫ u in c..d, F (u, t)) (∫ u in c..d, pt F (u, t)) t := by
  obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, Icc (t - δ) (t + δ) ⊆ Ioo a b := by
    refine ⟨min (t - a) (b - t) / 2, half_pos (lt_min (sub_pos.2 ht.1) (sub_pos.2 ht.2)), ?_⟩
    intro x hx
    have h1 := min_le_left (t - a) (b - t)
    have h2 := min_le_right (t - a) (b - t)
    have := ht.1; have := ht.2
    constructor <;> linarith [hx.1, hx.2]
  have hFt : ContinuousOn (pt F) (univ ×ˢ Ioo a b) :=
    (CSF.smooth_pt hF isOpen_strip).continuousOn
  have hK : IsCompact (uIcc c d ×ˢ Icc (t - δ) (t + δ)) := isCompact_uIcc.prod isCompact_Icc
  have hKs : uIcc c d ×ˢ Icc (t - δ) (t + δ) ⊆ univ ×ˢ Ioo a b :=
    prod_mono (subset_univ _) hδs
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hFt.mono hKs)
  have hs : Icc (t - δ) (t + δ) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (F := fun x u => F (u, x)) (F' := fun x u => pt F (u, x))
    (bound := fun _ => M) (a := c) (b := d) (x₀ := t) hs ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact (continuous_line_u hF.continuousOn hx).aestronglyMeasurable
  · exact (continuous_line_u hF.continuousOn ht).intervalIntegrable _ _
  · exact (continuous_line_u hFt ht).aestronglyMeasurable
  · refine MeasureTheory.ae_of_all _ fun u hu x hx => hM _ ⟨?_, hx⟩
    exact uIoc_subset_uIcc hu
  · exact intervalIntegrable_const
  · refine MeasureTheory.ae_of_all _ fun u _ x hx => ?_
    exact hasDerivAt_line_t (differentiableAt_of_smooth hF isOpen_strip (mem_strip (hδs hx)))

end lines

section lemma6

variable {γ : ℝ × ℝ → ℂ} {a b : ℝ}

/-- **Lemma 6 (i).** Let `γ` be a closed curve evolving by curve shortening flow for times
`t ∈ (a, b)`, and let `L(t)` be the length of `γ_t`. Then
`dL/dt = -∫_{γ_t} κ² ds = -∫₀^{2π} κ² v du`. -/
theorem lemma6_length_evolution (h : IsCSF γ (univ ×ˢ Ioo a b)) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (length γ)
      (-∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) ^ 2 * speed γ (u, t)) t := by
  have hR := h.toRegular
  have := hasDerivAt_integral_pt hR.smooth_speed ht 0 (2 * π)
  have e : (∫ u in (0 : ℝ)..2 * π, pt (speed γ) (u, t)) =
      -∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) ^ 2 * speed γ (u, t) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [h.lemma2_speed_evolution (mem_strip ht)]
    ring
  rw [e] at this
  exact this

/-- Pointwise identity used in the proof of Lemma 6 (ii): the time derivative of the integrand
of the area is a `u`-derivative plus `-2 κ v`. This encodes the integration by parts step in the proof of Lemma 6 (ii) of the notes. -/
lemma area_integrand_pt (h : IsCSF γ (univ ×ˢ Ioo a b)) {p : ℝ × ℝ}
    (hp : p ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ))) :
    pt (fun q => (γ q).re * (pu γ q).im - (γ q).im * (pu γ q).re) p =
      pu (fun q => (γ q).re * (pt γ q).im - (γ q).im * (pt γ q).re) p
        - 2 * (curvature γ p * speed γ p) := by
  have hR := h.toRegular
  have hU := h.isOpen
  have dγ := hR.diff hR.smooth hp
  have dw := hR.diff hR.smooth_pu hp
  have dg := hR.diff h.smooth_pt hp
  have re_d : ∀ {f : ℝ × ℝ → ℂ}, DifferentiableAt ℝ f p →
      DifferentiableAt ℝ (fun q => (f q).re) p := fun hf =>
    Complex.reCLM.differentiableAt.comp p hf
  have im_d : ∀ {f : ℝ × ℝ → ℂ}, DifferentiableAt ℝ f p →
      DifferentiableAt ℝ (fun q => (f q).im) p := fun hf =>
    Complex.imCLM.differentiableAt.comp p hf
  have ld_re : ∀ {f : ℝ × ℝ → ℂ} (e : ℝ × ℝ), DifferentiableAt ℝ f p →
      lineDeriv ℝ (fun q => (f q).re) p e = (lineDeriv ℝ f p e).re := by
    intro f e hf
    have hh := (Complex.reCLM.hasFDerivAt.comp p hf.hasFDerivAt).hasLineDerivAt e
    rw [show (fun q => (f q).re) = Complex.reCLM ∘ f from rfl, hh.lineDeriv,
      hf.lineDeriv_eq_fderiv]
    simp
  have ld_im : ∀ {f : ℝ × ℝ → ℂ} (e : ℝ × ℝ), DifferentiableAt ℝ f p →
      lineDeriv ℝ (fun q => (f q).im) p e = (lineDeriv ℝ f p e).im := by
    intro f e hf
    have hh := (Complex.imCLM.hasFDerivAt.comp p hf.hasFDerivAt).hasLineDerivAt e
    rw [show (fun q => (f q).im) = Complex.imCLM ∘ f from rfl, hh.lineDeriv,
      hf.lineDeriv_eq_fderiv]
    simp
  have d1 : DifferentiableAt ℝ (fun q => (γ q).re * (pu γ q).im) p := (re_d dγ).mul (im_d dw)
  have d2 : DifferentiableAt ℝ (fun q => (γ q).im * (pu γ q).re) p := (im_d dγ).mul (re_d dw)
  have d3 : DifferentiableAt ℝ (fun q => (γ q).re * (pt γ q).im) p := (re_d dγ).mul (im_d dg)
  have d4 : DifferentiableAt ℝ (fun q => (γ q).im * (pt γ q).re) p := (im_d dγ).mul (re_d dg)
  change lineDeriv ℝ (fun q => (γ q).re * (pu γ q).im - (γ q).im * (pu γ q).re) p (0, 1) =
    lineDeriv ℝ (fun q => (γ q).re * (pt γ q).im - (γ q).im * (pt γ q).re) p (1, 0) - _
  rw [ld_sub d1 d2, ld_sub d3 d4,
    ld_rmul (re_d dγ) (im_d dw), ld_rmul (im_d dγ) (re_d dw),
    ld_rmul (re_d dγ) (im_d dg), ld_rmul (im_d dγ) (re_d dg),
    ]
  simp only [ld_re (1, 0) dγ, ld_im (1, 0) dγ, ld_re (0, 1) dγ, ld_im (0, 1) dγ,
    ld_re (0, 1) dw, ld_im (0, 1) dw, ld_re (1, 0) dg, ld_im (1, 0) dg]
  have hc : lineDeriv ℝ (pu γ) p (0, 1) = lineDeriv ℝ (pt γ) p (1, 0) := pt_pu h.smooth hU hp
  rw [hc]
  simp only [show lineDeriv ℝ γ p (0, 1) = pt γ p from rfl,
    show lineDeriv ℝ γ p (1, 0) = pu γ p from rfl]
  rw [h.flow p hp, hR.pu_eq_speed_mul_tangent hp]
  simp only [normal, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  have hT := hR.norm_tangent hp
  have h2 : (tangent γ p).re * (tangent γ p).re + (tangent γ p).im * (tangent γ p).im = 1 := by
    have := Complex.normSq_eq_norm_sq (tangent γ p)
    rw [hT, Complex.normSq_apply] at this
    linarith
  linear_combination (-2 * curvature γ p * speed γ p) * h2

/-- The velocity `∂γ/∂t` of a closed curve is again `2π`-periodic in `u`. Auxiliary for Lemma 6 (ii) of the notes. -/
lemma pt_periodic (hcl : IsClosedCurve γ) (u t : ℝ) : pt γ (u + 2 * π, t) = pt γ (u, t) := by
  rw [pt_eq_deriv, pt_eq_deriv]
  simp only
  congr 1
  funext s
  exact hcl u s

/-- **Lemma 6 (ii)**, main computation: if `γ` is a closed curve evolving by curve shortening
flow, the enclosed area `A(t)` satisfies `dA/dt = -∫_{γ_t} κ ds = -∫₀^{2π} κ v du`. -/
theorem lemma6_area_evolution_total_curvature (h : IsCSF γ (univ ×ˢ Ioo a b))
    (hcl : IsClosedCurve γ) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (enclosedArea γ)
      (-∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) * speed γ (u, t)) t := by
  have hR := h.toRegular
  set F : ℝ × ℝ → ℝ := fun q => (γ q).re * (pu γ q).im - (γ q).im * (pu γ q).re with hFdef
  set G : ℝ × ℝ → ℝ := fun q => (γ q).re * (pt γ q).im - (γ q).im * (pt γ q).re with hGdef
  have reS : ∀ {f : ℝ × ℝ → ℂ}, ContDiffOn ℝ ∞ f (univ ×ˢ Ioo a b) →
      ContDiffOn ℝ ∞ (fun q => (f q).re) (univ ×ˢ Ioo a b) := fun hf =>
    Complex.reCLM.contDiff.comp_contDiffOn hf
  have imS : ∀ {f : ℝ × ℝ → ℂ}, ContDiffOn ℝ ∞ f (univ ×ˢ Ioo a b) →
      ContDiffOn ℝ ∞ (fun q => (f q).im) (univ ×ˢ Ioo a b) := fun hf =>
    Complex.imCLM.contDiff.comp_contDiffOn hf
  have hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo a b) :=
    ((reS hR.smooth).mul (imS hR.smooth_pu)).sub ((imS hR.smooth).mul (reS hR.smooth_pu))
  have hG : ContDiffOn ℝ ∞ G (univ ×ˢ Ioo a b) :=
    ((reS hR.smooth).mul (imS h.smooth_pt)).sub ((imS hR.smooth).mul (reS h.smooth_pt))
  have hkv : ContinuousOn (fun q => curvature γ q * speed γ q) (univ ×ˢ Ioo a b) :=
    hR.smooth_curvature.continuousOn.mul hR.smooth_speed.continuousOn
  have hpuG : ContinuousOn (pu G) (univ ×ˢ Ioo a b) :=
    (CSF.smooth_pu hG isOpen_strip).continuousOn
  have hint : (∫ u in (0 : ℝ)..2 * π, pu G (u, t)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => G (u, t))
      (fun u _ => hasDerivAt_line_u
        (differentiableAt_of_smooth hG isOpen_strip (mem_strip ht)))
      ((continuous_line_u hpuG ht).intervalIntegrable _ _)]
    have := hcl 0 t
    have h2 := pt_periodic hcl 0 t
    simp only [hGdef, zero_add] at this h2 ⊢
    rw [this, h2, sub_self]
  have hd := (hasDerivAt_integral_pt hF ht 0 (2 * π)).const_mul (1 / 2 : ℝ)
  have e : (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..2 * π, pt F (u, t)) =
      -∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) * speed γ (u, t) := by
    have e1 : (∫ u in (0 : ℝ)..2 * π, pt F (u, t)) =
        ∫ u in (0 : ℝ)..2 * π, (pu G (u, t) - 2 * (curvature γ (u, t) * speed γ (u, t))) :=
      intervalIntegral.integral_congr fun u _ => area_integrand_pt h (mem_strip ht)
    rw [e1, intervalIntegral.integral_sub ((continuous_line_u hpuG ht).intervalIntegrable _ _)
      ((show Continuous (fun u => 2 * (curvature γ (u, t) * speed γ (u, t))) from
        continuous_const.mul (continuous_line_u hkv ht)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hint]
    ring
  rw [e] at hd
  exact hd

/-- **Lemma 6 (ii).** Let `γ` be a closed embedded curve which evolves by curve shortening flow,
and let `A(t)` be the area it encloses, with `n` the inward pointing normal. Then
`dA/dt = -2π`.

In the notes, the last step "since each `γ_t` is a closed curve, `∫_{γ_t} κ ds = 2π`" is an
application of Hopf's Umlaufsatz (the total curvature of a positively oriented simple closed
curve equals `2π`). That theorem is not proved in the notes and is not available in Mathlib,
so it enters this statement as the explicit hypothesis `htotal`
(the rotation index of `γ_t` is `1`). -/
theorem lemma6_area_evolution (h : IsCSF γ (univ ×ˢ Ioo a b)) (hcl : IsClosedCurve γ)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (htotal : ∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) * speed γ (u, t) = 2 * π) :
    HasDerivAt (enclosedArea γ) (-(2 * π)) t := by
  have := lemma6_area_evolution_total_curvature h hcl ht
  rwa [htotal] at this

end lemma6

end CSF

end
