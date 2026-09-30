import RequestProject.LengthArea

/-!
# Chapter 3: the maximal existence time `T = A₀ / 2π`

Formalization of the paragraph following Lemma 6 in the notes.
-/

open scoped ContDiff Real Topology
open Complex Set Filter

noncomputable section

namespace CSF

variable {γ : ℝ × ℝ → ℂ} {T₀ : ℝ}

/-- Continuity of `t ↦ ∫₀^{2π} F(u, t) du` on `[0, T₀)`. Auxiliary for the remark after Lemma 6 of the notes. -/
lemma continuousOn_integral_Ico {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F (univ ×ˢ Ico 0 T₀)) :
    ContinuousOn (fun t => ∫ u in (0 : ℝ)..2 * π, F (u, t)) (Ico 0 T₀) := by
  rw [continuousOn_iff_continuous_restrict]
  let f : Ico (0 : ℝ) T₀ → ℝ → ℝ := fun x u => F (u, x)
  have hf : Continuous (Function.uncurry f) := by
    have : Function.uncurry f = F ∘ fun z : Ico (0 : ℝ) T₀ × ℝ => (z.2, (z.1 : ℝ)) := rfl
    rw [this]
    refine hF.comp_continuous (by fun_prop) fun z => ⟨mem_univ _, z.1.2⟩
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 (2 * π)

/-- Under the hypotheses of the remark after Lemma 6, the enclosed area decreases linearly:
`A(t) = A(0) - 2π t` for `t ∈ [0, T₀)`. Part of the remark after Lemma 6 of the notes. -/
theorem area_linear_decay (h : IsCSF γ (univ ×ˢ Ioo 0 T₀)) (hcl : IsClosedCurve γ)
    (hc0 : ContinuousOn γ (univ ×ˢ Ico 0 T₀)) (hc1 : ContinuousOn (pu γ) (univ ×ˢ Ico 0 T₀))
    (htotal : ∀ t ∈ Ioo 0 T₀,
      ∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) * speed γ (u, t) = 2 * π) :
    ∀ t ∈ Ico 0 T₀, enclosedArea γ t = enclosedArea γ 0 - 2 * π * t := by
  have hAc : ContinuousOn (enclosedArea γ) (Ico 0 T₀) := by
    have hF : ContinuousOn (fun q => (γ q).re * (pu γ q).im - (γ q).im * (pu γ q).re)
        (univ ×ˢ Ico 0 T₀) :=
      ((Complex.continuous_re.comp_continuousOn hc0).mul
        (Complex.continuous_im.comp_continuousOn hc1)).sub
      ((Complex.continuous_im.comp_continuousOn hc0).mul
        (Complex.continuous_re.comp_continuousOn hc1))
    exact continuousOn_const.mul (continuousOn_integral_Ico hF)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0; ring
  set g : ℝ → ℝ := fun s => enclosedArea γ s + 2 * π * s
  have hgc : ContinuousOn g (Icc 0 t) :=
    (hAc.mono (Icc_subset_Ico_right ht.2)).add (continuousOn_const.mul continuousOn_id)
  have hgd : ∀ s ∈ Ioo 0 t, HasDerivAt g 0 s := by
    intro s hs
    have hs' : s ∈ Ioo 0 T₀ := ⟨hs.1, hs.2.trans ht.2⟩
    have := (lemma6_area_evolution h hcl hs' (htotal s hs')).add
      ((hasDerivAt_id s).const_mul (2 * π))
    simpa using this
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope g (fun _ => 0) hpos hgc hgd
  have : g t = g 0 := by
    have hne : t - 0 ≠ 0 := by linarith
    field_simp at hc'
    linarith
  simp only [g] at this
  linarith

/-- **Remark after Lemma 6 (the flow cannot exist beyond `T = A₀/2π`).** Since the area
enclosed by a curve is non-negative and `dA/dt = -2π`, a curve shortening flow of closed
embedded curves defined on `[0, T₀)` must have `T₀ ≤ A₀ / 2π`, where `A₀` is the area enclosed
by the initial curve.

As in `CSF.lemma6_area_evolution`, the rotation index condition `htotal` (Hopf's Umlaufsatz
for the positively oriented embedded curves `γ_t`) is an explicit hypothesis, as is the
non-negativity `harea` of the enclosed area. The flow is assumed smooth for `t ∈ (0, T₀)`, and
`γ`, `∂γ/∂u` are assumed continuous up to `t = 0`. -/
theorem maximal_time_le (h : IsCSF γ (univ ×ˢ Ioo 0 T₀)) (hcl : IsClosedCurve γ)
    (hc0 : ContinuousOn γ (univ ×ˢ Ico 0 T₀)) (hc1 : ContinuousOn (pu γ) (univ ×ˢ Ico 0 T₀))
    (htotal : ∀ t ∈ Ioo 0 T₀,
      ∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) * speed γ (u, t) = 2 * π)
    (hT₀ : 0 < T₀) (harea : ∀ t ∈ Ico 0 T₀, 0 ≤ enclosedArea γ t) :
    T₀ ≤ enclosedArea γ 0 / (2 * π) := by
  have hlin := area_linear_decay h hcl hc0 hc1 htotal
  have hA0 : 0 ≤ enclosedArea γ 0 := harea 0 ⟨le_rfl, hT₀⟩
  by_contra hlt
  push_neg at hlt
  set t := (enclosedArea γ 0 / (2 * π) + T₀) / 2
  have h2π : 0 < 2 * π := by positivity
  have hq : 0 ≤ enclosedArea γ 0 / (2 * π) := div_nonneg hA0 h2π.le
  have ht : t ∈ Ico 0 T₀ := ⟨by positivity, by simp only [t]; linarith⟩
  have h1 := harea t ht
  rw [hlin t ht] at h1
  have h3 : enclosedArea γ 0 / (2 * π) < t := by simp only [t]; linarith
  rw [div_lt_iff₀ h2π] at h3
  linarith

/-- **Remark after Lemma 6 (the maximal time is `T = A₀/2π`).** If moreover the flow exists
until the curve shrinks to a point, at which point it has zero area (i.e. `A(t) → 0` as
`t → T₀⁻`), then `T₀ = A₀ / 2π`. -/
theorem maximal_time_eq (h : IsCSF γ (univ ×ˢ Ioo 0 T₀)) (hcl : IsClosedCurve γ)
    (hc0 : ContinuousOn γ (univ ×ˢ Ico 0 T₀)) (hc1 : ContinuousOn (pu γ) (univ ×ˢ Ico 0 T₀))
    (htotal : ∀ t ∈ Ioo 0 T₀,
      ∫ u in (0 : ℝ)..2 * π, curvature γ (u, t) * speed γ (u, t) = 2 * π)
    (hT₀ : 0 < T₀) (hlim : Tendsto (enclosedArea γ) (𝓝[<] T₀) (𝓝 0)) :
    T₀ = enclosedArea γ 0 / (2 * π) := by
  have hlin := area_linear_decay h hcl hc0 hc1 htotal
  have hev : (fun t => enclosedArea γ 0 - 2 * π * t) =ᶠ[𝓝[<] T₀] enclosedArea γ := by
    filter_upwards [Ioo_mem_nhdsLT hT₀] with t ht
    exact (hlin t ⟨ht.1.le, ht.2⟩).symm
  have h2 : Tendsto (fun t => enclosedArea γ 0 - 2 * π * t) (𝓝[<] T₀)
      (𝓝 (enclosedArea γ 0 - 2 * π * T₀)) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).tendsto T₀).mono_left
      nhdsWithin_le_nhds
  have h3 := tendsto_nhds_unique (h2.congr' hev) hlim
  have h2π : 0 < 2 * π := by positivity
  field_simp
  linarith

end CSF

end
