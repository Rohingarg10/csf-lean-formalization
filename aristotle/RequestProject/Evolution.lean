import RequestProject.Frenet

/-!
# Chapter 3: Lemmas 1–5 of the notes

Evolution equations for the speed, the unit tangent and normal vectors and the curvature of a
curve moving by curve shortening flow.
-/

open scoped ContDiff Real Topology
open Complex

noncomputable section

namespace CSF

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Inner products in an orthonormal frame `(T, I T)`. Auxiliary for the orthogonality arguments (`T · n = 0`) in the proofs of Lemmas 2 and 5 of the notes. -/
lemma inner_frame {T : ℂ} (hT : ‖T‖ = 1) (x₁ y₁ x₂ y₂ : ℝ) :
    inner ℝ ((x₁ : ℂ) * T + (y₁ : ℂ) * (I * T)) ((x₂ : ℂ) * T + (y₂ : ℂ) * (I * T)) =
      x₁ * x₂ + y₁ * y₂ := by
  have h2 : T.re * T.re + T.im * T.im = 1 := by
    have := Complex.normSq_eq_norm_sq T
    rw [hT, Complex.normSq_apply] at this
    linarith
  simp only [Complex.inner, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im]
  linear_combination (x₁ * x₂ + y₁ * y₂) * h2

/-- The partial derivative `∂f/∂u` is the derivative of `u ↦ f(u, t)`. Auxiliary, used for Lemma 1 of the notes. -/
lemma pu_eq_deriv (f : ℝ × ℝ → E) (p : ℝ × ℝ) :
    pu f p = deriv (fun u => f (u, p.2)) p.1 := by
  simp only [pu, lineDeriv]
  have : (fun τ : ℝ => f (p + τ • ((1 : ℝ), (0 : ℝ)))) = fun τ => (fun u => f (u, p.2)) (τ + p.1) := by
    funext τ; congr 1; ext <;> simp [add_comm]
  rw [this]
  simpa using deriv_comp_add_const (f := fun u => f (u, p.2)) (a := p.1) (x := 0)

/-- The partial derivative `∂f/∂t` is the derivative of `t ↦ f(u, t)`. Auxiliary, used for Lemma 6 of the notes. -/
lemma pt_eq_deriv (f : ℝ × ℝ → E) (p : ℝ × ℝ) :
    pt f p = deriv (fun t => f (p.1, t)) p.2 := by
  simp only [pt, lineDeriv]
  have : (fun τ : ℝ => f (p + τ • ((0 : ℝ), (1 : ℝ)))) = fun τ => (fun t => f (p.1, t)) (τ + p.2) := by
    funext τ; congr 1; ext <;> simp [add_comm]
  rw [this]
  simpa using deriv_comp_add_const (f := fun t => f (p.1, t)) (a := p.2) (x := 0)

/-- **Lemma 1** (first part of the proof): `∂s/∂u = ‖∂γ/∂u‖ = v`, where `s` is the arclength
parameter `s(u) = ∫₀ᵘ ‖∂γ/∂u‖ du'`. -/
theorem lemma1_arclength_hasDerivAt {γ : ℝ × ℝ → ℂ} {t : ℝ}
    (hcont : Continuous fun u' => speed γ (u', t)) (u : ℝ) :
    HasDerivAt (arclength γ t) (speed γ (u, t)) u :=
  intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- **Lemma 1.** Let `s` parametrize `γ` by arclength. Then as operators
`∂/∂s = (1/v) ∂/∂u`, where `v = ‖∂γ/∂u‖`.

Formally: if a quantity `f(u, t)` along the curve `γ(·, t)` is expressed as a function `g` of the
arclength parameter `s = s(u)`, i.e. `f(u, t) = g(s(u))`, then its derivative with respect to
arclength is `dg/ds (s(u)) = (1/v) ∂f/∂u (u, t) = CSF.ps γ f (u, t)`. -/
theorem lemma1_arclength_derivative {γ : ℝ × ℝ → ℂ} {t : ℝ}
    (hcont : Continuous fun u' => speed γ (u', t)) {f : ℝ × ℝ → E} {g : ℝ → E}
    (hfg : ∀ u', f (u', t) = g (arclength γ t u')) {u : ℝ}
    (hg : DifferentiableAt ℝ g (arclength γ t u)) (hv : speed γ (u, t) ≠ 0) :
    deriv g (arclength γ t u) = ps γ f (u, t) := by
  have h1 : HasDerivAt (fun u' => f (u', t)) (speed γ (u, t) • deriv g (arclength γ t u)) u := by
    have := hg.hasDerivAt.scomp u (lemma1_arclength_hasDerivAt hcont u)
    simpa [Function.comp_def, ← hfg] using this
  rw [ps, pu_eq_deriv, h1.deriv, smul_smul, inv_mul_cancel₀ hv, one_smul]

namespace IsCSF

variable {γ : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (h : IsCSF γ U)
include h

/-- The curve shortening flow equation (2.1) `∂γ/∂t = κ n` holds in a neighbourhood of each point (auxiliary for Lemmas 2–5 of the notes). -/
lemma pt_eventuallyEq {p : ℝ × ℝ} (hp : p ∈ U) :
    pt γ =ᶠ[𝓝 p] fun q => (curvature γ q : ℂ) * normal γ q := by
  filter_upwards [h.isOpen.mem_nhds hp] with q hq
  exact h.flow q hq

/-- The velocity `∂γ/∂t` of the flow is smooth (auxiliary for Lemmas 2–6 of the notes). -/
lemma smooth_pt : ContDiffOn ℝ ∞ (pt γ) U :=
  CSF.smooth_pt h.smooth h.isOpen

/-- `∂/∂t (∂γ/∂u) = ∂κ/∂u n - v κ² T`. This is the computation `∂/∂t (∂γ/∂u) = ∂/∂u (κ n) = ∂κ/∂u n - v κ² T` in the proof of Lemma 2 of the notes. -/
lemma pt_pu_gamma {p : ℝ × ℝ} (hp : p ∈ U) :
    pt (pu γ) p = ((pu (curvature γ) p : ℝ) : ℂ) * normal γ p
      - (speed γ p * curvature γ p ^ 2 : ℝ) * tangent γ p := by
  have hR := h.toRegular
  rw [pt_pu h.smooth h.isOpen hp]
  have e : pu (pt γ) p = pu (fun q => (curvature γ q : ℂ) * normal γ q) p :=
    Filter.EventuallyEq.lineDeriv_eq (h.pt_eventuallyEq hp)
  rw [e]
  have hk := hR.diff hR.smooth_curvature hp
  have hk' : DifferentiableAt ℝ (fun q => (curvature γ q : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hk
  simp only [pu] at *
  rw [ld_mul hk' (hR.diff hR.smooth_normal hp), ld_ofReal hk]
  have := hR.serret_frenet_normal_u hp
  simp only [pu] at this
  rw [this]
  push_cast
  ring

/-- **Lemma 2.** If `γ(u, t)` evolves under curve shortening flow, then `∂v/∂t = -κ² v`. -/
theorem lemma2_speed_evolution {p : ℝ × ℝ} (hp : p ∈ U) :
    pt (speed γ) p = -(curvature γ p) ^ 2 * speed γ p := by
  have hR := h.toRegular
  have h1 : pt (speed γ) p = inner ℝ (pu γ p) (pt (pu γ) p) / ‖pu γ p‖ :=
    ld_norm (hR.diff hR.smooth_pu hp) (h.regular p hp)
  rw [h1, h.pt_pu_gamma hp, hR.pu_eq_speed_mul_tangent hp]
  have hT := hR.norm_tangent hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hR.speed_pos hp), hT]
  have e1 : ((speed γ p : ℝ) : ℂ) * tangent γ p =
      ((speed γ p : ℝ) : ℂ) * tangent γ p + ((0 : ℝ) : ℂ) * (I * tangent γ p) := by simp
  have e2 : ((pu (curvature γ) p : ℝ) : ℂ) * normal γ p
      - (speed γ p * curvature γ p ^ 2 : ℝ) * tangent γ p =
      ((-(speed γ p * curvature γ p ^ 2) : ℝ) : ℂ) * tangent γ p
        + ((pu (curvature γ) p : ℝ) : ℂ) * (I * tangent γ p) := by
    simp only [normal]; push_cast; ring
  rw [e1, e2, inner_frame hT]
  have hv := hR.speed_ne hp
  field_simp
  ring

/-- **Lemma 3.** Under the CSF, as operators, `∂²/∂t∂s = ∂²/∂s∂t + κ² ∂/∂s`:
for every smooth function `f`, `∂/∂t (∂f/∂s) = ∂/∂s (∂f/∂t) + κ² ∂f/∂s`. -/
theorem lemma3_commutator {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) {p : ℝ × ℝ} (hp : p ∈ U) :
    pt (ps γ f) p = ps γ (pt f) p + (curvature γ p) ^ 2 • ps γ f p := by
  have hR := h.toRegular
  have hvi := hR.diff hR.smooth_speed_inv hp
  have hpf := hR.diff (CSF.smooth_pu hf h.isOpen) hp
  have e : ps γ f = fun q => (speed γ q)⁻¹ • pu f q := rfl
  rw [e]
  simp only [pt]
  rw [ld_smul hvi hpf, ld_inv (hR.diff hR.smooth_speed hp) (hR.speed_ne hp)]
  have h2 := h.lemma2_speed_evolution hp
  have h3 := pt_pu hf h.isOpen hp
  simp only [pt, pu] at h2 h3
  rw [h2, h3]
  simp only [ps, pu, smul_smul]
  have hv := hR.speed_ne hp
  rw [add_comm]
  congr 2
  field_simp

/-- **Lemma 4** (first part). If `γ(u, t)` evolves under curve shortening flow, then
`∂T/∂t = ∂κ/∂s n`. -/
theorem lemma4_tangent_evolution {p : ℝ × ℝ} (hp : p ∈ U) :
    pt (tangent γ) p = ((ps γ (curvature γ) p : ℝ) : ℂ) * normal γ p := by
  have hR := h.toRegular
  have e : tangent γ = ps γ γ := rfl
  rw [e, h.lemma3_commutator h.smooth hp]
  have e2 : ps γ (pt γ) p = ps γ (fun q => (curvature γ q : ℂ) * normal γ q) p := by
    simp only [ps]
    rw [show pu (pt γ) p = _ from Filter.EventuallyEq.lineDeriv_eq (h.pt_eventuallyEq hp)]
    rfl
  rw [e2, hR.ps_mul hR.smooth_curvature hR.smooth_normal hp, hR.serret_frenet_normal hp,
    ← e]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **Lemma 4** (second part). If `γ(u, t)` evolves under curve shortening flow, then
`∂n/∂t = -∂κ/∂s T`. -/
theorem lemma4_normal_evolution {p : ℝ × ℝ} (hp : p ∈ U) :
    pt (normal γ) p = -((ps γ (curvature γ) p : ℝ) : ℂ) * tangent γ p := by
  have hR := h.toRegular
  have e : normal γ = fun q => I * tangent γ q := rfl
  rw [e]
  simp only [pt]
  rw [ld_const_mul I (hR.diff hR.smooth_tangent hp)]
  have := h.lemma4_tangent_evolution hp
  simp only [pt] at this
  rw [this, normal]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Lemma 5.** The curvature changes with time following the equation
`∂κ/∂t = ∂²κ/∂s² + κ³`. -/
theorem lemma5_curvature_evolution {p : ℝ × ℝ} (hp : p ∈ U) :
    pt (curvature γ) p = ps γ (ps γ (curvature γ)) p + (curvature γ p) ^ 3 := by
  have hR := h.toRegular
  have e : curvature γ = fun q => inner ℝ (ps γ (tangent γ) q) (normal γ q) := rfl
  have hsT := hR.smooth_ps hR.smooth_tangent
  have hk := hR.smooth_curvature
  have hsk := hR.smooth_ps hk
  conv_lhs => rw [e]
  simp only [pt]
  rw [ld_inner (hR.diff hsT hp) (hR.diff hR.smooth_normal hp)]
  have h1 := h.lemma3_commutator hR.smooth_tangent hp
  have h2 := h.lemma4_normal_evolution hp
  simp only [pt] at h1 h2
  rw [h1, h2]
  -- `∂/∂s (∂T/∂t) = ∂/∂s (∂κ/∂s n)`
  have e3 : ps γ (pt (tangent γ)) p =
      ps γ (fun q => ((ps γ (curvature γ) q : ℝ) : ℂ) * normal γ q) p := by
    simp only [ps]
    congr 1
    show lineDeriv ℝ _ _ _ = lineDeriv ℝ _ _ _
    apply Filter.EventuallyEq.lineDeriv_eq
    filter_upwards [h.isOpen.mem_nhds hp] with q hq
    exact h.lemma4_tangent_evolution hq
  rw [e3, hR.ps_mul hsk hR.smooth_normal hp, hR.serret_frenet_normal hp,
    hR.serret_frenet_tangent hp]
  have hT := hR.norm_tangent hp
  simp only [normal, Complex.real_smul]
  have h2' : (tangent γ p).re * (tangent γ p).re + (tangent γ p).im * (tangent γ p).im = 1 := by
    have := Complex.normSq_eq_norm_sq (tangent γ p)
    rw [hT, Complex.normSq_apply] at this
    linarith
  generalize tangent γ p = T at h2' ⊢
  generalize ps γ (ps γ (curvature γ)) p = a
  generalize ps γ (curvature γ) p = b
  generalize curvature γ p = k
  simp only [Complex.inner, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im]
  linear_combination (a + k ^ 3) * h2'

end IsCSF

end CSF

end
