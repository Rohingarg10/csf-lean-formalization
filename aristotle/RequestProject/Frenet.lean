import RequestProject.Calculus

/-!
# Frenet frame along a regular smooth family of curves

Smoothness of the speed, tangent, normal and curvature, and the Serret–Frenet equations
(used in the proof of Lemma 2 of the notes).
-/

open scoped ContDiff Real Topology
open Complex

noncomputable section

namespace CSF

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth regular family of curves on an open set `U`. A regular smooth family of curves, the setting of Lemmas 1–5 of the notes. -/
structure IsRegularFamily (γ : ℝ × ℝ → ℂ) (U : Set (ℝ × ℝ)) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ ∞ γ U
  regular : ∀ p ∈ U, pu γ p ≠ 0

/-- A curve shortening flow is in particular a smooth regular family of curves (auxiliary). -/
lemma IsCSF.toRegular {γ : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (h : IsCSF γ U) :
    IsRegularFamily γ U := ⟨h.isOpen, h.smooth, h.regular⟩

namespace IsRegularFamily

variable {γ : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (h : IsRegularFamily γ U)
include h

/-- The speed `v = ‖∂γ/∂u‖` of a regular family is positive (so that `1/v` in Lemma 1 of the notes makes sense). -/
lemma speed_pos {p : ℝ × ℝ} (hp : p ∈ U) : 0 < speed γ p :=
  norm_pos_iff.mpr (h.regular p hp)

/-- The speed `v` of a regular family is non-zero (auxiliary). -/
lemma speed_ne {p : ℝ × ℝ} (hp : p ∈ U) : speed γ p ≠ 0 := (h.speed_pos hp).ne'

/-- `∂γ/∂u` is smooth (auxiliary). -/
lemma smooth_pu : ContDiffOn ℝ ∞ (pu γ) U := CSF.smooth_pu h.smooth h.isOpen

/-- The speed `v` is smooth (auxiliary). -/
lemma smooth_speed : ContDiffOn ℝ ∞ (speed γ) U := fun p hp =>
  ((h.smooth_pu.contDiffAt (h.isOpen.mem_nhds hp)).norm ℝ (h.regular p hp)).contDiffWithinAt

/-- `1/v` is smooth (auxiliary). -/
lemma smooth_speed_inv : ContDiffOn ℝ ∞ (fun q => (speed γ q)⁻¹) U :=
  h.smooth_speed.inv fun _ hp => h.speed_ne hp

/-- The arclength derivative `∂f/∂s` of Lemma 1 of the notes is smooth when `f` is (auxiliary). -/
lemma smooth_ps {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (ps γ f) U :=
  h.smooth_speed_inv.smul (CSF.smooth_pu hf h.isOpen)

/-- The unit tangent `T` is smooth (auxiliary). -/
lemma smooth_tangent : ContDiffOn ℝ ∞ (tangent γ) U := h.smooth_ps h.smooth

/-- The unit normal `n` is smooth (auxiliary). -/
lemma smooth_normal : ContDiffOn ℝ ∞ (normal γ) U :=
  contDiffOn_const.mul h.smooth_tangent

/-- The curvature `κ` is smooth (auxiliary). -/
lemma smooth_curvature : ContDiffOn ℝ ∞ (curvature γ) U :=
  (h.smooth_ps h.smooth_tangent).inner ℝ h.smooth_normal

/-- Smooth functions are differentiable at points of the (open) domain (auxiliary). -/
lemma diff {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) {p : ℝ × ℝ} (hp : p ∈ U) :
    DifferentiableAt ℝ f p := differentiableAt_of_smooth hf h.isOpen hp

/-- Arclength derivative of a product (real function times complex function). Product rule for `∂/∂s`, used in the proofs of Lemmas 4 and 5 of the notes. -/
lemma ps_mul {a : ℝ × ℝ → ℝ} {b : ℝ × ℝ → ℂ} (ha : ContDiffOn ℝ ∞ a U)
    (hb : ContDiffOn ℝ ∞ b U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ps γ (fun q => (a q : ℂ) * b q) p = ((ps γ a p : ℝ) : ℂ) * b p + a p * ps γ b p := by
  have hda := h.diff ha hp
  have hdb := h.diff hb hp
  simp only [ps, pu]
  have hda' : DifferentiableAt ℝ (fun q => (a q : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hda
  rw [ld_mul hda' hdb, ld_ofReal hda]
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- Arclength derivative of `c * f` for a constant `c`, e.g. `∂n/∂s = I ∂T/∂s` (auxiliary for the Serret–Frenet equations used in Lemma 2 of the notes). -/
lemma ps_const_mul (c : ℂ) {b : ℝ × ℝ → ℂ} (hb : ContDiffOn ℝ ∞ b U) {p : ℝ × ℝ}
    (hp : p ∈ U) : ps γ (fun q => c * b q) p = c * ps γ b p := by
  simp only [ps, pu]
  rw [ld_const_mul c (h.diff hb hp)]
  simp only [Complex.real_smul]
  ring

/-- `T` is a unit vector ("the unit tangent vector", proof of Lemma 2 of the notes). -/
lemma norm_tangent {p : ℝ × ℝ} (hp : p ∈ U) : ‖tangent γ p‖ = 1 := by
  simp only [tangent, ps, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (h.speed_pos hp)]
  exact inv_mul_cancel₀ (h.speed_ne hp)

/-- `∂γ/∂u = v T` (auxiliary). -/
lemma pu_eq_speed_mul_tangent {p : ℝ × ℝ} (hp : p ∈ U) :
    pu γ p = (speed γ p : ℂ) * tangent γ p := by
  simp only [tangent, ps, Complex.real_smul, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast h.speed_ne hp), one_mul]

end IsRegularFamily

/-- Algebraic helper: decomposition of a complex number in an orthonormal frame `(T, I T)`. Auxiliary for the Serret–Frenet equations used in the proof of Lemma 2 of the notes. -/
lemma decomp_frame {T : ℂ} (hT : ‖T‖ = 1) (z : ℂ) :
    z = (inner ℝ z T : ℝ) * T + (inner ℝ z (I * T) : ℝ) * (I * T) := by
  have h2 : T.re * T.re + T.im * T.im = 1 := by
    have := Complex.normSq_eq_norm_sq T
    rw [hT, Complex.normSq_apply] at this
    linarith
  apply Complex.ext <;>
  simp only [Complex.inner, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im]
  · linear_combination (-z.re) * h2
  · linear_combination (-z.im) * h2

namespace IsRegularFamily

variable {γ : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (h : IsRegularFamily γ U)
include h

/-- The derivative of the unit tangent is orthogonal to the tangent. Auxiliary for the Serret–Frenet equations used in the proof of Lemma 2 of the notes. -/
lemma inner_ps_tangent_tangent {p : ℝ × ℝ} (hp : p ∈ U) :
    inner ℝ (ps γ (tangent γ) p) (tangent γ p) = 0 := by
  have hT := h.smooth_tangent
  have hconst : (fun q => inner ℝ (tangent γ q) (tangent γ q)) =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
    filter_upwards [h.isOpen.mem_nhds hp] with q hq
    rw [real_inner_self_eq_norm_sq, h.norm_tangent hq]; simp
  have h1 := Filter.EventuallyEq.lineDeriv_eq (𝕜 := ℝ) (v := ((1 : ℝ), (0 : ℝ))) hconst
  rw [ld_inner (h.diff hT hp) (h.diff hT hp), ld_const] at h1
  have h2 : inner ℝ (lineDeriv ℝ (tangent γ) p (1, 0)) (tangent γ p) = 0 := by
    rw [real_inner_comm] at h1 ⊢; linarith
  simp only [ps, pu, real_inner_smul_left, h2, mul_zero]

/-- Serret–Frenet equation `∂T/∂s = κ n`. Used in the proofs of Lemmas 2, 4 and 5 of the notes. -/
lemma serret_frenet_tangent {p : ℝ × ℝ} (hp : p ∈ U) :
    ps γ (tangent γ) p = (curvature γ p : ℂ) * normal γ p := by
  have := decomp_frame (h.norm_tangent hp) (ps γ (tangent γ) p)
  rw [h.inner_ps_tangent_tangent hp] at this
  rw [this]
  simp [curvature, normal]

/-- Serret–Frenet equation `∂n/∂s = -κ T`. Used in the proofs of Lemmas 2, 4 and 5 of the notes. -/
lemma serret_frenet_normal {p : ℝ × ℝ} (hp : p ∈ U) :
    ps γ (normal γ) p = -(curvature γ p : ℂ) * tangent γ p := by
  have : normal γ = fun q => I * tangent γ q := rfl
  rw [this, h.ps_const_mul I h.smooth_tangent hp, h.serret_frenet_tangent hp, normal]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Serret–Frenet equation in the form of the notes: `∂T/∂u = v κ n`. -/
lemma serret_frenet_tangent_u {p : ℝ × ℝ} (hp : p ∈ U) :
    pu (tangent γ) p = (speed γ p : ℂ) * (curvature γ p : ℂ) * normal γ p := by
  have := h.serret_frenet_tangent hp
  simp only [ps, Complex.real_smul, Complex.ofReal_inv] at this
  have hv : (speed γ p : ℂ) ≠ 0 := by exact_mod_cast h.speed_ne hp
  rw [mul_assoc, ← this, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]

/-- Serret–Frenet equation in the form of the notes: `∂n/∂u = - v κ T`. -/
lemma serret_frenet_normal_u {p : ℝ × ℝ} (hp : p ∈ U) :
    pu (normal γ) p = -(speed γ p : ℂ) * (curvature γ p : ℂ) * tangent γ p := by
  have := h.serret_frenet_normal hp
  simp only [ps, Complex.real_smul, Complex.ofReal_inv] at this
  have hv : (speed γ p : ℂ) ≠ 0 := by exact_mod_cast h.speed_ne hp
  have e : pu (normal γ) p = (speed γ p : ℂ) * ((speed γ p : ℂ)⁻¹ * pu (normal γ) p) := by
    rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]
  rw [e, this]; ring

end IsRegularFamily

end CSF

end
