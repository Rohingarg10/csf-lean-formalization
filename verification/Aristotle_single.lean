import Mathlib

/-!
# Aristotle formalization of Chapter 3, as a single file

Mechanical concatenation of Aristotle's `RequestProject/*.lean` (Harmonic run
33cfe4c0-21b4-4419-b3ba-d700c3d3f1b4), in import order, for single-file checkers such as AXLE.
The only changes: `import RequestProject.*` lines removed, and each original file wrapped in its
own `section` so its `open` commands stay scoped as they were. No declaration was edited.
-/

-- ===== begin RequestProject/Defs.lean =====
section File_Defs


/-!
# Curve shortening flow: basic definitions

This file sets up the objects used in Chapter 3 ("Properties of Curve Shortening Flow")
of the attached notes `MTL603_PDE_project-9-13.pdf`.

A time-dependent plane curve is modelled as a map `γ : ℝ × ℝ → ℂ`, `(u, t) ↦ γ(u, t)`,
where we identify the plane `ℝ²` with `ℂ` (so that the anticlockwise rotation by `π/2`
is multiplication by `I`).  The first coordinate `u` is the curve parameter and the second
coordinate `t` is time.  Closed curves (parametrized by `S¹`) are modelled by maps which are
`2π`-periodic in `u`.
-/

open scoped ContDiff Real
open Complex

noncomputable section

namespace CSF

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative `∂f/∂u` of a function `f(u, t)` (the operator `∂/∂u` of Lemma 1 and throughout Chapter 3 of the notes): the derivative of `f` at `p`
in the direction `(1, 0)` (i.e. of `u ↦ f(u, t)`). -/
def pu (f : ℝ × ℝ → E) (p : ℝ × ℝ) : E := lineDeriv ℝ f p (1, 0)

/-- The partial derivative `∂f/∂t` of a function `f(u, t)` (the time derivative `∂/∂t` of Lemmas 2–6 of the notes): the derivative of `f` at `p`
in the direction `(0, 1)` (i.e. of `t ↦ f(u, t)`). -/
def pt (f : ℝ × ℝ → E) (p : ℝ × ℝ) : E := lineDeriv ℝ f p (0, 1)

/-- The speed `v = ‖∂γ/∂u‖` of the parametrization (notation of Lemma 1 in the notes). -/
def speed (γ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ := ‖pu γ p‖

/-- The arclength derivative `∂/∂s := (1/v) ∂/∂u` along the curve `γ`.
Lemma 1 of the notes (`CSF.lemma1_arclength_derivative`) justifies this definition: it is the
derivative with respect to the arclength parameter `s`. -/
def ps (γ : ℝ × ℝ → ℂ) (f : ℝ × ℝ → E) (p : ℝ × ℝ) : E := (speed γ p)⁻¹ • pu f p

/-- The unit tangent vector `T = ∂γ/∂s = (1/v) ∂γ/∂u`. -/
def tangent (γ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := ps γ γ p

/-- The unit normal vector `n`, obtained (as in the proof of Lemma 5 of the notes) by rotating
the unit tangent vector anticlockwise by the angle `π/2`, i.e. `n = I * T`. -/
def normal (γ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := I * tangent γ p

/-- The (signed) curvature `κ` induced by the choice of normal `n = I * T`
(as in the proof of Lemma 5 of the notes): `κ = ⟨∂T/∂s, n⟩`, so that `∂T/∂s = κ n`
(the Serret–Frenet equation, see `CSF.serret_frenet_tangent`). -/
def curvature (γ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ := inner ℝ (ps γ (tangent γ) p) (normal γ p)

/-- `γ` evolves by curve shortening flow (equation (2.1) of the notes) on the open set `U`
of parameter/time pairs `(u, t)`: `γ` is smooth on `U`, regular (`∂γ/∂u ≠ 0`), and
`∂γ/∂t = κ n` on `U`. -/
structure IsCSF (γ : ℝ × ℝ → ℂ) (U : Set (ℝ × ℝ)) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ ∞ γ U
  regular : ∀ p ∈ U, pu γ p ≠ 0
  flow : ∀ p ∈ U, pt γ p = (curvature γ p : ℂ) * normal γ p

/-- The arclength parameter `s(u) = ∫₀ᵘ ‖∂γ/∂u(u', t)‖ du'` of the curve `γ(·, t)`
(as in the proof of Lemma 1 of the notes). -/
def arclength (γ : ℝ × ℝ → ℂ) (t u : ℝ) : ℝ := ∫ u' in (0 : ℝ)..u, speed γ (u', t)

/-- A time-dependent curve is closed (parametrized by `S¹ = ℝ / 2πℤ`) if it is
`2π`-periodic in the curve parameter `u`. -/
def IsClosedCurve (γ : ℝ × ℝ → ℂ) : Prop := ∀ u t, γ (u + 2 * π, t) = γ (u, t)

/-- The length `L(t) = ∫₀^{2π} v du = ∫_{γ_t} ds` of the closed curve `γ_t` (Lemma 6). -/
def length (γ : ℝ × ℝ → ℂ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..2 * π, speed γ (u, t)

/-- The area `A(t)` enclosed by the closed curve `γ_t = (γ₁, γ₂)`, given (via Green's theorem,
as in the proof of Lemma 6 (ii) of the notes) by
`A(t) = ½ ∫₀^{2π} (γ₁ ∂γ₂/∂u - γ₂ ∂γ₁/∂u) du`.
This is the enclosed area for a positively (anticlockwise) oriented embedded curve, i.e. when
the normal `n = I * T` points inwards. -/
def enclosedArea (γ : ℝ × ℝ → ℂ) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ u in (0 : ℝ)..2 * π,
    ((γ (u, t)).re * (pu γ (u, t)).im - (γ (u, t)).im * (pu γ (u, t)).re)

/-- The closed curve `γ_t` is embedded (a simple closed curve): `u ↦ γ(u, t)` is injective
on a period `[0, 2π)`. -/
def IsEmbeddedAt (γ : ℝ × ℝ → ℂ) (t : ℝ) : Prop :=
  Set.InjOn (fun u => γ (u, t)) (Set.Ico 0 (2 * π))

end CSF

end

end File_Defs
-- ===== end RequestProject/Defs.lean =====

-- ===== begin RequestProject/Calculus.lean =====
section File_Calculus


/-!
# Calculus of partial derivatives

Auxiliary calculus rules for the directional derivatives `CSF.pu`, `CSF.pt`.
-/

open scoped ContDiff Real Topology
open Complex

noncomputable section

namespace CSF

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section rules

variable {p e : ℝ × ℝ}

/-- Sum rule for directional derivatives (auxiliary calculus used in the proofs of Lemmas 2–6 of the notes). -/
lemma ld_add {f g : ℝ × ℝ → E} (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    lineDeriv ℝ (fun q => f q + g q) p e = lineDeriv ℝ f p e + lineDeriv ℝ g p e := by
  rw [((hf.hasFDerivAt.fun_add hg.hasFDerivAt).hasLineDerivAt e).lineDeriv,
    hf.lineDeriv_eq_fderiv, hg.lineDeriv_eq_fderiv]
  rfl

/-- Difference rule for directional derivatives (auxiliary calculus used in the proofs of Lemmas 2–6 of the notes). -/
lemma ld_sub {f g : ℝ × ℝ → E} (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    lineDeriv ℝ (fun q => f q - g q) p e = lineDeriv ℝ f p e - lineDeriv ℝ g p e := by
  rw [((hf.hasFDerivAt.fun_sub hg.hasFDerivAt).hasLineDerivAt e).lineDeriv,
    hf.lineDeriv_eq_fderiv, hg.lineDeriv_eq_fderiv]
  rfl

/-- Negation rule for directional derivatives (auxiliary calculus used in the proofs of Lemmas 2–6 of the notes). -/
lemma ld_neg {f : ℝ × ℝ → E} :
    lineDeriv ℝ (fun q => - f q) p e = - lineDeriv ℝ f p e := by
  simp [lineDeriv, deriv.fun_neg]

/-- Directional derivatives of constants vanish (auxiliary calculus used in the proofs of Lemmas 2–6 of the notes). -/
lemma ld_const (c : E) : lineDeriv ℝ (fun _ : ℝ × ℝ => c) p e = 0 := by
  simp [lineDeriv]

/-- Product rule (real function times vector function) for directional derivatives, used in the proofs of Lemmas 2–5 of the notes. -/
lemma ld_smul {a : ℝ × ℝ → ℝ} {f : ℝ × ℝ → E} (ha : DifferentiableAt ℝ a p)
    (hf : DifferentiableAt ℝ f p) :
    lineDeriv ℝ (fun q => a q • f q) p e = lineDeriv ℝ a p e • f p + a p • lineDeriv ℝ f p e := by
  rw [((ha.hasFDerivAt.fun_smul hf.hasFDerivAt).hasLineDerivAt e).lineDeriv,
    ha.lineDeriv_eq_fderiv, hf.lineDeriv_eq_fderiv]
  simp [add_comm]

/-- Product rule for complex-valued functions, used e.g. for `∂(κ n)/∂u` in the proof of Lemma 2 of the notes. -/
lemma ld_mul {a b : ℝ × ℝ → ℂ} (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) :
    lineDeriv ℝ (fun q => a q * b q) p e = lineDeriv ℝ a p e * b p + a p * lineDeriv ℝ b p e := by
  rw [((ha.hasFDerivAt.fun_mul hb.hasFDerivAt).hasLineDerivAt e).lineDeriv,
    ha.lineDeriv_eq_fderiv, hb.lineDeriv_eq_fderiv]
  simp [add_comm, mul_comm]

/-- Product rule for real-valued functions, used e.g. in the proof of Lemma 6 (ii) of the notes. -/
lemma ld_rmul {a b : ℝ × ℝ → ℝ} (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) :
    lineDeriv ℝ (fun q => a q * b q) p e = lineDeriv ℝ a p e * b p + a p * lineDeriv ℝ b p e := by
  have := ld_smul (e := e) ha hb
  simpa [smul_eq_mul, mul_comm] using this

/-- Derivative of `c * f` for a constant `c` (e.g. `n = I * T`), used in the proofs of Lemmas 4 and 5 of the notes. -/
lemma ld_const_mul (c : ℂ) {a : ℝ × ℝ → ℂ} (ha : DifferentiableAt ℝ a p) :
    lineDeriv ℝ (fun q => c * a q) p e = c * lineDeriv ℝ a p e := by
  rw [ld_mul (differentiableAt_const c) ha, ld_const]
  simp

/-- Directional derivatives commute with the inclusion `ℝ → ℂ` (auxiliary calculus for Lemmas 2–5 of the notes). -/
lemma ld_ofReal {a : ℝ × ℝ → ℝ} (ha : DifferentiableAt ℝ a p) :
    lineDeriv ℝ (fun q => (a q : ℂ)) p e = ((lineDeriv ℝ a p e : ℝ) : ℂ) := by
  have h := (ofRealCLM.hasFDerivAt.comp p ha.hasFDerivAt).hasLineDerivAt e
  rw [show (fun q => (a q : ℂ)) = ofRealCLM ∘ a from rfl, h.lineDeriv]
  simp [ha.lineDeriv_eq_fderiv]

/-- Product rule for the inner product, as used in the proofs of Lemmas 2, 4 and 5 of the notes (differentiating `v²`, `T · n`, `κ = ⟨∂T/∂s, n⟩`). -/
lemma ld_inner {f g : ℝ × ℝ → ℂ} (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    lineDeriv ℝ (fun q => inner ℝ (f q) (g q)) p e =
      inner ℝ (lineDeriv ℝ f p e) (g p) + inner ℝ (f p) (lineDeriv ℝ g p e) := by
  rw [(hf.inner ℝ hg).lineDeriv_eq_fderiv, hf.lineDeriv_eq_fderiv, hg.lineDeriv_eq_fderiv,
    fderiv_inner_apply ℝ hf hg]
  ring

/-- Derivative of `1 / a`, used for `∂(1/v)/∂t` in the proof of Lemma 3 of the notes. -/
lemma ld_inv {a : ℝ × ℝ → ℝ} (ha : DifferentiableAt ℝ a p) (h0 : a p ≠ 0) :
    lineDeriv ℝ (fun q => (a q)⁻¹) p e = - lineDeriv ℝ a p e / (a p) ^ 2 := by
  have h := ((hasDerivAt_inv h0).comp_hasFDerivAt p ha.hasFDerivAt).hasLineDerivAt e
  rw [show (fun q => (a q)⁻¹) = (fun y : ℝ => y⁻¹) ∘ a from rfl, h.lineDeriv,
    ha.lineDeriv_eq_fderiv]
  simp
  ring

/-- Derivative of the norm, `∂‖f‖ = ⟨f, ∂f⟩ / ‖f‖`; this is the computation `∂(v²)/∂t = 2 v ∂v/∂t` in the proof of Lemma 2 of the notes. -/
lemma ld_norm {f : ℝ × ℝ → ℂ} (hf : DifferentiableAt ℝ f p) (h0 : f p ≠ 0) :
    lineDeriv ℝ (fun q => ‖f q‖) p e = inner ℝ (f p) (lineDeriv ℝ f p e) / ‖f p‖ := by
  have hn : DifferentiableAt ℝ (fun q => ‖f q‖) p := hf.norm ℝ h0
  have h1 := ld_rmul (e := e) hn hn
  have h2 := ld_inner (e := e) hf hf
  have heq : (fun q => ‖f q‖ * ‖f q‖) = fun q => inner ℝ (f q) (f q) := by
    funext q; rw [real_inner_self_eq_norm_mul_norm]
  rw [heq, h2, real_inner_comm] at h1
  have hpos : ‖f p‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  field_simp
  linarith

end rules

section smooth

variable {U : Set (ℝ × ℝ)}

/-- A function smooth on an open set is differentiable at each of its points (auxiliary). -/
lemma differentiableAt_of_smooth {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : ℝ × ℝ} (hp : p ∈ U) : DifferentiableAt ℝ f p :=
  (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)

/-- Near a point of smoothness, directional derivatives are given by the Fréchet derivative (auxiliary). -/
lemma ld_eventuallyEq_fderiv {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : ℝ × ℝ} (hp : p ∈ U) (e : ℝ × ℝ) :
    (fun q => lineDeriv ℝ f q e) =ᶠ[𝓝 p] fun q => fderiv ℝ f q e := by
  filter_upwards [hU.mem_nhds hp] with q hq
  exact (differentiableAt_of_smooth hf hU hq).lineDeriv_eq_fderiv

/-- Directional derivatives of smooth functions are smooth (auxiliary). -/
lemma smooth_ld {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (e : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (fun q => lineDeriv ℝ f q e) U := by
  have h1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ f q e) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  refine h1.congr fun q hq => ?_
  exact (differentiableAt_of_smooth hf hU hq).lineDeriv_eq_fderiv

/-- `∂f/∂u` is smooth when `f` is (auxiliary). -/
lemma smooth_pu {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (pu f) U := smooth_ld hf hU _

/-- `∂f/∂t` is smooth when `f` is (auxiliary). -/
lemma smooth_pt {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (pt f) U := smooth_ld hf hU _

/-- Mixed partial derivatives commute. -/
lemma ld_comm {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : ℝ × ℝ} (hp : p ∈ U) (e₁ e₂ : ℝ × ℝ) :
    lineDeriv ℝ (fun q => lineDeriv ℝ f q e₁) p e₂ =
      lineDeriv ℝ (fun q => lineDeriv ℝ f q e₂) p e₁ := by
  have key : ∀ a b : ℝ × ℝ, lineDeriv ℝ (fun q => lineDeriv ℝ f q a) p b =
      fderiv ℝ (fderiv ℝ f) p b a := by
    intro a b
    rw [(ld_eventuallyEq_fderiv hf hU hp a).lineDeriv_eq]
    have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
      differentiableAt_of_smooth (hf.fderiv_of_isOpen hU (by simp)) hU hp
    rw [(hd.clm_apply (differentiableAt_const a)).lineDeriv_eq_fderiv,
      fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  rw [key, key]
  exact ((hf.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt (by simpa using ENat.LEInfty.out)) e₂ e₁

/-- The operators `∂/∂u` and `∂/∂t` commute, as noted in the proof of Lemma 2 of the notes ("we note that `∂/∂u` and `∂/∂t` commute"). -/
lemma pt_pu {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : ℝ × ℝ} (hp : p ∈ U) : pt (pu f) p = pu (pt f) p :=
  ld_comm hf hU hp _ _

end smooth

end CSF

end

end File_Calculus
-- ===== end RequestProject/Calculus.lean =====

-- ===== begin RequestProject/Frenet.lean =====
section File_Frenet


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

end File_Frenet
-- ===== end RequestProject/Frenet.lean =====

-- ===== begin RequestProject/Evolution.lean =====
section File_Evolution


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

end File_Evolution
-- ===== end RequestProject/Evolution.lean =====

-- ===== begin RequestProject/LengthArea.lean =====
section File_LengthArea


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

end File_LengthArea
-- ===== end RequestProject/LengthArea.lean =====

-- ===== begin RequestProject/MaximalTime.lean =====
section File_MaximalTime


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

end File_MaximalTime
-- ===== end RequestProject/MaximalTime.lean =====

-- ===== begin RequestProject/MaxPrinciple.lean =====
section File_MaxPrinciple


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

end File_MaxPrinciple
-- ===== end RequestProject/MaxPrinciple.lean =====

-- ===== begin RequestProject/Embedded.lean =====
section File_Embedded


/-!
# Chapter 3: Theorem 3.0.1 (curve shortening flow keeps embedded curves embedded)
-/

open scoped ContDiff Real Topology
open Complex Set Filter

noncomputable section

namespace CSF

variable {γ : ℝ × ℝ → ℂ} {T₀ : ℝ}

/-- Periodicity of a closed curve under integer multiples of `2π` (auxiliary for Theorem 3.0.1 of the notes). -/
lemma periodic_int (hcl : IsClosedCurve γ) (u t : ℝ) (n : ℤ) :
    γ (u + n * (2 * π), t) = γ (u, t) := by
  have hper : Function.Periodic (fun u => γ (u, t)) (2 * π) := fun u => hcl u t
  exact (hper.int_mul n) u

/-- Reduction of the parameter of a closed curve to `[0, 2π)` (auxiliary for Theorem 3.0.1 of the notes). -/
lemma gamma_toIcoMod (hcl : IsClosedCurve γ) (x t : ℝ) :
    γ (toIcoMod Real.two_pi_pos 0 x, t) = γ (x, t) := by
  have e := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
  conv_rhs => rw [← e]
  rw [zsmul_eq_mul, periodic_int hcl]

/-- Reduction of the parameter of a closed curve to `[0, 2π)`, uniformly in time (auxiliary for Theorem 3.0.1 of the notes). -/
lemma reduce_mod (hcl : IsClosedCurve γ) (u : ℝ) :
    ∃ u' ∈ Ico 0 (2 * π), ∀ s t, γ (u + s, t) = γ (u' + s, t) := by
  refine ⟨toIcoMod Real.two_pi_pos 0 u, by simpa using toIcoMod_mem_Ico' Real.two_pi_pos u,
    fun s t => ?_⟩
  have e := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 u
  conv_lhs => rw [← e]
  rw [zsmul_eq_mul, show toIcoMod Real.two_pi_pos 0 u + ↑(toIcoDiv Real.two_pi_pos 0 u) * (2 * π)
    + s = (toIcoMod Real.two_pi_pos 0 u + s) + ↑(toIcoDiv Real.two_pi_pos 0 u) * (2 * π) by ring,
    periodic_int hcl]

/-- A non-zero partial derivative `∂γ/∂u` is a genuine derivative of `u ↦ γ(u, t)` (auxiliary for Theorem 3.0.1 of the notes). -/
lemma hasDerivAt_u_of_ne {u t : ℝ} (hne : pu γ (u, t) ≠ 0) :
    HasDerivAt (fun u => γ (u, t)) (pu γ (u, t)) u := by
  rw [pu_eq_deriv] at hne ⊢
  exact (differentiableAt_of_deriv_ne_zero hne).hasDerivAt

/-- Regularity of the flow on the whole time interval `[0, T₀)` (auxiliary for Theorem 3.0.1 of the notes). -/
lemma reg_Ico (h : IsCSF γ (univ ×ˢ Ioo 0 T₀)) (hreg0 : ∀ u, pu γ (u, 0) ≠ 0) :
    ∀ u, ∀ t ∈ Ico 0 T₀, pu γ (u, t) ≠ 0 := by
  intro u t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0; exact hreg0 u
  · exact h.regular _ (mem_strip ⟨hpos, ht.2⟩)

/-- Uniform local injectivity on a compact time interval. Auxiliary for the proof of Theorem 3.0.1 of the notes. -/
lemma local_inj (h : IsCSF γ (univ ×ˢ Ioo 0 T₀)) (hcl : IsClosedCurve γ)
    (hc1 : ContinuousOn (pu γ) (univ ×ˢ Ico 0 T₀)) (hreg0 : ∀ u, pu γ (u, 0) ≠ 0)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Ico 0 T₀) :
    ∃ η, 0 < η ∧ η < π ∧ ∀ t ∈ Icc 0 t₁, ∀ u r, r ∈ Ioc 0 η → γ (u + r, t) ≠ γ (u, t) := by
  have hreg := reg_Ico h hreg0
  set K : Set (ℝ × ℝ) := Icc 0 (2 * π + 1) ×ˢ Icc 0 t₁ with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ univ ×ˢ Ico 0 T₀ := prod_mono (subset_univ _)
    (Icc_subset_Ico_right ht₁.2)
  have hcK : ContinuousOn (pu γ) K := hc1.mono hKsub
  have hKne : K.Nonempty := ⟨(0, 0), ⟨by constructor <;> positivity, ⟨le_rfl, ht₁.1⟩⟩⟩
  obtain ⟨q0, hq0K, hq0min⟩ := hK.exists_isMinOn hKne (continuous_norm.comp_continuousOn hcK)
  set vmin := ‖pu γ q0‖ with hvmin
  have hvpos : 0 < vmin := norm_pos_iff.mpr
    (hreg q0.1 q0.2 (hKsub hq0K).2)
  obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hcK) vmin hvpos
  refine ⟨min (δ / 2) 1, lt_min (half_pos hδ) one_pos,
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_gt_three]), ?_⟩
  intro t ht u r hr hcol
  obtain ⟨u', hu', hred⟩ := reduce_mod hcl u
  have hcol' : γ (u' + r, t) = γ (u', t) := by
    rw [← hred r t, hcol]; simpa using hred 0 t
  have htIco : t ∈ Ico 0 T₀ := ⟨ht.1, lt_of_le_of_lt ht.2 ht₁.2⟩
  let w := pu γ (u', t)
  let hf : ℝ → ℝ := fun σ => inner ℝ (γ (σ, t) - γ (u', t)) w
  have hfd : ∀ σ, HasDerivAt hf (inner ℝ (pu γ (σ, t)) w) σ := by
    intro σ
    have := ((hasDerivAt_u_of_ne (hreg σ t htIco)).sub_const (γ (u', t))).inner ℝ
      (hasDerivAt_const σ w)
    simpa only [inner_zero_right, zero_add] using this
  have hr1 : r ≤ 1 := hr.2.trans (min_le_right _ _)
  have hrδ : r < δ := lt_of_le_of_lt (hr.2.trans (min_le_left _ _)) (half_lt_self hδ)
  obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope hf (fun σ => inner ℝ (pu γ (σ, t)) w)
    (show u' < u' + r by linarith [hr.1])
    (fun σ _ => (hfd σ).continuousAt.continuousWithinAt) (fun σ _ => hfd σ)
  have hξK : (ξ, t) ∈ K := ⟨⟨by linarith [hξ.1, hu'.1], by linarith [hξ.2, hu'.2]⟩, ht⟩
  have hu'K : (u', t) ∈ K := ⟨⟨hu'.1, by linarith [hu'.2]⟩, ht⟩
  have hdist : dist (ξ, t) (u', t) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_pos (by linarith [hξ.1])]
    rw [max_lt_iff]
    exact ⟨by linarith [hξ.2, hrδ], hδ⟩
  have hclose := hδK _ hξK _ hu'K hdist
  rw [dist_eq_norm] at hclose
  have hwmin : vmin ≤ ‖w‖ := hq0min hu'K
  have hpos : 0 < inner ℝ (pu γ (ξ, t)) w := by
    have e : inner ℝ (pu γ (ξ, t)) w = ‖w‖ ^ 2 + inner ℝ (pu γ (ξ, t) - w) w := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
    have hcs := real_inner_le_norm (-(pu γ (ξ, t) - w)) w
    rw [inner_neg_left, norm_neg] at hcs
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hvpos hwmin
    rw [e]
    nlinarith
  have hval : hf (u' + r) = 0 := by simp [hf, hcol']
  have hval0 : hf u' = 0 := by simp [hf]
  rw [hval, hval0, sub_zero, add_sub_cancel_left] at hξ'
  have : (0 : ℝ) / r = 0 := zero_div r
  rw [this] at hξ'
  linarith

/-- Embeddedness from the separation of pairs of parameters at distance at least `η`. Auxiliary for the proof of Theorem 3.0.1 of the notes. -/
lemma embedded_of_pairs (hcl : IsClosedCurve γ) {η t : ℝ}
    (hloc : ∀ u r, r ∈ Ioc 0 η → γ (u + r, t) ≠ γ (u, t))
    (hpairs : ∀ u ∈ Icc 0 (2 * π), ∀ r ∈ Icc η (2 * π - η), γ (u + r, t) ≠ γ (u, t)) :
    IsEmbeddedAt γ t := by
  have key : ∀ x ∈ Ico 0 (2 * π), ∀ y ∈ Ico 0 (2 * π), x < y → γ (x, t) ≠ γ (y, t) := by
    intro x hx y hy hxy heq
    by_cases h1 : y - x ≤ η
    · exact hloc x (y - x) ⟨by linarith, h1⟩ (by rw [show x + (y - x) = y by ring]; exact heq.symm)
    by_cases h2 : 2 * π - η ≤ y - x
    · apply hloc y (2 * π - (y - x)) ⟨by linarith [hx.1, hy.2], by linarith⟩
      rw [show y + (2 * π - (y - x)) = x + 2 * π by ring, hcl x t, heq]
    · push_neg at h1 h2
      exact hpairs x ⟨hx.1, hx.2.le⟩ (y - x) ⟨h1.le, h2.le⟩
        (by rw [show x + (y - x) = y by ring]; exact heq.symm)
  intro x hx y hy hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key x hx y hy hlt hxy
  · exact key y hy x hx hgt hxy.symm

/-- An embedded closed curve separates all pairs of parameters which differ by an amount in
`[η, 2π - η]`. Auxiliary for the proof of Theorem 3.0.1 of the notes. -/
lemma pairs_of_embedded (hcl : IsClosedCurve γ) {t : ℝ} (hemb : IsEmbeddedAt γ t) {η : ℝ}
    (hη0 : 0 < η) : ∀ u, ∀ r ∈ Icc η (2 * π - η), γ (u + r, t) ≠ γ (u, t) := by
  intro u r hr heq
  have ha := toIcoMod_mem_Ico' Real.two_pi_pos (u + r)
  have hb := toIcoMod_mem_Ico' Real.two_pi_pos u
  have hab : toIcoMod Real.two_pi_pos 0 (u + r) = toIcoMod Real.two_pi_pos 0 u := by
    apply hemb (by simpa using ha) (by simpa using hb)
    simp only
    rw [gamma_toIcoMod hcl, gamma_toIcoMod hcl, heq]
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod Real.two_pi_pos).mp hab
  rw [zsmul_eq_mul] at hn
  have hr0 : 0 < r := by linarith [hr.1]
  have hr2 : r < 2 * π := by linarith [hr.2]
  have h1 : (n : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have h2 : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have h1' : n < 0 := by exact_mod_cast h1
  have h2' : -1 < n := by exact_mod_cast h2
  omega

/-- The core of Theorem 3.0.1: pairs of parameters which are separated at time `0` remain
separated at every later time `t₁ ∈ (0, T₀)`. -/
lemma pairs_persist (h : IsCSF γ (univ ×ˢ Ioo 0 T₀)) (hcl : IsClosedCurve γ)
    (hc0 : ContinuousOn γ (univ ×ˢ Ico 0 T₀)) (hemb : IsEmbeddedAt γ 0)
    {t₁ η : ℝ} (ht₁ : t₁ ∈ Ioo 0 T₀) (hη0 : 0 < η) (hηπ : η < π)
    (hloc : ∀ t ∈ Icc 0 t₁, ∀ u r, r ∈ Ioc 0 η → γ (u + r, t) ≠ γ (u, t)) :
    ∀ u ∈ Icc 0 (2 * π), ∀ r ∈ Icc η (2 * π - η), γ (u + r, t₁) ≠ γ (u, t₁) := by
  have hIcc : Icc 0 t₁ ⊆ Ico 0 T₀ := Icc_subset_Ico_right ht₁.2
  set S : Set (ℝ × ℝ) := Icc 0 (2 * π) ×ˢ Icc η (2 * π - η) with hSdef
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSne : S.Nonempty := ⟨(0, η), ⟨⟨le_rfl, by positivity⟩, ⟨le_rfl, by linarith⟩⟩⟩
  let d : ℝ × ℝ → ℝ → ℝ := fun q s => ‖γ (q.1 + q.2, s) - γ (q.1, s)‖
  let D : ℝ → ℝ := fun s => sInf ((fun q => d q s) '' S)
  -- continuity of `d`
  have hdc : ∀ s ∈ Icc 0 t₁, Continuous fun q : ℝ × ℝ => d q s := by
    intro s hs
    have hmem : ∀ z : ℝ, (z, s) ∈ (univ ×ˢ Ico 0 T₀ : Set (ℝ × ℝ)) := fun z =>
      ⟨mem_univ _, hIcc hs⟩
    exact continuous_norm.comp ((hc0.comp_continuous (by fun_prop) fun q => hmem _).sub
      (hc0.comp_continuous (by fun_prop) fun q => hmem _))
  have hbdd : ∀ s, BddBelow ((fun q => d q s) '' S) :=
    fun s => ⟨0, by rintro _ ⟨q, _, rfl⟩; exact norm_nonneg _⟩
  have hDle : ∀ s, ∀ q ∈ S, D s ≤ d q s := fun s q hq =>
    csInf_le (hbdd s) (mem_image_of_mem _ hq)
  have hDmin : ∀ s ∈ Icc 0 t₁, ∃ q ∈ S, D s = d q s := by
    intro s hs
    obtain ⟨q, hq, hqmin⟩ := hS.exists_isMinOn hSne (hdc s hs).continuousOn
    refine ⟨q, hq, IsLeast.csInf_eq ⟨mem_image_of_mem _ hq, ?_⟩⟩
    rintro _ ⟨q', hq', rfl⟩
    exact hqmin hq'
  have hDc : ContinuousOn D (Icc 0 t₁) := by
    rw [continuousOn_iff_continuous_restrict]
    let f : Icc (0 : ℝ) t₁ → ℝ × ℝ → ℝ := fun s q => d q s
    have hf : Continuous (Function.uncurry f) := by
      have hmem : ∀ (z : ℝ) (s : Icc (0 : ℝ) t₁),
          (z, (s : ℝ)) ∈ (univ ×ˢ Ico 0 T₀ : Set (ℝ × ℝ)) := fun z s => ⟨mem_univ _, hIcc s.2⟩
      exact continuous_norm.comp
        ((hc0.comp_continuous (show Continuous (fun p : Icc (0 : ℝ) t₁ × (ℝ × ℝ) =>
          (p.2.1 + p.2.2, (p.1 : ℝ))) by fun_prop) fun p => hmem _ p.1).sub
        (hc0.comp_continuous (show Continuous (fun p : Icc (0 : ℝ) t₁ × (ℝ × ℝ) =>
          (p.2.1, (p.1 : ℝ))) by fun_prop) fun p => hmem _ p.1))
    exact hS.continuous_sInf hf
  -- extension of the lower bound to all parameters by periodicity
  have hDext : ∀ s, ∀ u, ∀ r ∈ Icc η (2 * π - η), D s ≤ ‖γ (u + r, s) - γ (u, s)‖ := by
    intro s u r hr
    obtain ⟨u', hu', hred⟩ := reduce_mod hcl u
    have e0 : γ (u, s) = γ (u', s) := by simpa using hred 0 s
    rw [hred r s, e0]
    exact hDle s (u', r) ⟨⟨hu'.1, hu'.2.le⟩, hr⟩
  -- positivity at time zero
  have hD0 : 0 < D 0 := by
    obtain ⟨q, hq, hDq⟩ := hDmin 0 ⟨le_rfl, ht₁.1.le⟩
    rw [hDq]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (pairs_of_embedded hcl hemb hη0 q.1 q.2 hq.2))
  -- a uniform lower bound for the chord on the boundary of `S`
  obtain ⟨m0, hm0pos, hm0⟩ : ∃ m0 > 0, ∀ s ∈ Icc 0 t₁, ∀ u,
      m0 ≤ ‖γ (u + η, s) - γ (u, s)‖ := by
    set K : Set (ℝ × ℝ) := Icc 0 (2 * π) ×ˢ Icc 0 t₁
    have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
    have hKne : K.Nonempty := ⟨(0, 0), ⟨⟨le_rfl, by positivity⟩, ⟨le_rfl, ht₁.1.le⟩⟩⟩
    have hmem : ∀ p ∈ K, ∀ z : ℝ, (z, p.2) ∈ (univ ×ˢ Ico 0 T₀ : Set (ℝ × ℝ)) :=
      fun p hp z => ⟨mem_univ _, hIcc hp.2⟩
    have hcK : ContinuousOn (fun p : ℝ × ℝ => ‖γ (p.1 + η, p.2) - γ (p.1, p.2)‖) K := by
      refine continuous_norm.comp_continuousOn (ContinuousOn.sub ?_ ?_)
      · exact hc0.comp (by fun_prop) fun p hp => hmem p hp _
      · exact hc0.comp (by fun_prop) fun p hp => hmem p hp _
    obtain ⟨p0, hp0, hp0min⟩ := hK.exists_isMinOn hKne hcK
    refine ⟨‖γ (p0.1 + η, p0.2) - γ (p0.1, p0.2)‖,
      norm_pos_iff.mpr (sub_ne_zero.mpr (hloc p0.2 hp0.2 p0.1 η ⟨hη0, le_rfl⟩)), ?_⟩
    intro s hs u
    obtain ⟨u', hu', hred⟩ := reduce_mod hcl u
    have e0 : γ (u, s) = γ (u', s) := by simpa using hred 0 s
    rw [hred η s, e0]
    exact hp0min (show (u', s) ∈ K from ⟨⟨hu'.1, hu'.2.le⟩, hs⟩)
  have hm0' : ∀ s ∈ Icc 0 t₁, ∀ u, m0 ≤ ‖γ (u + (2 * π - η), s) - γ (u, s)‖ := by
    intro s hs u
    have := hm0 s hs (u - η)
    rw [show u - η + η = u by ring] at this
    rw [show u + (2 * π - η) = (u - η) + 2 * π by ring, hcl, norm_sub_rev]
    exact this
  -- the perturbation argument
  set m := min (D 0) m0 / 2 with hmdef
  have hmin_pos : 0 < min (D 0) m0 := lt_min hD0 hm0pos
  have hm : 0 < m := half_pos hmin_pos
  have hmD0 : m < D 0 := by
    have := min_le_left (D 0) m0; linarith
  have hmm0 : m < m0 := by
    have := min_le_right (D 0) m0; linarith
  set ε := m / (2 * t₁) with hεdef
  have hε : 0 < ε := div_pos hm (by linarith [ht₁.1])
  have hεt₁ : ε * t₁ = m / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_eq_div_iff (by linarith [ht₁.1]) (by norm_num)]
    ring
  let Φ : ℝ → ℝ := fun s => D s + ε * s
  have hΦc : ContinuousOn Φ (Icc 0 t₁) := hDc.add (continuousOn_const.mul continuousOn_id)
  have claim : ∀ s ∈ Icc 0 t₁, m < Φ s := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s₀, hs₀, hΦs₀⟩ := hcon
    set B := Icc 0 t₁ ∩ Φ ⁻¹' Iic m with hBdef
    have hBc : IsClosed B := hΦc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hBne : B.Nonempty := ⟨s₀, hs₀, hΦs₀⟩
    have hBbdd : BddBelow B := ⟨0, fun s hs => hs.1.1⟩
    set ts := sInf B with htsdef
    have hts : ts ∈ B := hBc.csInf_mem hBne hBbdd
    have hts0 : 0 < ts := by
      rcases eq_or_lt_of_le hts.1.1 with h0 | hpos
      · have := hts.2
        simp only [mem_preimage, mem_Iic, ← h0, Φ, mul_zero, add_zero] at this
        linarith
      · exact hpos
    have hbefore : ∀ s ∈ Ico 0 ts, m < Φ s := by
      intro s hs
      by_contra hc
      push_neg at hc
      have hsB : s ∈ B := ⟨⟨hs.1, (hs.2.trans_le hts.1.2).le⟩, hc⟩
      have := csInf_le hBbdd hsB
      linarith [hs.2]
    have hΦts : m ≤ Φ ts := by
      have hcl' : ts ∈ closure (Ico 0 ts) := by
        rw [closure_Ico hts0.ne]; exact ⟨hts0.le, le_rfl⟩
      exact ContinuousWithinAt.closure_le hcl' continuousWithinAt_const
        ((hΦc ts hts.1).mono (fun s hs => ⟨hs.1, (hs.2.trans_le hts.1.2).le⟩))
        (fun s hs => (hbefore s hs).le)
    have hΦts' : Φ ts ≤ m := hts.2
    have htsT : ts ∈ Ioo 0 T₀ := ⟨hts0, lt_of_le_of_lt hts.1.2 ht₁.2⟩
    obtain ⟨q, hq, hDq⟩ := hDmin ts hts.1
    set x := q.1
    set r := q.2
    set y := x + r with hydef
    have hDts_lower : m / 2 ≤ D ts := by
      have : ε * ts ≤ ε * t₁ := mul_le_mul_of_nonneg_left hts.1.2 hε.le
      simp only [Φ] at hΦts; linarith
    have hDts_upper : D ts < m0 := by
      have : 0 < ε * ts := mul_pos hε hts0
      simp only [Φ] at hΦts'; linarith
    have hr : r ∈ Ioo η (2 * π - η) := by
      rcases eq_or_lt_of_le hq.2.1 with he | hlt
      · exfalso
        have := hm0 ts hts.1 x
        simp only [d] at hDq
        rw [← he] at hDq
        linarith
      rcases eq_or_lt_of_le hq.2.2 with he' | hlt'
      · exfalso
        have := hm0' ts hts.1 x
        simp only [d] at hDq
        rw [he'] at hDq
        linarith
      exact ⟨hlt, hlt'⟩
    have hzpos : 0 < ‖γ (y, ts) - γ (x, ts)‖ := by
      have : D ts = ‖γ (y, ts) - γ (x, ts)‖ := hDq
      linarith
    have hne : γ (y, ts) ≠ γ (x, ts) := sub_ne_zero.mp (norm_pos_iff.mp hzpos)
    have hloc_min : ∀ᶠ q' in 𝓝 (x, y),
        ‖γ (y, ts) - γ (x, ts)‖ ≤ ‖γ (q'.2, ts) - γ (q'.1, ts)‖ := by
      have hopen : IsOpen {q' : ℝ × ℝ | q'.2 - q'.1 ∈ Ioo η (2 * π - η)} :=
        isOpen_Ioo.preimage (by fun_prop)
      have hxy : (x, y) ∈ {q' : ℝ × ℝ | q'.2 - q'.1 ∈ Ioo η (2 * π - η)} := by
        simp only [mem_setOf_eq, hydef, add_sub_cancel_left]; exact hr
      filter_upwards [hopen.mem_nhds hxy] with q' hq'
      have := hDext ts q'.1 (q'.2 - q'.1) ⟨hq'.1.le, hq'.2.le⟩
      rw [show q'.1 + (q'.2 - q'.1) = q'.2 by ring] at this
      have e : D ts = ‖γ (y, ts) - γ (x, ts)‖ := hDq
      linarith
    have hmp := chord_max_principle h htsT hne hloc_min
    -- time derivative of the squared chord
    set z := γ (y, ts) - γ (x, ts) with hzdef
    set z' := pt γ (y, ts) - pt γ (x, ts)
    have hR := h.toRegular
    let c : ℝ → ℂ := fun s => γ (y, s) - γ (x, s)
    have hc : HasDerivAt c z' ts :=
      (hasDerivAt_line_t (hR.diff hR.smooth (mem_strip htsT))).sub
        (hasDerivAt_line_t (hR.diff hR.smooth (mem_strip htsT)))
    let G : ℝ → ℝ := fun s => inner ℝ (c s) (c s)
    have hG : HasDerivAt G (inner ℝ (c ts) z' + inner ℝ z' (c ts)) ts := hc.inner ℝ hc
    have hcts : c ts = z := rfl
    rw [hcts, real_inner_comm z z'] at hG
    have hslope := (hasDerivAt_iff_tendsto_slope.mp hG).mono_left
      (nhdsWithin_mono ts (fun s (hs : s ∈ Iio ts) => ne_of_lt hs))
    have hev : ∀ᶠ s in 𝓝[<] ts, slope G ts s ≤ -(m * ε) := by
      filter_upwards [Ioo_mem_nhdsLT hts0] with s hs
      have hsIcc : s ∈ Icc 0 t₁ := ⟨hs.1.le, (hs.2.trans_le hts.1.2).le⟩
      have hDs := hDext s x r hq.2
      have hΦs := hbefore s ⟨hs.1.le, hs.2⟩
      simp only [Φ] at hΦs hΦts'
      have e : D ts = ‖z‖ := hDq
      have hcs : ‖c s‖ = ‖γ (x + r, s) - γ (x, s)‖ := rfl
      have hgap : ‖z‖ + ε * (ts - s) < ‖c s‖ := by rw [hcs]; nlinarith
      have hzm : m / 2 ≤ ‖z‖ := by linarith
      have hGs : G s = ‖c s‖ ^ 2 := real_inner_self_eq_norm_sq _
      have hGts : G ts = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq _
      rw [slope_def_field, hGs, hGts]
      have hden : s - ts < 0 := by linarith [hs.2]
      rw [div_le_iff_of_neg hden]
      have hts_s : 0 < ts - s := by linarith [hs.2]
      have hεts : 0 < ε * (ts - s) := mul_pos hε hts_s
      have hA : ε * (ts - s) * (‖c s‖ + ‖z‖) ≤ (‖c s‖ - ‖z‖) * (‖c s‖ + ‖z‖) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hB : m * (ε * (ts - s)) ≤ (‖c s‖ + ‖z‖) * (ε * (ts - s)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith [hA, hB]
    have hle := le_of_tendsto hslope hev
    have : 0 < m * ε := mul_pos hm hε
    linarith
  -- conclusion at time `t₁`
  intro u hu r hr heq
  have hΦ := claim t₁ ⟨ht₁.1.le, le_rfl⟩
  simp only [Φ] at hΦ
  have hle := hDle t₁ (u, r) ⟨hu, hr⟩
  simp only [d, heq, sub_self, norm_zero] at hle
  linarith

/-- **Theorem 3.0.1.** Let `γ : S¹ × [0, T₀) → ℝ²` be a family of closed curves satisfying
equation (2.1) (curve shortening flow). If the initial curve `γ₀` is embedded and if there exists
`c ∈ ℝ` such that `κ(u, t) ≤ c` for all `(u, t) ∈ S¹ × [0, T₀)`, then `γ_t` is an embedded curve
for each `t ∈ [0, T₀)`.

Formalization: closed curves are `2π`-periodic in `u` (`hcl`); the flow equation and smoothness
hold for `t ∈ (0, T₀)` (`h`), while at `t = 0` we only require that `γ` and `∂γ/∂u` are
continuous up to `t = 0` (`hc0`, `hc1`) and that the initial curve is regular (`hreg0`).

The curvature bound `hκ` is part of the statement in the notes; it turns out not to be needed
in this proof (on each compact time interval `[0, t₁] ⊂ [0, T₀)` the required uniform estimates
follow from compactness), and it is kept only to match the notes. -/
theorem theorem_3_0_1 (h : IsCSF γ (univ ×ˢ Ioo 0 T₀)) (hcl : IsClosedCurve γ)
    (hc0 : ContinuousOn γ (univ ×ˢ Ico 0 T₀)) (hc1 : ContinuousOn (pu γ) (univ ×ˢ Ico 0 T₀))
    (hreg0 : ∀ u, pu γ (u, 0) ≠ 0) (hemb : IsEmbeddedAt γ 0) (c : ℝ)
    (hκ : ∀ u, ∀ t ∈ Ico 0 T₀, curvature γ (u, t) ≤ c) :
    ∀ t ∈ Ico 0 T₀, IsEmbeddedAt γ t := by
  have _ := hκ
  intro t₁ ht₁
  obtain ⟨η, hη0, hηπ, hloc⟩ := local_inj h hcl hc1 hreg0 ht₁
  apply embedded_of_pairs hcl (hloc t₁ ⟨ht₁.1, le_rfl⟩)
  rcases eq_or_lt_of_le ht₁.1 with h0 | hpos
  · subst h0
    exact fun u _ r hr => pairs_of_embedded hcl hemb hη0 u r hr
  · exact pairs_persist h hcl hc0 hemb ⟨hpos, ht₁.2⟩ hη0 hηπ hloc

end CSF

end

end File_Embedded
-- ===== end RequestProject/Embedded.lean =====

-- ===== begin RequestProject/Main.lean =====
section File_Main


/-!
# Formalization of Chapter 3 ("Properties of Curve Shortening Flow")
of `MTL603_PDE_project-9-13.pdf`

* Lemma 1: `CSF.lemma1_arclength_hasDerivAt`, `CSF.lemma1_arclength_derivative`
* Lemma 2: `CSF.IsCSF.lemma2_speed_evolution`
* Lemma 3: `CSF.IsCSF.lemma3_commutator`
* Lemma 4: `CSF.IsCSF.lemma4_tangent_evolution`, `CSF.IsCSF.lemma4_normal_evolution`
* Lemma 5: `CSF.IsCSF.lemma5_curvature_evolution`
* Lemma 6: `CSF.lemma6_length_evolution`, `CSF.lemma6_area_evolution_total_curvature`,
  `CSF.lemma6_area_evolution`
* Remark after Lemma 6: `CSF.area_linear_decay`, `CSF.maximal_time_le`, `CSF.maximal_time_eq`
* Theorem 3.0.1: `CSF.theorem_3_0_1`
-/

/-!
## Axiom check

Each result below should depend only on the standard axioms `propext`, `Classical.choice`,
and `Quot.sound`. Anything else (in particular `sorryAx`) indicates an unproved gap.
-/

#print axioms CSF.lemma1_arclength_derivative
#print axioms CSF.IsCSF.lemma2_speed_evolution
#print axioms CSF.IsCSF.lemma3_commutator
#print axioms CSF.IsCSF.lemma4_tangent_evolution
#print axioms CSF.IsCSF.lemma4_normal_evolution
#print axioms CSF.IsCSF.lemma5_curvature_evolution
#print axioms CSF.lemma6_length_evolution
#print axioms CSF.lemma6_area_evolution
#print axioms CSF.maximal_time_le
#print axioms CSF.maximal_time_eq
#print axioms CSF.theorem_3_0_1

end File_Main
-- ===== end RequestProject/Main.lean =====

