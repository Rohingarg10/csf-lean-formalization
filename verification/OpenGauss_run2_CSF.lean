import Mathlib

/-!
# Properties of curve shortening flow

Source: `MTL603_PDE_project-9-13.pdf`, Chapter 3, printed pages 8–12.
Each declaration below identifies its source claim. Analytic regularity assumptions are
explicit. The accompanying coverage document records which source claims remain unfinished.
-/

noncomputable section

open scoped InnerProductSpace Topology Interval
open Filter Set MeasureTheory

namespace CSF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The speed `v = ‖∂γ/∂u‖` in Lemma 1, printed page 8 of
`MTL603_PDE_project-9-13.pdf`. -/
def speed (γ : ℝ → E) (u : ℝ) : ℝ := ‖deriv γ u‖

/-- The arclength coordinate used in the proof of Lemma 1, printed page 8 of
`MTL603_PDE_project-9-13.pdf`, with an arbitrary base parameter `a`. -/
def arclength (γ : ℝ → E) (a u : ℝ) : ℝ := ∫ w in a..u, speed γ w

/-- Lemma 1, the identity `∂s/∂u = v`, printed page 8 of
`MTL603_PDE_project-9-13.pdf`. Continuity of speed makes the FTC applicable. -/
theorem hasDerivAt_arclength (γ : ℝ → E) (a u : ℝ)
    (h : Continuous (speed γ)) : HasDerivAt (arclength γ a) (speed γ u) u := by
  exact intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable a u)
    (h.stronglyMeasurableAtFilter _ _) h.continuousAt

/-- Lemma 1, the operator identity `∂/∂s = (1/v) ∂/∂u`, printed page 8 of
`MTL603_PDE_project-9-13.pdf`, expressed by testing it on an arbitrary differentiable
vector-valued function of the arclength coordinate. Regularity means `v ≠ 0`. -/
theorem arclength_chain_rule {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (γ : ℝ → E) (a u : ℝ) (f : ℝ → V)
    (h : Continuous (speed γ)) (hv : speed γ u ≠ 0)
    (hf : DifferentiableAt ℝ f (arclength γ a u)) :
    deriv f (arclength γ a u) =
      (speed γ u)⁻¹ • deriv (fun w ↦ f (arclength γ a w)) u := by
  change deriv f (arclength γ a u) = (speed γ u)⁻¹ • deriv (f ∘ arclength γ a) u
  rw [(hf.hasDerivAt.scomp u (hasDerivAt_arclength γ a u h)).deriv]
  simp [smul_smul, hv]

/-- The orthonormal tangent/normal frame used in Lemmas 2–5, printed pages 9–11 of
`MTL603_PDE_project-9-13.pdf`. The last field expresses that the ambient plane is
spanned by the two vectors; it rules out extra normal directions in higher dimension. -/
structure PlaneFrame (T n : E) : Prop where
  tangent_unit : ⟪T, T⟫_ℝ = 1
  normal_unit : ⟪n, n⟫_ℝ = 1
  orthogonal : ⟪T, n⟫_ℝ = 0
  expansion : ∀ w : E, w = ⟪T, w⟫_ℝ • T + ⟪n, w⟫_ℝ • n

/-- A calculus step used when differentiating the unit frame in Lemmas 2 and 4,
printed pages 9–10 of `MTL603_PDE_project-9-13.pdf`: the derivative of a unit vector
is orthogonal to that vector. -/
theorem inner_deriv_of_unit {f : ℝ → E} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hunit : ∀ᶠ y in 𝓝 x, ⟪f y, f y⟫_ℝ = 1) :
    ⟪f x, deriv f x⟫_ℝ = 0 := by
  have h := (hf.hasDerivAt.inner ℝ hf.hasDerivAt).unique
    ((hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hunit)
  rw [← real_inner_comm (deriv f x) (f x)] at h
  linarith

/-- The differentiation of `T · n = 0` used in Lemma 4, printed page 10 of
`MTL603_PDE_project-9-13.pdf`, with the unit-length and planar hypotheses made explicit. -/
theorem normal_derivative {T n : ℝ → E} {x : ℝ}
    (hT : DifferentiableAt ℝ T x) (hn : DifferentiableAt ℝ n x)
    (hframe : ∀ᶠ y in 𝓝 x, PlaneFrame (T y) (n y)) :
    deriv n x = -⟪n x, deriv T x⟫_ℝ • T x := by
  have hzero := inner_deriv_of_unit hn (hframe.mono fun _ h ↦ h.normal_unit)
  have horth := (hT.hasDerivAt.inner ℝ hn.hasDerivAt).unique
    ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (hframe.mono fun _ h ↦ h.orthogonal))
  rw [← real_inner_comm (deriv T x) (n x)] at horth
  rw [(hframe.self_of_nhds).expansion (deriv n x), hzero, zero_smul, add_zero]
  congr 1
  linarith

/-- A regular classical planar CSF with its Frenet frame, as used throughout Lemmas 2–5
of `MTL603_PDE_project-9-13.pdf`, printed pages 9–11. Time ranges over an open set `J`;
the spatial coordinate is a real lift of a curve parameter. The spatial Frenet equation
defines the signed curvature. Mixed-partial symmetry is stated explicitly as the analytic
regularity used by the source; no time-evolution conclusion is a field of this structure.
Closedness and embeddedness are separate global hypotheses, not part of this local model. -/
structure Flow (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (J : Set ℝ) where
  position : ℝ → ℝ → E
  tangent : ℝ → ℝ → E
  normal : ℝ → ℝ → E
  velocity : ℝ → ℝ → ℝ
  curvature : ℝ → ℝ → ℝ
  time_open : IsOpen J
  velocity_pos : ∀ u t, t ∈ J → 0 < velocity u t
  frame : ∀ u t, t ∈ J → PlaneFrame (tangent u t) (normal u t)
  position_u : ∀ u t, t ∈ J →
    HasDerivAt (fun w ↦ position w t) (velocity u t • tangent u t) u
  position_t : ∀ u t, t ∈ J →
    HasDerivAt (position u) (curvature u t • normal u t) t
  tangent_u : ∀ u t, t ∈ J →
    HasDerivAt (fun w ↦ tangent w t) ((velocity u t * curvature u t) • normal u t) u
  normal_u_diff : ∀ u t, t ∈ J → DifferentiableAt ℝ (fun w ↦ normal w t) u
  tangent_t_diff : ∀ u t, t ∈ J → DifferentiableAt ℝ (tangent u) t
  normal_t_diff : ∀ u t, t ∈ J → DifferentiableAt ℝ (normal u) t
  velocity_u_diff : ∀ u t, t ∈ J → DifferentiableAt ℝ (fun w ↦ velocity w t) u
  velocity_t_diff : ∀ u t, t ∈ J → DifferentiableAt ℝ (velocity u) t
  curvature_u_diff : ∀ u t, t ∈ J → DifferentiableAt ℝ (fun w ↦ curvature w t) u
  curvature_t_diff : ∀ u t, t ∈ J → DifferentiableAt ℝ (curvature u) t
  position_mixed : ∀ u t, t ∈ J →
    deriv (fun τ ↦ deriv (fun w ↦ position w τ) u) t =
      deriv (fun w ↦ deriv (position w) t) u
  tangent_mixed : ∀ u t, t ∈ J →
    deriv (fun τ ↦ deriv (fun w ↦ tangent w τ) u) t =
      deriv (fun w ↦ deriv (tangent w) t) u

namespace Flow

variable {J : Set ℝ} (F : Flow E J) {u t : ℝ}

/-- Identification of the positive coefficient in the Frenet frame with the speed
`v = ‖γᵤ‖` from Lemma 1, printed page 8 of `MTL603_PDE_project-9-13.pdf`. -/
theorem velocity_eq_speed (ht : t ∈ J) :
    F.velocity u t = speed (fun w ↦ F.position w t) u := by
  have hnorm : ‖F.tangent u t‖ = 1 := by
    have h := (F.frame u t ht).tangent_unit
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (F.tangent u t)]
  simp [speed, (F.position_u u t ht).deriv, norm_smul, hnorm,
    Real.norm_eq_abs, abs_of_pos (F.velocity_pos u t ht)]

/-- The second Serret–Frenet equation used in the proof of Lemma 2, printed page 9 of
`MTL603_PDE_project-9-13.pdf`. It follows from the first Frenet equation and orthonormality. -/
theorem normal_u (ht : t ∈ J) :
    HasDerivAt (fun w ↦ F.normal w t)
      (-(F.velocity u t * F.curvature u t) • F.tangent u t) u := by
  have h := normal_derivative (F.tangent_u u t ht).differentiableAt
    (F.normal_u_diff u t ht) (Filter.Eventually.of_forall fun w ↦ F.frame w t ht)
  rw [(F.tangent_u u t ht).deriv] at h
  simp only [inner_smul_right, (F.frame u t ht).normal_unit, mul_one] at h
  exact h ▸ (F.normal_u_diff u t ht).hasDerivAt

/-- The commuting mixed derivatives of `γ`, expanded using CSF and the Frenet equations
as in the proof of Lemma 2, printed page 9 of `MTL603_PDE_project-9-13.pdf`. -/
theorem mixed_frame_identity (ht : t ∈ J) :
    deriv (F.velocity u) t • F.tangent u t +
        F.velocity u t • deriv (F.tangent u) t =
      deriv (fun w ↦ F.curvature w t) u • F.normal u t +
        F.curvature u t • (-(F.velocity u t * F.curvature u t) • F.tangent u t) := by
  have hleft := ((F.velocity_t_diff u t ht).hasDerivAt.smul
    (F.tangent_t_diff u t ht).hasDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.mono (F.time_open.mem_nhds ht) fun τ hτ ↦ (F.position_u u τ hτ).deriv)
  have hright := ((F.curvature_u_diff u t ht).hasDerivAt.smul
    (F.normal_u ht)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w ↦ (F.position_t w t ht).deriv)
  simpa only [add_comm] using hleft.deriv.symm.trans
    ((F.position_mixed u t ht).trans hright.deriv)

/-- Lemma 2, `∂v/∂t = -κ²v`, printed pages 8–9 of `MTL603_PDE_project-9-13.pdf`. -/
theorem velocity_evolution (ht : t ∈ J) :
    deriv (F.velocity u) t = -(F.curvature u t)^2 * F.velocity u t := by
  have hz := inner_deriv_of_unit (F.tangent_t_diff u t ht)
    (Filter.Eventually.mono (F.time_open.mem_nhds ht) fun τ hτ ↦ (F.frame u τ hτ).tangent_unit)
  have h := congrArg (fun w ↦ ⟪F.tangent u t, w⟫_ℝ)
    (F.mixed_frame_identity (u := u) ht)
  simp only [inner_add_right, inner_smul_right, (F.frame u t ht).tangent_unit,
    (F.frame u t ht).orthogonal, hz, mul_one, mul_zero, add_zero, zero_add] at h
  nlinarith [h]

/-- The arclength differential operator from Lemma 1, used in Lemma 3,
printed pages 8–9 of `MTL603_PDE_project-9-13.pdf`. -/
def arcDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ → ℝ → V) (u t : ℝ) : V :=
  (F.velocity u t)⁻¹ • deriv (fun w ↦ f w t) u

/-- The time derivative of `1/v` calculated in Lemma 3's proof,
printed page 9 of `MTL603_PDE_project-9-13.pdf`. -/
theorem inverse_velocity_evolution (ht : t ∈ J) :
    HasDerivAt (fun τ ↦ (F.velocity u τ)⁻¹)
      ((F.curvature u t)^2 / F.velocity u t) t := by
  have hv := ne_of_gt (F.velocity_pos u t ht)
  convert (F.velocity_t_diff u t ht).hasDerivAt.inv hv using 1
  rw [F.velocity_evolution ht]
  field_simp

/-- Lemma 3, `[∂t, ∂s]f = κ² ∂s f`, printed page 9 of
`MTL603_PDE_project-9-13.pdf`. The test field can be scalar- or vector-valued.
Its mixed-partial symmetry and the differentiability needed for the product rule
are explicit hypotheses, as in the source's calculation. -/
theorem arclength_commutator {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ → ℝ → V) (ht : t ∈ J)
    (hd : DifferentiableAt ℝ (fun τ ↦ deriv (fun w ↦ f w τ) u) t)
    (hmix : deriv (fun τ ↦ deriv (fun w ↦ f w τ) u) t =
      deriv (fun w ↦ deriv (f w) t) u) :
    deriv (fun τ ↦ F.arcDeriv f u τ) t =
      F.arcDeriv (fun w τ ↦ deriv (f w) τ) u t +
        (F.curvature u t)^2 • F.arcDeriv f u t := by
  simpa only [arcDeriv, Pi.smul_apply, smul_smul, div_eq_mul_inv, hmix] using
    ((F.inverse_velocity_evolution (u := u) ht).smul hd.hasDerivAt).deriv

/-- Lemma 4, the tangent evolution `∂T/∂t = (∂κ/∂s)n`, printed page 10 of
`MTL603_PDE_project-9-13.pdf`. -/
theorem tangent_evolution (ht : t ∈ J) :
    deriv (F.tangent u) t = F.arcDeriv F.curvature u t • F.normal u t := by
  have hz := inner_deriv_of_unit (F.tangent_t_diff u t ht)
    (Filter.Eventually.mono (F.time_open.mem_nhds ht)
      fun τ hτ ↦ (F.frame u τ hτ).tangent_unit)
  have hnT : ⟪F.normal u t, F.tangent u t⟫_ℝ = 0 := by
    rw [real_inner_comm, (F.frame u t ht).orthogonal]
  have h := congrArg (fun w ↦ ⟪F.normal u t, w⟫_ℝ)
    (F.mixed_frame_identity (u := u) ht)
  simp only [inner_add_right, inner_smul_right, hnT, (F.frame u t ht).normal_unit,
    mul_zero, mul_one, zero_add, add_zero] at h
  rw [(F.frame u t ht).expansion (deriv (F.tangent u) t), hz, zero_smul, zero_add]
  congr 1
  dsimp [arcDeriv]
  rw [← h]
  field_simp [ne_of_gt (F.velocity_pos u t ht)]

/-- Lemma 4, the normal evolution `∂n/∂t = -(∂κ/∂s)T`, printed page 10 of
`MTL603_PDE_project-9-13.pdf`. The planar unit-frame argument supplies the
unit-normal constraint implicit in the source's proof. -/
theorem normal_evolution (ht : t ∈ J) :
    deriv (F.normal u) t = -F.arcDeriv F.curvature u t • F.tangent u t := by
  have h := normal_derivative (F.tangent_t_diff u t ht) (F.normal_t_diff u t ht)
    (Filter.Eventually.mono (F.time_open.mem_nhds ht) fun τ hτ ↦ F.frame u τ hτ)
  rw [F.tangent_evolution ht] at h
  simpa only [inner_smul_right, (F.frame u t ht).normal_unit, mul_one] using h

/-- Lemma 5, `∂κ/∂t = ∂²κ/∂s² + κ³`, printed pages 10–11 of
`MTL603_PDE_project-9-13.pdf`. The extra differentiability hypothesis is the existence
of the second spatial derivative appearing in the conclusion. This proof differentiates
the Frenet equation directly, avoiding a global choice of tangent angle. -/
theorem curvature_evolution (ht : t ∈ J)
    (hks : DifferentiableAt ℝ (fun w ↦ F.arcDeriv F.curvature w t) u) :
    deriv (F.curvature u) t =
      F.arcDeriv (F.arcDeriv F.curvature) u t + (F.curvature u t)^3 := by
  have hleft := (((F.velocity_t_diff u t ht).hasDerivAt.mul
    (F.curvature_t_diff u t ht).hasDerivAt).smul
      (F.normal_t_diff u t ht).hasDerivAt).congr_of_eventuallyEq
        (Filter.Eventually.mono (F.time_open.mem_nhds ht)
          fun τ hτ ↦ (F.tangent_u u τ hτ).deriv)
  have hright := (hks.hasDerivAt.smul (F.normal_u ht)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w ↦ F.tangent_evolution (u := w) ht)
  have h := congrArg (fun w ↦ ⟪F.normal u t, w⟫_ℝ)
    (hleft.deriv.symm.trans ((F.tangent_mixed u t ht).trans hright.deriv))
  have hz := inner_deriv_of_unit (F.normal_t_diff u t ht)
    (Filter.Eventually.mono (F.time_open.mem_nhds ht)
      fun τ hτ ↦ (F.frame u τ hτ).normal_unit)
  have hnT : ⟪F.normal u t, F.tangent u t⟫_ℝ = 0 := by
    rw [real_inner_comm, (F.frame u t ht).orthogonal]
  simp only [inner_add_right, inner_smul_right, hz, hnT,
    (F.frame u t ht).normal_unit, mul_zero, mul_one, zero_add,
    F.velocity_evolution ht] at h
  change deriv (F.curvature u) t = (F.velocity u t)⁻¹ *
    deriv (fun w ↦ F.arcDeriv F.curvature w t) u + (F.curvature u t)^3
  have hv := ne_of_gt (F.velocity_pos u t ht)
  apply (mul_left_cancel₀ hv)
  field_simp [hv] at h ⊢
  nlinarith [h]

/-- Differentiation under the parameter integral used in Lemma 6, printed page 11 of
`MTL603_PDE_project-9-13.pdf`. Joint continuity of the derivative on the open time
strip supplies a uniform bound on each compact parameter interval. -/
theorem hasDerivAt_intervalIntegral {f f' : ℝ → ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (hJ : IsOpen J) (ht : t ∈ J) (a b : ℝ)
    (hc : ∀ τ ∈ J, Continuous (fun u ↦ f u τ))
    (hc' : ContinuousOn (fun p : ℝ × ℝ ↦ f' p.1 p.2) (univ ×ˢ J))
    (hd : ∀ u τ, τ ∈ J → HasDerivAt (f u) (f' u τ) τ) :
    HasDerivAt (fun τ ↦ ∫ u in a..b, f u τ) (∫ u in a..b, f' u t) t := by
  obtain ⟨K, hKt, hKJ, hKc⟩ := local_compact_nhds (hJ.mem_nhds ht)
  have hsub : Set.uIcc a b ×ˢ K ⊆ (univ : Set ℝ) ×ˢ J :=
    fun _ hp ↦ ⟨mem_univ _, hKJ hp.2⟩
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod hKc).bddAbove_image (hc'.norm.mono hsub)
  have hct : Continuous (fun u ↦ f' u t) :=
    continuousOn_univ.mp
      (hc'.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ _ ↦ ⟨mem_univ _, ht⟩))
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ u ↦ f u τ) (F' := fun τ u ↦ f' u τ) (bound := fun _ ↦ C) hKt
    (Filter.Eventually.mono (hJ.mem_nhds ht) fun τ hτ ↦ (hc τ hτ).aestronglyMeasurable)
    ((hc t ht).intervalIntegrable a b) hct.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u hu τ hτ ↦
      hC (mem_image_of_mem (fun p : ℝ × ℝ ↦ ‖f' p.1 p.2‖)
        (show (u, τ) ∈ Set.uIcc a b ×ˢ K from ⟨uIoc_subset_uIcc hu, hτ⟩)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun u _ τ hτ ↦ hd u τ (hKJ hτ))).2

/-- Length `L(t) = ∫₀²π v(u,t) du` in Lemma 6(i), printed page 11 of
`MTL603_PDE_project-9-13.pdf`. The interval version also applies to an open arc. -/
def length (a b t : ℝ) : ℝ := ∫ u in a..b, F.velocity u t

/-- Integration against arclength `ds = v du`, used in Lemma 6,
printed page 11 of `MTL603_PDE_project-9-13.pdf`. -/
def arcIntegral (f : ℝ → ℝ → ℝ) (a b t : ℝ) : ℝ :=
  ∫ u in a..b, f u t * F.velocity u t

/-- Lemma 6(i), `dL/dt = -∫ κ² ds`, printed page 11 of
`MTL603_PDE_project-9-13.pdf`. For a closed curve take `a = 0`, `b = 2π`.
Joint continuity of speed and curvature is the explicit classical regularity needed
to differentiate under the integral; no integral-evolution identity is assumed. -/
theorem length_evolution (ht : t ∈ J) (a b : ℝ)
    (hv : ContinuousOn (fun p : ℝ × ℝ ↦ F.velocity p.1 p.2) (univ ×ˢ J))
    (hk : ContinuousOn (fun p : ℝ × ℝ ↦ F.curvature p.1 p.2) (univ ×ˢ J)) :
    HasDerivAt (F.length a b) (-F.arcIntegral (fun u t ↦ (F.curvature u t)^2) a b t) t := by
  have h := hasDerivAt_intervalIntegral F.time_open ht a b
    (fun τ hτ ↦ (show Differentiable ℝ (fun u ↦ F.velocity u τ) from
      fun u ↦ F.velocity_u_diff u τ hτ).continuous)
    ((hk.pow 2).neg.mul hv)
    (fun u τ hτ ↦ F.velocity_evolution hτ ▸ (F.velocity_t_diff u τ hτ).hasDerivAt)
  simpa only [length, arcIntegral, neg_mul, intervalIntegral.integral_neg] using h

/-- The support-function area density `v γ · n` in Lemma 6(ii), printed page 11 of
`MTL603_PDE_project-9-13.pdf`. -/
def support (u t : ℝ) : ℝ := F.velocity u t * ⟪F.position u t, F.normal u t⟫_ℝ

/-- The periodic boundary term integrated by parts in Lemma 6(ii), printed pages 11–12
of `MTL603_PDE_project-9-13.pdf`. -/
def tangentFlux (u t : ℝ) : ℝ := F.curvature u t * ⟪F.position u t, F.tangent u t⟫_ℝ

/-- The spatial derivative of the boundary term in Lemma 6(ii), printed pages 11–12
of `MTL603_PDE_project-9-13.pdf`, written without a derivative operator to make its
continuity assumptions transparent. -/
def tangentFluxDerivative (u t : ℝ) : ℝ :=
  deriv (fun w ↦ F.curvature w t) u * ⟪F.position u t, F.tangent u t⟫_ℝ +
    F.curvature u t * (F.velocity u t +
      F.velocity u t * F.curvature u t * ⟪F.position u t, F.normal u t⟫_ℝ)

/-- The product-rule calculation behind the integration by parts in Lemma 6(ii),
printed pages 11–12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem tangentFlux_hasDerivAt (ht : t ∈ J) :
    HasDerivAt (fun w ↦ F.tangentFlux w t) (F.tangentFluxDerivative u t) u := by
  convert (F.curvature_u_diff u t ht).hasDerivAt.mul
    ((F.position_u u t ht).inner ℝ (F.tangent_u u t ht)) using 1
  simp only [tangentFluxDerivative, inner_smul_right, real_inner_smul_left,
    (F.frame u t ht).tangent_unit, mul_one]
  ring

/-- The time derivative of the area density in Lemma 6(ii), printed pages 11–12 of
`MTL603_PDE_project-9-13.pdf`: `∂t(v γ·n) = 2κv - ∂u(κ γ·T)`. -/
theorem support_evolution (ht : t ∈ J) :
    HasDerivAt (F.support u)
      (2 * F.curvature u t * F.velocity u t - F.tangentFluxDerivative u t) t := by
  have h := (F.velocity_t_diff u t ht).hasDerivAt.mul
    ((F.position_t u t ht).inner ℝ (F.normal_t_diff u t ht).hasDerivAt)
  convert h using 1
  simp only [F.velocity_evolution ht, F.normal_evolution ht, inner_smul_right,
    real_inner_smul_left, (F.frame u t ht).normal_unit, mul_one, tangentFluxDerivative,
    arcDeriv, smul_eq_mul]
  field_simp [ne_of_gt (F.velocity_pos u t ht)]
  ring

/-- Joint continuity used to justify the integrals in Lemma 6(ii), printed pages 11–12
of `MTL603_PDE_project-9-13.pdf`. These are regularity hypotheses, not evolution laws.
They hold for a smooth regular classical flow with smooth curvature. -/
structure IntegralRegularity : Prop where
  position : ContinuousOn (fun p : ℝ × ℝ ↦ F.position p.1 p.2) (univ ×ˢ J)
  tangent : ContinuousOn (fun p : ℝ × ℝ ↦ F.tangent p.1 p.2) (univ ×ˢ J)
  normal : ContinuousOn (fun p : ℝ × ℝ ↦ F.normal p.1 p.2) (univ ×ˢ J)
  velocity : ContinuousOn (fun p : ℝ × ℝ ↦ F.velocity p.1 p.2) (univ ×ˢ J)
  curvature : ContinuousOn (fun p : ℝ × ℝ ↦ F.curvature p.1 p.2) (univ ×ˢ J)
  curvature_u :
    ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun w ↦ F.curvature w p.2) p.1) (univ ×ˢ J)

/-- Continuity of the boundary-term derivative in Lemma 6(ii), printed pages 11–12
of `MTL603_PDE_project-9-13.pdf`, needed for the fundamental theorem of calculus. -/
theorem tangentFluxDerivative_continuous (h : F.IntegralRegularity) :
    ContinuousOn (fun p : ℝ × ℝ ↦ F.tangentFluxDerivative p.1 p.2) (univ ×ˢ J) :=
  (h.curvature_u.mul (h.position.inner h.tangent)).add
    (h.curvature.mul (h.velocity.add
      ((h.velocity.mul h.curvature).mul (h.position.inner h.normal))))

/-- The Green/support integral for area in Lemma 6(ii), printed page 11 of
`MTL603_PDE_project-9-13.pdf`. For an inward-normal simple closed plane curve this is
the enclosed area by Green's theorem. That geometric identification is not built
into this definition: on general framed curves it is a signed support integral. -/
def signedArea (a b t : ℝ) : ℝ := -(1 / 2 : ℝ) * ∫ u in a..b, F.support u t

/-- The calculation in Lemma 6(ii), printed pages 11–12 of
`MTL603_PDE_project-9-13.pdf`, before cancellation of the periodic boundary term.
This is a theorem about the signed Green/support integral; identifying it with
geometric enclosed area requires Green's theorem for the given simple closed curve. -/
theorem signedArea_evolution_with_boundary (ht : t ∈ J) (a b : ℝ)
    (h : F.IntegralRegularity) :
    HasDerivAt (F.signedArea a b)
      (-F.arcIntegral F.curvature a b t + (F.tangentFlux b t - F.tangentFlux a t) / 2) t := by
  have hflux : Continuous (fun w ↦ F.tangentFluxDerivative w t) :=
    continuousOn_univ.mp ((F.tangentFluxDerivative_continuous h).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ _ ↦ ⟨mem_univ _, ht⟩))
  have hkv : Continuous (fun w ↦ F.curvature w t * F.velocity w t) :=
    (show Differentiable ℝ (fun w ↦ F.curvature w t) from
      fun w ↦ F.curvature_u_diff w t ht).continuous.mul
    (show Differentiable ℝ (fun w ↦ F.velocity w t) from
      fun w ↦ F.velocity_u_diff w t ht).continuous
  have hint := hasDerivAt_intervalIntegral F.time_open ht a b
    (f := F.support) (f' := fun u τ ↦
      2 * F.curvature u τ * F.velocity u τ - F.tangentFluxDerivative u τ)
    (fun τ hτ ↦ (show Differentiable ℝ (fun w ↦ F.velocity w τ) from
        fun w ↦ F.velocity_u_diff w τ hτ).continuous.mul
      ((show Differentiable ℝ (fun w ↦ F.position w τ) from
          fun w ↦ (F.position_u w τ hτ).differentiableAt).continuous.inner
        (show Differentiable ℝ (fun w ↦ F.normal w τ) from
          fun w ↦ F.normal_u_diff w τ hτ).continuous))
    (((continuousOn_const.mul h.curvature).mul h.velocity).sub
      (F.tangentFluxDerivative_continuous h))
    (fun u τ hτ ↦ F.support_evolution (u := u) hτ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ F.tangentFlux_hasDerivAt (u := u) ht) (hflux.intervalIntegrable a b)
  convert hint.const_mul (-(1 / 2 : ℝ)) using 1
  rw [intervalIntegral.integral_sub
    (by simpa only [mul_assoc] using (continuous_const.mul hkv).intervalIntegrable a b)
    (hflux.intervalIntegrable a b), hFTC]
  simp only [mul_assoc, intervalIntegral.integral_const_mul, arcIntegral]
  ring

/-- The integrated identity `dA/dt = -∫κ ds` in Lemma 6(ii), printed page 12 of
`MTL603_PDE_project-9-13.pdf`, for the signed Green/support integral of a closed framed
curve. Matching position, tangent, and curvature at the endpoints cancels the flux. -/
theorem signedArea_evolution (ht : t ∈ J) (a b : ℝ) (h : F.IntegralRegularity)
    (hγ : F.position b t = F.position a t) (hT : F.tangent b t = F.tangent a t)
    (hk : F.curvature b t = F.curvature a t) :
    HasDerivAt (F.signedArea a b) (-F.arcIntegral F.curvature a b t) t := by
  simpa only [tangentFlux, hγ, hT, hk, sub_self, zero_div, add_zero] using
    F.signedArea_evolution_with_boundary ht a b h

/-- The last algebraic step of Lemma 6(ii), printed page 12 of
`MTL603_PDE_project-9-13.pdf`, conditional on the total-turning identity `∫κ ds = 2π`.
This auxiliary theorem does not prove that identity from embeddedness. -/
theorem signedArea_evolution_of_total_curvature (ht : t ∈ J) (a b : ℝ)
    (h : F.IntegralRegularity) (hγ : F.position b t = F.position a t)
    (hT : F.tangent b t = F.tangent a t) (hk : F.curvature b t = F.curvature a t)
    (hturn : F.arcIntegral F.curvature a b t = 2 * Real.pi) :
    HasDerivAt (F.signedArea a b) (-(2 * Real.pi)) t := by
  simpa only [hturn] using F.signedArea_evolution ht a b h hγ hT hk

/-- Nonincrease of length asserted after Lemma 6, printed page 12 of
`MTL603_PDE_project-9-13.pdf`, on any convex open time interval. -/
theorem length_antitoneOn (hJ : Convex ℝ J) {a b : ℝ} (hab : a ≤ b)
    (hv : ContinuousOn (fun p : ℝ × ℝ ↦ F.velocity p.1 p.2) (univ ×ˢ J))
    (hk : ContinuousOn (fun p : ℝ × ℝ ↦ F.curvature p.1 p.2) (univ ×ˢ J)) :
    AntitoneOn (F.length a b) J := by
  have hd : ∀ t ∈ J, HasDerivAt (F.length a b)
      (-F.arcIntegral (fun u t ↦ (F.curvature u t)^2) a b t) t :=
    fun t ht ↦ F.length_evolution ht a b hv hk
  apply antitoneOn_of_deriv_nonpos hJ
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  apply neg_nonpos.mpr
  exact intervalIntegral.integral_nonneg_of_forall hab fun u ↦
    mul_nonneg (sq_nonneg _) (F.velocity_pos u t (interior_subset ht)).le

end Flow

/-- The Euclidean plane in Lemma 6 and Theorem 3.0.1, printed pages 11–12 of
`MTL603_PDE_project-9-13.pdf`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Flow

variable {J : Set ℝ} (F : Flow Plane J)

/-- A closed framed curve with parameter period `2π`, as used in Lemma 6 and
Theorem 3.0.1, printed pages 11–12 of `MTL603_PDE_project-9-13.pdf`.
This is a real-periodic lift of the circle parameter and its geometric fields. -/
structure ClosedAt (t : ℝ) : Prop where
  position : Function.Periodic (fun u ↦ F.position u t) (2 * Real.pi)
  tangent : Function.Periodic (fun u ↦ F.tangent u t) (2 * Real.pi)
  normal : Function.Periodic (fun u ↦ F.normal u t) (2 * Real.pi)
  velocity : Function.Periodic (fun u ↦ F.velocity u t) (2 * Real.pi)
  curvature : Function.Periodic (fun u ↦ F.curvature u t) (2 * Real.pi)

/-- Embeddedness in Lemma 6 and Theorem 3.0.1, printed pages 11–12 of
`MTL603_PDE_project-9-13.pdf`: the periodic curve is injective on one half-open period.
For a continuous regular closed curve this expresses embedding of its circle parameter. -/
def EmbeddedAt (t : ℝ) : Prop :=
  Set.InjOn (fun u ↦ F.position u t) (Ico 0 (2 * Real.pi))

/-- The region enclosed by a simple closed curve in Lemma 6(ii), printed page 11 of
`MTL603_PDE_project-9-13.pdf`, described as the union of bounded complementary
components. For a Jordan curve there is exactly one such component. -/
def enclosedRegion (t : ℝ) : Set Plane :=
  {x | x ∉ Set.range (fun u ↦ F.position u t) ∧
    Bornology.IsBounded (connectedComponentIn (Set.range (fun u ↦ F.position u t))ᶜ x)}

/-- The inward-normal choice in Lemma 6(ii), printed page 11 of
`MTL603_PDE_project-9-13.pdf`: sufficiently short positive normal segments lie inside
the curve. This fixes the sign needed for the total-curvature and area formulas. -/
def InwardAt (t : ℝ) : Prop :=
  ∀ u, ∃ ε > 0, ∀ r ∈ Ioo 0 ε, F.position u t + r • F.normal u t ∈ F.enclosedRegion t

/-- Geometric enclosed area `A(t)` in Lemma 6(ii), printed page 11 of
`MTL603_PDE_project-9-13.pdf`, as Lebesgue area of the bounded complementary region. -/
def enclosedArea (t : ℝ) : ℝ := (volume (F.enclosedRegion t)).toReal

/-- Nonnegativity of enclosed area used after Lemma 6, printed page 12 of
`MTL603_PDE_project-9-13.pdf`. -/
theorem enclosedArea_nonneg (t : ℝ) : 0 ≤ F.enclosedArea t := ENNReal.toReal_nonneg

/-- The Green's-theorem step explicitly invoked in Lemma 6(ii), printed page 11 of
`MTL603_PDE_project-9-13.pdf`.

UNFINISHED: requires Green's theorem for the Jordan region, including its measure and
boundary regularity. The definition of enclosed area is not replaced by the integral. -/
theorem signedArea_eq_enclosedArea {t : ℝ} (ht : t ∈ J) (hc : F.ClosedAt t)
    (he : F.EmbeddedAt t) (hn : F.InwardAt t) :
    F.signedArea 0 (2 * Real.pi) t = F.enclosedArea t := by
  sorry

/-- The total-turning step in Lemma 6(ii), printed page 12 of
`MTL603_PDE_project-9-13.pdf`: an embedded closed curve with inward unit normal has
total signed curvature `2π`. Embeddedness is essential; closedness alone does not suffice.

UNFINISHED: requires the turning-tangent theorem for regular simple closed planar curves. -/
theorem total_curvature_eq_two_pi {t : ℝ} (ht : t ∈ J) (hc : F.ClosedAt t)
    (he : F.EmbeddedAt t) (hn : F.InwardAt t) :
    F.arcIntegral F.curvature 0 (2 * Real.pi) t = 2 * Real.pi := by
  sorry

/-- Lemma 6(ii), `dA/dt = -2π`, printed pages 11–12 of
`MTL603_PDE_project-9-13.pdf`, for geometric enclosed area.
This proof currently depends on the two explicitly unfinished geometric lemmas above;
the analytic differentiation and integration-by-parts steps are proved independently. -/
theorem enclosedArea_evolution {t : ℝ} (ht : t ∈ J) (h : F.IntegralRegularity)
    (hc : ∀ τ ∈ J, F.ClosedAt τ) (he : ∀ τ ∈ J, F.EmbeddedAt τ)
    (hn : ∀ τ ∈ J, F.InwardAt τ) :
    HasDerivAt F.enclosedArea (-(2 * Real.pi)) t := by
  have hp : F.position (2 * Real.pi) t = F.position 0 t := by
    simpa only [zero_add] using (hc t ht).position 0
  have hT : F.tangent (2 * Real.pi) t = F.tangent 0 t := by
    simpa only [zero_add] using (hc t ht).tangent 0
  have hk : F.curvature (2 * Real.pi) t = F.curvature 0 t := by
    simpa only [zero_add] using (hc t ht).curvature 0
  apply (F.signedArea_evolution_of_total_curvature ht 0 (2 * Real.pi) h hp hT hk
    (F.total_curvature_eq_two_pi ht (hc t ht) (he t ht) (hn t ht))).congr_of_eventuallyEq
  exact Filter.Eventually.mono (F.time_open.mem_nhds ht) fun τ hτ ↦
    (F.signedArea_eq_enclosedArea hτ (hc τ hτ) (he τ hτ) (hn τ hτ)).symm

end Flow

/-- The linear area law implicit in the paragraph following Lemma 6, printed page 12 of
`MTL603_PDE_project-9-13.pdf`. This scalar consequence assumes the area evolution law;
it does not assume existence of a geometric flow up to the endpoint. -/
theorem area_affine {A : ℝ → ℝ} {T : ℝ} (hA : ContinuousOn A (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt A (-(2 * Real.pi)) t) {t : ℝ}
    (ht : t ∈ Icc 0 T) : A t = A 0 - 2 * Real.pi * t := by
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · simp [← heq]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope A (fun _ ↦ -(2 * Real.pi))
    hpos (hA.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs ↦ hd s ⟨hs.1, hs.2.trans_le ht.2⟩)
  have h := (eq_div_iff (ne_of_gt (sub_pos.mpr hpos))).mp hslope
  nlinarith [h]

/-- Strict decrease of area in the paragraph after Lemma 6, printed page 12 of
`MTL603_PDE_project-9-13.pdf`, as a consequence of `A' = -2π`. -/
theorem area_strictAntiOn {A : ℝ → ℝ} {T : ℝ} (hA : ContinuousOn A (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt A (-(2 * Real.pi)) t) :
    StrictAntiOn A (Icc 0 T) := by
  intro x hx y hy hxy
  rw [area_affine hA hd hx, area_affine hA hd hy]
  nlinarith [Real.pi_pos]

/-- The upper bound on the lifetime obtained from nonnegative area in the paragraph
after Lemma 6, printed page 12 of `MTL603_PDE_project-9-13.pdf`.
The endpoint `T` here is any time up to which a nonnegative continuous area exists. -/
theorem lifetime_le_of_nonnegative_area {A : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt A (-(2 * Real.pi)) t) (hnonneg : 0 ≤ A T) :
    T ≤ A 0 / (2 * Real.pi) := by
  have h := area_affine hA hd (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  nlinarith

/-- The extinction-time computation `T = A₀/(2π)` in the paragraph after Lemma 6,
printed page 12 of `MTL603_PDE_project-9-13.pdf`. Vanishing area at the endpoint is
explicit: the source invokes a prior shrinking-to-a-point/existence theorem for this
geometric input, which is not proved by this scalar calculation. -/
theorem extinction_time_of_zero_area {A : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt A (-(2 * Real.pi)) t) (hzero : A T = 0) :
    T = A 0 / (2 * Real.pi) := by
  have h := area_affine hA hd (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  apply (eq_div_iff (by positivity : 2 * Real.pi ≠ 0)).mpr
  nlinarith

/-- A classical closed CSF on the half-open time interval of Theorem 3.0.1,
printed page 12 of `MTL603_PDE_project-9-13.pdf`. The evolution equations hold at
positive interior times. At time zero the position and frame have continuous traces
and the initial curve is regular. This avoids assuming a backwards CSF extension
across time zero, which is not a hypothesis of the source theorem. -/
structure ClassicalClosedFlow (T₀ : ℝ) extends Flow Plane (Ioo 0 T₀) where
  closed : ∀ t ∈ Ico 0 T₀, toFlow.ClosedAt t
  position_continuous :
    ContinuousOn (fun p : ℝ × ℝ ↦ position p.1 p.2) (univ ×ˢ Ico 0 T₀)
  tangent_continuous :
    ContinuousOn (fun p : ℝ × ℝ ↦ tangent p.1 p.2) (univ ×ˢ Ico 0 T₀)
  normal_continuous :
    ContinuousOn (fun p : ℝ × ℝ ↦ normal p.1 p.2) (univ ×ˢ Ico 0 T₀)
  velocity_continuous :
    ContinuousOn (fun p : ℝ × ℝ ↦ velocity p.1 p.2) (univ ×ˢ Ico 0 T₀)
  curvature_continuous :
    ContinuousOn (fun p : ℝ × ℝ ↦ curvature p.1 p.2) (univ ×ˢ Ico 0 T₀)
  initial_position_u : ∀ u,
    HasDerivAt (fun w ↦ position w 0) (velocity u 0 • tangent u 0) u
  initial_velocity_pos : ∀ u, 0 < velocity u 0
  initial_frame : ∀ u, PlaneFrame (tangent u 0) (normal u 0)

/-- A second-derivative fact supporting the two-point minimum argument for Theorem 3.0.1,
printed page 12 of `MTL603_PDE_project-9-13.pdf`. A continuous function has nonnegative
second derivative at a local minimum (with Lean's totalized derivative convention). -/
theorem second_deriv_nonneg_of_localMin {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hneg := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hm, hmax] with y hmin hmax
    exact le_antisymm hmax hmin
  have hzero : deriv (deriv f) x = 0 := by
    simpa using heq.deriv.deriv_eq
  linarith

/-- At a nonzero common normal chord, planar unit tangents are parallel. This is a
geometric ingredient for Theorem 3.0.1, printed page 12 of
`MTL603_PDE_project-9-13.pdf`; the multiplier has square one. -/
theorem PlaneFrame.parallel_of_orthogonal {T n T' d : E} (hframe : PlaneFrame T n)
    (hunit : ⟪T', T'⟫_ℝ = 1) (hd : d ≠ 0) (hT : ⟪d, T⟫_ℝ = 0)
    (hT' : ⟪d, T'⟫_ℝ = 0) : ∃ a : ℝ, a^2 = 1 ∧ T' = a • T := by
  have hTd : ⟪T, d⟫_ℝ = 0 := by rw [real_inner_comm, hT]
  have hexp : d = ⟪n, d⟫_ℝ • n := by
    simpa only [hTd, zero_smul, zero_add] using hframe.expansion d
  have hb : ⟪n, d⟫_ℝ ≠ 0 := by
    intro hb
    apply hd
    simpa only [hb, zero_smul] using hexp
  have hprod : ⟪n, d⟫_ℝ * ⟪n, T'⟫_ℝ = 0 := by
    calc
      _ = ⟪⟪n, d⟫_ℝ • n, T'⟫_ℝ := (real_inner_smul_left _ _ _).symm
      _ = 0 := by rw [← hexp, hT']
  have hn : ⟪n, T'⟫_ℝ = 0 := (mul_eq_zero.mp hprod).resolve_left hb
  have hpar : T' = ⟪T, T'⟫_ℝ • T := by
    simpa only [hn, zero_smul, add_zero] using hframe.expansion T'
  refine ⟨⟪T, T'⟫_ℝ, ?_, hpar⟩
  have hnorm := hunit
  conv_lhs at hnorm => rw [hpar]
  simp only [real_inner_smul_left, inner_smul_right, hframe.tangent_unit, mul_one] at hnorm
  nlinarith

namespace Flow

variable {J : Set ℝ} (F : Flow E J) {u w t : ℝ}

/-- The acceleration test used for Theorem 3.0.1's distance minimum argument,
printed page 12 of `MTL603_PDE_project-9-13.pdf`: when velocity vanishes,
the second variation of squared norm is twice the inner product with acceleration. -/
theorem acceleration_nonneg_at_min {f f' : ℝ → E} {f'' : E}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf0 : f' 0 = 0)
    (hf2 : HasDerivAt f' f'' 0) (hm : IsLocalMin (fun s ↦ ‖f s‖^2) 0) :
    0 ≤ ⟪f 0, f''⟫_ℝ := by
  have heq : deriv (fun s ↦ ‖f s‖^2) = fun s ↦ 2 * ⟪f s, f' s⟫_ℝ :=
    funext fun s ↦ (hf s).norm_sq.deriv
  have hd : HasDerivAt (fun s ↦ 2 * ⟪f s, f' s⟫_ℝ) (2 * ⟪f 0, f''⟫_ℝ) 0 := by
    simpa only [hf0, inner_zero_left, inner_zero_right, add_zero] using
      ((hf 0).inner ℝ hf2).const_mul 2
  have hge := second_deriv_nonneg_of_localMin hm ((hf 0).continuousAt.norm.pow 2)
  rw [heq, hd.deriv] at hge
  linarith

/-- The spatial acceleration of the curve, used in the two-point argument for
Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem velocity_tangent_u (ht : t ∈ J) :
    HasDerivAt (fun x ↦ F.velocity x t • F.tangent x t)
      (deriv (fun x ↦ F.velocity x t) u • F.tangent u t +
        ((F.velocity u t)^2 * F.curvature u t) • F.normal u t) u := by
  convert (F.velocity_u_diff u t ht).hasDerivAt.smul (F.tangent_u u t ht) using 1
  simp only [smul_smul]
  module

/-- Affine parameter variation used in the two-point argument for Theorem 3.0.1,
printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem affine_parameter_derivative (a b s : ℝ) : HasDerivAt (fun x ↦ a + b*x) b s := by
  simpa only [mul_one] using ((hasDerivAt_id s).const_mul b).const_add a

/-- Squared two-point distance used in the avoidance argument for Theorem 3.0.1,
printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
def distanceSq (u w t : ℝ) : ℝ := ‖F.position u t - F.position w t‖^2

/-- Evolution of two-point squared distance under CSF, a supporting calculation for
Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem distanceSq_time (ht : t ∈ J) :
    HasDerivAt (F.distanceSq u w)
      (2 * ⟪F.position u t - F.position w t,
        F.curvature u t • F.normal u t - F.curvature w t • F.normal w t⟫_ℝ) t :=
  ((F.position_t u t ht).sub (F.position_t w t ht)).norm_sq

/-- First spatial derivative of two-point distance used in Theorem 3.0.1's avoidance
argument, printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem distanceSq_left (ht : t ∈ J) :
    HasDerivAt (fun x ↦ F.distanceSq x w t)
      (2 * F.velocity u t * ⟪F.position u t - F.position w t, F.tangent u t⟫_ℝ) u := by
  convert ((F.position_u u t ht).sub_const (F.position w t)).norm_sq using 1
  simp only [inner_smul_right]
  ring

/-- Second-parameter derivative of two-point distance used in Theorem 3.0.1's avoidance
argument, printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem distanceSq_right (ht : t ∈ J) :
    HasDerivAt (fun x ↦ F.distanceSq u x t)
      (-2 * F.velocity w t * ⟪F.position u t - F.position w t, F.tangent w t⟫_ℝ) w := by
  convert ((F.position_u w t ht).const_sub (F.position u t)).norm_sq using 1
  simp only [inner_neg_right, inner_smul_right]
  ring

/-- At a spatial minimum of squared distance, the chord is normal to both tangents.
This supports Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem distanceSq_min_orthogonal (ht : t ∈ J)
    (hu : IsLocalMin (fun x ↦ F.distanceSq x w t) u)
    (hw : IsLocalMin (fun x ↦ F.distanceSq u x t) w) :
    ⟪F.position u t - F.position w t, F.tangent u t⟫_ℝ = 0 ∧
      ⟪F.position u t - F.position w t, F.tangent w t⟫_ℝ = 0 := by
  have hleft := hu.hasDerivAt_eq_zero (F.distanceSq_left ht)
  have hright := hw.hasDerivAt_eq_zero (F.distanceSq_right ht)
  constructor
  · exact (mul_eq_zero.mp hleft).resolve_left (by
      have := F.velocity_pos u t ht
      positivity)
  · exact (mul_eq_zero.mp hright).resolve_left (by
      have := F.velocity_pos w t ht
      nlinarith)

/-- At a positive spatial local minimum, squared two-point distance cannot decrease
instantaneously under planar CSF. This is the differential part of the avoidance argument
for Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`. The simultaneous
parameter variation cancels the first-order velocities of the two endpoints. -/
theorem distanceSq_min_time_nonneg (ht : t ∈ J)
    (hdist : F.position u t ≠ F.position w t)
    (hm : IsLocalMin (fun p : ℝ × ℝ ↦ F.distanceSq p.1 p.2 t) (u, w)) :
    0 ≤ deriv (F.distanceSq u w) t := by
  have hleft : IsLocalMin (fun x ↦ F.distanceSq x w t) u :=
    hm.comp_continuous (g := fun x ↦ (x, w))
      (continuous_id.prodMk continuous_const).continuousAt
  have hright : IsLocalMin (fun x ↦ F.distanceSq u x t) w :=
    hm.comp_continuous (g := fun x ↦ (u, x))
      (continuous_const.prodMk continuous_id).continuousAt
  obtain ⟨hu, hw⟩ := F.distanceSq_min_orthogonal ht hleft hright
  obtain ⟨a, ha, hpar⟩ := (F.frame u t ht).parallel_of_orthogonal
    (F.frame w t ht).tangent_unit (sub_ne_zero.mpr hdist) hu hw
  let c := (F.velocity u t)⁻¹
  let d := a / F.velocity w t
  let P := fun s ↦ F.position (u + c*s) t - F.position (w + d*s) t
  let V := fun s ↦ c • (F.velocity (u + c*s) t • F.tangent (u + c*s) t) -
    d • (F.velocity (w + d*s) t • F.tangent (w + d*s) t)
  let A := fun x ↦ deriv (fun y ↦ F.velocity y t) x • F.tangent x t +
    ((F.velocity x t)^2 * F.curvature x t) • F.normal x t
  have hP : ∀ s, HasDerivAt P (V s) s := by
    intro s
    simpa only [P, V, Function.comp_def, Pi.sub_apply] using
      ((F.position_u (u + c*s) t ht).scomp s (affine_parameter_derivative u c s)).sub
        ((F.position_u (w + d*s) t ht).scomp s (affine_parameter_derivative w d s))
  have hV : HasDerivAt V (c • (c • A u) - d • (d • A w)) 0 := by
    have hU := ((F.velocity_tangent_u (u := u) ht).scomp_of_eq 0
      (affine_parameter_derivative u c 0) (by simp)).const_smul c
    have hW := ((F.velocity_tangent_u (u := w) ht).scomp_of_eq 0
      (affine_parameter_derivative w d 0) (by simp)).const_smul d
    exact hU.sub hW
  have hvu := ne_of_gt (F.velocity_pos u t ht)
  have hvw := ne_of_gt (F.velocity_pos w t ht)
  have hV0 : V 0 = 0 := by
    dsimp only [V, c, d]
    simp only [mul_zero, add_zero, smul_smul, inv_mul_cancel₀ hvu, one_smul, hpar]
    have hcoef : a / F.velocity w t * (F.velocity w t * a) = 1 := by
      field_simp [hvw]
      nlinarith [ha]
    rw [hcoef, one_smul, sub_self]
  have hmP : IsLocalMin (fun s ↦ ‖P s‖^2) 0 := by
    have hmap : ContinuousAt (fun s : ℝ ↦ (u + c*s, w + d*s)) 0 := by fun_prop
    have hm' : IsLocalMin (fun p : ℝ × ℝ ↦ F.distanceSq p.1 p.2 t)
        ((fun s : ℝ ↦ (u + c*s, w + d*s)) 0) := by simpa using hm
    exact hm'.comp_continuous (g := fun s : ℝ ↦ (u + c*s, w + d*s)) hmap
  have hge := acceleration_nonneg_at_min hP hV0 hV hmP
  have hacc : ⟪P 0, c • (c • A u) - d • (d • A w)⟫_ℝ =
      ⟪F.position u t - F.position w t,
        F.curvature u t • F.normal u t - F.curvature w t • F.normal w t⟫_ℝ := by
    dsimp only [P, A, c, d]
    simp only [mul_zero, add_zero, inner_sub_right, inner_smul_right,
      inner_add_right, hu, hw, mul_zero, zero_add]
    field_simp [hvu, hvw]
    ring_nf
    simp only [ha, one_mul]
  rw [hacc] at hge
  rw [(F.distanceSq_time ht).deriv]
  positivity

/-- The zero-chord case of the minimum inequality is automatic. This version of the
two-point estimate supports Theorem 3.0.1, printed page 12 of
`MTL603_PDE_project-9-13.pdf`, without assuming embeddedness at the time of evaluation. -/
theorem distanceSq_min_time_nonneg' (ht : t ∈ J)
    (hm : IsLocalMin (fun p : ℝ × ℝ ↦ F.distanceSq p.1 p.2 t) (u, w)) :
    0 ≤ deriv (F.distanceSq u w) t := by
  by_cases heq : F.position u t = F.position w t
  · rw [(F.distanceSq_time ht).deriv]
    simp only [heq, sub_self, inner_zero_left, mul_zero, le_refl]
  · exact F.distanceSq_min_time_nonneg ht heq hm

/-- A compact minimum principle supporting the avoidance argument for Theorem 3.0.1,
printed page 12 of `MTL603_PDE_project-9-13.pdf`. A lower bound on initial data and
the designated spatial boundary is preserved if the time derivative is nonnegative
at every other spatial minimum. The proof uses a strict linear-in-time perturbation. -/
theorem compact_minimum_principle {X : Type*} [TopologicalSpace X] {K B : Set X}
    {f : X → ℝ → ℝ} {T m : ℝ} (hK : IsCompact K) (hT : 0 ≤ T)
    (hc : ContinuousOn (fun p : X × ℝ ↦ f p.1 p.2) (K ×ˢ Icc 0 T))
    (hinit : ∀ x ∈ K, m ≤ f x 0)
    (hboundary : ∀ x ∈ K, x ∈ B → ∀ s ∈ Icc 0 T, m ≤ f x s)
    (hdt : ∀ x ∈ K, x ∉ B → ∀ s ∈ Ioc 0 T, IsMinOn (fun y ↦ f y s) K x →
      DifferentiableAt ℝ (f x) s ∧ 0 ≤ deriv (f x) s) :
    ∀ x ∈ K, ∀ s ∈ Icc 0 T, m ≤ f x s := by
  intro x hx s hs
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  let ε := (m - f x s) / (2 * (T + 1))
  have hden : 0 < 2 * (T + 1) := by positivity
  have hε : 0 < ε := div_pos (sub_pos.mpr hlt) hden
  have hεeq : ε * (2 * (T + 1)) = m - f x s := div_mul_cancel₀ _ hden.ne'
  have hεs : f x s + ε*s < m := by nlinarith [hs.2]
  obtain ⟨p, hp, hmin⟩ := (hK.prod isCompact_Icc).exists_isMinOn
    (show (K ×ˢ Icc 0 T).Nonempty from ⟨(x, 0), hx, le_rfl, hT⟩)
    (hc.add (continuous_const.mul continuous_snd).continuousOn :
      ContinuousOn (fun p : X × ℝ ↦ f p.1 p.2 + ε*p.2) (K ×ˢ Icc 0 T))
  have hlow : f p.1 p.2 + ε*p.2 < m := lt_of_le_of_lt
    (hmin (show (x, s) ∈ K ×ˢ Icc 0 T from ⟨hx, hs⟩)) hεs
  have htime : 0 < p.2 := by
    by_contra h
    have hp0 : p.2 = 0 := le_antisymm (le_of_not_gt h) hp.2.1
    have hi := hinit p.1 hp.1
    simp only [hp0, mul_zero, add_zero] at hlow
    linarith
  have hnotB : p.1 ∉ B := by
    intro hB
    have hb := hboundary p.1 hp.1 hB p.2 hp.2
    nlinarith [hp.2.1]
  have hspace : IsMinOn (fun y ↦ f y p.2) K p.1 := by
    intro y hy
    have h := hmin (show (y, p.2) ∈ K ×ˢ Icc 0 T from ⟨hy, hp.2⟩)
    dsimp at h
    exact le_of_add_le_add_right h
  obtain ⟨hd, hdpos⟩ := hdt p.1 hp.1 hnotB p.2 ⟨htime, hp.2.2⟩ hspace
  have htimeMin : IsMinOn (fun s ↦ f p.1 s + ε*s) (Icc 0 T) p.2 :=
    fun y hy ↦ hmin (show (p.1, y) ∈ K ×ˢ Icc 0 T from ⟨hp.1, hy⟩)
  have hder := hd.hasDerivAt.add ((hasDerivAt_id p.2).const_mul ε)
  have hcone : 0 - p.2 ∈ posTangentConeAt (Icc 0 T) p.2 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 T).segment_subset hp.2 ⟨le_rfl, hT⟩)
  have hlocal : IsLocalMinOn (fun s ↦ f p.1 s + ε*s) (Icc 0 T) p.2 :=
    Filter.Eventually.mono self_mem_nhdsWithin (fun _ hy ↦ htimeMin hy)
  have hineq := hlocal.hasFDerivWithinAt_nonneg
    hder.hasFDerivAt.hasFDerivWithinAt hcone
  change 0 ≤ (0 - p.2) * (deriv (f p.1) p.2 + ε*1) at hineq
  nlinarith

end Flow

namespace ClassicalClosedFlow

variable {T₀ : ℝ} (F : ClassicalClosedFlow T₀)

/-- Regularity including the initial time in Theorem 3.0.1, printed page 12 of
`MTL603_PDE_project-9-13.pdf`. -/
theorem velocity_pos_at {t : ℝ} (ht : t ∈ Ico 0 T₀) (u : ℝ) : 0 < F.velocity u t := by
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · simpa only [← heq] using F.initial_velocity_pos u
  · exact F.velocity_pos u t ⟨hpos, ht.2⟩

/-- The unit frame including the initial time in Theorem 3.0.1, printed page 12 of
`MTL603_PDE_project-9-13.pdf`. -/
theorem frame_at {t : ℝ} (ht : t ∈ Ico 0 T₀) (u : ℝ) :
    PlaneFrame (F.tangent u t) (F.normal u t) := by
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · simpa only [← heq] using F.initial_frame u
  · exact F.frame u t ⟨hpos, ht.2⟩

/-- The spatial derivative including the initial time in Theorem 3.0.1, printed page 12
of `MTL603_PDE_project-9-13.pdf`. -/
theorem position_u_at {t : ℝ} (ht : t ∈ Ico 0 T₀) (u : ℝ) :
    HasDerivAt (fun x ↦ F.position x t) (F.velocity u t • F.tangent u t) u := by
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · simpa only [← heq] using F.initial_position_u u
  · exact F.position_u u t ⟨hpos, ht.2⟩

/-- Uniform local injectivity on a compact time interval, a near-diagonal ingredient
for Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`.
Uniform continuity of the unit tangent gives a strictly increasing scalar projection
on every sufficiently short parameter interval. No global embeddedness is assumed. -/
theorem uniform_local_injective {T : ℝ} (_hT : 0 ≤ T) (hTT : T < T₀) :
    ∃ δ > 0, ∀ u ∈ Icc 0 (2 * Real.pi), ∀ t ∈ Icc 0 T,
      Set.InjOn (fun x ↦ F.position x t) (Icc (u - δ) (u + δ)) := by
  let K := Icc (-1 : ℝ) (2 * Real.pi + 1) ×ˢ Icc 0 T
  have hsub : K ⊆ (univ : Set ℝ) ×ˢ Ico 0 T₀ :=
    fun p hp ↦ ⟨mem_univ _, hp.2.1, hp.2.2.trans_lt hTT⟩
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (F.tangent_continuous.mono hsub)
  obtain ⟨ε, hε, heps⟩ := Metric.uniformContinuousOn_iff.mp huc 1 zero_lt_one
  let δ := min ε 1 / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; have := min_le_left ε 1; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; have := min_le_right ε 1; linarith
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  have ht₀ : t ∈ Ico 0 T₀ := ⟨ht.1, ht.2.trans_lt hTT⟩
  let g := fun x ↦ ⟪F.tangent u t, F.position x t⟫_ℝ
  have hg : ∀ x, HasDerivAt g
      (F.velocity x t * ⟪F.tangent u t, F.tangent x t⟫_ℝ) x := by
    intro x
    simpa only [inner_smul_right, inner_zero_left, add_zero] using
      (hasDerivAt_const x (F.tangent u t)).inner ℝ (F.position_u_at ht₀ x)
  have hmono : StrictMonoOn g (Icc (u - δ) (u + δ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x _ ↦ (hg x).continuousAt.continuousWithinAt)
    intro x hx
    have hx' := interior_subset hx
    have hxK : (x, t) ∈ K := ⟨⟨by linarith [hu.1, hx'.1],
      by linarith [hu.2, hx'.2]⟩, ht⟩
    have huK : (u, t) ∈ K := ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, ht⟩
    have hdist : dist (u, t) (x, t) < ε := by
      rw [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg), Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
    have hclose := heps (u, t) huK (x, t) hxK hdist
    rw [dist_eq_norm] at hclose
    have hunitU := (F.frame_at ht₀ u).tangent_unit
    have hunitX := (F.frame_at ht₀ x).tangent_unit
    rw [real_inner_self_eq_norm_sq] at hunitU hunitX
    have hsq := norm_sub_sq_real (F.tangent u t) (F.tangent x t)
    have hinner : 0 < ⟪F.tangent u t, F.tangent x t⟫_ℝ := by
      nlinarith [norm_nonneg (F.tangent u t - F.tangent x t)]
    rw [(hg x).deriv]
    exact mul_pos (F.velocity_pos_at ht₀ x) hinner
  intro x hx y hy heq
  exact hmono.injOn hx hy (congrArg (fun p ↦ ⟪F.tangent u t, p⟫_ℝ) heq)

/-- Periodic parameter bookkeeping for Theorem 3.0.1, printed page 12 of
`MTL603_PDE_project-9-13.pdf`: injectivity on one half-open period excludes every
nontrivial return with parameter increment strictly between zero and a full period. -/
theorem periodic_injOn_ne {Y : Type*} {f : ℝ → Y} {P x h : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P) (hinj : Set.InjOn f (Ico 0 P))
    (hx : x ∈ Icc 0 P) (hh : h ∈ Ioo 0 P) : f x ≠ f (x + h) := by
  have hbase : ∀ y ∈ Ico 0 P, f y ≠ f (y + h) := by
    intro y hy heq
    by_cases hyh : y + h < P
    · have heq' := hinj hy (show y + h ∈ Ico 0 P from ⟨by linarith [hy.1, hh.1], hyh⟩) heq
      linarith [hh.1]
    · have hyh' : y + h - P ∈ Ico 0 P := ⟨by linarith, by linarith [hy.2, hh.2]⟩
      have hper' : f (y + h) = f (y + h - P) := by
        simpa only [sub_add_cancel] using hper (y + h - P)
      have heq' := hinj hy hyh' (heq.trans hper')
      linarith [hh.2]
  rcases lt_or_eq_of_le hx.2 with hxp | hxp
  · exact hbase x ⟨hx.1, hxp⟩
  · have hper0 : f P = f 0 := by simpa only [zero_add] using hper 0
    have hperh : f (P + h) = f h := by simpa only [add_comm] using hper h
    simpa only [hxp, hper0, hperh, zero_add] using hbase 0 ⟨le_rfl, hP⟩

/-- A minimum on a full-period strip is a local minimum even at the artificial period
seam. This supports Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem periodic_strip_localMin {f : ℝ → ℝ → ℝ} {P a b u h : ℝ} (hP : 0 < P)
    (hper : ∀ h, Function.Periodic (fun u ↦ f u h) P)
    (hm : IsMinOn (fun p : ℝ × ℝ ↦ f p.1 p.2) (Icc 0 P ×ˢ Icc a b) (u, h))
    (hh : h ∈ Ioo a b) : IsLocalMin (fun p : ℝ × ℝ ↦ f p.1 p.2) (u, h) := by
  change ∀ᶠ p in 𝓝 (u, h), f u h ≤ f p.1 p.2
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (u, h), p.2 ∈ Icc a b :=
    continuous_snd.continuousAt.preimage_mem_nhds (Icc_mem_nhds hh.1 hh.2)
  filter_upwards [hev] with p hp
  obtain ⟨v, hv, heq⟩ := (hper p.2).exists_mem_Ico₀ hP p.1
  rw [heq]
  exact hm (show (v, p.2) ∈ Icc 0 P ×ˢ Icc a b from ⟨⟨hv.1, hv.2.le⟩, hp⟩)

/-- The two-point differential inequality on a parameter strip, including its period
seam, used for Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`. -/
theorem shifted_distance_min_nonneg {t u h a b : ℝ} (ht : t ∈ Ioo 0 T₀)
    (hm : IsMinOn (fun p : ℝ × ℝ ↦ F.toFlow.distanceSq p.1 (p.1 + p.2) t)
      (Icc 0 (2 * Real.pi) ×ˢ Icc a b) (u, h)) (hh : h ∈ Ioo a b) :
    0 ≤ deriv (F.toFlow.distanceSq u (u + h)) t := by
  have hp := (F.closed t ⟨ht.1.le, ht.2⟩).position
  change ∀ x, F.position (x + 2 * Real.pi) t = F.position x t at hp
  have hper : ∀ h, Function.Periodic (fun u ↦ F.toFlow.distanceSq u (u + h) t)
      (2 * Real.pi) := by
    intro h u
    dsimp only [Flow.distanceSq]
    rw [hp u, show u + 2 * Real.pi + h = (u + h) + 2 * Real.pi by ring, hp (u + h)]
  have hlocal := periodic_strip_localMin (by positivity) hper hm hh
  have hlocal' : IsLocalMin
      (fun p : ℝ × ℝ ↦ F.toFlow.distanceSq p.1 (p.1 + p.2) t)
      ((fun p : ℝ × ℝ ↦ (p.1, p.2 - p.1)) (u, u + h)) := by simpa using hlocal
  have hcomp := hlocal'.comp_continuous (g := fun p : ℝ × ℝ ↦ (p.1, p.2 - p.1))
    (by fun_prop)
  apply F.toFlow.distanceSq_min_time_nonneg' ht
  simpa only [Function.comp_def, add_sub_cancel] using hcomp

set_option maxHeartbeats 800000 in
/-- Positive separation of distinct circle parameters under classical CSF, supplying
the compactness step in Theorem 3.0.1, printed page 12 of
`MTL603_PDE_project-9-13.pdf`. The argument only uses regularity on each compact time
interval, so the source's global curvature bound is not needed for this stronger lemma. -/
theorem shifted_distance_positive {T u h : ℝ} (hT : 0 < T) (hTT : T < T₀)
    (hinitial : F.toFlow.EmbeddedAt 0) (hu : u ∈ Icc 0 (2 * Real.pi))
    (hh : h ∈ Ioo 0 (2 * Real.pi)) : 0 < F.toFlow.distanceSq u (u + h) T := by
  let P := 2 * Real.pi
  have hh0 : 0 < h := hh.1
  have hhP : 0 < P - h := sub_pos.mpr hh.2
  obtain ⟨r, hr, hlocal⟩ := F.uniform_local_injective hT.le hTT
  let δ := min r (min h (P - h)) / 2
  have hδ : 0 < δ := div_pos (lt_min hr (lt_min hh0 hhP)) (by norm_num)
  have hδr : δ < r := by
    have := min_le_left r (min h (P - h))
    dsimp [δ]
    linarith
  have hδh : δ < h := by
    have hle : 2 * δ ≤ h := by
      dsimp [δ]
      linarith [(min_le_right r (min h (P - h))).trans (min_le_left h (P - h))]
    linarith
  have hδPh : δ < P - h := by
    have hle : 2 * δ ≤ P - h := by
      dsimp [δ]
      linarith [(min_le_right r (min h (P - h))).trans (min_le_right h (P - h))]
    linarith
  let K := Icc 0 P ×ˢ Icc δ (P - δ)
  let B := Icc 0 P ×ˢ ({δ, P - δ} : Set ℝ)
  let f := fun (p : ℝ × ℝ) t ↦ F.toFlow.distanceSq p.1 (p.1 + p.2) t
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hB : IsCompact B :=
    isCompact_Icc.prod ((Set.finite_singleton (P - δ)).insert δ).isCompact
  have hc : ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ f q.1 q.2) (univ ×ˢ Icc 0 T) := by
    have h₁ : ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ F.position q.1.1 q.2)
        (univ ×ˢ Icc 0 T) :=
      F.position_continuous.comp (f := fun q : (ℝ × ℝ) × ℝ ↦ (q.1.1, q.2))
        (by fun_prop) (fun q hq ↦ ⟨mem_univ _, hq.2.1, hq.2.2.trans_lt hTT⟩)
    have h₂ : ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ F.position (q.1.1 + q.1.2) q.2)
        (univ ×ˢ Icc 0 T) :=
      F.position_continuous.comp (f := fun q : (ℝ × ℝ) × ℝ ↦ (q.1.1 + q.1.2, q.2))
        (by fun_prop) (fun q hq ↦ ⟨mem_univ _, hq.2.1, hq.2.2.trans_lt hTT⟩)
    exact (h₁.sub h₂).norm.pow 2
  have hc0 : ContinuousOn (fun p ↦ f p 0) K :=
    hc.comp (f := fun p : ℝ × ℝ ↦ (p, 0)) (by fun_prop)
      (fun _ _ ↦ ⟨mem_univ _, le_rfl, hT.le⟩)
  have hcB : ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ f q.1 q.2) (B ×ˢ Icc 0 T) :=
    hc.mono (fun _ hq ↦ ⟨mem_univ _, hq.2⟩)
  have hinitpos : ∀ p ∈ K, 0 < f p 0 := by
    intro p hp
    have hne := periodic_injOn_ne (by positivity : 0 < P)
      (F.closed 0 ⟨le_rfl, hT.trans hTT⟩).position hinitial hp.1
      (show p.2 ∈ Ioo 0 P from ⟨hδ.trans_le hp.2.1, by linarith [hp.2.2]⟩)
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hboundarypos : ∀ q ∈ B ×ˢ Icc 0 T, 0 < f q.1 q.2 := by
    rintro ⟨⟨x, a⟩, t⟩ ⟨⟨hx, ha⟩, ht⟩
    have hnear := hlocal x hx t ht
    have hxnear : x ∈ Icc (x-r) (x+r) := ⟨by linarith, by linarith⟩
    have hne : F.position x t ≠ F.position (x + a) t := by
      rcases ha with ha | ha
      · have ha' : a = δ := ha
        rw [ha']
        intro heq
        have he := hnear hxnear (show x + δ ∈ Icc (x-r) (x+r) from
          ⟨by linarith, by linarith⟩) heq
        linarith
      · have ha' : a = P - δ := ha
        rw [ha']
        intro heq
        have hp := (F.closed t ⟨ht.1, ht.2.trans_lt hTT⟩).position (x - δ)
        change F.position (x - δ + P) t = F.position (x - δ) t at hp
        have heq' : F.position x t = F.position (x - δ) t := by
          rw [show x - δ = x + (P - δ) - P by ring] at hp ⊢
          simp only [sub_add_cancel] at hp
          exact heq.trans hp
        have he := hnear hxnear (show x - δ ∈ Icc (x-r) (x+r) from
          ⟨by linarith, by linarith⟩) heq'
        linarith
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  obtain ⟨m₀, hm₀, hmin₀⟩ := hK.exists_forall_le' hc0 hinitpos
  obtain ⟨mb, hmb, hminb⟩ := (hB.prod isCompact_Icc).exists_forall_le' hcB hboundarypos
  let m := min m₀ mb
  have hm : 0 < m := lt_min hm₀ hmb
  have hbound := Flow.compact_minimum_principle (K := K) (B := B) (f := f) (m := m)
    hK hT.le (hc.mono (fun _ hq ↦ ⟨mem_univ _, hq.2⟩))
    (fun p hp ↦ (min_le_left m₀ mb).trans (hmin₀ p hp))
    (fun p _ hp t ht ↦ (min_le_right m₀ mb).trans (hminb (p, t) ⟨hp, ht⟩)) ?_
  · exact hm.trans_le (hbound (u, h) ⟨hu, hδh.le, by linarith⟩ T ⟨hT.le, le_rfl⟩)
  intro p hp hpB t ht hmin
  have hpt : p.2 ∈ Ioo δ (P - δ) := by
    have hnL : p.2 ≠ δ := fun heq ↦ hpB ⟨hp.1, Or.inl heq⟩
    have hnR : p.2 ≠ P - δ := fun heq ↦ hpB ⟨hp.1, Or.inr heq⟩
    exact ⟨lt_of_le_of_ne hp.2.1 hnL.symm, lt_of_le_of_ne hp.2.2 hnR⟩
  have htt : t ∈ Ioo 0 T₀ := ⟨ht.1, ht.2.trans_lt hTT⟩
  exact ⟨(F.toFlow.distanceSq_time htt).differentiableAt,
    F.shifted_distance_min_nonneg htt hmin hpt⟩

end ClassicalClosedFlow

/-- Theorem 3.0.1, printed page 12 of `MTL603_PDE_project-9-13.pdf`: a classical
closed CSF that is initially embedded and has the stated uniform upper curvature bound
remains embedded. The one-sided bound is preserved exactly as printed in the source.

The proof uses uniform local injectivity, the two-point spatial minimum inequality,
and a compact minimum principle. In fact this establishes the conclusion without
using the source's additional global curvature bound. -/
theorem embeddedness_preserved {T₀ : ℝ} (_hT₀ : 0 < T₀) (F : ClassicalClosedFlow T₀)
    (hinitial : F.toFlow.EmbeddedAt 0)
    (_hbound : ∃ c : ℝ, ∀ u t, t ∈ Ico 0 T₀ → F.curvature u t ≤ c) :
    ∀ t ∈ Ico 0 T₀, F.toFlow.EmbeddedAt t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · simpa only [← heq] using hinitial
  · intro x hx y hy heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · have hsep := F.shifted_distance_positive (u := x) (h := y - x) hpos ht.2 hinitial
        ⟨hx.1, hx.2.le⟩ ⟨sub_pos.mpr hxy, by linarith [hy.2, hx.1]⟩
      rw [show x + (y - x) = y by ring] at hsep
      simp only [Flow.distanceSq, heq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
        lt_self_iff_false] at hsep
    · have hsep := F.shifted_distance_positive (u := y) (h := x - y) hpos ht.2 hinitial
        ⟨hy.1, hy.2.le⟩ ⟨sub_pos.mpr hyx, by linarith [hx.2, hy.1]⟩
      rw [show y + (x - y) = x by ring] at hsep
      simp only [Flow.distanceSq, heq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
        lt_self_iff_false] at hsep

end CSF
