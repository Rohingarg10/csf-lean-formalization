import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Curve shortening flow: local differential identities

Source: `MTL603_PDE_project-9-13.pdf`, Chapter 3, printed pages 8–12.
The docstrings identify the source of each declaration and any explicit analytic hypotheses.
This file is a partial formalization, not a proof of all the results in the source.
-/

namespace PDE

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `MTL603_PDE_project-9-13.pdf`, Lemma 1, p. 8: the speed `v = ‖∂γ/∂u‖`. -/
noncomputable def speed (γ : ℝ → E) (u : ℝ) : ℝ := ‖deriv γ u‖

/-- `MTL603_PDE_project-9-13.pdf`, proof of Lemma 1, p. 8: arclength from `0` to `u`.
This is signed arclength when `u < 0`. -/
noncomputable def arcLength (γ : ℝ → E) (u : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..u, speed γ r

/-- `MTL603_PDE_project-9-13.pdf`, proof of Lemma 1, p. 8: `ds/du = v`.
Continuity of speed is made explicit for the fundamental theorem of calculus. -/
theorem hasDerivAt_arcLength (γ : ℝ → E) (hv : Continuous (speed γ)) (u : ℝ) :
    HasDerivAt (arcLength γ) (speed γ u) u := by
  exact intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

/-- `MTL603_PDE_project-9-13.pdf`, Lemma 1, p. 8: the operator identity
`∂/∂s = (1/v) ∂/∂u`, applied to a differentiable vector-valued test function.
The test function is expressed in the arclength coordinate; regularity is `v ≠ 0`. -/
theorem arclength_chain_rule (γ : ℝ → E) (hv : Continuous (speed γ)) (u : ℝ)
    (hregular : speed γ u ≠ 0) (f : ℝ → E)
    (hf : DifferentiableAt ℝ f (arcLength γ u)) :
    deriv f (arcLength γ u) =
      (speed γ u)⁻¹ • deriv (fun r ↦ f (arcLength γ r)) u := by
  have h := (hf.hasDerivAt.scomp u (hasDerivAt_arcLength γ hv u)).deriv
  simp only [Function.comp_def] at h
  rw [h]
  simp [smul_smul, hregular]

/-- `MTL603_PDE_project-9-13.pdf`, Lemma 2, pp. 8–9, local analytic form.
Here `w` is `∂γ/∂u` as a function of time at the point in question, and `v = ‖w t‖`.
The mixed-partial identity from CSF is supplied as `hflow`; `hN` is the spatial
Serret–Frenet equation. These local hypotheses expose precisely the ingredients
used in the source calculation, without asserting a global existence theorem. -/
theorem speed_evolution_local (w : ℝ → E) (k : ℝ → ℝ) (N : ℝ → E)
    (u t v : ℝ) (T : E) (hv : 0 < v) (hw : w t = v • T)
    (hunit : inner ℝ T T = 1) (horth : inner ℝ T (N u) = 0)
    (hk : DifferentiableAt ℝ k u)
    (hN : HasDerivAt N (-(v * k u) • T) u)
    (hflow : HasDerivAt w (deriv (fun r ↦ k r • N r) u) t) :
    HasDerivAt (fun τ ↦ ‖w τ‖) (-(k u)^2 * v) t := by
  have hprod := hk.hasDerivAt.smul hN
  have hnormT : ‖T‖ = 1 := by
    have hsq : ‖T‖ ^ 2 = 1 := by simpa only [real_inner_self_eq_norm_sq] using hunit
    nlinarith [norm_nonneg T]
  have hnorm : ‖w t‖ = v := by simp [hw, norm_smul, abs_of_pos hv, hnormT]
  have hnz : w t ≠ 0 := by
    intro h
    simp [h] at hnorm
    linarith
  have hd := (hflow.differentiableAt.norm ℝ hnz).hasDerivAt
  have heq := (hd.pow 2).unique hflow.norm_sq
  have hp := hprod.deriv
  change deriv (fun r ↦ k r • N r) u = _ at hp
  rw [hp] at heq
  simp only [hw, real_inner_smul_left, inner_add_right, real_inner_smul_right,
    horth, hunit, mul_zero, mul_one, add_zero] at heq
  have hvalue : deriv (fun τ ↦ ‖w τ‖) t = -(k u)^2 * v := by
    simp [norm_smul, abs_of_pos hv, hnormT] at heq
    nlinarith
  rwa [hvalue] at hd

/-- `MTL603_PDE_project-9-13.pdf`, Lemma 3, p. 9: the local commutator computation.
`q` represents `∂f/∂u` and `qₜ` its time derivative. Under commuting mixed partials,
`v⁻¹ • qₜ` is `∂s∂t f`; the extra term is `κ² ∂s f`. -/
theorem arclength_commutator_local (v : ℝ → ℝ) (q : ℝ → E) (t κ : ℝ) (qₜ : E)
    (hv0 : v t ≠ 0) (hv : HasDerivAt v (-κ^2 * v t) t)
    (hq : HasDerivAt q qₜ t) :
    HasDerivAt (fun τ ↦ (v τ)⁻¹ • q τ)
      ((v t)⁻¹ • qₜ + κ^2 • ((v t)⁻¹ • q t)) t := by
  have hi : HasDerivAt (fun τ ↦ (v τ)⁻¹) (κ^2 * (v t)⁻¹) t := by
    convert hv.inv hv0 using 1
    field_simp
  simpa [smul_smul] using hi.smul hq

/-- `MTL603_PDE_project-9-13.pdf`, first identity of Lemma 4, p. 10, local form.
`q = ∂u γ` and `v` is speed. The derivative `hq` is the spatial derivative of the
CSF velocity expanded using the Serret–Frenet equation, as in Lemma 2. -/
theorem tangent_evolution_local (v : ℝ → ℝ) (q : ℝ → E) (t κ κᵤ : ℝ) (T N : E)
    (hv0 : v t ≠ 0) (hv : HasDerivAt v (-κ^2 * v t) t)
    (hqt : q t = v t • T)
    (hq : HasDerivAt q (κᵤ • N - (v t * κ^2) • T) t) :
    HasDerivAt (fun τ ↦ (v τ)⁻¹ • q τ) ((κᵤ / v t) • N) t := by
  convert arclength_commutator_local v q t κ _ hv0 hv hq using 1
  simp [hqt, smul_sub, smul_smul, hv0, div_eq_mul_inv, mul_comm]

/-- `MTL603_PDE_project-9-13.pdf`, second identity of Lemma 4, p. 10.
The fixed continuous linear map `J` represents rotation through `π/2` and the
normal is `J ∘ T`. The relation `J² T = -T` makes the orientation explicit. -/
theorem normal_evolution_local (T : ℝ → E) (J : E →L[ℝ] E) (t κₛ : ℝ)
    (hJ : J (J (T t)) = -T t) (hT : HasDerivAt T (κₛ • J (T t)) t) :
    HasDerivAt (fun τ ↦ J (T τ)) (-κₛ • T t) t := by
  have h := J.hasFDerivAt.comp_hasDerivAt t hT
  simpa [map_smul, hJ, smul_neg, neg_smul] using h

/-- `MTL603_PDE_project-9-13.pdf`, proof of Lemma 5, pp. 10–11: the curvature
PDE follows from the commutator of Lemma 3 and the angle identities `Ds θ = κ`,
`Dt θ = Ds κ`. This is the operator-algebra step; construction of a local angle
and verification of these identities for a geometric flow are separate obligations. -/
theorem curvature_evolution_of_angle {X : Type*}
    (Ds Dt : (X → ℝ) → (X → ℝ)) (θ κ : X → ℝ)
    (hcomm : Dt (Ds θ) = fun x ↦ Ds (Dt θ) x + κ x ^ 2 * Ds θ x)
    (hspace : Ds θ = κ) (htime : Dt θ = Ds κ) :
    Dt κ = fun x ↦ Ds (Ds κ) x + κ x ^ 3 := by
  rw [hspace, htime] at hcomm
  rw [hcomm]
  funext x
  ring

open MeasureTheory Filter
open scoped Topology

/-- `MTL603_PDE_project-9-13.pdf`, Lemma 6(i), p. 11: differentiate the length
integral using the speed evolution law. The measurable domination assumptions
justify the source's exchange of differentiation and integration. This statement
uses `κ² v du`, the parameter form of `κ² ds`. -/
theorem length_evolution_of_speed (v k : ℝ → ℝ → ℝ) (t : ℝ)
    (s : Set ℝ) (bound : ℝ → ℝ) (hs : s ∈ 𝓝 t)
    (hv : ∀ τ, Continuous (v τ)) (hk : Continuous (k t))
    (hb : IntervalIntegrable bound volume 0 (2 * Real.pi))
    (hbound : ∀ u ∈ Set.uIoc 0 (2 * Real.pi), ∀ τ ∈ s,
      ‖-(k τ u)^2 * v τ u‖ ≤ bound u)
    (hevol : ∀ u ∈ Set.uIoc 0 (2 * Real.pi), ∀ τ ∈ s,
      HasDerivAt (fun r ↦ v r u) (-(k τ u)^2 * v τ u) τ) :
    HasDerivAt (fun τ ↦ ∫ u in (0 : ℝ)..(2 * Real.pi), v τ u)
      (-(∫ u in (0 : ℝ)..(2 * Real.pi), (k t u)^2 * v t u)) t := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := v) (F' := fun τ u ↦ -(k τ u)^2 * v τ u) hs
    (Filter.Eventually.of_forall fun τ ↦ (hv τ).aestronglyMeasurable.restrict)
    ((hv t).intervalIntegrable _ _)
    (((hk.pow 2).neg.mul (hv t)).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall hbound) hb (Filter.Eventually.of_forall hevol)
  simpa only [neg_mul, intervalIntegral.integral_neg] using h.2

end PDE
