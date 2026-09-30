import Mathlib

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
