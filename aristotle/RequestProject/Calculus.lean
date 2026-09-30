import RequestProject.Defs

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
