import RequestProject.MaxPrinciple

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
