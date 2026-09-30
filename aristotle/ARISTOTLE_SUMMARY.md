# Summary of changes for run 33cfe4c0-21b4-4419-b3ba-d700c3d3f1b4
I formalized all of Chapter 3 ("Properties of Curve Shortening Flow") of `MTL603_PDE_project-9-13.pdf` in Lean 4. Everything builds with no `sorry` and only the standard axioms. Every declaration has a docstring naming the lemma, theorem or proof step of the notes it corresponds to. Two points are handled differently from the notes, and one of them adds an assumption:

- **Hopf's Umlaufsatz is an explicit hypothesis.** In Lemma 6 (ii) the notes use, without proof, that a closed embedded curve with inward normal has total curvature `∫ κ ds = 2π`. This is not formalized here. It enters as a hypothesis (`htotal`) in Lemma 6 (ii) and in the maximal-time remark. Without it, I proved `dA/dt = −∫ κ ds` (`CSF.lemma6_area_evolution_total_curvature`).
- **Theorem 3.0.1 is proved, but the curvature bound isn't needed.** The notes state it without proof. Compactness on each time interval `[0, t₁]` already gives the estimates the proof needs, so the bound `κ ≤ c` is unused; I kept it only to match the notes.

**Setup** (`RequestProject/Defs.lean`): the plane is identified with `ℂ`, and a moving curve is a map `γ(u, t)`. The file defines:
- the partial derivatives in `u` and `t`, the speed `v = ‖∂γ/∂u‖`, and `∂/∂s = (1/v) ∂/∂u`;
- the unit tangent `T` and the normal `n = I·T`;
- the curvature `κ = ⟨∂T/∂s, n⟩`;
- curve shortening flow (`IsCSF`: smooth, regular, `∂γ/∂t = κ n`, i.e. equation (2.1));
- closed curves (2π-periodic in `u`), embeddedness, arclength, length, and the Green's-formula area.

**Results:**
- **Lemma 1**: `∂s/∂u = v` and `∂/∂s = (1/v)∂/∂u` (`CSF.lemma1_arclength_hasDerivAt`, `CSF.lemma1_arclength_derivative`).
- **Lemma 2**: `∂v/∂t = −κ² v` (`CSF.IsCSF.lemma2_speed_evolution`). This uses the Serret–Frenet equations `∂T/∂u = vκn`, `∂n/∂u = −vκT`, which I also proved.
- **Lemma 3**: `∂²/∂t∂s = ∂²/∂s∂t + κ² ∂/∂s`, for every smooth function (`CSF.IsCSF.lemma3_commutator`).
- **Lemma 4**: `∂T/∂t = (∂κ/∂s) n` and `∂n/∂t = −(∂κ/∂s) T` (`CSF.IsCSF.lemma4_tangent_evolution`, `CSF.IsCSF.lemma4_normal_evolution`).
- **Lemma 5**: `∂κ/∂t = ∂²κ/∂s² + κ³` (`CSF.IsCSF.lemma5_curvature_evolution`). The proof uses Lemmas 3 and 4 rather than the tangent-angle argument in the notes.
- **Lemma 6**:
  - (i) `dL/dt = −∫ κ² v du` (`CSF.lemma6_length_evolution`).
  - (ii) `dA/dt = −∫ κ v du`, and hence `dA/dt = −2π` under `htotal` (`CSF.lemma6_area_evolution`).
- **Remark after Lemma 6** (`RequestProject/MaximalTime.lean`): `A(t) = A₀ − 2πt` and `T₀ ≤ A₀/2π`. If the area tends to 0 as `t → T₀`, then `T₀ = A₀/2π`. That last condition is a hypothesis because the existence theory the notes appeal to is not formalized.
- **Theorem 3.0.1** (`CSF.theorem_3_0_1`): the flow keeps embedded closed curves embedded on `[0, T₀)`. The flow is assumed smooth for `t > 0`; at `t = 0` only continuity of `γ` and `∂γ/∂u` and regularity are assumed. The proof uses a two-point maximum principle for the chord length, in `RequestProject/MaxPrinciple.lean` and `RequestProject/Embedded.lean`.

The supporting calculus is in `RequestProject/Calculus.lean`, `RequestProject/Frenet.lean` and `RequestProject/LengthArea.lean`. `RequestProject/Main.lean` imports everything and lists each result of the notes next to its Lean name.