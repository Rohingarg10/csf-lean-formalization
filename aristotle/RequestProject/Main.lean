import RequestProject.Defs
import RequestProject.Calculus
import RequestProject.Frenet
import RequestProject.Evolution
import RequestProject.LengthArea
import RequestProject.MaximalTime
import RequestProject.MaxPrinciple
import RequestProject.Embedded

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
