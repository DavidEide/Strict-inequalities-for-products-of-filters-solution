/-
Copyright (c) 2026 David Immanuel Eidenas.
SPDX-License-Identifier: MIT
-/
import StrictProducts

/-! External checks of the paper's complete conclusions and axiom dependencies. -/

open Set Filter StrictProducts

example :
    NeBot Phi ∧ (∀ A : Set ℕ, Phi ≠ 𝓟 A) ∧
    secondProduct Phi Phi = ⊥ ∧
    secondProduct Phi Phi < obliqueProduct Phi Phi ∧
    obliqueProduct Phi Phi < classicalProduct Phi Phi :=
  frechet_solution

example :
    NeBot deltaPlus ∧ (∀ A : Set ℝ, deltaPlus ≠ 𝓟 A) ∧
    secondProduct deltaPlus deltaPlus = ⊥ ∧
    secondProduct deltaPlus deltaPlus < obliqueProduct deltaPlus deltaPlus ∧
    obliqueProduct deltaPlus deltaPlus < classicalProduct deltaPlus deltaPlus :=
  real_solution

example :
    let F : Filter ℝ := delta ⊓ 𝓟 (Ioi (0 : ℝ))
    NeBot F ∧ (∀ A : Set ℝ, F ≠ 𝓟 A) ∧
    secondProduct F F = ⊥ ∧
    secondProduct F F < obliqueProduct F F ∧
    obliqueProduct F F < classicalProduct F F :=
  proposed_pair_solution

example : ∃ F G : Filter ℕ, NeBot F ∧ NeBot G ∧
    secondProduct F G < obliqueProduct F G ∧
    obliqueProduct F G < classicalProduct F G :=
  existential_solution

-- These audits must have only propext, Classical.choice, and Quot.sound.
#print axioms mesh_iff_common_lower
#print axioms imageFilter_eq_generate
#print axioms upper_iff_positive_hits
#print axioms upper_iff_images_mem
#print axioms upper_principal_iff_columns
#print axioms outward_eq_iInf
#print axioms oblique_eq_columnFilter
#print axioms classical_eq_prod
#print axioms second_le_oblique
#print axioms oblique_le_classical
#print axioms delta_eq_iInf
#print axioms deltaPlus_eq_inf
#print axioms frechet_solution
#print axioms real_solution
#print axioms proposed_pair_solution
#print axioms existential_solution
