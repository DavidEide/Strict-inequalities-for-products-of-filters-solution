/-
Copyright (c) 2026 David Immanuel Eidenas.
SPDX-License-Identifier: MIT
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Interval.Finset.Nat

/-!
# Strict inequalities for products of filters

Formal companion to `paper.tex`, by David Immanuel Eidenas.

Filters are Mathlib filters, ordered by reverse inclusion. Reloids are filters
on Cartesian products. The funcoid definitions below are the filter-valued-map
definitions used in Porton's source; only the operations needed by the proof
are developed. The oblique product uses the author's corrected existential
quantifier. Both the natural-number and real-number examples are formalised.
-/

noncomputable section

open Set Filter

namespace StrictProducts

universe u v
variable {α : Type u} {β : Type v}

/-! ## Meshing, positive sets, and relation images -/

/-- Two filters mesh precisely when their meet is proper. -/
def Mesh (F G : Filter α) : Prop := NeBot (F ⊓ G)

/-- A set is positive when its principal filter meshes with the given filter. -/
def Positive (F : Filter α) (S : Set α) : Prop := Mesh (𝓟 S) F

theorem mesh_iff_common_lower (F G : Filter α) :
    Mesh F G ↔ ∃ C : Filter α, NeBot C ∧ C ≤ F ∧ C ≤ G :=
  ⟨fun h => ⟨F ⊓ G, h, inf_le_left, inf_le_right⟩,
    fun ⟨_, hC, hCF, hCG⟩ => hC.mono (le_inf hCF hCG)⟩

theorem mesh_iff_sets (F G : Filter α) :
    Mesh F G ↔ ∀ A ∈ F, ∀ B ∈ G, (A ∩ B).Nonempty := by
  constructor
  · intro h A hA B hB
    exact (h : NeBot (F ⊓ G)).nonempty_of_mem (inter_mem_inf hA hB)
  · intro h
    apply forall_mem_nonempty_iff_neBot.mp
    intro S hS
    obtain ⟨A, hA, B, hB, rfl⟩ := mem_inf_iff.mp hS
    exact h A hA B hB

theorem mesh_symm {F G : Filter α} (h : Mesh F G) : Mesh G F := by
  simpa only [Mesh, inf_comm] using h

@[simp] theorem mesh_bot_right (F : Filter α) : ¬ Mesh F ⊥ := by
  simp [Mesh, Filter.neBot_iff]

@[simp] theorem mesh_bot_left (F : Filter α) : ¬ Mesh ⊥ F := by
  simp [Mesh, Filter.neBot_iff]

theorem positive_iff_sets (F : Filter α) (S : Set α) :
    Positive F S ↔ ∀ A ∈ F, (S ∩ A).Nonempty := by
  constructor
  · intro h A hA
    exact (mesh_iff_sets (𝓟 S) F).mp h S (mem_principal_self S) A hA
  · intro h
    apply (mesh_iff_sets (𝓟 S) F).mpr
    intro T hT A hA
    obtain ⟨x, hxS, hxA⟩ := h A hA
    exact ⟨x, hT hxS, hxA⟩

theorem positive_iff_compl_not_mem (F : Filter α) (S : Set α) :
    Positive F S ↔ Sᶜ ∉ F := by
  rw [Positive, Mesh, inf_comm, Filter.neBot_iff, Ne, inf_principal_eq_bot]

theorem positive_principal_iff (A S : Set α) :
    Positive (𝓟 A) S ↔ (S ∩ A).Nonempty := by
  simp [Positive, Mesh]

theorem positive_of_mesh_member {X F : Filter α} (h : Mesh X F)
    {A : Set α} (hA : A ∈ X) : Positive F A :=
  (positive_iff_sets F A).mpr fun B hB => (mesh_iff_sets X F).mp h A hA B hB

/-- Lemma 2.1 of the paper: filter members are exactly the sets meeting every positive set. -/
theorem mem_iff_meets_positive (F : Filter α) (C : Set α) :
    C ∈ F ↔ ∀ X, Positive F X → (X ∩ C).Nonempty := by
  constructor
  · intro hC X hX
    exact (positive_iff_sets F X).mp hX C hC
  · intro h
    by_contra hC
    have hpos : Positive F Cᶜ := by
      rw [positive_iff_compl_not_mem, compl_compl]
      exact hC
    obtain ⟨x, hxnot, hxC⟩ := h Cᶜ hpos
    exact hxnot hxC

abbrev Rel (α : Type u) (β : Type v) := Set (α × β)

def relImage (R : Rel α β) (A : Set α) : Set β :=
  {y | ∃ x ∈ A, (x, y) ∈ R}

def column (R : Rel α β) (y : β) : Set α := {x | (x, y) ∈ R}

def Hits (R : Rel α β) (A : Set α) (B : Set β) : Prop :=
  ∃ x ∈ A, ∃ y ∈ B, (x, y) ∈ R

/-- The image filter of a relation; its image sets form a directed filter base. -/
def imageFilter (R : Rel α β) (X : Filter α) : Filter β where
  sets := {S | ∃ A ∈ X, relImage R A ⊆ S}
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := by
    rintro S T ⟨A, hA, hAS⟩ hST
    exact ⟨A, hA, hAS.trans hST⟩
  inter_sets := by
    rintro S T ⟨A, hA, hAS⟩ ⟨B, hB, hBT⟩
    refine ⟨A ∩ B, inter_mem hA hB, ?_⟩
    rintro y ⟨x, hx, hR⟩
    exact ⟨hAS ⟨x, hx.1, hR⟩, hBT ⟨x, hx.2, hR⟩⟩

theorem imageFilter_eq_generate (R : Rel α β) (X : Filter α) :
    imageFilter R X = generate {S | ∃ A ∈ X, S = relImage R A} := by
  apply le_antisymm
  · apply le_generate_iff.mpr
    rintro S ⟨A, hA, rfl⟩
    exact ⟨A, hA, Subset.rfl⟩
  · rintro S ⟨A, hA, hsub⟩
    exact mem_of_superset (mem_generate_of_mem ⟨A, hA, rfl⟩) hsub

theorem mesh_imageFilter_iff (R : Rel α β) (X : Filter α) (Y : Filter β) :
    Mesh Y (imageFilter R X) ↔ ∀ A ∈ X, ∀ B ∈ Y, Hits R A B := by
  constructor
  · intro h A hA B hB
    have hI : relImage R A ∈ imageFilter R X := ⟨A, hA, Subset.rfl⟩
    obtain ⟨y, hyB, x, hxA, hR⟩ :=
      (mesh_iff_sets Y (imageFilter R X)).mp h B hB (relImage R A) hI
    exact ⟨x, hxA, y, hyB, hR⟩
  · intro h
    apply (mesh_iff_sets Y (imageFilter R X)).mpr
    rintro B hB S ⟨A, hA, hAS⟩
    obtain ⟨x, hxA, y, hyB, hR⟩ := h A hA B hB
    exact ⟨y, hyB, hAS ⟨x, hxA, hR⟩⟩

/-! ## The required funcoids, with their defining meshing equivalence -/

structure Funcoid (α : Type u) (β : Type v) where
  forward : Filter α → Filter β
  backward : Filter β → Filter α
  mesh_duality : ∀ X Y, Mesh Y (forward X) ↔ Mesh X (backward Y)

def Funcoid.graph (f : Funcoid α β) (X : Filter α) (Y : Filter β) : Prop :=
  Mesh Y (f.forward X)

def FuncoidLE (f g : Funcoid α β) : Prop := ∀ X Y, f.graph X Y → g.graph X Y

def principalFuncoid (R : Rel α β) : Funcoid α β where
  forward := imageFilter R
  backward := imageFilter {p | (p.2, p.1) ∈ R}
  mesh_duality := by
    intro X Y
    rw [mesh_imageFilter_iff, mesh_imageFilter_iff]
    constructor
    · intro h B hB A hA
      obtain ⟨x, hxA, y, hyB, hR⟩ := h A hA B hB
      exact ⟨y, hyB, x, hxA, hR⟩
    · intro h A hA B hB
      obtain ⟨y, hyB, x, hxA, hR⟩ := h B hB A hA
      exact ⟨x, hxA, y, hyB, hR⟩

def productFuncoid (F : Filter α) (G : Filter β) : Funcoid α β := by
  classical
  exact {
    forward := fun X => if Mesh X F then G else ⊥
    backward := fun Y => if Mesh Y G then F else ⊥
    mesh_duality := by
      intro X Y
      by_cases hX : Mesh X F <;> by_cases hY : Mesh Y G <;>
        simp [hX, hY]
  }

theorem principalFuncoid_graph (R : Rel α β) (X : Filter α) (Y : Filter β) :
    (principalFuncoid R).graph X Y ↔ ∀ A ∈ X, ∀ B ∈ Y, Hits R A B :=
  mesh_imageFilter_iff R X Y

theorem productFuncoid_graph (F : Filter α) (G : Filter β)
    (X : Filter α) (Y : Filter β) :
    (productFuncoid F G).graph X Y ↔ Mesh X F ∧ Mesh Y G := by
  classical
  by_cases h : Mesh X F <;> simp [Funcoid.graph, productFuncoid, h]

/-- A relation lies above the funcoidal product in graph order. -/
def Upper (F : Filter α) (G : Filter β) (R : Rel α β) : Prop :=
  FuncoidLE (productFuncoid F G) (principalFuncoid R)

/-- Lemma 2.2, first equivalence, derived from the actual filter-graph definitions. -/
theorem upper_iff_positive_hits (F : Filter α) (G : Filter β) (R : Rel α β) :
    Upper F G R ↔ ∀ A B, Positive F A → Positive G B → Hits R A B := by
  constructor
  · intro h A B hA hB
    have hg := h (𝓟 A) (𝓟 B)
      ((productFuncoid_graph F G (𝓟 A) (𝓟 B)).mpr ⟨hA, hB⟩)
    exact (principalFuncoid_graph R (𝓟 A) (𝓟 B)).mp hg
      A (mem_principal_self A) B (mem_principal_self B)
  · intro h X Y hg
    obtain ⟨hX, hY⟩ := (productFuncoid_graph F G X Y).mp hg
    apply (principalFuncoid_graph R X Y).mpr
    intro A hA B hB
    exact h A B (positive_of_mesh_member hX hA) (positive_of_mesh_member hY hB)

theorem upper_iff_images_mem (F : Filter α) (G : Filter β) (R : Rel α β) :
    Upper F G R ↔ ∀ A, Positive F A → relImage R A ∈ G := by
  rw [upper_iff_positive_hits]
  constructor
  · intro h A hA
    apply (mem_iff_meets_positive G (relImage R A)).mpr
    intro B hB
    obtain ⟨x, hxA, y, hyB, hR⟩ := h A B hA hB
    exact ⟨y, hyB, x, hxA, hR⟩
  · intro h A B hA hB
    obtain ⟨y, hyB, x, hxA, hR⟩ :=
      (positive_iff_sets G B).mp hB (relImage R A) (h A hA)
    exact ⟨x, hxA, y, hyB, hR⟩

theorem upper_principal_iff_image (F : Filter α) (B0 : Set β) (R : Rel α β) :
    Upper F (𝓟 B0) R ↔ ∀ A, Positive F A → B0 ⊆ relImage R A := by
  constructor
  · intro h A hA y hy
    have hY : Positive (𝓟 B0) ({y} : Set β) :=
      (positive_principal_iff B0 {y}).mpr ⟨y, mem_singleton y, hy⟩
    obtain ⟨x, hxA, z, hz, hR⟩ :=
      (upper_iff_positive_hits F (𝓟 B0) R).mp h A {y} hA hY
    have hzy : z = y := mem_singleton_iff.mp hz
    subst z
    exact ⟨x, hxA, hR⟩
  · intro h
    apply (upper_iff_positive_hits F (𝓟 B0) R).mpr
    intro A B hA hB
    obtain ⟨y, hyB, hyB0⟩ := (positive_principal_iff B0 B).mp hB
    obtain ⟨x, hxA, hR⟩ := h A hA hyB0
    exact ⟨x, hxA, y, hyB, hR⟩

theorem upper_principal_iff_columns (F : Filter α) (B0 : Set β) (R : Rel α β) :
    Upper F (𝓟 B0) R ↔ ∀ y ∈ B0, column R y ∈ F := by
  rw [upper_principal_iff_image]
  constructor
  · intro h y hy
    apply (mem_iff_meets_positive F (column R y)).mpr
    intro A hA
    obtain ⟨x, hxA, hR⟩ := h A hA hy
    exact ⟨x, hxA, hR⟩
  · intro h A hA y hy
    obtain ⟨x, hxA, hR⟩ := (positive_iff_sets F A).mp hA (column R y) (h y hy)
    exact ⟨x, hxA, hR⟩

/-! ## Reloid products and the general chain -/

abbrev Reloid (α : Type u) (β : Type v) := Filter (α × β)

/-- Porton's outward reloid: the meet of principal relations above the funcoid. -/
def outward (f : Funcoid α β) : Reloid α β :=
  generate {R | FuncoidLE f (principalFuncoid R)}

theorem outward_eq_iInf (f : Funcoid α β) :
    outward f = ⨅ (R : Rel α β) (_ : FuncoidLE f (principalFuncoid R)), 𝓟 R :=
  generate_eq_biInf _

def secondProduct (F : Filter α) (G : Filter β) : Reloid α β :=
  outward (productFuncoid F G)

def obliqueIndex (F : Filter α) (G : Filter β) : Set (Rel α β) :=
  {R | ∃ B0 ∈ G, Upper F (𝓟 B0) R}

def obliqueProduct (F : Filter α) (G : Filter β) : Reloid α β :=
  generate (obliqueIndex F G)

def rectangleIndex (F : Filter α) (G : Filter β) : Set (Rel α β) :=
  {R | ∃ A ∈ F, ∃ B ∈ G, R = A ×ˢ B}

def classicalProduct (F : Filter α) (G : Filter β) : Reloid α β :=
  generate (rectangleIndex F G)

/-- The column family is itself a genuine filter, including the universal relation. -/
def columnFilter (F : Filter α) (G : Filter β) : Reloid α β where
  sets := {R | ∃ B0 ∈ G, ∀ y ∈ B0, column R y ∈ F}
  univ_sets := ⟨univ, univ_mem, fun _ _ => by simp [column]⟩
  sets_of_superset := by
    rintro R S ⟨B0, hB0, hcol⟩ hRS
    exact ⟨B0, hB0, fun y hy => mem_of_superset (hcol y hy) (fun _ hx => hRS hx)⟩
  inter_sets := by
    rintro R S ⟨B1, hB1, hcol1⟩ ⟨B2, hB2, hcol2⟩
    refine ⟨B1 ∩ B2, inter_mem hB1 hB2, fun y hy => ?_⟩
    change column R y ∩ column S y ∈ F
    exact inter_mem (hcol1 y hy.1) (hcol2 y hy.2)

theorem generate_filter_sets (F : Filter α) : generate F.sets = F :=
  le_antisymm (fun _ h => mem_generate_of_mem h) (le_generate_iff.mpr fun _ h => h)

theorem oblique_eq_columnFilter (F : Filter α) (G : Filter β) :
    obliqueProduct F G = columnFilter F G := by
  have hJ : obliqueIndex F G = (columnFilter F G).sets := by
    ext R
    change (∃ B0 ∈ G, Upper F (𝓟 B0) R) ↔ _
    simp only [upper_principal_iff_columns]
    rfl
  unfold obliqueProduct
  rw [hJ, generate_filter_sets]

theorem mem_oblique_iff_columns (F : Filter α) (G : Filter β) (R : Rel α β) :
    R ∈ obliqueProduct F G ↔ ∃ B0 ∈ G, ∀ y ∈ B0, column R y ∈ F := by
  rw [oblique_eq_columnFilter]
  rfl

theorem oblique_neBot (F : Filter α) (G : Filter β) (hF : NeBot F) (hG : NeBot G) :
    NeBot (obliqueProduct F G) := by
  apply forall_mem_nonempty_iff_neBot.mp
  intro R hR
  obtain ⟨B0, hB0, hcol⟩ := (mem_oblique_iff_columns F G R).mp hR
  obtain ⟨y, hy⟩ := hG.nonempty_of_mem hB0
  obtain ⟨x, hx⟩ := hF.nonempty_of_mem (hcol y hy)
  exact ⟨(x, y), hx⟩

theorem classical_eq_prod (F : Filter α) (G : Filter β) :
    classicalProduct F G = F ×ˢ G := by
  apply le_antisymm
  · intro R hR
    obtain ⟨A, hA, B, hB, hsub⟩ := mem_prod_iff.mp hR
    have hrect : A ×ˢ B ∈ classicalProduct F G :=
      mem_generate_of_mem ⟨A, hA, B, hB, rfl⟩
    exact mem_of_superset hrect hsub
  · apply le_generate_iff.mpr
    rintro R ⟨A, hA, B, hB, rfl⟩
    exact prod_mem_prod hA hB

theorem mem_classical_iff (F : Filter α) (G : Filter β) (R : Rel α β) :
    R ∈ classicalProduct F G ↔ ∃ A ∈ F, ∃ B ∈ G, A ×ˢ B ⊆ R := by
  rw [classical_eq_prod, mem_prod_iff]

theorem second_le_oblique (F : Filter α) (G : Filter β) :
    secondProduct F G ≤ obliqueProduct F G := by
  apply le_generate_iff.mpr
  rintro R ⟨B0, hB0, hR⟩
  apply mem_generate_of_mem
  apply (upper_iff_positive_hits F G R).mpr
  intro A B hA hB
  obtain ⟨y, hyB, hyB0⟩ := (positive_iff_sets G B).mp hB B0 hB0
  obtain ⟨x, hxA, hxy⟩ := (upper_principal_iff_image F B0 R).mp hR A hA hyB0
  exact ⟨x, hxA, y, hyB, hxy⟩

theorem oblique_le_classical (F : Filter α) (G : Filter β) :
    obliqueProduct F G ≤ classicalProduct F G := by
  intro R hR
  obtain ⟨A, hA, B, hB, hsub⟩ := (mem_classical_iff F G R).mp hR
  apply (mem_oblique_iff_columns F G R).mpr
  exact ⟨B, hB, fun y hy => mem_of_superset hA (fun x hx => hsub ⟨hx, hy⟩)⟩

theorem second_eq_bot_of_disjoint {F : Filter α} {G : Filter β} {L H : Rel α β}
    (hL : Upper F G L) (hH : Upper F G H)
    (hdisj : ∀ p, p ∈ L → p ∈ H → False) : secondProduct F G = ⊥ := by
  apply empty_mem_iff_bot.mp
  have hLm : L ∈ secondProduct F G := mem_generate_of_mem hL
  have hHm : H ∈ secondProduct F G := mem_generate_of_mem hH
  exact mem_of_superset (inter_mem hLm hHm) (fun p hp => (hdisj p hp.1 hp.2).elim)

def offDiagonal (α : Type u) : Rel α α := {p | p.1 ≠ p.2}

theorem offDiagonal_mem_oblique (F : Filter α)
    (homit : ∀ x : α, {x}ᶜ ∈ F) : offDiagonal α ∈ obliqueProduct F F := by
  apply (mem_oblique_iff_columns F F (offDiagonal α)).mpr
  refine ⟨univ, univ_mem, fun y _ => ?_⟩
  simpa [column, offDiagonal] using homit y

theorem offDiagonal_not_mem_classical (F : Filter α) (hF : NeBot F) :
    offDiagonal α ∉ classicalProduct F F := by
  intro hD
  obtain ⟨A, hA, B, hB, hsub⟩ := (mem_classical_iff F F (offDiagonal α)).mp hD
  obtain ⟨x, hxA, hxB⟩ := hF.nonempty_of_mem (inter_mem hA hB)
  have hdiag : (x, x) ∈ offDiagonal α :=
    hsub (show (x, x) ∈ A ×ˢ B from ⟨hxA, hxB⟩)
  exact hdiag rfl

def StrictChain (F : Filter α) (G : Filter β) : Prop :=
  secondProduct F G < obliqueProduct F G ∧ obliqueProduct F G < classicalProduct F G

theorem strictChain_of_collapse (F : Filter α) (hF : NeBot F)
    (homit : ∀ x : α, {x}ᶜ ∈ F) (hcollapse : secondProduct F F = ⊥) :
    StrictChain F F := by
  constructor
  · rw [hcollapse]
    exact bot_lt_iff_ne_bot.mpr (oblique_neBot F F hF hF).ne
  · apply lt_iff_le_not_ge.mpr
    exact ⟨oblique_le_classical F F,
      fun h => offDiagonal_not_mem_classical F hF (h (offDiagonal_mem_oblique F homit))⟩

theorem not_principal_of_omit_singletons (F : Filter α) (hF : NeBot F)
    (homit : ∀ x : α, {x}ᶜ ∈ F) (A : Set α) : F ≠ 𝓟 A := by
  intro hEq
  have hA : A ∈ F := hEq ▸ mem_principal_self A
  obtain ⟨x, hxA⟩ := hF.nonempty_of_mem hA
  have hcomp : {x}ᶜ ∈ 𝓟 A := hEq ▸ homit x
  exact hcomp hxA (mem_singleton x)

/-! ## The cofinite filter on the natural numbers (Theorem 3.1) -/

def Phi : Filter ℕ := cofinite

theorem phi_neBot : NeBot Phi := cofinite_neBot

theorem phi_omit_singletons (x : ℕ) : {x}ᶜ ∈ Phi :=
  (finite_singleton x).compl_mem_cofinite

theorem positive_phi_iff (A : Set ℕ) : Positive Phi A ↔ A.Infinite := by
  rw [positive_iff_compl_not_mem]
  change ¬ (Aᶜ)ᶜ.Finite ↔ A.Infinite
  rw [compl_compl]
  rfl

def lowerNat : Rel ℕ ℕ := {p | p.2 < p.1}
def upperNat : Rel ℕ ℕ := {p | p.1 < p.2}

theorem lowerNat_upper : Upper Phi Phi lowerNat := by
  apply (upper_iff_positive_hits Phi Phi lowerNat).mpr
  intro A B hA hB
  obtain ⟨y, hyB⟩ := ((positive_phi_iff B).mp hB).nonempty
  obtain ⟨x, hxA, hyx⟩ := ((positive_phi_iff A).mp hA).exists_gt y
  exact ⟨x, hxA, y, hyB, hyx⟩

theorem upperNat_upper : Upper Phi Phi upperNat := by
  apply (upper_iff_positive_hits Phi Phi upperNat).mpr
  intro A B hA hB
  obtain ⟨x, hxA⟩ := ((positive_phi_iff A).mp hA).nonempty
  obtain ⟨y, hyB, hxy⟩ := ((positive_phi_iff B).mp hB).exists_gt x
  exact ⟨x, hxA, y, hyB, hxy⟩

theorem frechet_second_eq_bot : secondProduct Phi Phi = ⊥ := by
  apply second_eq_bot_of_disjoint lowerNat_upper upperNat_upper
  intro p hL hH
  exact lt_asymm (a := p.2) (b := p.1) hL hH

theorem frechet_strict_chain : StrictChain Phi Phi :=
  strictChain_of_collapse Phi phi_neBot phi_omit_singletons frechet_second_eq_bot

theorem frechet_solution :
    NeBot Phi ∧ (∀ A : Set ℕ, Phi ≠ 𝓟 A) ∧
    secondProduct Phi Phi = ⊥ ∧ StrictChain Phi Phi :=
  ⟨phi_neBot, not_principal_of_omit_singletons Phi phi_neBot phi_omit_singletons,
    frechet_second_eq_bot, frechet_strict_chain⟩

/-! ## The exact proposed filter on the real numbers (Theorem 4.1) -/

/-- The neighbourhood filter of zero, presented by symmetric intervals. -/
def delta : Filter ℝ where
  sets := {S | ∃ ε : ℝ, 0 < ε ∧ Ioo (-ε) ε ⊆ S}
  univ_sets := ⟨1, zero_lt_one, subset_univ _⟩
  sets_of_superset := by
    rintro S T ⟨ε, hε, hsub⟩ hST
    exact ⟨ε, hε, hsub.trans hST⟩
  inter_sets := by
    rintro S T ⟨ε, hε, hS⟩ ⟨δ, hδ, hT⟩
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    intro x hx
    exact ⟨hS ⟨lt_of_le_of_lt (neg_le_neg (min_le_left ε δ)) hx.1,
                  lt_of_lt_of_le hx.2 (min_le_left ε δ)⟩,
           hT ⟨lt_of_le_of_lt (neg_le_neg (min_le_right ε δ)) hx.1,
                  lt_of_lt_of_le hx.2 (min_le_right ε δ)⟩⟩

/-- The filter generated by all positive intervals `(0, ε)`. -/
def deltaPlus : Filter ℝ where
  sets := {S | ∃ ε : ℝ, 0 < ε ∧ Ioo 0 ε ⊆ S}
  univ_sets := ⟨1, zero_lt_one, subset_univ _⟩
  sets_of_superset := by
    rintro S T ⟨ε, hε, hsub⟩ hST
    exact ⟨ε, hε, hsub.trans hST⟩
  inter_sets := by
    rintro S T ⟨ε, hε, hS⟩ ⟨δ, hδ, hT⟩
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    intro x hx
    exact ⟨hS ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left ε δ)⟩,
           hT ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right ε δ)⟩⟩

theorem delta_eq_iInf :
    delta = ⨅ (ε : ℝ) (_ : 0 < ε), 𝓟 (Ioo (-ε) ε) := by
  apply le_antisymm
  · exact le_iInf fun ε => le_iInf fun hε => le_principal_iff.mpr ⟨ε, hε, Subset.rfl⟩
  · rintro S ⟨ε, hε, hsub⟩
    have hcore : (⨅ (r : ℝ) (_ : 0 < r), 𝓟 (Ioo (-r) r)) ≤ 𝓟 (Ioo (-ε) ε) :=
      iInf_le_of_le ε (iInf_le _ hε)
    exact mem_of_superset (le_principal_iff.mp hcore) hsub

/-- Identification with the exact meet appearing in the original problem. -/
theorem deltaPlus_eq_inf : deltaPlus = delta ⊓ 𝓟 (Ioi (0 : ℝ)) := by
  apply le_antisymm
  · apply le_inf
    · rintro S ⟨ε, hε, hsub⟩
      refine ⟨ε, hε, fun x hx => hsub ⟨?_, hx.2⟩⟩
      exact lt_trans (neg_lt_zero.mpr hε) hx.1
    · exact le_principal_iff.mpr ⟨1, zero_lt_one, fun _ hx => hx.1⟩
  · rintro S ⟨ε, hε, hsub⟩
    exact mem_inf_of_inter
      (show Ioo (-ε) ε ∈ delta from ⟨ε, hε, Subset.rfl⟩)
      (mem_principal_self (Ioi (0 : ℝ)))
      (fun x hx => hsub ⟨hx.2, hx.1.2⟩)

theorem deltaPlus_neBot : NeBot deltaPlus := by
  apply forall_mem_nonempty_iff_neBot.mp
  rintro S ⟨ε, hε, hsub⟩
  exact ⟨ε / 2, hsub ⟨half_pos hε, half_lt_self hε⟩⟩

theorem deltaPlus_omit_singletons (y : ℝ) : {y}ᶜ ∈ deltaPlus := by
  by_cases hy : 0 < y
  · refine ⟨y, hy, ?_⟩
    intro x hx hxy
    exact (ne_of_lt hx.2) (mem_singleton_iff.mp hxy)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hxy
    exact hy ((mem_singleton_iff.mp hxy) ▸ hx.1)

theorem positive_deltaPlus_iff (A : Set ℝ) :
    Positive deltaPlus A ↔ ∀ ε : ℝ, 0 < ε → (A ∩ Ioo 0 ε).Nonempty := by
  constructor
  · intro h ε hε
    exact (positive_iff_sets deltaPlus A).mp h (Ioo 0 ε) ⟨ε, hε, Subset.rfl⟩
  · intro h
    apply (positive_iff_sets deltaPlus A).mpr
    rintro S ⟨ε, hε, hsub⟩
    obtain ⟨x, hxA, hxI⟩ := h ε hε
    exact ⟨x, hxA, hsub hxI⟩

def lowerReal : Rel ℝ ℝ := {p | p.2 < p.1}
def upperReal : Rel ℝ ℝ := {p | p.1 < p.2}

theorem lowerReal_upper : Upper deltaPlus deltaPlus lowerReal := by
  apply (upper_iff_positive_hits deltaPlus deltaPlus lowerReal).mpr
  intro A B hA hB
  obtain ⟨x, hxA, hxI⟩ := (positive_deltaPlus_iff A).mp hA 1 zero_lt_one
  obtain ⟨y, hyB, hyI⟩ := (positive_deltaPlus_iff B).mp hB x hxI.1
  exact ⟨x, hxA, y, hyB, hyI.2⟩

theorem upperReal_upper : Upper deltaPlus deltaPlus upperReal := by
  apply (upper_iff_positive_hits deltaPlus deltaPlus upperReal).mpr
  intro A B hA hB
  obtain ⟨y, hyB, hyI⟩ := (positive_deltaPlus_iff B).mp hB 1 zero_lt_one
  obtain ⟨x, hxA, hxI⟩ := (positive_deltaPlus_iff A).mp hA y hyI.1
  exact ⟨x, hxA, y, hyB, hxI.2⟩

theorem real_second_eq_bot : secondProduct deltaPlus deltaPlus = ⊥ := by
  apply second_eq_bot_of_disjoint lowerReal_upper upperReal_upper
  intro p hL hH
  exact lt_asymm (a := p.2) (b := p.1) hL hH

theorem real_strict_chain : StrictChain deltaPlus deltaPlus :=
  strictChain_of_collapse deltaPlus deltaPlus_neBot deltaPlus_omit_singletons real_second_eq_bot

theorem real_solution :
    NeBot deltaPlus ∧ (∀ A : Set ℝ, deltaPlus ≠ 𝓟 A) ∧
    secondProduct deltaPlus deltaPlus = ⊥ ∧ StrictChain deltaPlus deltaPlus :=
  ⟨deltaPlus_neBot,
    not_principal_of_omit_singletons deltaPlus deltaPlus_neBot deltaPlus_omit_singletons,
    real_second_eq_bot, real_strict_chain⟩

/-- Both existential conjectures, with proper input filters on the same infinite base. -/
theorem existential_solution :
    ∃ F G : Filter ℕ, NeBot F ∧ NeBot G ∧ StrictChain F G :=
  ⟨Phi, Phi, phi_neBot, phi_neBot, frechet_strict_chain⟩

/-- The real-number result restated at the literal pair named by Porton. -/
theorem proposed_pair_solution :
    let F := delta ⊓ 𝓟 (Ioi (0 : ℝ))
    NeBot F ∧ (∀ A : Set ℝ, F ≠ 𝓟 A) ∧ secondProduct F F = ⊥ ∧ StrictChain F F := by
  simpa only [deltaPlus_eq_inf] using real_solution

end StrictProducts
