
import Mathlib.Init.Set
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.LocallyFinite

/-
2.2 List the elements in the following sets where E is the set
of evens
-/

def Even (i : Int) : Prop := Int.mod i 2 = 0

instance : DecidablePred Even := by
  simp [DecidablePred]
  intro H
  rw [Even]
  apply inferInstance

def E : Set Int := Even

instance (i : Int) : Decidable (i ∈ E) := by
  simp [Membership.mem, Set.Mem, E]
  apply inferInstance

-- (1)

def A : Set Int := {n | -4 ≤ n ∧ n ≤ 15 ∧ n ∈ E}

instance (n : Int) : Decidable (n ∈ A) := by
  simp [Membership.mem, Set.Mem]
  rw [A, setOf]
  apply inferInstance

instance : Finite A := by
  simp [A, setOf]
  have H : A ⊆ ↑(Finset.Icc (-4) 15) := by sorry


instance (S : Finset Int) :
Decidable (A = ↑S) := by
  have H : A = ↑S ↔ A ⊆ ↑S ∧ ↑S ⊆ A := by exact Set.Subset.antisymm_iff
  rw [H]
  have dec_S_sube_A : Decidable (↑S ⊆ A) := by
    simp [Set.subset_def, A]
    apply inferInstance
  have dec_mem_S (n : Int) : Decidable (n ∈ ↑S) := by
    apply inferInstance
  have dec_A_sube_S : Decidable (A ⊆ ↑S) := by
    simp [Set.subset_def, Membership.mem, Set.Mem]

    sorry
  sorry


#eval List.Forall (· ∈ A) [-4, -2, 0, 2, 4, 6, 8, 10, 12, 14]


-- (2)
def B : Set Int := {x : Int | x^2 = 9}

instance (n : Int) : Decidable (n ∈ B) := by
  simp [Membership.mem, Set.Mem]
  rw [B, setOf]
  apply inferInstance

#check List.Forall (· ∈ B) [-3, 3]
