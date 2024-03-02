
--import Mathlib.Init.Set
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Range

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

-- instance : Inhabited A := ⟨0, by simp[Membership.mem, Set.Mem, A, setOf, E, Even]⟩

--Uses Classical.choice
instance FA : Fintype ↑A := by
  let s : Set ℤ := {n | -4 ≤ n ∧ n ≤ 15}
  suffices H : Fintype ↑(s ∩ {n | n ∈ E}) by
    simp [Inter.inter, Set.inter, and_assoc] at H
    simp [A]
    exact H
  suffices H2 : Fintype ↑s by
    apply Set.fintypeInterOfLeft
  exact Set.fintypeIcc (-4) 15

-- #print axioms FA

--Where is Classical Choice Coming from?
--theorem FS : Fintype (Finset.Icc (-1) 4) := by



#print axioms Set.fintypeIcc

instance (S : Finset Int) : Decidable (↑S ⊆ A) := by
  simp [Set.subset_def, A]
  apply inferInstance

instance (S : Finset Int) : Decidable (A = ↑S) := by
  suffices _ : Decidable (A ⊆ ↑S ∧ ↑S ⊆ A) by
    rw [Set.Subset.antisymm_iff]
    assumption
  have H1 : Decidable (A ⊆ ↑S) := by
    simp [Set.subset_def]
    rw [(Set.coe_toFinset A).symm]
    exact Finset.decidableDforallFinset
  have H2 : Decidable (↑S ⊆ A) := by
    simp [Set.subset_def, A]
    apply inferInstance
  exact And.decidable

#eval A = ({-4, -2, 0, 2, 4, 6, 8, 10, 12, 14, 15} : Finset Int)
example : A = ({-4, -2, 0, 2, 4, 6, 8, 10, 12, 14, 15} : Finset Int) := by decide

lemma lt_neq_eq_prev {a b : Int} : a < b -> a ≠ b - 1 -> a < b - 1 := by
  intro H1
  contrapose!
  intro H2
  simp [le_iff_lt_or_eq] at *
  cases H2
  linarith
  tauto

lemma lt_eq_sub1 {a b : Int} : a < b -> a = b - 1 ∨ a < b - 1 := by
  intro H
  by_cases (a < b - 1)
  . case _ =>
    apply Or.inr;
    assumption
  . case _ =>
    apply Or.inl;
    linarith

example : A = ({-4, -2, 0, 2, 4, 6, 8, 10, 12, 14} : Finset Int) := by
  apply Set.eq_of_subset_of_subset
  . case _ =>
    intro x
    simp [Set.subset_def, A]
    contrapose!
    intro H
    aesop --to convert all conjucts to hypotheses
    simp [Set.Mem, Membership.mem, E, Even] at left_1
    have : x < 15 := by
      simp [le_iff_lt_or_eq] at left
      cases left
      . case inl => assumption
      . case inr H2 => rw [H2] at left_1; simp [Int.mod] at left_1;
    have : x < 14 := by
      have H := lt_neq_eq_prev this right
      tauto
    have : x < 13 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H => rw [H] at left_1; simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < 12 := by
      have H := lt_neq_eq_prev this left_10
      tauto
    have : x < 11 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H => rw [H] at left_1; simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < 10 := by
      have H := lt_neq_eq_prev this left_9
      tauto
    have : x < 9 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H => rw [H] at left_1; simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < 8 := by
      have H := lt_neq_eq_prev this left_8
      tauto
    have : x < 7 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H => rw [H] at left_1; simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < 6 := by
      have H := lt_neq_eq_prev this left_7
      tauto
    have : x < 5 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H => rw [H] at left_1; simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < 4 := by
      have H := lt_neq_eq_prev this left_6
      tauto
    have : x < 3 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H => rw [H] at left_1; simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < 2 := by
      have H := lt_neq_eq_prev this left_5
      tauto
    have : x < 1 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H => rw [H] at left_1; simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < 0 := by
      have H := lt_neq_eq_prev this left_4
      tauto
    have : x < -1 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H =>
        rw [H] at left_1;
        simp at left_1;
        have H : -1 = Int.negSucc 0 := by rfl;
        rw [H] at left_1;
        simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < -2 := by
      have H := lt_neq_eq_prev this left_3
      tauto
    have : x < -3 := by
      have H := lt_eq_sub1 this
      cases H
      . case inl H =>
        rw [H] at left_1;
        simp at left_1;
        have H : -3 = Int.negSucc 2 := by rfl;
        rw [H] at left_1;
        simp [Int.mod] at left_1;
      . case inr H => assumption
    have : x < -4 := by
      have H := lt_neq_eq_prev this left_2
      tauto
    exact this
  . case _ => decide


-- (2)
def B : Set Int := {x : Int | x^2 = 9}

instance (n : Int) : Decidable (n ∈ B) := by
  simp [Membership.mem, Set.Mem]
  rw [B, setOf]
  apply inferInstance

#check List.Forall (· ∈ B) [-3, 3]
