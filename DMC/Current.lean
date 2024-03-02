
import Mathlib

/-
2.2 List the elements in the following sets where E is the set
of evens
-/

def E : Set Int := fun i => i % 2 = 0

instance (i : Int) : Decidable (i ∈ E) := by
  simp [Membership.mem, Set.Mem, E]
  apply inferInstance

def A : Set Int := {n | -4 ≤ n ∧ n ≤ 15 ∧ n ∈ E}

instance (n : Int) : Decidable (n ∈ A) := by
  simp [Membership.mem, Set.Mem]
  rw [A, setOf]
  apply inferInstance

instance instDecSsubA (S : Finset Int) : Decidable (↑S ⊆ A) := by
  rewrite [Set.subset_def, A, Membership.mem]
  --apply inferInstance



example : A = ({-4, -2, 0, 2, 4, 6, 8, 10, 12, 14} : Finset Int) := by
  apply Set.eq_of_subset_of_subset ?a_sub_b ?b_sub_a
  . case a_sub_b => -- A ⊆ ↑{-4, -2, 0, 2, 4, 6, 8, 10, 12, 14}
    simp [A, E, Even]
    intro n
    contrapose
    simp only [Int.reduceNeg, Set.mem_setOf_eq, not_and]
    intros NOT_IN_SET LE_N4 LE_15 EVEN_IN_N
    have EVEN_N : n % 2 = 0 := by exact EVEN_IN_N
    simp at NOT_IN_SET
    omega
  . case b_sub_a => -- ↑{-4, -2, 0, 2, 4, 6, 8, 10, 12, 14} ⊆ A
    simp [A, Set.subset_def]
    trivial

def B : Set Int := {n | n^2 = 9}

example : B = {3, -3} := by
  apply Set.eq_of_subset_of_subset ?a_sub_b ?b_sub_a
  . case a_sub_b =>
    simp [B, Set.subset_def]
    intros n H
    rw [<-abs_eq, <-Int.coe_natAbs, <-Int.sqrt_eq, <-pow_two, H]
    repeat' decide
  . case b_sub_a =>
    simp [B, Set.subset_def]

def C : Set Int := {n | n^2 = 6}

example : C = (∅ : Set Int) := by
  apply Set.eq_of_subset_of_subset ?a_sub_b ?b_sub_a
  . case a_sub_b =>
    rw [C, Set.subset_def]
    intros n H
    simp at H
    rw [pow_two] at H

  . case b_sub_a =>
    tauto

def D : Set Real := {(n : Real) | n = n^2 - 1}

example : D = {, -3} := by
  apply Set.eq_of_subset_of_subset ?a_sub_b ?b_sub_a
  . case a_sub_b =>
    simp [B, Set.subset_def]
    intros n H
    rw [<-abs_eq, <-Int.coe_natAbs, <-Int.sqrt_eq, <-pow_two, H]
    decide
    decide
  . case b_sub_a =>
    simp [B, Set.subset_def]

/-
2.3 Give a formal definition of the following sets using a variable
We formally define this by saying there exists a predicate that constructs
a set using setof such that the elements that are provided in the elipses
are a subset of the new set.
-/

example : {0, 1, 4, 9, 16, 25, 36} ⊆ {(x : Nat) | ∃ (n : Nat), x = n^2} := by
  simp [Set.subset_def]
  apply And.intro
  .

--2.6
example : ∃ α : Type, ∃ (A B : Set α), ¬(A ⊆ B) ∧ ¬(B ⊆ A) := by
  existsi Nat, {0}, {1}
  simp [Set.subset_def]
