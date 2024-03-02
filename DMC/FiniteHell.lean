import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Range

def B : Set ℤ := Set.Icc (-4) 15
instance FinsetB : Fintype B := by
  apply Set.fintypeIcc

def x : Finset ℤ := (Finset.Icc (-4) 15)

instance FinsetB' : Fintype B := {
  elems := x
  complete := by
    apply Finset.fintypeIcc

}


#print axioms FinsetB

-- instance (a b : Int) : Fintype (Finset.Icc a b) := {
--   elems := (Finset.Icc a b)
--   complete := by
--     apply Finset.fintypeIcc
-- }


def r : Int → Int → Prop :=  (· ≤ ·)
instance : DecidableRel r := by
  simp [DecidableRel, r]
  apply inferInstance
instance : IsTrans Int r := by
  apply IsTrans.mk
  simp [r]
  intro a b c H1 H2
  linarith
instance : IsAntisymm Int r := by
  apply IsAntisymm.mk
  simp [r]
  intro a b H1 H2
  linarith
instance : IsTotal Int r := by
  apply IsTotal.mk
  simp [r]
  intro a b
  exact Int.le_total a b
--#eval Finset.sort r B.toFinset
