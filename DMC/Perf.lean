
import Mathlib

def divisors (n : Nat): Finset Nat :=
  let rec loop : Nat -> Finset Nat
  | 0 => {}
  | m + 1 =>
    if (m + 1) ∣ n then
      insert (m + 1) (loop m)
    else
      loop m
  loop n

#eval divisors 35

--Euler's sigma function
--AKA: the σ₁ Divisor function
--Sums all divisors of n
def σ (n : Nat) : Nat :=
  let rec loop : Nat -> Nat
  | 0 => 0
  | m + 1 =>
    if (m + 1) ∣ n then
      (m + 1) + (loop m)
    else
      loop m
  loop n

theorem σ_multiplicitive (a b : Nat) (H : Nat.Coprime a b) :
σ (a * b) = σ a * σ b := by
  simp [σ]
  induction a
  induction b
  . case zero => simp [σ.loop]
  . case zero.succ => simp [σ.loop]
  . case succ IH =>
    simp [σ.loop]




--A number is perfect if it equals the sum of its divsors minus itself
def perfect (n : Nat) : Prop :=
  n = σ n - n

--Theorem 9 in https://math.dartmouth.edu/~jvoight/notes/perfelem.pdf
lemma Euler (n : Nat) (H1 : Even n) (H2 : perfect n) :
  ∃p, Prime (2^p - 1) -> (n = 2^(p-1) * (2^p - 1)) := by
  apply Exists.intro
  intro H3


lemma Euclid (n : Nat) (H1 : Even n) (H2 : perfect n) :
  ∃p, (n = 2^(p-1) * (2^p - 1) ∧ Prime (2^p - 1)) := by
  apply Exists.intro
  apply And.intro
  . apply H2
  . apply H3

theorem EuclidEuler (n : Nat) (H1 : Even n) :
  perfect n ↔ ∃p, (n = 2^(p-1) * (2^p - 1) ∧ Prime (2^p - 1)) := by
  apply Iff.intro
  . case mp =>
    intros H2
