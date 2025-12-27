import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Setoid.Partition
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Defs
import LeanCourse25.Projects.Prereq.Ramsey
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

open Finset Setoid Nat SimpleGraph

variable {α : Type*}

theorem schur (c : ℕ) (hc : c > 0) :
  ∃ S, ∀ (C : Finset (Set (Fin S))),
  (IsPartition C.toSet ∧ #C = c) → ∃ a ∈ C, ∃ x ∈ a, ∃ y ∈ a, ∃ z ∈ a, x + y = z := by
  let n : (Fin c → ℕ) := fun _ ↦ 3
  have ramval : (∃ N, ∀ D : TopEdgeLabelling (Fin N) (Fin c), ∃ (p : Finset (Fin N)) (color : _),
   D.MonochromaticOf p color ∧ n color ≤ p.card) := by apply ramsey_fin_exists n
  obtain ⟨N, ramval⟩ := ramval
  use N
  simp
  intro C PartC CardC
  have index : (Fin N → C) := by
    intro x
    let q : (Set (Fin N)) → Prop := fun y ↦ x ∈ y
    have dec : DecidablePred q := by exact Classical.decPred q
    use Finset.choose q C (PartC.2 x)
    exact choose_mem q C (PartC.2 x)
  have Ctoc : C ≃ Fin c := by exact equivFinOfCardEq CardC
  let tel : (TopEdgeLabelling (Fin N) (Fin c)) :=
    fun x ↦ Ctoc.1 (index (max x.1.out.fst x.1.out.snd - min x.1.out.fst x.1.out.snd))
    --TODO: maybe we can find an appropriate norm function
  specialize ramval tel
  obtain ⟨p, c1, elm, hp⟩ := ramval
  use p.toSet
  constructor
  · sorry
  · have Cardp: #p ≥ 3 := by gcongr
    have : ∃ i ∈ p, ∃ j ∈ p, ∃ k ∈ p, i > j ∧ j > k ∧ i > k := by
      sorry
    obtain ⟨i, hi, j, hj, k, hk, hij, hjk, hik⟩ := this
    use i - j --TODO: use a better structure than combining constructors
    constructor
    · simp  -- Type 1
      have elmij : tel ⟨s(i, j), (Ne.symm (Fin.ne_of_lt hij))⟩ = c1 := by
          specialize elm hi hj (Ne.symm (Fin.ne_of_lt hij)); exact elm
      have quoti: (Quot.out s(i, j)).1 = i := by sorry  -- Type 2
      have quotj: (Quot.out s(i, j)).2 = j := by sorry  -- Type 2
      have : Ctoc.1 (index (i - j)) = c1 := by
        rw[←elmij]
        unfold tel
        simp
        rw??
        rw[quoti, quotj]
        rw [max_eq_left ?_]
        rw [min_eq_right ?_]
        gcongr
        exact Fin.le_of_lt hij

      sorry  -- Type 1
    · use j - k
      constructor
      · sorry -- Type 1
      · simp
        have:  i - k = i - j + (j - k):= by sorry
        rw[←this]
        sorry  -- Type 1
