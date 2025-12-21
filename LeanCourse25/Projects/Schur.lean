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

lemma finset_set_fin_nat_partition_has_index (S : ℕ) (C : Finset (Set (Fin S))) :
  IsPartition C.toSet → ∃ (ι : (Fin S → Fin #C)), ι.Bijective := by sorry

theorem schur (c : ℕ) (hc : c > 0) :
  ∃ S, ∀ (C : Finset (Set (Fin S))),
  (IsPartition C.toSet ∧ #C = c) → ∃ a ∈ C, ∃ x ∈ a, ∃ y ∈ a, ∃ z ∈ a, x + y = z := by
  let n : (Fin c → ℕ) := fun _ ↦ 3
  have ramval : (∃ N, ∀ D : TopEdgeLabelling (Fin N) (Fin c), ∃ (p : Finset (Fin N)) (c : _),
   D.MonochromaticOf p c ∧ n c ≤ p.card) := by apply ramsey_fin_exists n
  obtain ⟨N, ramval⟩ := ramval
  use N
  simp
  intro C PartC CardC
  have index: ∃ (ι : (Fin N → Fin c)), ι.Bijective :=
      by rw[← CardC]; apply finset_set_fin_nat_partition_has_index N C; apply PartC
  obtain ⟨ι, hι⟩ := index
  let tel : (TopEdgeLabelling (Fin N) (Fin c)) :=
    fun x ↦ ι (max (x.1.out.fst - x.1.out.snd) (x.1.out.snd - x.1.out.fst))
    --TODO: maybe we can find an appropriate norm function
  specialize ramval tel
  obtain ⟨p, c1, elm, hp⟩ := ramval
  use p.toSet
  constructor
  · sorry
  · have : #p ≥ 3 := by gcongr
    have : ∃ i ∈ p, ∃ j ∈ p, ∃ k ∈ p, i > j ∧ j > k ∧ i > k := by sorry
    obtain ⟨i, hi, j, hj, k, hk, hij, hjk, hik⟩ := this
    use i - j --TODO: use a better structure than combining constructors
    constructor
    · simp
      have elmij : tel ⟨s(i, j), (Ne.symm (Fin.ne_of_lt hij))⟩ = c1 := by
          specialize elm hi hj (Ne.symm (Fin.ne_of_lt hij)); exact elm
      have quoti: (Quot.out s(i, j)).1 = i := by sorry
      have quotj: (Quot.out s(i, j)).2 = j := by sorry
      have : ι (i - j) = c1 := by
        rw[←elmij]
        unfold tel
        simp
        rw[quoti, quotj]
        rw [max_eq_left ?_]
        sorry
      sorry
    · use j - k
      constructor
      · sorry
      · simp
        have:  i - k = i - j + (j - k):= by sorry
        rw[←this]
        sorry
