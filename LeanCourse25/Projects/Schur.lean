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

/-lemma finset_set_fin_nat_partition_has_index (S : ℕ) (C : Finset (Set (Fin S))) :
  IsPartition C.toSet → ∃ (ι : (C → Fin #C)), ι.Bijective := sorry-/

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
  /-have index: ∃ (ι : (C → Fin #C)), ι.Bijective :=
      by apply finset_set_fin_nat_partition_has_index (ramseyNumber n) C; apply PartC
  obtain ⟨i, hi⟩ := index -/
  let tel : (TopEdgeLabelling (Fin N) (Fin c)) := fun x ↦ sorry
  specialize ramval tel
  obtain ⟨p, c1, elm, hp2⟩ := ramval
  have: #p ≥ 3 := by (have: n c1 ≥ 3 := by gcongr); gcongr
  use p.toSet
  constructor
  · sorry
  · sorry
