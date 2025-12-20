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
  obtain ⟨i, hi⟩ := index
  let tel : (TopEdgeLabelling (Fin N) (Fin c)) :=
    fun x ↦ i (max (x.1.out.fst - x.1.out.snd) (x.1.out.snd - x.1.out.fst))
    --TODO: maybe we can find an appropriate norm function
  specialize ramval tel
  obtain ⟨p, c1, elm, hp⟩ := ramval
  use p.toSet
  constructor
  · sorry
  · have : #p ≥ 3 := by gcongr
    have : ∃ x ∈ p, ∃ y ∈ p, ∃ z ∈ p, x ≠ y ∧ y ≠ z ∧ x ≠ z := by sorry
    obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz⟩ := this
    use x --TODO: use a better structure than combining constructors
    constructor
    · exact hx
    · use y
      constructor
      · exact hy
      · have: z = x + y := by
         simp at elm
         have elmxy : EdgeLabelling.get tel x y hxy = c1 := by specialize elm hx hy hxy; exact elm
         have elmyz : EdgeLabelling.get tel y z hyz = c1 := by specialize elm hy hz hyz; exact elm
         have elmxz : EdgeLabelling.get tel x z hxz = c1 := by specialize elm hx hz hxz; exact elm
         simp[tel] at elmxy elmyz elmxz
         sorry
        exact Set.mem_of_eq_of_mem (id (Eq.symm this)) hz
