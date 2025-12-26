import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Dist
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

lemma nat_dist_le_max (n m : ℕ) : n.dist m ≤ max n m := by sorry

#check Finset.univ (α := Fin 3)


namespace IsPartition

variable [Fintype α] [DecidableEq α] {C: Finset (Set α)}

-- TODO: rename
lemma set_univ_map_eq :
  Fintype.finsetOrderIsoSet.symm (Set.univ (α := α)) = univ (α := α)
  := by simp only [Set.le_eq_subset, le_eq_subset, Fintype.coe_finsetOrderIsoSet_symm,
    Fintype.finsetEquivSet_symm_apply, Set.toFinset_univ]

-- TODO: cleanup reqs?
lemma finpartition_parts_cast_heq {a b : α} [Lattice α] [OrderBot α] (p : Finpartition a) (h : a = b) :
  (Equiv.cast (congrArg Finpartition h) p).parts = p.parts := by
  congr
  · exact h.symm
  · simp

noncomputable def finite_partition_of_finite_to_finpartition
  (P : IsPartition C.toSet)
  : Finpartition (Finset.univ (α := α)) :=
  Equiv.cast (congrArg Finpartition set_univ_map_eq) (P.finpartition.map (Fintype.finsetOrderIsoSet (α := α)).symm)

lemma parts_of_above_are_correct (P : IsPartition C.toSet) :
  (finite_partition_of_finite_to_finpartition P).parts = C.map Fintype.finsetEquivSet.symm.toEmbedding := by
  unfold finite_partition_of_finite_to_finpartition
  rw [finpartition_parts_cast_heq _ set_univ_map_eq]
  simp
  norm_cast

end IsPartition

open IsPartition

variable {S : ℕ} {C : Finset (Set (Fin S))}

theorem schur (c : ℕ) (hc : c > 0) :
  ∃ S, ∀ (C : Finset (Set (Fin S))),
  (IsPartition C.toSet ∧ #C = c) → ∃ a ∈ C, ∃ x ∈ a, ∃ y ∈ a, ∃ z ∈ a, x + y = z := by
  let n : (Fin c → ℕ) := fun _ ↦ 3
  let N := ramseyNumber n
  -- have ramval : (∃ N, ∀ D : TopEdgeLabelling (Fin N) (Fin c), ∃ (p : Finset (Fin N)) (color : _),
  --  D.MonochromaticOf p color ∧ n color ≤ p.card) := by apply ramsey_fin_exists n
  -- obtain ⟨N, ramval⟩ := ramval
  have N_pos : NeZero N := by
    apply NeZero.of_pos
    apply ramseyNumber_pos.mpr
    simp
  use N
  simp
  intro C PartC CardC

  let FinpartC : Finpartition (Finset.univ (α := Fin N)):=
    finite_partition_of_finite_to_finpartition PartC
  #check FinpartC.part (Fin.ofNat N 0)
  have enumeration : C ≃ Fin c := Finset.equivFinOfCardEq CardC
  let something2 : Fin N → Fin c := by
    intro n
    have part := (FinpartC.part n).toSet
    have part_in_C : part.fintypeSubset ∈ FinpartC.parts := by
      apply FinpartC.part_mem.mpr
    apply something.1
    sorry
    -- obtain ⟨n_color, n_color_appropriate⟩ := PartC.2 n
    -- apply Cardinal.outMkEquiv
  -- have index: ∃ (ι : (C → Fin c)), ι.Bijective := sorry
      -- by rw[← CardC]; apply finset_set_fin_nat_partition_has_index N C; apply PartC
  let tel : (TopEdgeLabelling (Fin N) (Fin c)) := by
    intro x
    refine something2 (Fin.mk (Nat.dist (x.1.out.fst : ℕ) (x.1.out.snd : ℕ)) ?_)
    grw [nat_dist_le_max]
    sorry
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
