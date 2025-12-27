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
  let N:= ramseyNumber n
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
  have ramval : ∀ D : TopEdgeLabelling (Fin N) (Fin c), ∃ (p : Finset (Fin N)) (color : _),
    D.MonochromaticOf p color ∧ n color ≤ p.card := by apply ramseyNumber_spec_fin n
  specialize ramval tel
  obtain ⟨p, c1, elm, hp⟩ := ramval
  have Cardp: #p ≥ 3 := by gcongr
  have : ∃ i ∈ p, ∃ j ∈ p, ∃ k ∈ p, i > j ∧ j > k ∧ i > k := by
      sorry
  obtain ⟨i, hi, j, hj, k, hk, hij, hjk, hik⟩ := this
  use index (i - j)
  constructor
  · exact coe_mem (index (i - j))
  · use i - j
    constructor
    · sorry
    · use j - k
      constructor
      · sorry
      · sorry
