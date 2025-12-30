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
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Fin.Basic

-- TODO : check which imports are necessary

open Finset Setoid Nat SimpleGraph

variable {α : Type*}

theorem schur (c : ℕ) (hc : c > 0) :
  ∃ S, ∀ (C : Finset (Set (Fin S))),
  (IsPartition C.toSet ∧ #C = c) → ∃ a ∈ C, ∃ x ∈ a, ∃ y ∈ a, ∃ z ∈ a, x + y = z := by
  let n : (Fin c → ℕ) := fun _ ↦ 3
  let N := ramseyNumber n
  use N
  simp
  intro C PartC CardC
  let q : (Fin N) → (Set (Fin N)) → Prop := fun x ↦ fun y ↦ x ∈ y
  have dec (x : Fin N) : DecidablePred (q x) := by
    have (y : Set (Fin N)): Fintype y := by exact Fintype.ofFinite ↑y
    have : q = fun x y ↦ x ∈ y.toFinset := by
      ext x y
      exact Iff.symm Set.mem_toFinset
    rw [this]
    infer_instance
  let index : (Fin N → C) := by
    intro x
    let f : Set (Fin N) := by apply Finset.choose (q x) C (PartC.2 x)
    let prop : q x f := by apply Finset.choose_property
    use f
    exact choose_mem (q x) C (PartC.2 x)

  have indexself: ∀ (x : Fin N), q x (index x) := by
    intro x
    simp [index]
    apply Finset.choose_property

  have Ctoc : C ≃ Fin c := by exact equivFinOfCardEq CardC
  have CtocCtocsymmid : Ctoc.symm ∘ Ctoc = id := by
    exact Equiv.symm_comp_self Ctoc
  let tel : (TopEdgeLabelling (Fin N) (Fin c)) := fun x ↦ Ctoc (index (x.1.sup - x.1.inf))
  have ramval : ∀ D : TopEdgeLabelling (Fin N) (Fin c), ∃ (p : Finset (Fin N)) (color : _),
    D.MonochromaticOf p color ∧ n color ≤ p.card := by apply ramseyNumber_spec_fin n
  specialize ramval tel
  obtain ⟨p, c1, elm, hp⟩ := ramval
  have Cardp: #p ≥ 3 := by gcongr
  have : ∃ i ∈ p, ∃ j ∈ p, ∃ k ∈ p, i > j ∧ j > k ∧ i > k := by
      sorry
  obtain ⟨i, hi, j, hj, k, hk, hij, hjk, hik⟩ := this
  use index (i - j)

-- TODO: do it in a shorter way
-- start
  have elmij : tel ⟨s(i, j), (Ne.symm (Fin.ne_of_lt hij))⟩ = c1 := by
    specialize elm hi hj (Ne.symm (Fin.ne_of_lt hij)); exact elm
  have elmjk : tel ⟨s(j, k), (Ne.symm (Fin.ne_of_lt hjk))⟩ = c1 := by
    specialize elm hj hk (Ne.symm (Fin.ne_of_lt hjk)); exact elm
  have elmik : tel ⟨s(i, k), (Ne.symm (Fin.ne_of_lt hik))⟩ = c1 := by
    specialize elm hi hk (Ne.symm (Fin.ne_of_lt hik)); exact elm
  have ijc1: Ctoc (index (i - j)) = c1 := by
    rw[←elmij]
    unfold tel
    simp
    rw [max_eq_left ?_, min_eq_right ?_]
    gcongr
    gcongr
  have jkc1: Ctoc (index (j - k)) = c1 := by
    rw[←elmjk]
    unfold tel
    simp
    rw [max_eq_left ?_, min_eq_right ?_]
    gcongr
    gcongr
  have ikc1: Ctoc (index (i - k)) = c1 := by
    rw[←elmik]
    unfold tel
    simp
    rw [max_eq_left ?_, min_eq_right ?_]
    gcongr
    gcongr
  have ijc: (index (i - j)) = Ctoc.symm c1 := by
    rw[← ijc1]
    calc
      index (i - j) = id (index (i - j)) := by rfl
      _ = (Ctoc.symm ∘ Ctoc) (index (i - j)) := by
        exact congrFun (id (Eq.symm CtocCtocsymmid)) (index (i - j))
  have jkc: (index (j - k)) = Ctoc.symm c1 := by
    rw[← jkc1]
    calc
      index (j - k) = id (index (j - k)) := by rfl
      _ = (Ctoc.symm ∘ Ctoc) (index (j - k)) := by
        exact congrFun (id (Eq.symm CtocCtocsymmid)) (index (j - k))
  have ikc: (index (i - k)) = Ctoc.symm c1 := by
    rw[← ikc1]
    calc
      index (i - k) = id (index (i - k)) := by rfl
      _ = (Ctoc.symm ∘ Ctoc) (index (i-k)) := by
        exact congrFun (id (Eq.symm CtocCtocsymmid)) (index (i - k))
-- end

  constructor
  · exact coe_mem (index (i - j))
  · use i - j
    constructor
    · exact indexself (i - j)
    · use j - k
      constructor
      · suffices (index (i - j)).val = (index (j - k)).val by
          rw [this]
          exact indexself (j - k)
        rw [ijc, jkc]
      · have : NeZero N := by refine NeZero.of_pos (Fin.pos i)
        have : i - j + (j - k) = i - k := by
          rw [Fin.sub_eq_add_neg i j, (Fin.instAddRightCancelSemigroup N).toAddSemigroup.add_assoc,
          Fin.sub_eq_add_neg j k,←(Fin.instAddRightCancelSemigroup N).toAddSemigroup.add_assoc (-j),
          neg_add_cancel j, Fin.zero_add (-k), ← Fin.sub_eq_add_neg i k]
        rw [this]
        suffices (index (i - j)).val = (index (i - k)).val by
          rw [this]
          exact indexself (i - k)
        rw [ijc, ikc]
