import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.List.Sort
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

theorem schur (c : ℕ) :
  ∃ S, ∀ (C : Finset (Set (Fin S))),
  (IsPartition C.toSet ∧ #C = c) → ∃ a ∈ C, ∃ x ∈ a, ∃ y ∈ a, ∃ z ∈ a, (x : ℕ) + ↑y = ↑z := by
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
  have : ∃ i ∈ p, ∃ j ∈ p, ∃ k ∈ p, j < i ∧ k < j ∧ k < i := by
    let sorted_elems := (p.sort (· ≥ ·))
    have : sorted_elems.length ≥ 3 := by
      rw [Finset.length_sort]
      exact Cardp
    have : NeZero sorted_elems.length := by exact NeZero.of_gt this
    let get_sorted (index : ℕ) : Fin N := sorted_elems.get (Fin.ofNat sorted_elems.length index)
    let i := get_sorted 0
    let j := get_sorted 1
    let k := get_sorted 2
    have mem_p (n : ℕ) : get_sorted n ∈ p := by
      apply (mem_sort (· ≥ ·)).mp
      apply List.get_mem
    refine ⟨i, mem_p 0, ?_⟩
    refine ⟨j, mem_p 1, ?_⟩
    refine ⟨k, mem_p 2, ?_⟩
    have order (i j : ℕ) (hij : i < j) (indices_in_bounds : j < sorted_elems.length) :
      get_sorted i > get_sorted j := by
      suffices StrictAnti sorted_elems.get by
        apply this
        apply Fin.lt_def.mpr
        simp
        rw [mod_eq_of_lt (by linarith), mod_eq_of_lt indices_in_bounds]
        exact hij
      refine List.sorted_gt_ofFn_iff.mp ?_
      simp
      apply Finset.sort_sorted_gt
    refine ⟨?_, ?_, ?_⟩ <;> apply order <;> linarith
  obtain ⟨i, hi, j, hj, k, hk, hij, hjk, hik⟩ := this

  have elim_to_c {i j} (hi : i ∈ p) (hj : j ∈ p) (hij : j < i) :
    index (i - j) = Ctoc.symm c1 := by
    have : tel ⟨s(i, j), (Ne.symm (Fin.ne_of_lt hij))⟩ = c1 := elm hi hj (Fin.ne_of_lt hij).symm
    suffices Ctoc (index (i - j)) = c1 by
      rw[← this]
      calc
        index (i - j) = id (index (i - j)) := by rfl
        _ = (Ctoc.symm ∘ Ctoc) (index (i - j)) := by
          exact congrFun (id (Eq.symm CtocCtocsymmid)) (index (i - j))
    rw [← this]
    simp [tel]
    rw [max_eq_left ?_, min_eq_right ?_]
    · gcongr
    · gcongr

  have ijc := elim_to_c hi hj hij
  have jkc := elim_to_c hj hk hjk
  have ikc := elim_to_c hi hk hik

  refine ⟨index (i - j), by apply coe_mem, ?_⟩
  refine ⟨(i - j), by apply indexself, ?_⟩
  refine ⟨(j - k), by rw [ijc, ← jkc]; apply indexself, ?_⟩
  refine ⟨(i - k), by rw [ijc, ← ikc]; apply indexself, ?_⟩
  repeat rw [Fin.sub_val_of_le (by gcongr)]
  refine Nat.sub_add_sub_cancel ?_ ?_ <;> apply le_of_succ_le <;> assumption
