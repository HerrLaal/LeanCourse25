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
  let q : (Fin N) → (Set (Fin N)) → Prop := fun x ↦ fun y ↦ x ∈ y
  let index : (Fin N → C) := by
    intro x
    have dec : DecidablePred (q x) := by exact Classical.decPred (q x)
    let f : Set (Fin N) := by apply Finset.choose (q x) C (PartC.2 x)
    let prop : q x f := by apply Finset.choose_property
    use f
    exact choose_mem (q x) C (PartC.2 x)

  have indexself: ∀ (x : Fin N), q x (index x) := by
    intro x
    unfold index
    simp
    have dec : DecidablePred (q x) := by exact Classical.decPred (q x)
    --apply Finset.choose_property
    have prop : q x (Finset.choose (q x) C (PartC.2 x)) := by apply Finset.choose_property
    unfold q at prop
    --exact prop
    sorry
    --apply choose_property q C (PartC.2 x)

  have Ctoc : C ≃ Fin c := by exact equivFinOfCardEq CardC
  have CtocCtocsymmid : Ctoc.symm ∘ Ctoc = id := by
    exact Equiv.symm_comp_self Ctoc
  let tel : (TopEdgeLabelling (Fin N) (Fin c)) :=
    fun x ↦ Ctoc (index (max x.1.out.fst x.1.out.snd - min x.1.out.fst x.1.out.snd))
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
-- TODO: do it in a shorter way
-- start
  have elmij : tel ⟨s(i, j), (Ne.symm (Fin.ne_of_lt hij))⟩ = c1 := by
    specialize elm hi hj (Ne.symm (Fin.ne_of_lt hij)); exact elm
  have elmjk : tel ⟨s(j, k), (Ne.symm (Fin.ne_of_lt hjk))⟩ = c1 := by
    specialize elm hj hk (Ne.symm (Fin.ne_of_lt hjk)); exact elm
  have elmik : tel ⟨s(i, k), (Ne.symm (Fin.ne_of_lt hik))⟩ = c1 := by
    specialize elm hi hk (Ne.symm (Fin.ne_of_lt hik)); exact elm
  have quotiji: (Quot.out s(i, j)).1 = i := by sorry
  have quotijj: (Quot.out s(i, j)).2 = j := by sorry
  have quotjkj: (Quot.out s(j, k)).1 = j := by sorry
  have quotjkk: (Quot.out s(j, k)).2 = k := by sorry
  have quotiki: (Quot.out s(i, k)).1 = i := by sorry
  have quotikk: (Quot.out s(i, k)).2 = k := by sorry
  have ijc1: Ctoc (index (i - j)) = c1 := by
    rw[←elmij]
    unfold tel
    rw[quotiji, quotijj, max_eq_left ?_, min_eq_right ?_]
    gcongr
    gcongr
  have jkc1: Ctoc (index (j - k)) = c1 := by
    rw[←elmjk]
    unfold tel
    rw[quotjkj, quotjkk, max_eq_left ?_, min_eq_right ?_]
    gcongr
    gcongr
  have ikc1: Ctoc (index (i - k)) = c1 := by
    rw[←elmik]
    unfold tel
    rw[quotiki, quotikk, max_eq_left ?_, min_eq_right ?_]
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
      · have : i - j + (j - k) = i - k := by
          refine Eq.symm (Fin.ext ?_)
          sorry
        rw [this]
        suffices (index (i - j)).val = (index (i - k)).val by
          rw [this]
          exact indexself (i - k)
        rw [ijc, ikc]
