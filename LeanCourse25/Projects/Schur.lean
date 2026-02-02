import LeanCourse25.Projects.Prereq.Ramsey
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset Nat Setoid SimpleGraph

section Finiteness

variable {α : Type*} [Finite α] [DecidableEq α]

noncomputable instance (a : α) : DecidablePred (fun (y : Set α) => a ∈ y) := by
  have (y : Set α): Fintype y := by exact Fintype.ofFinite ↑y
  have : (a ∈ ·) = (a ∈ Set.toFinset ·) := by
    ext y
    exact Iff.symm Set.mem_toFinset
  rw [this]
  infer_instance

end Finiteness

section Sym2

lemma icc_diff_bounds {N : ℕ} {i j : Icc 1 N} (hij : i > j) : (i : ℕ) - j ∈ Icc 1 N := by
  simp
  constructor
  · exact Nat.le_sub_of_add_le' hij
  · have : i ≤ N := (mem_Icc.mp i.prop).2
    linarith

lemma sym2_of_icc_diff_le {N : ℕ} (a : Sym2 (Icc 1 N)) : (a.sup : ℕ) - (a.inf : ℕ) ≤ N := by
  have : a.sup ≤ N := (mem_Icc.mp a.sup.prop).2
  have : a.inf ≥ (1 : ℕ) := (mem_Icc.mp a.inf.prop).1
  refine sub_le_of_le_add ?_
  linarith

variable {α : Type*} [LinearOrder α]

lemma sym2_mk_inf_sup (a : Sym2 α) : a = s(a.inf, a.sup) := by
  induction a with
  | _ x y => simp [le_total]

lemma sym2_sup_mem (a : Sym2 α) : a.sup ∈ a := by
  rw [sym2_mk_inf_sup a]
  simp
  right
  apply Sym2.inf_le_sup

lemma sym2_other_of_inf (a : Sym2 α) : Sym2.Mem.other' (sym2_sup_mem a) = a.inf := by
  have := Sym2.other_spec' (sym2_sup_mem a)
  nth_rewrite 5 [sym2_mk_inf_sup a] at this
  rw [Sym2.eq_iff] at this
  obtain h|h := this
  · rw [← h.1]
    exact h.2
  · exact h.2

end Sym2

/-- Given an integer `c`, there exists an integer `S`, such that for all partitions of
`\{0, ..., S - 1\}` into `c` parts, at least one of them contains integers `x`, `y` and `z` with
`x + y = z`.
-/
theorem schur (c : ℕ) :
  ∃ S, ∀ (C : Finset (Set (Icc 1 S))),
  (IsPartition C.toSet ∧ #C = c) → ∃ a ∈ C, ∃ x ∈ a, ∃ y ∈ a, ∃ z ∈ a, (x : ℕ) + ↑y = ↑z := by
  let n : (Fin c → ℕ) := fun _ ↦ 3
  let N := ramseyNumber n
  use N
  simp
  intro C PartC CardC
  let mem_prop : (Icc 1 N) → (Set (Icc 1 N)) → Prop := fun x ↦ fun y ↦ x ∈ y
  let index : (Icc 1 N → C) := by
    intro x
    use (Finset.choose (mem_prop x) C (PartC.2 x))
    exact choose_mem (mem_prop x) C (PartC.2 x)

  have indexself: ∀ (x : Icc 1 N), mem_prop x (index x) := by
    intro x
    simp [index]
    apply Finset.choose_property

  have Ctoc : C ≃ Fin c := by exact equivFinOfCardEq CardC
  have CtocCtocsymmid : Ctoc.symm ∘ Ctoc = id := by
    exact Equiv.symm_comp_self Ctoc
  let edge_to_label {G : SimpleGraph (Icc 1 N)} (x : G.edgeSet) : Icc 1 N := by
    let diff := (x.1.sup : ℕ) - x.1.inf
    refine ⟨diff, ?_⟩
    refine mem_Icc.mpr ?_
    constructor
    · have : x.1.inf < x.1.sup := by
        refine lt_of_le_of_ne x.1.inf_le_sup ?_
        have : ¬x.1.IsDiag := by
          apply SimpleGraph.not_isDiag_of_mem_edgeSet G
          exact Subtype.coe_prop x
        have := x.1.other_ne this (sym2_sup_mem x.1)
        rw [Sym2.other_eq_other'] at this
        rw [sym2_other_of_inf] at this
        assumption
      apply Nat.le_sub_of_add_le' this
    · apply sym2_of_icc_diff_le
  let tel : (TopEdgeLabelling (Icc 1 N) (Fin c)) := fun x ↦ Ctoc (index (edge_to_label x))
  have ramsey_spec : ∀ D : TopEdgeLabelling (Icc 1 N) (Fin c), ∃ (p : Finset (Icc 1 N)) (color : _),
    D.MonochromaticOf p color ∧ n color ≤ p.card := by
    apply ramseyNumber_spec
    simp [N]
  specialize ramsey_spec tel
  obtain ⟨p, c1, elm, hp⟩ := ramsey_spec
  have Cardp: #p ≥ 3 := by gcongr
  have : ∃ i ∈ p, ∃ j ∈ p, ∃ k ∈ p, j < i ∧ k < j ∧ k < i := by
    let sorted_elems := (p.sort (· ≥ ·))
    have : sorted_elems.length ≥ 3 := by
      rw [Finset.length_sort]
      exact Cardp
    have : NeZero sorted_elems.length := by exact NeZero.of_gt this
    let get_sorted (index : ℕ) : Icc 1 N := sorted_elems.get (Fin.ofNat sorted_elems.length index)
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

  let icc_sub {i j : Icc 1 N} (hij : j < i) : Icc 1 N := ⟨i - j, icc_diff_bounds hij⟩
  have elim_to_c {i j} (hi : i ∈ p) (hj : j ∈ p) (hij : j < i) :
    index (icc_sub hij) = Ctoc.symm c1 := by
    have : tel ⟨s(i, j), (Ne.symm (_root_.ne_of_lt hij))⟩ = c1 := elm hi hj (_root_.ne_of_gt hij)
    suffices Ctoc (index (icc_sub hij)) = c1 by
      rw [← this]
      calc
        index (icc_sub hij) = id (index (icc_sub hij)) := by rfl
        _ = (Ctoc.symm ∘ Ctoc) (index (icc_sub hij)) := by
          exact congrFun (id (Eq.symm CtocCtocsymmid)) (index (icc_sub hij))
    rw [← this]
    simp [tel, icc_sub, edge_to_label]
    congr <;> symm
    · exact max_eq_left_of_lt hij
    · exact min_eq_right_of_lt hij

  have ijc := elim_to_c hi hj hij
  have jkc := elim_to_c hj hk hjk
  have ikc := elim_to_c hi hk hik

  have sub_bounds {i j : Icc 1 N} (hij : j < i) : 1 ≤ (i : ℕ) - j ∧ i - j ≤ N := by
    have := icc_diff_bounds hij
    simp at ⊢ this
    assumption

  refine ⟨index (icc_sub hij), by apply coe_mem, ?_⟩
  refine ⟨(i - j), sub_bounds hij, by apply indexself, ?_⟩
  refine ⟨(j - k), sub_bounds hjk, by rw [ijc, ← jkc]; apply indexself, ?_⟩
  have : (i : ℕ) - j + (j - k) = i - k := by
    refine Nat.sub_add_sub_cancel ?_ ?_ <;> apply le_of_succ_le <;> assumption
  rw [this]
  refine ⟨sub_bounds hik, ?_⟩
  rw [ijc, ← ikc]
  apply indexself
