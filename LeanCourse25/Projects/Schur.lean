import LeanCourse25.Projects.Prereq.Ramsey
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset Nat Setoid SimpleGraph

section Decidability

variable {α : Type*} [Finite α] [DecidableEq α]

noncomputable instance (a : α) : DecidablePred (fun (y : Set α) => a ∈ y) := by
  have (y : Set α): Fintype y := by exact Fintype.ofFinite ↑y
  have : (a ∈ ·) = (a ∈ Set.toFinset ·) := by
    ext y
    exact Iff.symm Set.mem_toFinset
  rw [this]
  infer_instance

end Decidability

namespace Finset

variable {α : Type*}

@[reducible]
def IsPartitionOfCard (a : Finset (Set α)) (k : ℕ) := IsPartition (SetLike.coe a) ∧ #a = k

end Finset

section Icc

lemma Icc_bds {a b : ℕ} (t : Icc a b) : a ≤ t ∧ t ≤ b := mem_Icc.mp t.prop

lemma Icc_LB {a b : ℕ} (t : Icc a b) : a ≤ t := (Icc_bds t).1

lemma Icc_UB {a b : ℕ} (t : Icc a b) : t ≤ b := (Icc_bds t).2

lemma icc_diff_bounds {N : ℕ} {i j : Icc 1 N} (hij : i > j) : (i : ℕ) - j ∈ Icc 1 N := by
  simp
  constructor
  · exact Nat.le_sub_of_add_le' hij
  · linarith [Icc_UB i]

end Icc

section Sym2

lemma sym2_of_icc_diff_le {N : ℕ} (a : Sym2 (Icc 1 N)) : (a.sup : ℕ) - (a.inf : ℕ) ≤ N := by
  refine sub_le_of_le_add ?_
  linarith [Icc_LB a.inf, Icc_UB a.sup]

variable {α : Type*} [LinearOrder α]

lemma sym2_mk_inf_sup (a : Sym2 α) : a = s(a.inf, a.sup) := by
  induction a with
  | _ x y => simp [le_total]

lemma sym2_sup_mem (a : Sym2 α) : a.sup ∈ a := by
  rw [sym2_mk_inf_sup a]
  simp
  right
  exact Sym2.inf_le_sup a

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
`\{1, ..., S\}` into `c` parts, at least one of them contains integers `x`, `y` and `z` with
`x + y = z`.
-/
theorem schur (c : ℕ) :
  ∃ S, ∀ (C : Finset (Set (Icc 1 S))), C.IsPartitionOfCard c
  → ∃ a ∈ C, ∃ x ∈ a, ∃ y ∈ a, ∃ z ∈ a, (x : ℕ) + ↑y = ↑z := by
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
      refine List.sortedGT_iff_strictAnti_get.mp ?_
      apply Finset.sortedGT_sort
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

def nonempty_subset_sums {k N : ℕ} (a : Fin k → (Icc 1 N)) : Set ℕ :=
  (fun (s : Set (Fin k)) => ∑ k ∈ s, a k) '' { s | s.Nonempty }

def coe_to_nat {N : ℕ} (a : Set (Icc 1 N)) : Set ℕ :=
  (fun (k : Icc 1 N) => k) '' a

theorem generalized_schur (c k : ℕ) :
  ∃ S : ℕ, ∀ (C : Finset (Set (Icc 1 S))), C.IsPartitionOfCard c
  → ∃ C₀ ∈ C, ∃ a : Fin k → Icc 1 S, nonempty_subset_sums a ⊆ coe_to_nat C₀ := by
  match k with
  | 0 =>
    use 1
    intro C hC
    obtain ⟨C_is_partition, _⟩ := hC
    obtain ⟨s, ⟨hs, _⟩, _⟩ := C_is_partition.2 ⟨1, by simp⟩
    refine ⟨s, hs, ?_⟩
    use fun (s : Fin 0) => ⟨1, by simp⟩
    simp [nonempty_subset_sums, coe_to_nat]
    apply Set.subset_empty_iff.mp
    intro s hs
    simp at hs
    obtain ⟨i, _⟩ := hs
    apply i.elim0
  | 1 =>
    use 1
    intro C hC
    obtain ⟨C_is_partition, _⟩ := hC
    obtain ⟨s, ⟨hs, h_1_in_s⟩, _⟩ := C_is_partition.2 ⟨1, by simp⟩
    refine ⟨s, hs, ?_⟩
    use fun (_: Fin 1) => ⟨1, by simp⟩
    unfold nonempty_subset_sums coe_to_nat
    intro d hd
    simp
    obtain ⟨D, hD, hdD⟩ := hd
    have : D = Set.univ := Subsingleton.eq_univ_of_nonempty hD
    subst D
    simp at hdD
    subst d
    simp
    assumption
  | 2 =>
    obtain ⟨S, hSchur⟩ := schur c
    use S
    intro C hC
    specialize hSchur C hC
    obtain ⟨C₀, hC₀, h⟩ := hSchur
    refine ⟨C₀, hC₀, ?_⟩
    obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ := h
    let a (i : Fin 2) : Icc 1 S := match i with
    | 0 => x
    | 1 => y
    use a
    intro sum hsum
    simp [nonempty_subset_sums] at hsum
    obtain ⟨s, hs_nonempty, hs⟩ := hsum
    subst sum

    rw [← Fintype.sum_ite_mem s.toFinset, Fin.sum_univ_two]
    simp [a]
    suffices ∃ d ∈ C₀, ((if 0 ∈ s then (x : ℕ) else 0) + if 1 ∈ s then ↑y else 0) = ↑d by
      obtain ⟨d, hd, d_equality⟩ := this
      rw [d_equality]
      simp [coe_to_nat]
      exact hd
    by_cases h₀ : 0 ∈ s <;> by_cases h₁ : 1 ∈ s
    · refine ⟨z, hz, ?_⟩
      simp [h₀, h₁]
      exact hxyz
    · refine ⟨x, hx, ?_⟩
      simp [h₀, h₁]
    · refine ⟨y, hy, ?_⟩
      simp [h₀, h₁]
    · obtain ⟨i, hi⟩ := hs_nonempty
      match i with
      | 0 => contradiction
      | 1 => contradiction
  | succ n' =>
    have := generalized_schur c n'
    sorry

def nonempty_subset_sums' {N : ℕ} (A : Finset (Icc 1 N)) : Set ℕ :=
  (fun (s : Finset (Icc 1 N)) => ∑ k ∈ s, k) '' { s | s ⊆ A ∧ s.Nonempty }

-- This is a corollary from the generalized version of Schur's theorem, stating that the chosen
-- elements `a i` can be assumed to be distinict.
theorem generalized_schur' (c k : ℕ) :
  ∃ S : ℕ, ∀ (C : Finset (Set (Icc 1 S))), C.IsPartitionOfCard c
  → ∃ C₀ ∈ C, ∃ A : Finset (Icc 1 S), #A = k ∧ nonempty_subset_sums' A ⊆ coe_to_nat C₀ := by
  have reduction := generalized_schur c (k ^ 3)
  obtain ⟨S, hS⟩ := reduction
  use S
  intro C hC
  specialize hS C hC
  obtain ⟨C₀, hC₀, a, ha⟩ := hS
  refine ⟨C₀, hC₀, ?_⟩
  let A := image a Finset.univ
  by_cases h : k ≤ #A
  · -- case 1: there are already at least k different a i, so we just use them
    obtain ⟨A', hA', card_of_A'⟩ := Finset.exists_subset_card_eq h
    refine ⟨A', card_of_A', ?_⟩
    suffices nonempty_subset_sums' A' ⊆ nonempty_subset_sums a by
      intro x hx
      exact ha (this hx)
    intro sum hsum
    simp [nonempty_subset_sums]
    obtain ⟨summands, ⟨summands_subset_A', summands_nonempty⟩, hsummands⟩ := hsum
    have ⟨default_summand, hdefault_summand⟩ := summands_nonempty

    have summands_have_preimage {s : Icc 1 S} (hs : s ∈ summands) : ∃ i, a i = s := by
      suffices s ∈ image a univ by
        simp at this
        exact this
      apply hA'
      apply summands_subset_A'
      exact hs

    let indices : Icc 1 S → Fin (k ^ 3) := by
      intro s
      let s' := if s ∈ summands then s else default_summand
      have : s' ∈ summands := by
        by_cases h : s ∈ summands
        · simp [s', h]
        · simp [s', h]
          exact hdefault_summand
      exact Fin.find (a · = s') (summands_have_preimage this)
    have indices_prop : ∀ s ∈ summands, a (indices s) = s := by
      intro s hs
      simp [indices, hs]
      exact Fin.find_spec (summands_have_preimage hs)
    use (indices '' summands)
    constructor <;> simp
    · exact summands_nonempty
    · calc ∑ k ∈ image indices summands, (a k : ℕ)
        _ = ∑ s ∈ summands, ↑s := ?_
        _ = sum := by simp_rw [hsummands]
      apply Finset.sum_bij (fun i _ => a i)
      · -- well-definedness: a (indices (summands)) ⊆ summands
        intro i hi
        rw [mem_image] at hi
        obtain ⟨a', ha', index_of_a'⟩ := hi
        subst i
        rw [indices_prop a' ha']
        exact ha'
      · -- injectivity
        intro i₁ hi₁ i₂ hi₂ hi₁i₂
        rw [mem_image] at hi₁ hi₂
        obtain ⟨a₁, ha₁, @subst⟩ := hi₁
        obtain ⟨a₂, ha₂, @subst⟩ := hi₂
        rw [indices_prop a₁ ha₁, indices_prop a₂ ha₂] at hi₁i₂
        rw [hi₁i₂]
      · -- surjectivity
        intro s hs
        refine ⟨indices s, mem_image_of_mem indices hs, ?_⟩
        exact indices_prop s hs
      · -- trivial equality of summands
        exact fun _ _ => rfl
  · -- case 2: too many a i are the same element s, we can use i*s for i ∈ Icc 1 k
    simp at h
    have k_pos : 0 < k := zero_lt_of_lt h
    have : ∃ s ∈ A, k ^ 2 < ↑{ i ∈ univ (α := Fin (k ^ 3)) | a i = s}.card := by
      apply exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (M := ℕ)
      · simp [A]
      · simp
        calc #A * k ^ 2
          _ < k * k ^ 2 := by gcongr
          _ = k ^ 3 := by ring
    obtain ⟨s, _, s_has_many_preimages⟩ := this
    let multiple : Icc 1 k → Icc 1 S := by
      intro i
      refine ⟨i * s, ?_⟩
      simp
      constructor
      · exact Right.one_le_mul (Icc_LB i) (Icc_LB s)
      · -- we use i * s = ∑ j ∈ Icc 1 i, s ∈ C₀
        suffices (i : ℕ) * (s : ℕ) ∈ coe_to_nat C₀ by
          simp only [coe_to_nat, Set.mem_image] at this
          obtain ⟨k, ⟨_, hk⟩⟩ := this
          rw [← hk]
          exact Icc_UB k
        apply ha
        simp [nonempty_subset_sums]
        have : i ≤ #{i | a i = s} := by nlinarith [Icc_UB i]
        obtain ⟨I, hI, card_of_I⟩ := Finset.exists_subset_card_eq this
        use I
        constructor
        · apply one_le_card.mp
          rw [card_of_I]
          exact Icc_LB i
        · simp
          suffices ∀ i ∈ I, (a i : ℕ) = s by
            rw [sum_const_nat this, card_of_I]
          intro i hi
          specialize hI hi
          simp at hI
          norm_cast
    let multiple : Icc 1 k ↪ Icc 1 S := by
      refine ⟨multiple, ?_⟩
      intro i i'
      simp [multiple]
      intro h
      obtain h|h := h
      · assumption
      · linarith [Icc_LB s]
    let A : Finset (Icc 1 S) := { multiple i | i : Icc 1 k }
    use A
    constructor
    · -- A has cardinality k
      simp [A]
      rw [Finset.card_image_of_injective]
      · simp
      · exact Function.Embedding.injective multiple
    · intro sum hsum
      apply ha
      simp [nonempty_subset_sums'] at hsum
      obtain ⟨B, ⟨B_subset_A, B_nonempty⟩, hB⟩ := hsum
      -- determine the total multiple of s in the sum
      have : ∃ i ∈ Icc 1 (k ^ 2), (i : ℕ) * s = ∑ k ∈ B, (k : ℕ) := by
        let I := multiple ⁻¹' B
        let i := ∑ j ∈ I, (j : ℕ)
        have multiple_inv {b : Icc 1 S} (hb : b ∈ B) : ∃ i, multiple i = b := by
          have b_mem_A := B_subset_A hb
          simp only [univ_eq_attach, mem_filter, mem_attach, true_and, A] at b_mem_A
          assumption
        have : i ∈ Icc 1 (k ^ 2) := by
          simp
          constructor <;> simp [i]
          · rw [Nat.one_le_iff_ne_zero, ← zero_lt_iff]
            apply Finset.sum_pos_iff.mpr
            obtain ⟨b, hb⟩ := B_nonempty
            obtain ⟨i, hi⟩ := multiple_inv hb
            use i
            refine ⟨?_, by linarith [Icc_bds i]⟩
            simp [I]
            rw [hi]
            exact hb
          · calc ∑ j ∈ I.toFinset, ↑j
              _ ≤ ∑ j ∈ I.toFinset, k := by apply Finset.sum_le_sum; intro i hi; exact Icc_UB i
              _ = I.ncard * k := by rw [Set.ncard_eq_toFinset_card', sum_const, smul_eq_mul]
              _ ≤ #(Icc 1 k) * k := by gcongr; rw [← card_eq_finsetCard]; apply Set.ncard_le_card
              _ = k * k := by congr; rw [Nat.card_Icc, Nat.add_one_sub_one]
              _ = k ^ 2 := by ring
        refine ⟨i, this, ?_⟩
        unfold i
        have multiple_spec (j : Icc 1 k) : (j : ℕ) * s = multiple j := by norm_cast
        rw [sum_mul, sum_congr rfl (fun j _ => multiple_spec j)]
        have B_eq_image_of_multiple : B = Finset.map multiple I.toFinset := by
          ext b
          constructor <;> intro hb
          · obtain ⟨i, hi⟩ := multiple_inv hb
            simp only [mem_map, Set.mem_toFinset]
            have i_mem_I : i ∈ I := by simp [I, hi, hb]
            exact ⟨i, i_mem_I, hi⟩
          · simp only [mem_map, Set.mem_toFinset] at hb
            obtain ⟨i, i_mem_I, @subst⟩ := hb
            exact mem_def.mpr i_mem_I
        rw [B_eq_image_of_multiple]
        exact Eq.symm (sum_map I.toFinset multiple Subtype.val)
      obtain ⟨i, i_mem_Icc, hi⟩ := this
      -- get i different indices j, such that a j = s
      have : i ≤ #{j | a j = s} := by linarith [Icc_UB ⟨i, i_mem_Icc⟩]
      obtain ⟨J, hJ, card_of_J⟩ := Finset.exists_subset_card_eq this
      simp [nonempty_subset_sums]
      use J
      constructor
      · simp
        apply Finset.one_le_card.mp
        linarith [Icc_LB ⟨i, i_mem_Icc⟩]
      · simp
        rw [Finset.sum_const_nat (m := (s : ℕ)), card_of_J, hi, hB]
        intro j hj
        specialize hJ hj
        simp at hJ
        norm_cast
