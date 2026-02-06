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
-- A simple definitional alias, which we use multiple times.
def IsPartitionOfCard (a : Finset (Set α)) (k : ℕ) := IsPartition (SetLike.coe a) ∧ #a = k

end Finset

section Icc
/- A couple of Icc lemmas that we use countless times. -/

lemma Icc_bds {a b : ℕ} (t : Icc a b) : a ≤ t ∧ t ≤ b := mem_Icc.mp t.prop

lemma Icc_LB {a b : ℕ} (t : Icc a b) : a ≤ t := (Icc_bds t).1

lemma Icc_UB {a b : ℕ} (t : Icc a b) : t ≤ b := (Icc_bds t).2

lemma Icc_diff_bounds {N : ℕ} {i j : Icc 1 N} (hij : i > j) : (i : ℕ) - j ∈ Icc 1 N := by
  simp
  constructor
  · exact Nat.le_sub_of_add_le' hij
  · linarith [Icc_UB i]

def Icc_sub {N : ℕ} {s t : Icc 1 N} (hst : t < s) : Icc 1 N := ⟨(s : ℕ) - t, Icc_diff_bounds hst⟩

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

def edge_diff {N : ℕ} {G : SimpleGraph (Icc 1 N)} (x : G.edgeSet) : Icc 1 N := by
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
  let tel : (TopEdgeLabelling (Icc 1 N) (Fin c)) := fun x ↦ Ctoc (index (edge_diff x))
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

  have elim_to_c {i j} (hi : i ∈ p) (hj : j ∈ p) (hij : j < i) :
    index (Icc_sub hij) = Ctoc.symm c1 := by
    have : tel ⟨s(i, j), (Ne.symm (_root_.ne_of_lt hij))⟩ = c1 := elm hi hj (_root_.ne_of_gt hij)
    suffices Ctoc (index (Icc_sub hij)) = c1 by
      rw [← this]
      calc
        index (Icc_sub hij) = id (index (Icc_sub hij)) := by rfl
        _ = (Ctoc.symm ∘ Ctoc) (index (Icc_sub hij)) := by
          exact congrFun (id (Eq.symm CtocCtocsymmid)) (index (Icc_sub hij))
    rw [← this]
    simp [tel, Icc_sub, edge_diff]
    congr <;> symm
    · exact max_eq_left_of_lt hij
    · exact min_eq_right_of_lt hij

  have ijc := elim_to_c hi hj hij
  have jkc := elim_to_c hj hk hjk
  have ikc := elim_to_c hi hk hik

  have sub_bounds {i j : Icc 1 N} (hij : j < i) : 1 ≤ (i : ℕ) - j ∧ i - j ≤ N := by
    have := Icc_diff_bounds hij
    simp at ⊢ this
    assumption

  refine ⟨index (Icc_sub hij), by apply coe_mem, ?_⟩
  refine ⟨(i - j), sub_bounds hij, by apply indexself, ?_⟩
  refine ⟨(j - k), sub_bounds hjk, by rw [ijc, ← jkc]; apply indexself, ?_⟩
  have : (i : ℕ) - j + (j - k) = i - k := by
    refine Nat.sub_add_sub_cancel ?_ ?_ <;> apply le_of_succ_le <;> assumption
  rw [this]
  exact ⟨sub_bounds hik, by rw [ijc, ← ikc]; apply indexself⟩

def nonempty_subset_sums {k N : ℕ} (a : Fin k → (Icc 1 N)) : Set ℕ :=
  (fun (s : Set (Fin k)) => ∑ k ∈ s, a k) '' { s | s.Nonempty }


lemma nonempty_subset_sums_mono {k l N : ℕ} (emb_k_l : Fin k ↪ Fin l)
  (a : Fin k → (Icc 1 N)) (a' : Fin l → (Icc 1 N)) (h_compat : a = a' ∘ emb_k_l) :
  nonempty_subset_sums a ⊆ nonempty_subset_sums a' := by
  intro sum hsum
  rw [h_compat] at hsum
  simp [nonempty_subset_sums] at hsum ⊢
  obtain ⟨I, hI⟩ := hsum
  use emb_k_l '' I
  simp
  exact hI

lemma nonempty_subset_sums_mono' {k l N : ℕ} (hkl : k ≤ l) (a : Fin l → (Icc 1 N)) :
  nonempty_subset_sums (fun (i : Fin k) => a (i.castLE hkl)) ⊆ nonempty_subset_sums a := by
  let emb_k_l := Fin.castLEEmb hkl
  apply nonempty_subset_sums_mono emb_k_l
  exact List.ofFn_inj.mp rfl

def coe_to_nat {N : ℕ} (a : Set (Icc 1 N)) : Set ℕ :=
  (fun (k : Icc 1 N) => k) '' a

-- Alternative formulation of `schur` using `a : Fin 2 → Icc 1 S` instead of `x` and `y`, which
-- corresponds more to the following formalization of the generalization.
theorem schur' (c : ℕ) :
  ∃ S : ℕ, ∀ (C : Finset (Set (Icc 1 S))), C.IsPartitionOfCard c
  → ∃ C₀ ∈ C, ∃ a : Fin 2 → Icc 1 S, nonempty_subset_sums a ⊆ coe_to_nat C₀ := by
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
    | 0 | 1 => contradiction

theorem generalized_schur (c k : ℕ) :
  ∃ S : ℕ, ∀ (C : Finset (Set (Icc 1 S))), C.IsPartitionOfCard c
  → ∃ C₀ ∈ C, ∃ a : Fin k → Icc 1 S, nonempty_subset_sums a ⊆ coe_to_nat C₀ := by
  match h : k with
  | 0 | 1 => -- reduce to schur'
    obtain ⟨S, hS⟩ := schur' c
    use S
    intro C hC
    obtain ⟨C₀, C₀_in_C, ⟨a, ha⟩⟩ := hS C hC
    refine ⟨C₀, C₀_in_C, ?_⟩
    use (fun i => a (i.castLE (by linarith)))
    intro sum hsum
    apply ha
    apply nonempty_subset_sums_mono' (by linarith) a
    subst h
    exact hsum
  | 2 =>
    exact schur' c
  | n' + 1 =>
    sorry

def nonempty_subset_sums' {N : ℕ} (A : Finset (Icc 1 N)) : Set ℕ :=
  (fun (s : Finset (Icc 1 N)) => ∑ k ∈ s, k) '' { s | s ⊆ A ∧ s.Nonempty }

lemma nonempty_subset_sums_def_eq {N : ℕ} (A : Finset (Icc 1 N)) :
  nonempty_subset_sums' A = nonempty_subset_sums (fun i : Fin #A => (A.equivFin.symm i).val) := by
  let to_index {A' : Finset (Icc 1 N)} (hA' : A' ⊆ A) (a : Icc 1 N) (ha : a ∈ A') : Fin #A :=
    (A.equivFin ⟨a, hA' ha⟩)
  let to_element (i : Fin #A) : Icc 1 N := (A.equivFin.symm i).val
  ext sum
  simp [nonempty_subset_sums, nonempty_subset_sums']
  constructor <;> intro hsum
  · obtain ⟨summands, ⟨summands_subset_A, summands_Nonempty⟩, hsummands⟩ := hsum
    let to_index₀ := to_index summands_subset_A
    let I := (fun (a : summands) => to_index₀ a.val a.prop) '' Set.univ (α := summands)
    use I
    constructor
    · -- I is nonempty
      rw [Set.image_nonempty, ← Set.nonempty_iff_univ_nonempty]
      exact Nonempty.to_subtype summands_Nonempty
    · -- the sums are equal
      rw [← hsummands]
      apply Finset.sum_bij' (fun i _ => (A.equivFin.symm i).val) -- i
                            (fun a ha => A.equivFin ⟨a, summands_subset_A ha⟩) -- j
      <;> try {simp; done}
      · intro s hs
        simp [I, to_index, to_index₀]
        exact hs
      · intro i hi
        simp only [Set.image_univ, Set.toFinset_range, univ_eq_attach, mem_image, mem_attach,
          true_and, I, to_index, to_index₀] at hi
        obtain ⟨s, @subst⟩ := hi
        simp
  · obtain ⟨I, I_Nonempty, hI⟩ := hsum
    let A' := (to_element '' I).toFinset
    use A'
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [A']
    · intro a ha
      simp at ha
      obtain ⟨i, hi, @subst⟩ := ha
      simp [to_element]
    · exact I_Nonempty
    · simp [to_element]
      exact hI

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
    rw [nonempty_subset_sums_def_eq A']
    suffices ∃ emb : Fin #A' ↪ Fin (k ^ 3), (fun i ↦ ↑(A'.equivFin.symm i)) = a ∘ emb by
      obtain ⟨emb, hemb⟩ := this
      apply nonempty_subset_sums_mono emb
      exact hemb
    subst k
    have have_preimages (s : Fin #A') : ↑(A'.equivFin.symm s) ∈ A := by
      apply hA'
      simp
    simp [A] at have_preimages
    let emb_fn : Fin #A' → Fin (#A' ^ 3) := by
      intro s
      exact Fin.find (a · = (A'.equivFin.symm s)) (have_preimages s)
    have emb_compat : (fun i ↦ ↑(A'.equivFin.symm i)) = a ∘ emb_fn := by
      ext i
      simp [emb_fn]
      rw [Fin.find_spec (have_preimages i)]
    let emb : Fin #A' ↪ Fin (#A' ^ 3) := {
      toFun := emb_fn
      inj' := by
        apply Function.Injective.of_comp (f := a)
        rw [← emb_compat]
        simp [Function.Injective]
    }
    use emb
    exact emb_compat
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
    let multiple_fn : Icc 1 k → Icc 1 S := by
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
    let multiple : Icc 1 k ↪ Icc 1 S := {
      toFun := multiple_fn
      inj' i j h := by
        simp [multiple_fn] at h
        obtain h|h := h
        · assumption
        · linarith [Icc_LB s]
    }
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
