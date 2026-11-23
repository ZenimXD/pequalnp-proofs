import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_651_step

/-!
# World 1 and Petersen-minus-vertex-0 (`p0Fun`) lower-bound results

This file applies the read-2 monotone formula lower bound (`read2_or_tree_bound`) and wire-budget
machinery from `L_meta_651_step` to:
1. Petersen minus vertex 0 (`p0Fun` on `Fin 9`, matching `L_meta_651_world1.p0Fun`):
   - `p0_read2_leaves_ge_17`: every read-2 monotone formula computing `p0Fun` has ≥ 17 leaves.
   - `p0_size15_three_read_once`: every minimal circuit of ≤ 15 gates computing `p0Fun` reads at
     least **three** distinct inputs exactly once (upgrading `p0_size15_two_read_once` from ≥ 2).
2. World 1 (`petersenFun` with `wireFanOut 10 C 0 = 1`):
   - `world1_and_partner_is_gate`: if `x 0` is read once by an `AND` gate `x 0 ∧ h`, then `h` must
     evaluate to `true` on `singleInput 1`, `singleInput 4`, `singleInput 5`, so `h` cannot be an
     input wire (`10 ≤ h`, i.e., `h` is a gate wire).
   - `world1_or_partner_false_on_nbrs`: if `x 0` is read once by an `OR` gate `x 0 ∨ h`, then `h`
     must evaluate to `false` on `singleInput 1`, `singleInput 4`, `singleInput 5`.
-/

namespace PEqualNP.Outside.L_meta_651_p0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_651_step

/-! ### 1. Petersen minus vertex 0 (`p0Fun`) and its read-2 leaf bound -/

/-- Edge function of Petersen minus vertex 0 (vertices 1..9 renamed 0..8), matching
`L_meta_651_world1.p0Fun`. -/
def p0Fun (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 5) || (x 1 && x 6) ||
  (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 6) || (x 6 && x 8) || (x 8 && x 5) ||
  (x 5 && x 7) || (x 7 && x 4)

def p0Fun10 (x : Fin 10 → Bool) : Bool :=
  petersenFun (Function.update x 0 false)

lemma p0Fun_eq_p0Fun10 (x : Fin 10 → Bool) :
    p0Fun (fun i : Fin 9 => x i.succ) = p0Fun10 x := by
  have h : ∀ a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
      ((a1 && a2) || (a2 && a3) || (a3 && a4) || (a1 && a6) || (a2 && a7) ||
       (a3 && a8) || (a4 && a9) || (a5 && a7) || (a7 && a9) || (a9 && a6) ||
       (a6 && a8) || (a8 && a5)) =
      ((false && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && false) ||
       (false && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a4 && a9) ||
       (a5 && a7) || (a7 && a9) || (a9 && a6) || (a6 && a8) || (a8 && a5)) := by
    decide
  have h1 := h (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
  simpa [p0Fun, p0Fun10, petersenFun, Function.update] using h1

lemma p0Fun10_le_petersenFun (x : Fin 10 → Bool) (h : p0Fun10 x = true) :
    petersenFun x = true := by
  have hm : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
      ((false && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && false) ||
       (false && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a4 && a9) ||
       (a5 && a7) || (a7 && a9) || (a9 && a6) || (a6 && a8) || (a8 && a5)) = true →
      ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
       (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a4 && a9) ||
       (a5 && a7) || (a7 && a9) || (a9 && a6) || (a6 && a8) || (a8 && a5)) = true := by
    decide
  apply hm (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
  simpa [p0Fun10, petersenFun, Function.update] using h

def p0Edges : Finset (Fin 10 × Fin 10) :=
  petersenEdges.filter fun e => e.1 ≠ 0 ∧ e.2 ≠ 0

lemma p0Edges_card : p0Edges.card = 12 := by
  decide

lemma p0_tau_ge_5 (T : Finset (Fin 10))
    (hcov : ∀ e ∈ p0Edges, e.1 ∈ T ∨ e.2 ∈ T) :
    5 ≤ T.card := by
  let I := (Finset.univ.erase (0 : Fin 10)) \ T
  have hind : ∀ e ∈ p0Edges, ¬ (e.1 ∈ I ∧ e.2 ∈ I) := by
    intro e he ⟨h1, h2⟩
    simp only [I, Finset.mem_sdiff] at h1 h2
    rcases hcov e he with h | h
    · exact h1.2 h
    · exact h2.2 h
  have hI_le4 : I.card ≤ 4 := by
    -- Partition {1..9} into 4 edges + 1 vertex? Even better: C5 {5,7,9,6,8} (indep ≤ 2) + P4 {1,2,3,4} (indep ≤ 2)!
    let inner : Finset (Fin 10) := {5, 7, 9, 6, 8}
    let outer : Finset (Fin 10) := {1, 2, 3, 4}
    have hpair : ∀ a b : Fin 10, (a, b) ∈ p0Edges → (I ∩ {a, b}).card ≤ 1 := by
      intro a b hab
      by_cases ha : a ∈ I <;> by_cases hb : b ∈ I
      · exact absurd ⟨ha, hb⟩ (hind (a, b) hab)
      · have hs : I ∩ {a, b} ⊆ {a} := by
          intro u hu; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu.2 with rfl | rfl; exact rfl; exact absurd hu.1 hb
        exact le_trans (Finset.card_le_card hs) (by simp)
      · have hs : I ∩ {a, b} ⊆ {b} := by
          intro u hu; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu.2 with rfl | rfl; exact absurd hu.1 ha; exact rfl
        exact le_trans (Finset.card_le_card hs) (by simp)
      · have hs : I ∩ {a, b} = ∅ := by
          ext u; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨hu, rfl | rfl⟩; exact ha hu; exact hb hu
        rw [hs]; simp
    have hinner : (I ∩ inner).card ≤ 2 := by
      have h57 := hpair 5 7 (by decide)
      have h79 := hpair 7 9 (by decide)
      have h69 := hpair 6 9 (by decide)
      have h68 := hpair 6 8 (by decide)
      have h58 := hpair 5 8 (by decide)
      have hsub1 : I ∩ inner ⊆ (I ∩ {5, 7}) ∪ (I ∩ {6, 9}) ∪ (I ∩ {8}) := by
        intro u hu; simp only [inner, Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu.2 with rfl | rfl | rfl | rfl | rfl <;> tauto
      by_cases h8 : (8 : Fin 10) ∈ I
      · have h5not : (5 : Fin 10) ∉ I := fun h5 => hind (5, 8) (by decide) ⟨h5, h8⟩
        have h6not : (6 : Fin 10) ∉ I := fun h6 => hind (6, 8) (by decide) ⟨h6, h8⟩
        have hsub2 : I ∩ inner ⊆ (I ∩ {7, 9}) ∪ {8} := by
          intro u hu; simp only [inner, Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu.2 with rfl | rfl | rfl | rfl | rfl
          · exact absurd hu.1 h5not
          · exact Or.inl ⟨hu.1, Or.inl rfl⟩
          · exact Or.inl ⟨hu.1, Or.inr rfl⟩
          · exact absurd hu.1 h6not
          · exact Or.inr rfl
        have := le_trans (Finset.card_le_card hsub2) (Finset.card_union_le _ _)
        simp at this; omega
      · have h80 : I ∩ {8} = ∅ := by ext u; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]; rintro ⟨hu, rfl⟩; exact h8 hu
        rw [h80, Finset.union_empty] at hsub1
        have := le_trans (Finset.card_le_card hsub1) (Finset.card_union_le _ _)
        omega
    have houter : (I ∩ outer).card ≤ 2 := by
      have h12 := hpair 1 2 (by decide)
      have h34 := hpair 3 4 (by decide)
      have hsub1 : I ∩ outer ⊆ (I ∩ {1, 2}) ∪ (I ∩ {3, 4}) := by
        intro u hu; simp only [outer, Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu.2 with rfl | rfl | rfl | rfl <;> tauto
      have := le_trans (Finset.card_le_card hsub1) (Finset.card_union_le _ _)
      omega
    have hsub : I ⊆ (I ∩ inner) ∪ (I ∩ outer) := by
      intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hu).1).1
      have h9 : u ∈ inner ∪ outer := by revert hu0; generalize u = v; revert v; decide
      rcases Finset.mem_union.mp h9 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, h⟩)
    exact le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) (by omega))
  have hsub9 : Finset.univ.erase (0 : Fin 10) ⊆ I ∪ T := by
    intro u hu
    by_cases h : u ∈ T
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, h⟩)
  have h9 : 9 ≤ I.card + T.card := by
    have hc := Finset.card_le_card hsub9
    have hu := Finset.card_union_le I T
    have he : (Finset.univ.erase (0 : Fin 10)).card = 9 := by decide
    omega
  omega

/-- Every read-2 monotone formula computing Petersen minus vertex 0 has at least 17 leaves. -/
theorem p0_read2_leaves_ge_17 (F : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, F.varCount v ≤ 2)
    (hev : ∀ x : Fin 10 → Bool, F.eval x = p0Fun10 x) :
    17 ≤ F.leaves := by
  obtain ⟨T, E, hE, hcovT, hbd⟩ := read2_or_tree_bound F hr2
    (fun x hx => p0Fun10_le_petersenFun x (by rw [← hev x, hx]))
  have hsub : p0Edges ⊆ E := by
    intro e he
    simp only [p0Edges, Finset.mem_filter] at he
    apply hE e he.1
    rw [hev]
    have hupd : Function.update (pairInput e.1 e.2) 0 false = pairInput e.1 e.2 := by
      funext i
      by_cases hi : i = 0
      · subst hi; simp [Function.update, pairInput, Ne.symm he.2.1, Ne.symm he.2.2]
      · simp [Function.update, hi]
    unfold p0Fun10
    rw [hupd, petersenFun_pair_iff]
    exact petersenEdges_adj e he.1
  have hE12 : 12 ≤ E.card := by rw [← p0Edges_card]; exact Finset.card_le_card hsub
  have hT5 : 5 ≤ T.card := p0_tau_ge_5 T (fun e he => hcovT e (hsub he))
  omega

/-! ### 2. General telescoping for `wireToFormula` and lifting 9-input circuits to 10 inputs -/

lemma wireToFormula_leaves_general (C : Circuit)
    (hout_ge : 10 ≤ C.output) (hout_lt : C.output < 10 + C.size)
    (hout0 : wireFanOut 10 C C.output = 0)
    (hgate1 : ∀ j : Fin C.size, 10 + j.val ≠ C.output → wireFanOut 10 C (10 + j.val) = 1)
    (hstruct : ∀ j : Fin C.size,
      (C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C.gates[j.val].inputs = [a, b] ∧ a < 10 + j.val ∧ b < 10 + j.val) :
    (wireToFormula C C.output).leaves = ∑ i : Fin 10, wireFanOut 10 C i.val := by
  let L : ℕ → ℕ := fun w => (wireToFormula C w).leaves
  have hL_in : ∀ i : Fin 10, L i.val = 1 := by
    intro i; dsimp [L]; rw [wireToFormula]; simp [i.isLt, MonoFormula.leaves]
  have hL_gate : ∀ j : Fin C.size,
      L (10 + j.val) = ∑ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w := by
    intro j
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hstruct j
    have hL_eq : L (10 + j.val) = L a + L b := by
      dsimp [L]; rw [wireToFormula]
      have hnot10 : ¬ (10 + j.val < 10) := by omega
      have hsub : 10 + j.val - 10 = j.val := by omega
      have hj' : 10 + j.val - 10 < C.gates.length := by rw [hsub]; exact j.isLt
      simp only [hnot10, ↓reduceDIte, hj']
      have hgin : (C.gates[10 + j.val - 10]'hj').inputs = [a, b] := by
        have hidx : C.gates[10 + j.val - 10]'hj' = C.gates[j.val] := by congr 1
        rw [hidx]; exact hin
      have hgop : (C.gates[10 + j.val - 10]'hj').op = GateOp.and ∨
          (C.gates[10 + j.val - 10]'hj').op = GateOp.or := by
        have hidx : C.gates[10 + j.val - 10]'hj' = C.gates[j.val] := by congr 1
        rw [hidx]; exact hop
      rw [hgin]; simp only [ha, hb, ↓reduceDIte]
      rcases hgop with h | h <;> rw [h] <;> simp [MonoFormula.leaves]
    rw [hL_eq]
    have ha_lt : a < 10 + C.size := by omega
    have hb_lt : b < 10 + C.size := by omega
    have hsum_pair : ∀ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w =
        (if w = a then L a else 0) + (if w = b then L b else 0) := by
      intro w _; rw [hin]
      by_cases hwa : w = a <;> by_cases hwb : w = b
      · subst hwa; subst hwb; simp [ha, List.count_cons, Nat.two_mul]
      · subst hwa; have hba : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [ha, hwb, hba, List.count_cons]
      · subst hwb; have hab : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        simp [hb, hwa, hab, List.count_cons]
      · have hab : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        have hba : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [hwa, hwb, hab, hba, List.count_cons]
    rw [Finset.sum_congr rfl hsum_pair, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp [Finset.mem_range, ha_lt, hb_lt]
  have hsum_L : ∑ j : Fin C.size, L (10 + j.val) =
      ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
    calc ∑ j : Fin C.size, L (10 + j.val)
        = ∑ j : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_congr rfl fun j _ => hL_gate j
      _ = ∑ w ∈ Finset.range (10 + C.size), ∑ j : Fin C.size,
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_comm
      _ = ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
          apply Finset.sum_congr rfl; intro w _; unfold wireFanOut; rw [Finset.sum_mul]
  rw [Finset.sum_range_add,
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C x * L x),
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C (10 + x) * L (10 + x))] at hsum_L
  have hin_sum : (∑ i : Fin 10, wireFanOut 10 C i.val * L i.val) = ∑ i : Fin 10, wireFanOut 10 C i.val := by
    apply Finset.sum_congr rfl; intro i _; rw [hL_in i, mul_one]
  let j0 : Fin C.size := ⟨C.output - 10, by omega⟩
  have hj0_eq : 10 + j0.val = C.output := by dsimp [j0]; omega
  have hgate_sum : (∑ j : Fin C.size, wireFanOut 10 C (10 + j.val) * L (10 + j.val)) + L C.output =
      ∑ j : Fin C.size, L (10 + j.val) := by
    rw [← hj0_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0),
      ← Finset.add_sum_erase _ (fun j : Fin C.size => L (10 + j.val)) (Finset.mem_univ j0)]
    rw [hj0_eq, hout0, zero_mul, zero_add]
    have heq : ∑ j ∈ Finset.univ.erase j0, wireFanOut 10 C (10 + j.val) * L (10 + j.val) =
        ∑ j ∈ Finset.univ.erase j0, L (10 + j.val) := by
      apply Finset.sum_congr rfl; intro j hj
      have hne : 10 + j.val ≠ C.output := by
        intro h; exact (Finset.mem_erase.mp hj).1 (Fin.ext (by dsimp [j0]; omega))
      rw [hgate1 j hne, one_mul]
    rw [heq]; omega
  rw [hin_sum] at hsum_L
  change L C.output = ∑ i : Fin 10, wireFanOut 10 C i.val
  omega

lemma wireToFormula_varCount_general (C : Circuit)
    (hout_ge : 10 ≤ C.output) (hout_lt : C.output < 10 + C.size)
    (hout0 : wireFanOut 10 C C.output = 0)
    (hgate1 : ∀ j : Fin C.size, 10 + j.val ≠ C.output → wireFanOut 10 C (10 + j.val) = 1)
    (hstruct : ∀ j : Fin C.size,
      (C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C.gates[j.val].inputs = [a, b] ∧ a < 10 + j.val ∧ b < 10 + j.val)
    (v : Fin 10) :
    (wireToFormula C C.output).varCount v = wireFanOut 10 C v.val := by
  let L : ℕ → ℕ := fun w => (wireToFormula C w).varCount v
  have hL_in : ∀ i : Fin 10, L i.val = if i = v then 1 else 0 := by
    intro i; dsimp [L]; rw [wireToFormula]; simp [i.isLt, MonoFormula.varCount]
  have hL_gate : ∀ j : Fin C.size,
      L (10 + j.val) = ∑ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w := by
    intro j
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hstruct j
    have hL_eq : L (10 + j.val) = L a + L b := by
      dsimp [L]; rw [wireToFormula]
      have hnot10 : ¬ (10 + j.val < 10) := by omega
      have hsub : 10 + j.val - 10 = j.val := by omega
      have hj' : 10 + j.val - 10 < C.gates.length := by rw [hsub]; exact j.isLt
      simp only [hnot10, ↓reduceDIte, hj']
      have hgin : (C.gates[10 + j.val - 10]'hj').inputs = [a, b] := by
        have hidx : C.gates[10 + j.val - 10]'hj' = C.gates[j.val] := by congr 1
        rw [hidx]; exact hin
      have hgop : (C.gates[10 + j.val - 10]'hj').op = GateOp.and ∨
          (C.gates[10 + j.val - 10]'hj').op = GateOp.or := by
        have hidx : C.gates[10 + j.val - 10]'hj' = C.gates[j.val] := by congr 1
        rw [hidx]; exact hop
      rw [hgin]; simp only [ha, hb, ↓reduceDIte]
      rcases hgop with h | h <;> rw [h] <;> simp [MonoFormula.varCount]
    rw [hL_eq]
    have ha_lt : a < 10 + C.size := by omega
    have hb_lt : b < 10 + C.size := by omega
    have hsum_pair : ∀ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w =
        (if w = a then L a else 0) + (if w = b then L b else 0) := by
      intro w _; rw [hin]
      by_cases hwa : w = a <;> by_cases hwb : w = b
      · subst hwa; subst hwb; simp [ha, List.count_cons, Nat.two_mul]
      · subst hwa; have hba : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [ha, hwb, hba, List.count_cons]
      · subst hwb; have hab : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        simp [hb, hwa, hab, List.count_cons]
      · have hab : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        have hba : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [hwa, hwb, hab, hba, List.count_cons]
    rw [Finset.sum_congr rfl hsum_pair, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp [Finset.mem_range, ha_lt, hb_lt]
  have hsum_L : ∑ j : Fin C.size, L (10 + j.val) =
      ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
    calc ∑ j : Fin C.size, L (10 + j.val)
        = ∑ j : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_congr rfl fun j _ => hL_gate j
      _ = ∑ w ∈ Finset.range (10 + C.size), ∑ j : Fin C.size,
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_comm
      _ = ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
          apply Finset.sum_congr rfl; intro w _; unfold wireFanOut; rw [Finset.sum_mul]
  rw [Finset.sum_range_add,
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C x * L x),
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C (10 + x) * L (10 + x))] at hsum_L
  have hin_sum : (∑ i : Fin 10, wireFanOut 10 C i.val * L i.val) = wireFanOut 10 C v.val := by
    have hite : ∀ i : Fin 10, wireFanOut 10 C i.val * L i.val = if i = v then wireFanOut 10 C v.val else 0 := by
      intro i; rw [hL_in i]; split_ifs with h
      · subst h; simp
      · simp
    simp_rw [hite]; simp
  let j0 : Fin C.size := ⟨C.output - 10, by omega⟩
  have hj0_eq : 10 + j0.val = C.output := by dsimp [j0]; omega
  have hgate_sum : (∑ j : Fin C.size, wireFanOut 10 C (10 + j.val) * L (10 + j.val)) + L C.output =
      ∑ j : Fin C.size, L (10 + j.val) := by
    rw [← hj0_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0),
      ← Finset.add_sum_erase _ (fun j : Fin C.size => L (10 + j.val)) (Finset.mem_univ j0)]
    rw [hj0_eq, hout0, zero_mul, zero_add]
    have heq : ∑ j ∈ Finset.univ.erase j0, wireFanOut 10 C (10 + j.val) * L (10 + j.val) =
        ∑ j ∈ Finset.univ.erase j0, L (10 + j.val) := by
      apply Finset.sum_congr rfl; intro j hj
      have hne : 10 + j.val ≠ C.output := by
        intro h; exact (Finset.mem_erase.mp hj).1 (Fin.ext (by dsimp [j0]; omega))
      rw [hgate1 j hne, one_mul]
    rw [heq]; omega
  rw [hin_sum] at hsum_L
  change L C.output = wireFanOut 10 C v.val
  omega

/-- Lift a 9-input circuit to a 10-input circuit by shifting all wire indices by `+1` (so input 0
is unused and input `i : Fin 9` becomes input `i.succ : Fin 10`). -/
def lift9To10 (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (· + 1)⟩, C.output + 1⟩

lemma lift9To10_size (C : Circuit) : (lift9To10 C).size = C.size := by
  simp [lift9To10, Circuit.size]

lemma foldl_lift9To10 (gs : List Gate) (b0 : Bool) (acc : List Bool) :
    (gs.map fun g => (⟨g.op, g.inputs.map (· + 1)⟩ : Gate)).foldl stepWires (b0 :: acc) =
      b0 :: gs.foldl stepWires acc := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hstep : stepWires (b0 :: acc) ⟨g.op, g.inputs.map (· + 1)⟩ = b0 :: stepWires acc g := by
      unfold stepWires
      simp only [List.cons_append, List.map_map]
      congr 3
    rw [hstep, ih]

lemma lift9To10_eval (C : Circuit) (x : Fin 10 → Bool) :
    (lift9To10 C).eval (List.ofFn x) = C.eval (List.ofFn fun i : Fin 9 => x i.succ) := by
  have hof : List.ofFn x = x 0 :: List.ofFn (fun i : Fin 9 => x i.succ) := List.ofFn_succ
  simp only [Circuit.eval, wires_eq_foldl, lift9To10]
  rw [hof, foldl_lift9To10]
  rfl

lemma lift9To10_wireFanOut_zero (C : Circuit) : wireFanOut 10 (lift9To10 C) 0 = 0 := by
  unfold wireFanOut
  apply Finset.sum_eq_zero; intro j _
  split_ifs
  · simp only [lift9To10, List.getElem_map]
    apply List.count_eq_zero.mpr
    simp
  · rfl

lemma lift9To10_wireFanOut_succ (C : Circuit) (w : ℕ) :
    wireFanOut 10 (lift9To10 C) (w + 1) = wireFanOut 9 C w := by
  unfold wireFanOut
  have hsz : (lift9To10 C).size = C.size := lift9To10_size C
  refine Finset.sum_bij (fun j _ => ⟨j.val, hsz ▸ j.isLt⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun j _ => ⟨⟨j.val, hsz.symm ▸ j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun j _ => ?_)
  have hiff : w + 1 < 10 + j.val ↔ w < 9 + j.val := by omega
  simp only [hiff, lift9To10, List.getElem_map]
  split_ifs
  · exact List.count_map_of_injective _ _ (fun a b h => by omega) w
  · rfl

/-! ### 3. Upgrading `p0_size15_two_read_once` to `p0_size15_three_read_once` -/

def p0Nbr (v : Fin 9) : Fin 9 :=
  match v.val with
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 0 | 6 => 1 | 7 => 2 | _ => 3

lemma p0Fun_essential (v : Fin 9) :
    ∃ x : Fin 9 → Bool, p0Fun x ≠ p0Fun (Function.update x v (!x v)) := by
  refine ⟨fun i => decide (i = p0Nbr v), ?_⟩
  fin_cases v <;> decide

lemma p0Fun_not_false : ∃ x : Fin 9 → Bool, p0Fun x ≠ false :=
  ⟨fun i => decide (i = 0 ∨ i = 1), by decide⟩

lemma p0Fun_not_proj (i : Fin 9) : ∃ x : Fin 9 → Bool, p0Fun x ≠ x i := by
  refine ⟨fun j => decide (j = i), ?_⟩
  fin_cases i <;> decide

set_option maxHeartbeats 600000 in
/-- A minimal circuit of ≤ 15 gates for `p0Fun` cannot be a tight 15-gate read-2 monotone tree. -/
lemma p0_size15_not_tight_read2 (C : Circuit)
    (hF : FanInTwo C) (hle : C.size ≤ 15)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = p0Fun x)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hmin : ∀ C' : Circuit, FanInTwo C' → (∀ x : Fin 9 → Bool, C'.eval (List.ofFn x) = p0Fun x) →
      C.size ≤ C'.size)
    (hsum16 : (∑ i : Fin 9, wireFanOut 9 C i.val) = 16)
    (hr2 : ∀ i : Fin 9, wireFanOut 9 C i.val ≤ 2) : False := by
  have hbud := wire_budget_minimal 9 p0Fun C hF hNot hev hmin p0Fun_not_false p0Fun_not_proj
  have hsz15 : C.size = 15 := by omega
  have hnot0 : notCount C = 0 := by omega
  have hno_not : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
    intro g hg hgn
    have hpos : 0 < notCount C := by
      unfold notCount
      exact List.length_pos_iff_exists_mem.mpr ⟨g, List.mem_filter.mpr ⟨hg, (isNotOp_eq_true _).mpr hgn⟩⟩
    omega
  obtain ⟨hout_ge, hout_lt⟩ := minimal_output_is_gate 9 p0Fun C hev p0Fun_not_false p0Fun_not_proj
  have hgate1 : ∀ j : Fin C.size, 9 + j.val ≠ C.output → wireFanOut 9 C (9 + j.val) = 1 := by
    intro j hne
    have hpos := minimal_no_dead_gate 9 p0Fun C hF hev hmin j hne
    have hzero : (if 9 + j.val = C.output then 0 else wireFanOut 9 C (9 + j.val) - 1) = 0 := by
      have hsum0 : (∑ k : Fin C.size, if 9 + k.val = C.output then 0 else wireFanOut 9 C (9 + k.val) - 1) = 0 := by omega
      exact Finset.sum_eq_zero_iff.mp hsum0 j (Finset.mem_univ j)
    simp only [hne, ↓reduceIte] at hzero
    omega
  -- Tighten wire_budget_raw to get fo(out) = 0 and exact 2 valid inputs per gate
  have hraw := wire_budget_raw 9 C hF hNot
  have hsum_all : (∑ i : Fin 9, wireFanOut 9 C i.val) +
      (∑ j : Fin C.size, wireFanOut 9 C (9 + j.val)) = 30 := by
    have hge14 : 14 + wireFanOut 9 C C.output ≤ ∑ j : Fin C.size, wireFanOut 9 C (9 + j.val) := by
      let j0 : Fin C.size := ⟨C.output - 9, by omega⟩
      have hj0 : 9 + j0.val = C.output := by dsimp [j0]; omega
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hj0]
      have h14 : ∑ j ∈ Finset.univ.erase j0, wireFanOut 9 C (9 + j.val) = 14 := by
        have h1 : ∀ j ∈ Finset.univ.erase j0, wireFanOut 9 C (9 + j.val) = 1 := fun j hj =>
          hgate1 j (fun h => (Finset.mem_erase.mp hj).1 (Fin.ext (by dsimp [j0]; omega)))
        rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin, hsz15]
      omega
    omega
  have hout0 : wireFanOut 9 C C.output = 0 := by
    let j0 : Fin C.size := ⟨C.output - 9, by omega⟩
    have hj0 : 9 + j0.val = C.output := by dsimp [j0]; omega
    have hge14 : ∑ j : Fin C.size, wireFanOut 9 C (9 + j.val) = 14 + wireFanOut 9 C C.output := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hj0]
      have h14 : ∑ j ∈ Finset.univ.erase j0, wireFanOut 9 C (9 + j.val) = 14 := by
        have h1 : ∀ j ∈ Finset.univ.erase j0, wireFanOut 9 C (9 + j.val) = 1 := fun j hj =>
          hgate1 j (fun h => (Finset.mem_erase.mp hj).1 (Fin.ext (by dsimp [j0]; omega)))
        rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin, hsz15]
      omega
    omega
  have hstruct9 : ∀ j : Fin C.size,
      (C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C.gates[j.val].inputs = [a, b] ∧ a < 9 + j.val ∧ b < 9 + j.val := by
    have hswap : ∑ j : Fin C.size, ∑ w ∈ Finset.range (9 + C.size),
          (if w < 9 + j.val then C.gates[j.val].inputs.count w else 0) = 30 := by
      rw [Finset.sum_comm]
      change (∑ w ∈ Finset.range (9 + C.size), wireFanOut 9 C w) = 30
      have hsplit : (∑ i : Fin 9, wireFanOut 9 C i.val) +
          (∑ j : Fin C.size, wireFanOut 9 C (9 + j.val)) =
          ∑ w ∈ Finset.range (9 + C.size), wireFanOut 9 C w := by
        rw [Finset.sum_range_add,
          Fin.sum_univ_eq_sum_range (fun x => wireFanOut 9 C x),
          Fin.sum_univ_eq_sum_range (fun x => wireFanOut 9 C (9 + x))]
      rw [← hsplit]; exact hsum_all
    have hle2 : ∀ j : Fin C.size,
        ∑ w ∈ Finset.range (9 + C.size), (if w < 9 + j.val then C.gates[j.val].inputs.count w else 0) ≤ 2 := by
      intro j
      calc ∑ w ∈ Finset.range (9 + C.size), (if w < 9 + j.val then C.gates[j.val].inputs.count w else 0)
          ≤ ∑ w ∈ Finset.range (9 + C.size), C.gates[j.val].inputs.count w :=
            Finset.sum_le_sum fun w _ => by split_ifs <;> omega
        _ ≤ C.gates[j.val].inputs.length := sum_count_range_le _ _
        _ ≤ 2 := (hF _ (List.getElem_mem j.isLt)).2
    have heq2 : ∀ j : Fin C.size,
        ∑ w ∈ Finset.range (9 + C.size), (if w < 9 + j.val then C.gates[j.val].inputs.count w else 0) = 2 := by
      intro j
      by_contra hne
      have hlt : ∑ w ∈ Finset.range (9 + C.size), (if w < 9 + j.val then C.gates[j.val].inputs.count w else 0) ≤ 1 := by
        have := hle2 j; omega
      have hsum_le : ∑ k : Fin C.size, ∑ w ∈ Finset.range (9 + C.size),
          (if w < 9 + k.val then C.gates[k.val].inputs.count w else 0) ≤ 29 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have hrest : ∑ k ∈ Finset.univ.erase j, ∑ w ∈ Finset.range (9 + C.size),
            (if w < 9 + k.val then C.gates[k.val].inputs.count w else 0) ≤ 28 := by
          calc _ ≤ ∑ _k ∈ Finset.univ.erase j, 2 := Finset.sum_le_sum fun k _ => hle2 k
            _ = 28 := by rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin, hsz15]
        omega
      omega
    intro j
    have hm := hF _ (List.getElem_mem j.isLt)
    have hop : C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or := by
      have hnn := hno_not _ (List.getElem_mem j.isLt)
      rcases hm.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hnn
    refine ⟨hop, ?_⟩
    have hj2 := heq2 j
    have hlen2 : C.gates[j.val].inputs.length = 2 := by
      have h1 : 2 ≤ C.gates[j.val].inputs.length := by
        calc 2 = ∑ w ∈ Finset.range (9 + C.size), (if w < 9 + j.val then C.gates[j.val].inputs.count w else 0) := hj2.symm
          _ ≤ ∑ w ∈ Finset.range (9 + C.size), C.gates[j.val].inputs.count w :=
              Finset.sum_le_sum fun w _ => by split_ifs <;> omega
          _ ≤ C.gates[j.val].inputs.length := sum_count_range_le _ _
      have h2 := hm.2
      omega
    rcases hl : C.gates[j.val].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [hl] at hlen2
    · simp [hl] at hlen2
    · refine ⟨a, b, rfl, ?_, ?_⟩
      · by_contra hge
        have hsum_le1 : ∑ w ∈ Finset.range (9 + C.size), (if w < 9 + j.val then ([a, b] : List ℕ).count w else 0) ≤ 1 := by
          have h1 : ∀ w ∈ Finset.range (9 + C.size),
              (if w < 9 + j.val then ([a, b] : List ℕ).count w else 0) ≤ if w = b then 1 else 0 := by
            intro w _
            by_cases hw : w < 9 + j.val
            · have hwa : w ≠ a := by omega
              have hab : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
              by_cases hwb : w = b
              · subst hwb; simp [hw, hab, List.count_cons]
              · have hbw : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
                simp [hw, hab, hbw, hwb, List.count_cons]
            · simp [hw]
          calc _ ≤ ∑ w ∈ Finset.range (9 + C.size), (if w = b then 1 else 0) := Finset.sum_le_sum h1
            _ ≤ 1 := by rw [Finset.sum_ite_eq']; split_ifs <;> omega
        rw [hl] at hj2; omega
      · by_contra hge
        have hsum_le1 : ∑ w ∈ Finset.range (9 + C.size), (if w < 9 + j.val then ([a, b] : List ℕ).count w else 0) ≤ 1 := by
          have h1 : ∀ w ∈ Finset.range (9 + C.size),
              (if w < 9 + j.val then ([a, b] : List ℕ).count w else 0) ≤ if w = a then 1 else 0 := by
            intro w _
            by_cases hw : w < 9 + j.val
            · have hwb : w ≠ b := by omega
              have hbw : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
              by_cases hwa : w = a
              · subst hwa; simp [hw, hbw, List.count_cons]
              · have hab : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
                simp [hw, hab, hbw, hwa, List.count_cons]
            · simp [hw]
          calc _ ≤ ∑ w ∈ Finset.range (9 + C.size), (if w = a then 1 else 0) := Finset.sum_le_sum h1
            _ ≤ 1 := by rw [Finset.sum_ite_eq']; split_ifs <;> omega
        rw [hl] at hj2; omega
    · simp [hl] at hlen2
  -- Lift C to a 10-input circuit and convert to a read-2 MonoFormula 10
  let C10 := lift9To10 C
  have hsz10 : C10.size = C.size := lift9To10_size C
  have hout10_ge : 10 ≤ C10.output := by dsimp [C10, lift9To10]; omega
  have hout10_lt : C10.output < 10 + C10.size := by rw [hsz10]; dsimp [C10, lift9To10]; omega
  have hout10_0 : wireFanOut 10 C10 C10.output = 0 := by
    dsimp [C10]; change wireFanOut 10 (lift9To10 C) (C.output + 1) = 0
    rw [lift9To10_wireFanOut_succ]; exact hout0
  have hgate10_1 : ∀ j : Fin C10.size, 10 + j.val ≠ C10.output → wireFanOut 10 C10 (10 + j.val) = 1 := by
    intro j hne
    have hj9 : j.val < C.size := hsz10 ▸ j.isLt
    have heq : 10 + j.val = (9 + j.val) + 1 := by omega
    rw [heq]; dsimp [C10]; rw [lift9To10_wireFanOut_succ]
    apply hgate1 ⟨j.val, hj9⟩
    intro h; apply hne; dsimp only at h; change 10 + j.val = C.output + 1; omega
  have hstruct10 : ∀ j : Fin C10.size,
      (C10.gates[j.val].op = GateOp.and ∨ C10.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C10.gates[j.val].inputs = [a, b] ∧ a < 10 + j.val ∧ b < 10 + j.val := by
    intro j
    have hj9 : j.val < C.size := hsz10 ▸ j.isLt
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hstruct9 ⟨j.val, hj9⟩
    dsimp only at hop hin ha hb
    refine ⟨?_, a + 1, b + 1, ?_, by omega, by omega⟩
    · simp only [C10, lift9To10, List.getElem_map]; exact hop
    · simp only [C10, lift9To10, List.getElem_map]; simp [hin]
  let F := wireToFormula C10 C10.output
  have hFeval : ∀ x : Fin 10 → Bool, F.eval x = p0Fun10 x := by
    intro x
    dsimp [F]
    rw [wireToFormula_eval C10 hstruct10 x C10.output hout10_lt]
    change C10.eval (List.ofFn x) = p0Fun10 x
    dsimp [C10]
    rw [lift9To10_eval, hev, p0Fun_eq_p0Fun10]
  have hFleaves : F.leaves = 16 := by
    dsimp [F]
    rw [wireToFormula_leaves_general C10 hout10_ge hout10_lt hout10_0 hgate10_1 hstruct10]
    rw [Fin.sum_univ_succ]
    dsimp [C10]
    rw [lift9To10_wireFanOut_zero, zero_add]
    have hsucc : (∑ i : Fin 9, wireFanOut 10 (lift9To10 C) (i.val + 1)) =
        ∑ i : Fin 9, wireFanOut 9 C i.val := by
      apply Finset.sum_congr rfl; intro i _
      exact lift9To10_wireFanOut_succ C i.val
    rw [hsucc, hsum16]
  have hFr2 : ∀ v : Fin 10, F.varCount v ≤ 2 := by
    intro v
    dsimp [F]
    rw [wireToFormula_varCount_general C10 hout10_ge hout10_lt hout10_0 hgate10_1 hstruct10 v]
    cases v using Fin.cases with
    | zero => dsimp [C10]; rw [lift9To10_wireFanOut_zero]; omega
    | succ i => dsimp [C10]; rw [lift9To10_wireFanOut_succ]; exact hr2 i
  have h17 := p0_read2_leaves_ge_17 F hFr2 hFeval
  omega

/-- Every minimal circuit of at most 15 gates computing `p0Fun` reads at least **three** distinct
inputs exactly once (upgrading `p0_size15_two_read_once` from ≥ 2 to ≥ 3). -/
theorem p0_size15_three_read_once (h : HasCircuitSize 9 p0Fun 15) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 15 ∧
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = p0Fun x) ∧
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ C' : Circuit, FanInTwo C' → (∀ x : Fin 9 → Bool, C'.eval (List.ofFn x) = p0Fun x) →
        C.size ≤ C'.size) ∧
      3 ≤ (Finset.univ.filter fun i : Fin 9 => wireFanOut 9 C i.val = 1).card := by
  obtain ⟨C, hF, hle, hev, hNot, hmin⟩ := minimal_circuit_exists 9 15 p0Fun h
  have hbud := wire_budget_minimal 9 p0Fun C hF hNot hev hmin p0Fun_not_false p0Fun_not_proj
  obtain ⟨hout_ge, _⟩ := minimal_output_is_gate 9 p0Fun C hev p0Fun_not_false p0Fun_not_proj
  have hpos : ∀ i : Fin 9, 1 ≤ wireFanOut 9 C i.val :=
    minimal_input_fanout_pos 9 p0Fun C hev hout_ge p0Fun_essential
  have hsum : (∑ i : Fin 9, wireFanOut 9 C i.val) ≤ 16 := by omega
  refine ⟨C, hF, hle, hev, hNot, hmin, ?_⟩
  let S1 := Finset.univ.filter fun i : Fin 9 => wireFanOut 9 C i.val = 1
  change 3 ≤ S1.card
  have hcalc : (∑ i : Fin 9, (if wireFanOut 9 C i.val = 1 then 1 else 2)) =
      S1.card + 2 * (Finset.univ.filter fun i : Fin 9 => ¬ wireFanOut 9 C i.val = 1).card := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    ring
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 9))) (fun i : Fin 9 => wireFanOut 9 C i.val = 1)
  change S1.card + (Finset.univ.filter fun i : Fin 9 => ¬ wireFanOut 9 C i.val = 1).card = (Finset.univ : Finset (Fin 9)).card at hpart
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  by_cases hsum15 : (∑ i : Fin 9, wireFanOut 9 C i.val) ≤ 15
  · have hlow : ∀ i : Fin 9, (if wireFanOut 9 C i.val = 1 then 1 else 2) ≤ wireFanOut 9 C i.val := by
      intro i; have := hpos i; split_ifs <;> omega
    have hge := le_trans (Finset.sum_le_sum fun i _ => hlow i) hsum15
    omega
  · have hsum16 : (∑ i : Fin 9, wireFanOut 9 C i.val) = 16 := by omega
    have hex3 : ∃ i0 : Fin 9, 3 ≤ wireFanOut 9 C i0.val := by
      by_contra hall
      push Not at hall
      exact p0_size15_not_tight_read2 C hF hle hev hNot hmin hsum16 (fun i => by have := hall i; omega)
    obtain ⟨i0, hi0⟩ := hex3
    have hlow : ∀ i : Fin 9,
        (if wireFanOut 9 C i.val = 1 then 1 else 2) + (if i = i0 then 1 else 0) ≤ wireFanOut 9 C i.val := by
      intro i; have := hpos i
      by_cases h1 : wireFanOut 9 C i.val = 1 <;> by_cases h2 : i = i0
      · subst h2; omega
      · simp [h1, h2]
      · subst h2; simp [h1]; omega
      · simp [h1, h2]; omega
    have hge : (∑ i : Fin 9, ((if wireFanOut 9 C i.val = 1 then 1 else 2) + (if i = i0 then 1 else 0))) ≤ 16 :=
      le_trans (Finset.sum_le_sum fun i _ => hlow i) (by omega)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hge
    simp only [Finset.mem_univ, ↓reduceIte] at hge
    omega

/-! ### 4. World 1 elimination structure at `x 0` -/

lemma wire_independent_of_zero_if_no_read (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length)
    (hag : ∀ k, k ≠ 0 → w1.getD k false = w2.getD k false)
    (hno : ∀ g ∈ gs, 0 ∉ g.inputs) :
    ∀ k, k ≠ 0 → (gs.foldl stepWires w1).getD k false = (gs.foldl stepWires w2).getD k false :=
  (foldl_unused_input gs w1 w2 0 hlen hag hno).2

/-- In any World 1 circuit computing `petersenFun` where `x 0` is read only once, by gate `j`
with `g = x 0 ∧ h` (with `h < 10 + j`, `C.output ≠ 0`), the partner wire `h` must evaluate to
`true` on `singleInput 1`, `singleInput 4`, and `singleInput 5`; hence `h` cannot be an input
wire (`10 ≤ h`). -/
theorem world1_and_partner_is_gate (C : Circuit)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x)
    (hfo0 : wireFanOut 10 C 0 = 1)
    (j : Fin C.size) (hop : C.gates[j.val].op = GateOp.and)
    (h : ℕ) (hh : h < 10 + j.val)
    (hin : C.gates[j.val].inputs = [0, h] ∨ C.gates[j.val].inputs = [h, 0]) :
    (∀ v ∈ ({1, 4, 5} : Finset (Fin 10)), (C.wires (List.ofFn (singleInput v))).getD h false = true) ∧
    10 ≤ h := by
  have hno_before : ∀ g ∈ C.gates.take j.val, 0 ∉ g.inputs := by
    intro g hg hin0
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hm_lt : m < j.val := by simp only [List.length_take] at hm; omega
    have hm_sz : m < C.size := by omega
    have hgm : (C.gates.take j.val)[m] = C.gates[m] := List.getElem_take
    rw [hgm] at hin0
    have hsub : (∑ k ∈ ({⟨m, hm_sz⟩, j} : Finset (Fin C.size)),
        (if 0 < 10 + k.val then C.gates[k.val].inputs.count 0 else 0)) ≤ wireFanOut 10 C 0 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hne : (⟨m, hm_sz⟩ : Fin C.size) ≠ j := fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega
    rw [Finset.sum_pair hne] at hsub
    have c1 : 0 < C.gates[m].inputs.count 0 := List.count_pos_iff.mpr hin0
    have c2 : 0 < C.gates[j.val].inputs.count 0 := List.count_pos_iff.mpr (by rcases hin with h' | h' <;> simp [h'])
    simp only [Nat.zero_lt_of_lt (by omega : 0 < 10 + m), Nat.zero_lt_of_lt (by omega : 0 < 10 + j.val), ↓reduceIte] at hsub
    omega
  have hno_after : ∀ g ∈ C.gates.drop (j.val + 1), 0 ∉ g.inputs := by
    intro g hg hin0
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hm_sz : j.val + 1 + m < C.size := by
      simp only [List.length_drop] at hm; exact Nat.add_lt_of_lt_sub' hm
    have hgm : (C.gates.drop (j.val + 1))[m] = C.gates[j.val + 1 + m] := List.getElem_drop
    rw [hgm] at hin0
    have hsub : (∑ k ∈ ({j, ⟨j.val + 1 + m, hm_sz⟩} : Finset (Fin C.size)),
        (if 0 < 10 + k.val then C.gates[k.val].inputs.count 0 else 0)) ≤ wireFanOut 10 C 0 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hne : j ≠ (⟨j.val + 1 + m, hm_sz⟩ : Fin C.size) := fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega
    rw [Finset.sum_pair hne] at hsub
    have c1 : 0 < C.gates[j.val].inputs.count 0 := List.count_pos_iff.mpr (by rcases hin with h' | h' <;> simp [h'])
    have c2 : 0 < C.gates[j.val + 1 + m].inputs.count 0 := List.count_pos_iff.mpr hin0
    simp only [Nat.zero_lt_of_lt (by omega : 0 < 10 + j.val), Nat.zero_lt_of_lt (by omega : 0 < 10 + (j.val + 1 + m)), ↓reduceIte] at hsub
    omega
  have htrue : ∀ v ∈ ({1, 4, 5} : Finset (Fin 10)),
      (C.wires (List.ofFn (singleInput v))).getD h false = true := by
    intro v hv
    by_contra hnot
    have hfalse : (C.wires (List.ofFn (singleInput v))).getD h false = false := by
      cases hc : (C.wires (List.ofFn (singleInput v))).getD h false
      · rfl
      · exact absurd hc hnot
    let x0 := singleInput v
    let x1 := Function.update (singleInput v) 0 true
    have hsplit : C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val + 1) := by
      have h1 := List.take_append_drop j.val C.gates
      have h2 : C.gates.drop j.val = C.gates[j.val] :: C.gates.drop (j.val + 1) := List.drop_eq_getElem_cons j.isLt
      rw [h2] at h1; exact h1.symm
    have htake_len : (C.gates.take j.val).length = j.val := List.length_take_of_le (Nat.le_of_lt j.isLt)
    set w0 := (C.gates.take j.val).foldl stepWires (List.ofFn x0)
    set w1 := (C.gates.take j.val).foldl stepWires (List.ofFn x1)
    have hw0_len : w0.length = 10 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
    have hw1_len : w1.length = 10 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
    have hag_init : ∀ k, k ≠ 0 → (List.ofFn x0).getD k false = (List.ofFn x1).getD k false := by
      intro k hk
      by_cases h10 : k < 10
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h10, ↓reduceDIte]
        have hne : (⟨k, h10⟩ : Fin 10) ≠ 0 := fun heq => hk (congrArg Fin.val heq)
        simp [x0, x1, Function.update_of_ne hne]
      · simp [List.getD_eq_getElem?_getD, h10]
    have hag_w : ∀ k, k ≠ 0 → w0.getD k false = w1.getD k false :=
      wire_independent_of_zero_if_no_read (C.gates.take j.val) _ _ (by simp) hag_init hno_before
    have hh0_val : w0.getD h false = false := by
      obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix (C.gates[j.val] :: C.gates.drop (j.val + 1)) w0
      have hfull : C.wires (List.ofFn x0) = w0 ++ suf := by
        rw [wires_eq_foldl, hsplit, List.foldl_append]; exact hsuf
      rw [hfull, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)] at hfalse
      simpa [List.getD_eq_getElem?_getD] using hfalse
    have hhne0 : h ≠ 0 := by
      intro h0; subst h0
      -- if h = 0, then inputs = [0, 0], so wireFanOut 10 C 0 ≥ 2
      have hcount : C.gates[j.val].inputs.count 0 = 2 := by rcases hin with h' | h' <;> simp [h']
      have hle : (if 0 < 10 + j.val then C.gates[j.val].inputs.count 0 else 0) ≤ wireFanOut 10 C 0 := by
        unfold wireFanOut
        exact Finset.single_le_sum (f := fun k : Fin C.size => if 0 < 10 + k.val then C.gates[k.val].inputs.count 0 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      simp only [Nat.zero_lt_of_lt (by omega : 0 < 10 + j.val), ↓reduceIte, hcount] at hle
      omega
    have hh1_val : w1.getD h false = false := by rw [← hag_w h hhne0, hh0_val]
    have hgate_eq : C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => w0.getD i false) =
        C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => w1.getD i false) := by
      rw [hop]
      rcases hin with h' | h' <;> simp only [h', List.map_cons, List.map_nil, hh0_val, hh1_val, GateOp.eval] <;>
        cases w0.getD 0 false <;> cases w1.getD 0 false <;> rfl
    have hag_step : ∀ k, k ≠ 0 → (stepWires w0 C.gates[j.val]).getD k false =
        (stepWires w1 C.gates[j.val]).getD k false := by
      intro k hk
      unfold stepWires; rw [hgate_eq]
      by_cases hlt : k < 10 + j.val
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < w0.length),
          List.getElem?_append_left (by omega : k < w1.length)]
        simpa [List.getD_eq_getElem?_getD] using hag_w k hk
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ k),
          List.getElem?_append_right (by omega : w1.length ≤ k), hw0_len, hw1_len]
    have hag_fin := wire_independent_of_zero_if_no_read (C.gates.drop (j.val + 1))
      (stepWires w0 C.gates[j.val]) (stepWires w1 C.gates[j.val])
      (by simp [stepWires, hw0_len, hw1_len]) hag_step hno_after
    have hout_ne0 : C.output ≠ 0 := by
      have hout := (minimal_output_is_gate 10 petersenFun C hev petersenFun_not_false petersenFun_not_proj).1
      omega
    have heval_eq : C.eval (List.ofFn x0) = C.eval (List.ofFn x1) := by
      simp only [Circuit.eval, wires_eq_foldl]
      rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
      exact hag_fin C.output hout_ne0
    rw [hev x0, hev x1] at heval_eq
    have hdiff : petersenFun x0 ≠ petersenFun x1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> decide
    exact hdiff heval_eq
  refine ⟨htrue, ?_⟩
  by_contra hlt10
  push Not at hlt10
  have hget : ∀ v : Fin 10, (C.wires (List.ofFn (singleInput v))).getD h false = singleInput v ⟨h, hlt10⟩ := by
    intro v
    obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix C.gates (List.ofFn (singleInput v))
    rw [wires_eq_foldl, hsuf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp [hlt10]), List.getElem?_ofFn, dif_pos hlt10]
    rfl
  have h1 := htrue 1 (by simp); rw [hget 1] at h1
  have h4 := htrue 4 (by simp); rw [hget 4] at h4
  simp only [singleInput, decide_eq_true_eq] at h1 h4
  have : (1 : Fin 10) = 4 := h1.symm.trans h4
  exact absurd this (by decide)

/-- In any World 1 circuit computing `petersenFun` where `x 0` is read only once, by gate `j`
with `g = x 0 ∨ h` (with `h < 10 + j`), the partner wire `h` must evaluate to `false` on
`singleInput 1`, `singleInput 4`, and `singleInput 5` (so `h ∉ {1, 4, 5}`). -/
theorem world1_or_partner_false_on_nbrs (C : Circuit)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x)
    (hfo0 : wireFanOut 10 C 0 = 1)
    (j : Fin C.size) (hop : C.gates[j.val].op = GateOp.or)
    (h : ℕ) (hh : h < 10 + j.val)
    (hin : C.gates[j.val].inputs = [0, h] ∨ C.gates[j.val].inputs = [h, 0]) :
    ∀ v ∈ ({1, 4, 5} : Finset (Fin 10)),
      (C.wires (List.ofFn (singleInput v))).getD h false = false := by
  have hno_before : ∀ g ∈ C.gates.take j.val, 0 ∉ g.inputs := by
    intro g hg hin0
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hm_lt : m < j.val := by simp only [List.length_take] at hm; omega
    have hm_sz : m < C.size := by omega
    have hgm : (C.gates.take j.val)[m] = C.gates[m] := List.getElem_take
    rw [hgm] at hin0
    have hsub : (∑ k ∈ ({⟨m, hm_sz⟩, j} : Finset (Fin C.size)),
        (if 0 < 10 + k.val then C.gates[k.val].inputs.count 0 else 0)) ≤ wireFanOut 10 C 0 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hne : (⟨m, hm_sz⟩ : Fin C.size) ≠ j := fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega
    rw [Finset.sum_pair hne] at hsub
    have c1 : 0 < C.gates[m].inputs.count 0 := List.count_pos_iff.mpr hin0
    have c2 : 0 < C.gates[j.val].inputs.count 0 := List.count_pos_iff.mpr (by rcases hin with h' | h' <;> simp [h'])
    simp only [Nat.zero_lt_of_lt (by omega : 0 < 10 + m), Nat.zero_lt_of_lt (by omega : 0 < 10 + j.val), ↓reduceIte] at hsub
    omega
  have hno_after : ∀ g ∈ C.gates.drop (j.val + 1), 0 ∉ g.inputs := by
    intro g hg hin0
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hm_sz : j.val + 1 + m < C.size := by
      simp only [List.length_drop] at hm; exact Nat.add_lt_of_lt_sub' hm
    have hgm : (C.gates.drop (j.val + 1))[m] = C.gates[j.val + 1 + m] := List.getElem_drop
    rw [hgm] at hin0
    have hsub : (∑ k ∈ ({j, ⟨j.val + 1 + m, hm_sz⟩} : Finset (Fin C.size)),
        (if 0 < 10 + k.val then C.gates[k.val].inputs.count 0 else 0)) ≤ wireFanOut 10 C 0 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hne : j ≠ (⟨j.val + 1 + m, hm_sz⟩ : Fin C.size) := fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega
    rw [Finset.sum_pair hne] at hsub
    have c1 : 0 < C.gates[j.val].inputs.count 0 := List.count_pos_iff.mpr (by rcases hin with h' | h' <;> simp [h'])
    have c2 : 0 < C.gates[j.val + 1 + m].inputs.count 0 := List.count_pos_iff.mpr hin0
    simp only [Nat.zero_lt_of_lt (by omega : 0 < 10 + j.val), Nat.zero_lt_of_lt (by omega : 0 < 10 + (j.val + 1 + m)), ↓reduceIte] at hsub
    omega
  intro v hv
  by_contra hnot
  have htrue : (C.wires (List.ofFn (singleInput v))).getD h false = true := by
    cases hc : (C.wires (List.ofFn (singleInput v))).getD h false
    · exact absurd hc hnot
    · rfl
  let x0 := singleInput v
  let x1 := Function.update (singleInput v) 0 true
  have hsplit : C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val + 1) := by
    have h1 := List.take_append_drop j.val C.gates
    have h2 : C.gates.drop j.val = C.gates[j.val] :: C.gates.drop (j.val + 1) := List.drop_eq_getElem_cons j.isLt
    rw [h2] at h1; exact h1.symm
  have htake_len : (C.gates.take j.val).length = j.val := List.length_take_of_le (Nat.le_of_lt j.isLt)
  set w0 := (C.gates.take j.val).foldl stepWires (List.ofFn x0)
  set w1 := (C.gates.take j.val).foldl stepWires (List.ofFn x1)
  have hw0_len : w0.length = 10 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
  have hw1_len : w1.length = 10 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
  have hag_init : ∀ k, k ≠ 0 → (List.ofFn x0).getD k false = (List.ofFn x1).getD k false := by
    intro k hk
    by_cases h10 : k < 10
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h10, ↓reduceDIte]
      have hne : (⟨k, h10⟩ : Fin 10) ≠ 0 := fun heq => hk (congrArg Fin.val heq)
      simp [x0, x1, Function.update_of_ne hne]
    · simp [List.getD_eq_getElem?_getD, h10]
  have hag_w : ∀ k, k ≠ 0 → w0.getD k false = w1.getD k false :=
    wire_independent_of_zero_if_no_read (C.gates.take j.val) _ _ (by simp) hag_init hno_before
  have hh0_val : w0.getD h false = true := by
    obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix (C.gates[j.val] :: C.gates.drop (j.val + 1)) w0
    have hfull : C.wires (List.ofFn x0) = w0 ++ suf := by
      rw [wires_eq_foldl, hsplit, List.foldl_append]; exact hsuf
    rw [hfull, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)] at htrue
    simpa [List.getD_eq_getElem?_getD] using htrue
  have hhne0 : h ≠ 0 := by
    intro h0; subst h0
    have hcount : C.gates[j.val].inputs.count 0 = 2 := by rcases hin with h' | h' <;> simp [h']
    have hle : (if 0 < 10 + j.val then C.gates[j.val].inputs.count 0 else 0) ≤ wireFanOut 10 C 0 := by
      unfold wireFanOut
      exact Finset.single_le_sum (f := fun k : Fin C.size => if 0 < 10 + k.val then C.gates[k.val].inputs.count 0 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Nat.zero_lt_of_lt (by omega : 0 < 10 + j.val), ↓reduceIte, hcount] at hle
    omega
  have hh1_val : w1.getD h false = true := by rw [← hag_w h hhne0, hh0_val]
  have hgate_eq : C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => w0.getD i false) =
      C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => w1.getD i false) := by
    rw [hop]
    rcases hin with h' | h' <;> simp only [h', List.map_cons, List.map_nil, hh0_val, hh1_val, GateOp.eval] <;>
      cases w0.getD 0 false <;> cases w1.getD 0 false <;> rfl
  have hag_step : ∀ k, k ≠ 0 → (stepWires w0 C.gates[j.val]).getD k false =
      (stepWires w1 C.gates[j.val]).getD k false := by
    intro k hk
    unfold stepWires; rw [hgate_eq]
    by_cases hlt : k < 10 + j.val
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < w0.length),
        List.getElem?_append_left (by omega : k < w1.length)]
      simpa [List.getD_eq_getElem?_getD] using hag_w k hk
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ k),
        List.getElem?_append_right (by omega : w1.length ≤ k), hw0_len, hw1_len]
  have hag_fin := wire_independent_of_zero_if_no_read (C.gates.drop (j.val + 1))
    (stepWires w0 C.gates[j.val]) (stepWires w1 C.gates[j.val])
    (by simp [stepWires, hw0_len, hw1_len]) hag_step hno_after
  have hout_ne0 : C.output ≠ 0 := by
    have hout := (minimal_output_is_gate 10 petersenFun C hev petersenFun_not_false petersenFun_not_proj).1
    omega
  have heval_eq : C.eval (List.ofFn x0) = C.eval (List.ofFn x1) := by
    simp only [Circuit.eval, wires_eq_foldl]
    rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
    exact hag_fin C.output hout_ne0
  rw [hev x0, hev x1] at heval_eq
  have hdiff : petersenFun x0 ≠ petersenFun x1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> decide
  exact hdiff heval_eq

/-! ### 5. Further lower-bound structure for `p0Fun` (arbitrary `varCount` Σ₃, AND-partner, distinct readers) -/

/-- Every Σ₃ monotone formula (`andDepth ≤ 1`, arbitrary variable multiplicity) computing
Petersen minus vertex 0 has at least 17 leaves. -/
theorem p0_sigma3_leaves_ge_17 (F : MonoFormula 10)
    (hd : F.andDepth ≤ 1)
    (hev : ∀ x : Fin 10 → Bool, F.eval x = p0Fun10 x) :
    17 ≤ F.leaves := by
  obtain ⟨T, E, hE, hcovT, hbd⟩ := sigma3_subformula_bound F hd
    (fun x hx => p0Fun10_le_petersenFun x (by rw [← hev x, hx]))
  have hsub : p0Edges ⊆ E := by
    intro e he
    simp only [p0Edges, Finset.mem_filter] at he
    apply hE e he.1
    rw [hev]
    have hupd : Function.update (pairInput e.1 e.2) 0 false = pairInput e.1 e.2 := by
      funext i
      by_cases hi : i = 0
      · subst hi; simp [Function.update, pairInput, Ne.symm he.2.1, Ne.symm he.2.2]
      · simp [Function.update, hi]
    unfold p0Fun10
    rw [hupd, petersenFun_pair_iff]
    exact petersenEdges_adj e he.1
  have hE12 : 12 ≤ E.card := by rw [← p0Edges_card]; exact Finset.card_le_card hsub
  have hT5 : 5 ≤ T.card := p0_tau_ge_5 T (fun e he => hcovT e (hsub he))
  omega

def p0Adj (u v : Fin 9) : Bool :=
  petersenAdj u.succ v.succ

def singleInput9 (v : Fin 9) : Fin 9 → Bool :=
  fun i => decide (i = v)

lemma p0Fun_single9 (v : Fin 9) : p0Fun (singleInput9 v) = false := by
  fin_cases v <;> decide

lemma p0Fun_pair9_adj (u v : Fin 9) (hadj : p0Adj u v = true) :
    p0Fun (Function.update (singleInput9 v) u true) = true := by
  revert hadj; fin_cases u <;> fin_cases v <;> decide

lemma p0_two_distinct_nbrs (u : Fin 9) :
    ∃ w1 w2 : Fin 9, w1 ≠ w2 ∧ p0Adj u w1 = true ∧ p0Adj u w2 = true := by
  fin_cases u
  · exact ⟨1, 5, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨1, 3, by decide, by decide, by decide⟩
  · exact ⟨2, 8, by decide, by decide, by decide⟩
  · exact ⟨6, 7, by decide, by decide, by decide⟩
  · exact ⟨0, 7, by decide, by decide, by decide⟩
  · exact ⟨1, 4, by decide, by decide, by decide⟩
  · exact ⟨2, 4, by decide, by decide, by decide⟩
  · exact ⟨3, 5, by decide, by decide, by decide⟩

/-- In any circuit computing `p0Fun`, if an input `u : Fin 9` is read exactly once, by an `AND`
gate `u ∧ h` (with `h < 9 + j`), then wire `h` must evaluate to `true` on `singleInput9 w` for
every neighbor `w` of `u` in `P - 0`. Since every vertex of `P - 0` has degree ≥ 2, `h` cannot
be an input wire (`9 ≤ h`). -/
theorem p0_and_partner_is_gate (C : Circuit)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = p0Fun x)
    (u : Fin 9) (hfou : wireFanOut 9 C u.val = 1)
    (j : Fin C.size) (hop : C.gates[j.val].op = GateOp.and)
    (h : ℕ) (hh : h < 9 + j.val)
    (hin : C.gates[j.val].inputs = [u.val, h] ∨ C.gates[j.val].inputs = [h, u.val]) :
    (∀ w : Fin 9, p0Adj u w = true → (C.wires (List.ofFn (singleInput9 w))).getD h false = true) ∧
    9 ≤ h := by
  have hno_before : ∀ g ∈ C.gates.take j.val, u.val ∉ g.inputs := by
    intro g hg hinu
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hm_lt : m < j.val := by simp only [List.length_take] at hm; omega
    have hm_sz : m < C.size := by omega
    have hgm : (C.gates.take j.val)[m] = C.gates[m] := List.getElem_take
    rw [hgm] at hinu
    have hsub : (∑ k ∈ ({⟨m, hm_sz⟩, j} : Finset (Fin C.size)),
        (if u.val < 9 + k.val then C.gates[k.val].inputs.count u.val else 0)) ≤ wireFanOut 9 C u.val :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hne : (⟨m, hm_sz⟩ : Fin C.size) ≠ j := fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega
    rw [Finset.sum_pair hne] at hsub
    have c1 : 0 < C.gates[m].inputs.count u.val := List.count_pos_iff.mpr hinu
    have c2 : 0 < C.gates[j.val].inputs.count u.val := List.count_pos_iff.mpr (by rcases hin with h' | h' <;> simp [h'])
    simp only [show u.val < 9 + m by omega, show u.val < 9 + j.val by omega, ↓reduceIte] at hsub
    omega
  have hno_after : ∀ g ∈ C.gates.drop (j.val + 1), u.val ∉ g.inputs := by
    intro g hg hinu
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hm_sz : j.val + 1 + m < C.size := by
      simp only [List.length_drop] at hm; exact Nat.add_lt_of_lt_sub' hm
    have hgm : (C.gates.drop (j.val + 1))[m] = C.gates[j.val + 1 + m] := List.getElem_drop
    rw [hgm] at hinu
    have hsub : (∑ k ∈ ({j, ⟨j.val + 1 + m, hm_sz⟩} : Finset (Fin C.size)),
        (if u.val < 9 + k.val then C.gates[k.val].inputs.count u.val else 0)) ≤ wireFanOut 9 C u.val :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hne : j ≠ (⟨j.val + 1 + m, hm_sz⟩ : Fin C.size) := fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega
    rw [Finset.sum_pair hne] at hsub
    have c1 : 0 < C.gates[j.val].inputs.count u.val := List.count_pos_iff.mpr (by rcases hin with h' | h' <;> simp [h'])
    have c2 : 0 < C.gates[j.val + 1 + m].inputs.count u.val := List.count_pos_iff.mpr hinu
    simp only [show u.val < 9 + j.val by omega, show u.val < 9 + (j.val + 1 + m) by omega, ↓reduceIte] at hsub
    omega
  have htrue : ∀ w : Fin 9, p0Adj u w = true →
      (C.wires (List.ofFn (singleInput9 w))).getD h false = true := by
    intro w hadj
    by_contra hnot
    have hfalse : (C.wires (List.ofFn (singleInput9 w))).getD h false = false := by
      cases hc : (C.wires (List.ofFn (singleInput9 w))).getD h false
      · rfl
      · exact absurd hc hnot
    let x0 := singleInput9 w
    let x1 := Function.update (singleInput9 w) u true
    have hsplit : C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val + 1) := by
      have h1 := List.take_append_drop j.val C.gates
      have h2 : C.gates.drop j.val = C.gates[j.val] :: C.gates.drop (j.val + 1) := List.drop_eq_getElem_cons j.isLt
      rw [h2] at h1; exact h1.symm
    have htake_len : (C.gates.take j.val).length = j.val := List.length_take_of_le (Nat.le_of_lt j.isLt)
    set w0 := (C.gates.take j.val).foldl stepWires (List.ofFn x0)
    set w1 := (C.gates.take j.val).foldl stepWires (List.ofFn x1)
    have hw0_len : w0.length = 9 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
    have hw1_len : w1.length = 9 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
    have hag_init : ∀ k, k ≠ u.val → (List.ofFn x0).getD k false = (List.ofFn x1).getD k false := by
      intro k hk
      by_cases h9 : k < 9
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h9, ↓reduceDIte]
        have hne : (⟨k, h9⟩ : Fin 9) ≠ u := fun heq => hk (congrArg Fin.val heq)
        simp [x0, x1, Function.update_of_ne hne]
      · simp [List.getD_eq_getElem?_getD, h9]
    have hag_w : ∀ k, k ≠ u.val → w0.getD k false = w1.getD k false :=
      (foldl_unused_input (C.gates.take j.val) _ _ u.val (by simp) hag_init hno_before).2
    have hh0_val : w0.getD h false = false := by
      obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix (C.gates[j.val] :: C.gates.drop (j.val + 1)) w0
      have hfull : C.wires (List.ofFn x0) = w0 ++ suf := by
        rw [wires_eq_foldl, hsplit, List.foldl_append]; exact hsuf
      rw [hfull, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)] at hfalse
      simpa [List.getD_eq_getElem?_getD] using hfalse
    have hhneu : h ≠ u.val := by
      intro hu; subst hu
      have hcount : C.gates[j.val].inputs.count u.val = 2 := by rcases hin with h' | h' <;> simp [h']
      have hle : (if u.val < 9 + j.val then C.gates[j.val].inputs.count u.val else 0) ≤ wireFanOut 9 C u.val := by
        unfold wireFanOut
        exact Finset.single_le_sum (f := fun k : Fin C.size => if u.val < 9 + k.val then C.gates[k.val].inputs.count u.val else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      simp only [show u.val < 9 + j.val by omega, ↓reduceIte, hcount] at hle
      omega
    have hh1_val : w1.getD h false = false := by rw [← hag_w h hhneu, hh0_val]
    have hgate_eq : C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => w0.getD i false) =
        C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => w1.getD i false) := by
      rw [hop]
      rcases hin with h' | h' <;> simp only [h', List.map_cons, List.map_nil, hh0_val, hh1_val, GateOp.eval] <;>
        cases w0.getD u.val false <;> cases w1.getD u.val false <;> rfl
    have hag_step : ∀ k, k ≠ u.val → (stepWires w0 C.gates[j.val]).getD k false =
        (stepWires w1 C.gates[j.val]).getD k false := by
      intro k hk
      unfold stepWires; rw [hgate_eq]
      by_cases hlt : k < 9 + j.val
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < w0.length),
          List.getElem?_append_left (by omega : k < w1.length)]
        simpa [List.getD_eq_getElem?_getD] using hag_w k hk
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ k),
          List.getElem?_append_right (by omega : w1.length ≤ k), hw0_len, hw1_len]
    have hag_fin := (foldl_unused_input (C.gates.drop (j.val + 1))
      (stepWires w0 C.gates[j.val]) (stepWires w1 C.gates[j.val]) u.val
      (by simp [stepWires, hw0_len, hw1_len]) hag_step hno_after).2
    have hout_neu : C.output ≠ u.val := by
      have hout := (minimal_output_is_gate 9 p0Fun C hev p0Fun_not_false p0Fun_not_proj).1
      omega
    have heval_eq : C.eval (List.ofFn x0) = C.eval (List.ofFn x1) := by
      simp only [Circuit.eval, wires_eq_foldl]
      rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
      exact hag_fin C.output hout_neu
    rw [hev x0, hev x1, p0Fun_single9 w, p0Fun_pair9_adj u w hadj] at heval_eq
    exact absurd heval_eq (by decide)
  refine ⟨htrue, ?_⟩
  by_contra hlt9
  push Not at hlt9
  obtain ⟨w1, w2, hne, hadj1, hadj2⟩ := p0_two_distinct_nbrs u
  have hget : ∀ w : Fin 9, (C.wires (List.ofFn (singleInput9 w))).getD h false = singleInput9 w ⟨h, hlt9⟩ := by
    intro w
    obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix C.gates (List.ofFn (singleInput9 w))
    rw [wires_eq_foldl, hsuf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp [hlt9]), List.getElem?_ofFn, dif_pos hlt9]
    rfl
  have h1 := htrue w1 hadj1; rw [hget w1] at h1
  have h2 := htrue w2 hadj2; rw [hget w2] at h2
  simp only [singleInput9, decide_eq_true_eq] at h1 h2
  exact hne (h1.symm.trans h2)

lemma foldl_unused_two (gs : List Gate) (w1 w2 : List Bool) (i1 i2 : ℕ)
    (hlen : w1.length = w2.length)
    (hag : ∀ k, k ≠ i1 → k ≠ i2 → w1.getD k false = w2.getD k false)
    (hno : ∀ g ∈ gs, i1 ∉ g.inputs ∧ i2 ∉ g.inputs) :
    ∀ k, k ≠ i1 → k ≠ i2 → (gs.foldl stepWires w1).getD k false = (gs.foldl stepWires w2).getD k false := by
  induction gs generalizing w1 w2 with
  | nil => exact hag
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hno g List.mem_cons_self
    have hbit : g.op.eval (g.inputs.map fun k => w1.getD k false) =
        g.op.eval (g.inputs.map fun k => w2.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact hag k (fun h => hg.1 (h ▸ hk)) (fun h => hg.2 (h ▸ hk))
    apply ih
    · simp [stepWires, hlen]
    · intro k hk1 hk2
      unfold stepWires; rw [hbit]
      by_cases hlt : k < w1.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getElem?_append_left (by omega : k < w2.length)]
        simpa [List.getD_eq_getElem?_getD] using hag k hk1 hk2
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w1.length ≤ k),
          List.getElem?_append_right (by omega : w2.length ≤ k), hlen]
    · exact fun x hx => hno x (List.mem_cons_of_mem _ hx)

lemma p0Fun_sep_pairs (u v : Fin 9) (huv : u ≠ v) :
    (∃ w : Fin 9, w ≠ u ∧ w ≠ v ∧ p0Adj u w = true ∧ p0Adj v w = false) ∧
    (∃ w : Fin 9, w ≠ u ∧ w ≠ v ∧ p0Adj v w = true ∧ p0Adj u w = false) := by
  revert huv; fin_cases u <;> fin_cases v <;> decide

/-- Two distinct read-once inputs `u ≠ v` of `p0Fun` cannot be read by the same gate. -/
theorem p0_read_once_distinct_readers (C : Circuit) (hF : FanInTwo C)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = p0Fun x)
    (u v : Fin 9) (huv : u ≠ v)
    (hfou : wireFanOut 9 C u.val = 1) (hfov : wireFanOut 9 C v.val = 1)
    (j : Fin C.size) (hu : u.val ∈ C.gates[j.val].inputs) (hv : v.val ∈ C.gates[j.val].inputs) :
    False := by
  have hlen2 : C.gates[j.val].inputs.length ≤ 2 := (hF _ (List.getElem_mem j.isLt)).2
  have hin_eq : C.gates[j.val].inputs = [u.val, v.val] ∨ C.gates[j.val].inputs = [v.val, u.val] := by
    have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
    rcases hl : C.gates[j.val].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · rw [hl] at hu; simp at hu
    · rw [hl] at hu hv; simp at hu hv; exact absurd (hu.trans hv.symm) hne
    · rw [hl] at hu hv; simp at hu hv
      rcases hu with rfl | rfl <;> rcases hv with h | h
      · exact absurd h.symm hne
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
      · exact absurd h.symm hne
    · rw [hl] at hlen2; simp at hlen2
  have hno_other : ∀ m : Fin C.size, m ≠ j → u.val ∉ C.gates[m.val].inputs ∧ v.val ∉ C.gates[m.val].inputs := by
    intro m hmj
    constructor
    · intro hm
      have hsub : (∑ k ∈ ({m, j} : Finset (Fin C.size)),
          (if u.val < 9 + k.val then C.gates[k.val].inputs.count u.val else 0)) ≤ wireFanOut 9 C u.val :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_pair hmj] at hsub
      have c1 : 0 < C.gates[m.val].inputs.count u.val := List.count_pos_iff.mpr hm
      have c2 : 0 < C.gates[j.val].inputs.count u.val := List.count_pos_iff.mpr hu
      simp only [show u.val < 9 + m.val by omega, show u.val < 9 + j.val by omega, ↓reduceIte] at hsub
      omega
    · intro hm
      have hsub : (∑ k ∈ ({m, j} : Finset (Fin C.size)),
          (if v.val < 9 + k.val then C.gates[k.val].inputs.count v.val else 0)) ≤ wireFanOut 9 C v.val :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_pair hmj] at hsub
      have c1 : 0 < C.gates[m.val].inputs.count v.val := List.count_pos_iff.mpr hm
      have c2 : 0 < C.gates[j.val].inputs.count v.val := List.count_pos_iff.mpr hv
      simp only [show v.val < 9 + m.val by omega, show v.val < 9 + j.val by omega, ↓reduceIte] at hsub
      omega
  have hno_before : ∀ g ∈ C.gates.take j.val, u.val ∉ g.inputs ∧ v.val ∉ g.inputs := by
    intro g hg; rw [List.mem_iff_getElem] at hg; obtain ⟨m, hm, rfl⟩ := hg
    have hm_lt : m < j.val := by simp only [List.length_take] at hm; omega
    have hm_sz : m < C.size := by omega
    rw [List.getElem_take]; exact hno_other ⟨m, hm_sz⟩ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)
  have hno_after : ∀ g ∈ C.gates.drop (j.val + 1), u.val ∉ g.inputs ∧ v.val ∉ g.inputs := by
    intro g hg; rw [List.mem_iff_getElem] at hg; obtain ⟨m, hm, rfl⟩ := hg
    have hm_sz : j.val + 1 + m < C.size := by simp only [List.length_drop] at hm; exact Nat.add_lt_of_lt_sub' hm
    rw [List.getElem_drop]; exact hno_other ⟨j.val + 1 + m, hm_sz⟩ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)
  have hsame : ∀ (x y : Fin 9 → Bool),
      (∀ k : Fin 9, k ≠ u → k ≠ v → x k = y k) →
      C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => (List.ofFn x).getD i false) =
      C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => (List.ofFn y).getD i false) →
      p0Fun x = p0Fun y := by
    intro x y hag hgeq
    have hsplit : C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val + 1) := by
      have h1 := List.take_append_drop j.val C.gates
      have h2 : C.gates.drop j.val = C.gates[j.val] :: C.gates.drop (j.val + 1) := List.drop_eq_getElem_cons j.isLt
      rw [h2] at h1; exact h1.symm
    have htake_len : (C.gates.take j.val).length = j.val := List.length_take_of_le (Nat.le_of_lt j.isLt)
    set wx := (C.gates.take j.val).foldl stepWires (List.ofFn x)
    set wy := (C.gates.take j.val).foldl stepWires (List.ofFn y)
    have hwx_len : wx.length = 9 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
    have hwy_len : wy.length = 9 + j.val := by rw [foldl_stepWires_length, List.length_ofFn, htake_len]
    have hag_init : ∀ k, k ≠ u.val → k ≠ v.val → (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
      intro k hk1 hk2
      by_cases h9 : k < 9
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h9, ↓reduceDIte]
        exact hag ⟨k, h9⟩ (fun h => hk1 (congrArg Fin.val h)) (fun h => hk2 (congrArg Fin.val h))
      · simp [List.getD_eq_getElem?_getD, h9]
    have hag_w := foldl_unused_two (C.gates.take j.val) _ _ u.val v.val (by simp) hag_init hno_before
    have hpref_get : ∀ (z : Fin 9 → Bool) (i : Fin 9),
        ((C.gates.take j.val).foldl stepWires (List.ofFn z)).getD i.val false = (List.ofFn z).getD i.val false := by
      intro z i
      obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix (C.gates.take j.val) (List.ofFn z)
      rw [hsuf, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [i.isLt])]
      rfl
    have hgate_eq' : C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => wx.getD i false) =
        C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => wy.getD i false) := by
      have hmx : C.gates[j.val].inputs.map (fun i => wx.getD i false) =
          C.gates[j.val].inputs.map (fun i => (List.ofFn x).getD i false) := by
        rcases hin_eq with h' | h'
        · simp only [h', List.map_cons, List.map_nil]; rw [hpref_get x u, hpref_get x v]
        · simp only [h', List.map_cons, List.map_nil]; rw [hpref_get x v, hpref_get x u]
      have hmy : C.gates[j.val].inputs.map (fun i => wy.getD i false) =
          C.gates[j.val].inputs.map (fun i => (List.ofFn y).getD i false) := by
        rcases hin_eq with h' | h'
        · simp only [h', List.map_cons, List.map_nil]; rw [hpref_get y u, hpref_get y v]
        · simp only [h', List.map_cons, List.map_nil]; rw [hpref_get y v, hpref_get y u]
      rw [hmx, hmy]; exact hgeq
    have hag_step : ∀ k, k ≠ u.val → k ≠ v.val →
        (stepWires wx C.gates[j.val]).getD k false = (stepWires wy C.gates[j.val]).getD k false := by
      intro k hk1 hk2
      unfold stepWires; rw [hgate_eq']
      by_cases hlt : k < 9 + j.val
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < wx.length),
          List.getElem?_append_left (by omega : k < wy.length)]
        rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
        exact hag_w k hk1 hk2
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : wx.length ≤ k),
          List.getElem?_append_right (by omega : wy.length ≤ k), hwx_len, hwy_len]
    have hag_fin := foldl_unused_two (C.gates.drop (j.val + 1))
      (stepWires wx C.gates[j.val]) (stepWires wy C.gates[j.val]) u.val v.val
      (by simp [stepWires, hwx_len, hwy_len]) hag_step hno_after
    have hout_ge := (minimal_output_is_gate 9 p0Fun C hev p0Fun_not_false p0Fun_not_proj).1
    rw [← hev x, ← hev y]
    simp only [Circuit.eval, wires_eq_foldl]
    rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
    exact hag_fin C.output (by omega) (by omega)
  -- Now evaluate C.gates[j].op on (0,0), (1,0), (0,1): two of these three inputs must produce the
  -- same Bool output, contradicting p0Fun_sep_pairs!
  obtain ⟨⟨wu, hwu_u, hwu_v, hwu_adj, hwu_nadj⟩, ⟨wv, hwv_u, hwv_v, hwv_adj, hwv_nadj⟩⟩ := p0Fun_sep_pairs u v huv
  let eval2 : Bool → Bool → Bool := fun bu bv =>
    C.gates[j.val].op.eval (if C.gates[j.val].inputs = [u.val, v.val] then [bu, bv] else [bv, bu])
  have hneq_list : ([v.val, u.val] : List ℕ) ≠ [u.val, v.val] := by
    intro h; simp at h; exact huv (Fin.ext h.1.symm)
  have heval_fn : ∀ (z : Fin 9 → Bool),
      C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => (List.ofFn z).getD i false) =
      eval2 (z u) (z v) := by
    intro z
    have hget : ∀ i : Fin 9, (List.ofFn z).getD i.val false = z i := by
      intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte]; rfl
    dsimp [eval2]
    rcases hin_eq with h' | h'
    · simp only [h', List.map_cons, List.map_nil, hget, ↓reduceIte]
    · simp only [h', List.map_cons, List.map_nil, hget, hneq_list, ↓reduceIte]
  have hneq_00_10 : eval2 false false ≠ eval2 true false := by
    intro heq
    have hs := hsame (singleInput9 wu) (Function.update (singleInput9 wu) u true)
      (fun k hk1 _ => by simp [Function.update_of_ne hk1]) (by
        rw [heval_fn, heval_fn]
        simp [singleInput9, hwu_u.symm, hwu_v.symm, Function.update_of_ne huv.symm, heq])
    rw [p0Fun_single9 wu, p0Fun_pair9_adj u wu hwu_adj] at hs
    exact absurd hs (by decide)
  have hneq_00_01 : eval2 false false ≠ eval2 false true := by
    intro heq
    have hs := hsame (singleInput9 wv) (Function.update (singleInput9 wv) v true)
      (fun k _ hk2 => by simp [Function.update_of_ne hk2]) (by
        rw [heval_fn, heval_fn]
        simp [singleInput9, hwv_u.symm, hwv_v.symm, Function.update_of_ne huv, heq])
    rw [p0Fun_single9 wv, p0Fun_pair9_adj v wv hwv_adj] at hs
    exact absurd hs (by decide)
  have hneq_10_01 : eval2 true false ≠ eval2 false true := by
    intro heq
    have hs := hsame (Function.update (singleInput9 wu) u true) (Function.update (singleInput9 wu) v true)
      (fun k hk1 hk2 => by simp [Function.update_of_ne hk1, Function.update_of_ne hk2]) (by
        rw [heval_fn, heval_fn]
        simp [singleInput9, hwu_u.symm, hwu_v.symm, Function.update_of_ne huv, Function.update_of_ne huv.symm, heq])
    have htrue : p0Fun (Function.update (singleInput9 wu) u true) = true := p0Fun_pair9_adj u wu hwu_adj
    have hfalse : p0Fun (Function.update (singleInput9 wu) v true) = false := by
      revert hwu_nadj hwu_v; generalize wu = w; fin_cases v <;> fin_cases w <;> decide
    rw [htrue, hfalse] at hs
    exact absurd hs (by decide)
  cases h00 : eval2 false false <;> cases h10 : eval2 true false <;> cases h01 : eval2 false true <;>
    simp [h00, h10, h01] at hneq_00_10 hneq_00_01 hneq_10_01

end PEqualNP.Outside.L_meta_651_p0
