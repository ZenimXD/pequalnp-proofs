import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_651_world1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuit machinery copied from L_meta_651_step (lines 8 to 754), in this namespace.
def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWires x := rfl

lemma foldl_stepWires_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepWires acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWires, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  foldl_stepWires_length C.gates x

lemma foldl_stepWires_prefix (gs : List Gate) (acc : List Bool) :
    ∃ suf : List Bool, gs.foldl stepWires acc = acc ++ suf ∧ suf.length = gs.length := by
  induction gs generalizing acc with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨suf, hsuf, hlen⟩ := ih (stepWires acc g)
    refine ⟨g.op.eval (g.inputs.map fun i => acc.getD i false) :: suf, ?_, by simp [hlen]⟩
    simpa [List.foldl_cons, stepWires, List.append_assoc] using hsuf

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma isNotOp_eq_true (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

def trimNot (g : Gate) : Gate :=
  if isNotOp g.op then ⟨GateOp.not, g.inputs.take 1⟩ else g

def trimNots (C : Circuit) : Circuit :=
  ⟨C.gates.map trimNot, C.output⟩

lemma stepWires_trimNot (w : List Bool) (g : Gate) :
    stepWires w (trimNot g) = stepWires w g := by
  unfold trimNot stepWires
  split_ifs with h
  · have hnot : g.op = GateOp.not := (isNotOp_eq_true g.op).mp h
    rw [hnot]
    simp only [GateOp.eval]
    cases g.inputs with
    | nil => simp
    | cons a rest => simp
  · rfl

lemma trimNots_wires (C : Circuit) (x : List Bool) :
    (trimNots C).wires x = C.wires x := by
  simp only [wires_eq_foldl, trimNots]
  suffices ∀ (gs : List Gate) (acc : List Bool),
      (gs.map trimNot).foldl stepWires acc = gs.foldl stepWires acc from this C.gates x
  intro gs
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons, stepWires_trimNot, ih]

lemma trimNots_eval (C : Circuit) (x : List Bool) :
    (trimNots C).eval x = C.eval x := by
  unfold Circuit.eval
  rw [trimNots_wires]
  rfl

lemma trimNots_size (C : Circuit) : (trimNots C).size = C.size := by
  simp [Circuit.size, trimNots]

lemma trimNots_fanInTwo (C : Circuit) (h : FanInTwo C) : FanInTwo (trimNots C) := by
  intro g hg
  simp only [trimNots, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := h g0 hg0
  unfold trimNot
  split_ifs with hnot
  · have h0 : g0.op = GateOp.not := (isNotOp_eq_true g0.op).mp hnot
    refine ⟨by simp, ?_⟩
    simp only [List.length_take]
    omega
  · exact ⟨hop, hlen⟩

lemma trimNots_not_len (C : Circuit) :
    ∀ g ∈ (trimNots C).gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg hnot
  simp only [trimNots, List.mem_map] at hg
  obtain ⟨g0, _, rfl⟩ := hg
  unfold trimNot at hnot ⊢
  split_ifs at hnot ⊢ with h0
  · simp only [List.length_take]; omega
  · exact absurd ((isNotOp_eq_true g0.op).mpr hnot) h0

def notCount (C : Circuit) : ℕ :=
  (C.gates.filter fun g => isNotOp g.op).length

def wireFanOut (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  ∑ j : Fin C.size, if w < n + j.val then (C.gates[j.val].inputs.count w) else 0

lemma sum_count_range_le (l : List ℕ) (N : ℕ) :
    ∑ w ∈ Finset.range N, l.count w ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.length_cons]
    have h1 : ∑ w ∈ Finset.range N, (l.count w + (if a == w then 1 else 0)) =
        (∑ w ∈ Finset.range N, l.count w) + ∑ w ∈ Finset.range N, (if a == w then 1 else 0) :=
      Finset.sum_add_distrib
    rw [h1]
    have h2 : ∑ w ∈ Finset.range N, (if a == w then 1 else 0) ≤ 1 := by
      have : (∑ w ∈ Finset.range N, if a == w then 1 else 0) =
          ∑ w ∈ Finset.range N, if w = a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hwa : w = a
        · subst hwa; simp
        · have hab : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
          simp [hwa, hab]
      rw [this, Finset.sum_ite_eq']
      split_ifs <;> omega
    omega

lemma sum_inputs_len_bound (C : Circuit) (hF : FanInTwo C)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) :
    (∑ j : Fin C.size, C.gates[j.val].inputs.length) + notCount C ≤ 2 * C.size := by
  suffices ∀ (gs : List Gate),
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1) →
      (∑ j : Fin gs.length, gs[j.val].inputs.length) +
        (gs.filter fun g => isNotOp g.op).length ≤ 2 * gs.length by
    exact this C.gates (fun g hg => (hF g hg).2) hNot
  intro gs h2 h1
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hsum : (∑ j : Fin (g :: gs).length, (g :: gs)[j.val].inputs.length) =
        g.inputs.length + ∑ j : Fin gs.length, gs[j.val].inputs.length :=
      Fin.sum_univ_succ (fun j : Fin (gs.length + 1) => (g :: gs)[j.val].inputs.length)
    rw [hsum]
    simp only [List.length_cons, List.filter_cons]
    have ih' := ih (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
                   (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
    have hg2 := h2 g List.mem_cons_self
    cases hgn : isNotOp g.op
    · simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have hg1 := h1 g List.mem_cons_self ((isNotOp_eq_true g.op).mp hgn)
      simp only [↓reduceIte, List.length_cons]
      omega

lemma wire_budget_raw (n : ℕ) (C : Circuit) (hF : FanInTwo C)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) :
    (∑ i : Fin n, wireFanOut n C i.val) +
    (∑ j : Fin C.size, wireFanOut n C (n + j.val)) +
    notCount C ≤ 2 * C.size := by
  have hsplit : (∑ i : Fin n, wireFanOut n C i.val) +
      (∑ j : Fin C.size, wireFanOut n C (n + j.val)) =
      ∑ w ∈ Finset.range (n + C.size), wireFanOut n C w := by
    rw [Finset.sum_range_add,
      Fin.sum_univ_eq_sum_range (fun x => wireFanOut n C x),
      Fin.sum_univ_eq_sum_range (fun x => wireFanOut n C (n + x))]
  rw [hsplit]
  have hswap : ∑ w ∈ Finset.range (n + C.size), wireFanOut n C w =
      ∑ j : Fin C.size, ∑ w ∈ Finset.range (n + C.size),
        (if w < n + j.val then C.gates[j.val].inputs.count w else 0) := by
    unfold wireFanOut
    exact Finset.sum_comm
  rw [hswap]
  have hle : ∑ j : Fin C.size, ∑ w ∈ Finset.range (n + C.size),
        (if w < n + j.val then C.gates[j.val].inputs.count w else 0) ≤
      ∑ j : Fin C.size, C.gates[j.val].inputs.length := by
    apply Finset.sum_le_sum
    intro j _
    calc ∑ w ∈ Finset.range (n + C.size),
            (if w < n + j.val then C.gates[j.val].inputs.count w else 0)
        ≤ ∑ w ∈ Finset.range (n + C.size), C.gates[j.val].inputs.count w := by
          apply Finset.sum_le_sum
          intro w _
          split_ifs <;> omega
      _ ≤ C.gates[j.val].inputs.length := sum_count_range_le _ _
  have hbound := sum_inputs_len_bound C hF hNot
  omega

def shiftIdx (k w : ℕ) : ℕ := if k < w then w - 1 else w

def shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftIdx k)⟩

def deleteGate (n : ℕ) (C : Circuit) (j : ℕ) : Circuit :=
  ⟨(C.gates.eraseIdx j).map (shiftGate (n + j)), shiftIdx (n + j) C.output⟩

lemma deleteGate_size (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size) :
    (deleteGate n C j).size = C.size - 1 := by
  simp [deleteGate, Circuit.size, List.length_eraseIdx_of_lt hj]

lemma deleteGate_fanInTwo (n : ℕ) (C : Circuit) (j : ℕ) (hF : FanInTwo C) :
    FanInTwo (deleteGate n C j) := by
  intro g hg
  simp only [deleteGate, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have hg0' : g0 ∈ C.gates := List.mem_of_mem_eraseIdx hg0
  obtain ⟨hop, hlen⟩ := hF g0 hg0'
  exact ⟨hop, by simp [shiftGate, hlen]⟩

lemma getD_shift_prefix (w : List Bool) (k i : ℕ) (hw : w.length ≤ k) :
    w.getD (shiftIdx k i) false = w.getD i false := by
  unfold shiftIdx
  split_ifs with h
  · have h1 : w.length ≤ i - 1 := by omega
    have h2 : w.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]
  · rfl

lemma foldl_shift_prefix (gs : List Gate) (acc : List Bool) (k : ℕ)
    (hk : acc.length + gs.length ≤ k) :
    (gs.map (shiftGate k)).foldl stepWires acc = gs.foldl stepWires acc := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hstep : stepWires acc (shiftGate k g) = stepWires acc g := by
      unfold stepWires shiftGate
      congr 2
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro i _
      exact getD_shift_prefix acc k i (by simp at hk; omega)
    rw [hstep]
    apply ih
    simp only [stepWires, List.length_append, List.length_singleton]
    simp only [List.length_cons] at hk
    omega

lemma getD_shift_suffix (w1 suf : List Bool) (b : Bool) (i : ℕ) (hne : i ≠ w1.length) :
    (w1 ++ suf).getD (shiftIdx w1.length i) false = (w1 ++ b :: suf).getD i false := by
  unfold shiftIdx
  split_ifs with h
  · have h1 : i = w1.length + 1 + (i - w1.length - 1) := by omega
    have h2 : i - 1 = w1.length + (i - w1.length - 1) := by omega
    simp only [List.getD_eq_getElem?_getD]
    rw [h2, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    have h3 : (w1 ++ b :: suf)[i]? = ((w1 ++ [b]) ++ suf)[i]? := by simp
    rw [h3, h1]
    have hlen : (w1 ++ [b]).length = w1.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
  · have hlt : i < w1.length := by omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]

lemma foldl_shift_suffix (gs : List Gate) (w1 suf : List Bool) (b : Bool)
    (hno : ∀ g ∈ gs, w1.length ∉ g.inputs) :
    ∃ suf' : List Bool,
      (gs.map (shiftGate w1.length)).foldl stepWires (w1 ++ suf) = w1 ++ suf' ∧
      gs.foldl stepWires (w1 ++ b :: suf) = w1 ++ b :: suf' := by
  induction gs generalizing suf with
  | nil => exact ⟨suf, rfl, rfl⟩
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg : w1.length ∉ g.inputs := hno g List.mem_cons_self
    have hbit : g.op.eval ((g.inputs.map (shiftIdx w1.length)).map fun i => (w1 ++ suf).getD i false) =
        g.op.eval (g.inputs.map fun i => (w1 ++ b :: suf).getD i false) := by
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact getD_shift_suffix w1 suf b i (fun heq => hg (heq ▸ hi))
    have hs1 : stepWires (w1 ++ suf) (shiftGate w1.length g) =
        w1 ++ (suf ++ [g.op.eval (g.inputs.map fun i => (w1 ++ b :: suf).getD i false)]) := by
      unfold stepWires shiftGate
      rw [hbit, List.append_assoc]
    have hs2 : stepWires (w1 ++ b :: suf) g =
        w1 ++ b :: (suf ++ [g.op.eval (g.inputs.map fun i => (w1 ++ b :: suf).getD i false)]) := by
      unfold stepWires
      simp [List.append_assoc]
    rw [hs1, hs2]
    exact ih _ (fun x hx => hno x (List.mem_cons_of_mem _ hx))

lemma deleteGate_eval (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size)
    (hout : C.output ≠ n + j)
    (hdead : wireFanOut n C (n + j) = 0)
    (x : List Bool) (hx : x.length = n) :
    (deleteGate n C j).eval x = C.eval x := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm
  have herase : C.gates.eraseIdx j = C.gates.take j ++ C.gates.drop (j + 1) := by
    rw [List.eraseIdx_eq_take_drop_succ]
  have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hno : ∀ g ∈ C.gates.drop (j + 1), n + j ∉ g.inputs := by
    intro g hg hin
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hm_lt : j + 1 + m < C.size := by
      simp only [List.length_drop] at hm
      exact Nat.add_lt_of_lt_sub' hm
    have hcount_pos : 0 < C.gates[j + 1 + m].inputs.count (n + j) := by
      have : C.gates[j + 1 + m] = (C.gates.drop (j + 1))[m] := (List.getElem_drop).symm
      rw [this]
      exact List.count_pos_iff.mpr hin
    have hzero : (if n + j < n + (j + 1 + m) then C.gates[j + 1 + m].inputs.count (n + j) else 0) = 0 := by
      have h := Finset.sum_eq_zero_iff.mp hdead ⟨j + 1 + m, hm_lt⟩ (Finset.mem_univ _)
      exact h
    simp only [show n + j < n + (j + 1 + m) by omega, ↓reduceIte] at hzero
    omega
  set w1 := (C.gates.take j).foldl stepWires x
  have hw1_len : w1.length = n + j := by
    rw [foldl_stepWires_length, hx, htake_len]
  have hpref : ((C.gates.take j).map (shiftGate (n + j))).foldl stepWires x = w1 :=
    foldl_shift_prefix (C.gates.take j) x (n + j) (by rw [hx, htake_len])
  set b := C.gates[j].op.eval (C.gates[j].inputs.map fun i => w1.getD i false)
  have hno' : ∀ g ∈ C.gates.drop (j + 1), w1.length ∉ g.inputs := by
    rwa [hw1_len]
  obtain ⟨suf', hs1, hs2⟩ := foldl_shift_suffix (C.gates.drop (j + 1)) w1 [] b hno'
  simp only [Circuit.eval, wires_eq_foldl, deleteGate]
  rw [herase, List.map_append, List.foldl_append, hpref]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have hstep_j : stepWires w1 C.gates[j] = w1 ++ b :: [] := rfl
  rw [hstep_j]
  have hs1' : ((C.gates.drop (j + 1)).map (shiftGate (n + j))).foldl stepWires w1 = w1 ++ suf' := by
    simpa [hw1_len] using hs1
  rw [hs1', hs2]
  have hout' : C.output ≠ w1.length := by rwa [hw1_len]
  simpa [hw1_len] using getD_shift_suffix w1 suf' b C.output hout'

lemma foldl_unused_input (gs : List Gate) (w1 w2 : List Bool) (i : ℕ)
    (hlen : w1.length = w2.length)
    (hag : ∀ k, k ≠ i → w1.getD k false = w2.getD k false)
    (hno : ∀ g ∈ gs, i ∉ g.inputs) :
    (gs.foldl stepWires w1).length = (gs.foldl stepWires w2).length ∧
    ∀ k, k ≠ i → (gs.foldl stepWires w1).getD k false = (gs.foldl stepWires w2).getD k false := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨hlen, hag⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg : i ∉ g.inputs := hno g List.mem_cons_self
    have hbit : g.op.eval (g.inputs.map fun k => w1.getD k false) =
        g.op.eval (g.inputs.map fun k => w2.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact hag k (fun heq => hg (heq ▸ hk))
    apply ih
    · simp [stepWires, hlen]
    · intro k hki
      unfold stepWires
      rw [hbit]
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getElem?_append_left hlt2]
        simpa [List.getD_eq_getElem?_getD] using hag k hki
      · simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega : w1.length ≤ k),
          List.getElem?_append_right (by omega : w2.length ≤ k), hlen]
    · exact fun x hx => hno x (List.mem_cons_of_mem _ hx)

lemma unused_input_eval_eq (n : ℕ) (C : Circuit) (i : Fin n)
    (hout : C.output ≠ i.val)
    (hdead : wireFanOut n C i.val = 0)
    (x : Fin n → Bool) :
    C.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x i (!x i))) := by
  have hno : ∀ g ∈ C.gates, i.val ∉ g.inputs := by
    intro g hg hin
    rw [List.mem_iff_getElem] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    have hcount : 0 < C.gates[j].inputs.count i.val := List.count_pos_iff.mpr hin
    have hzero := Finset.sum_eq_zero_iff.mp hdead ⟨j, hj⟩ (Finset.mem_univ _)
    simp only [show i.val < n + j by omega, ↓reduceIte] at hzero
    omega
  have hres := foldl_unused_input C.gates (List.ofFn x) (List.ofFn (Function.update x i (!x i)))
    i.val (by simp) (by
      intro k hki
      by_cases hk : k < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, ↓reduceDIte]
        have hne : (⟨k, hk⟩ : Fin n) ≠ i := by intro h; apply hki; exact congrArg Fin.val h
        simp [Function.update_of_ne hne]
      · simp [List.getD_eq_getElem?_getD, hk]) hno
  exact hres.2 C.output hout

def permWire (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

lemma permWire_injective (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permWire n σ) := by
  intro a b hab
  unfold permWire at hab
  split_ifs at hab with ha hb hb
  · have hfin : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := Fin.ext hab
    have hfin' := σ.injective hfin
    exact congrArg Fin.val hfin'
  · have := (σ ⟨a, ha⟩).isLt; omega
  · have := (σ ⟨b, hb⟩).isLt; omega
  · exact hab

def permuteCircuit (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (permWire n σ)⟩, permWire n σ C.output⟩

lemma permuteCircuit_size (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (permuteCircuit n σ C).size = C.size := by
  simp [permuteCircuit, Circuit.size]

lemma permuteCircuit_fanInTwo (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (hF : FanInTwo C) :
    FanInTwo (permuteCircuit n σ C) := by
  intro g hg
  simp only [permuteCircuit, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := hF g0 hg0
  exact ⟨hop, by simp [hlen]⟩

lemma permuteCircuit_not_len (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) :
    ∀ g ∈ (permuteCircuit n σ C).gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg hnot
  simp only [permuteCircuit, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa using hNot g0 hg0 hnot

lemma permuteCircuit_notCount (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    notCount (permuteCircuit n σ C) = notCount C := by
  unfold notCount permuteCircuit
  rw [List.filter_map]
  simp only [List.length_map, Function.comp_def]

lemma getD_permWire (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool) (suf : List Bool) (w : ℕ) :
    (List.ofFn x ++ suf).getD (permWire n σ w) false =
    (List.ofFn (x ∘ σ) ++ suf).getD w false := by
  unfold permWire
  split_ifs with h
  · have hlt : (σ ⟨w, h⟩).val < (List.ofFn x).length := by simp
    have hlt2 : w < (List.ofFn (x ∘ σ)).length := by simp [h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
      List.getElem?_append_left hlt2, List.getElem?_ofFn, (σ ⟨w, h⟩).isLt, h, ↓reduceDIte]
    rfl
  · have hge1 : (List.ofFn x).length ≤ w := by simp; omega
    have hge2 : (List.ofFn (x ∘ σ)).length ≤ w := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge1,
      List.getElem?_append_right hge2, List.length_ofFn]

lemma foldl_permuteCircuit (n : ℕ) (σ : Equiv.Perm (Fin n)) (gs : List Gate)
    (x : Fin n → Bool) (suf : List Bool) :
    ∃ suf' : List Bool,
      (gs.map fun g => ⟨g.op, g.inputs.map (permWire n σ)⟩).foldl stepWires (List.ofFn x ++ suf) =
        List.ofFn x ++ suf' ∧
      gs.foldl stepWires (List.ofFn (x ∘ σ) ++ suf) =
        List.ofFn (x ∘ σ) ++ suf' := by
  induction gs generalizing suf with
  | nil => exact ⟨suf, rfl, rfl⟩
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hbit : g.op.eval ((g.inputs.map (permWire n σ)).map fun w => (List.ofFn x ++ suf).getD w false) =
        g.op.eval (g.inputs.map fun w => (List.ofFn (x ∘ σ) ++ suf).getD w false) := by
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro w _
      exact getD_permWire n σ x suf w
    have hs1 : stepWires (List.ofFn x ++ suf) ⟨g.op, g.inputs.map (permWire n σ)⟩ =
        List.ofFn x ++ (suf ++ [g.op.eval (g.inputs.map fun w => (List.ofFn (x ∘ σ) ++ suf).getD w false)]) := by
      unfold stepWires
      rw [hbit, List.append_assoc]
    have hs2 : stepWires (List.ofFn (x ∘ σ) ++ suf) g =
        List.ofFn (x ∘ σ) ++ (suf ++ [g.op.eval (g.inputs.map fun w => (List.ofFn (x ∘ σ) ++ suf).getD w false)]) := by
      unfold stepWires
      rw [List.append_assoc]
    rw [hs1, hs2]
    exact ih _

lemma permuteCircuit_eval (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    (permuteCircuit n σ C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := by
  obtain ⟨suf', hs1, hs2⟩ := foldl_permuteCircuit n σ C.gates x []
  simp only [Circuit.eval, wires_eq_foldl, permuteCircuit]
  simp only [List.append_nil] at hs1 hs2
  rw [hs1, hs2]
  exact getD_permWire n σ x suf' C.output

lemma permuteCircuit_wireFanOut_input (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (i : Fin n) :
    wireFanOut n (permuteCircuit n σ C) (σ i).val = wireFanOut n C i.val := by
  unfold wireFanOut
  have hsz : (permuteCircuit n σ C).size = C.size := permuteCircuit_size n σ C
  refine Finset.sum_bij (fun j _ => ⟨j.val, hsz ▸ j.isLt⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun j _ => ⟨⟨j.val, hsz.symm ▸ j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun j _ => ?_)
  have h1 : (σ i).val < n + j.val := by omega
  have h2 : i.val < n + j.val := by omega
  simp only [h1, h2, ↓reduceIte, permuteCircuit, List.getElem_map]
  have hpw : permWire n σ i.val = (σ i).val := by simp [permWire, i.isLt]
  conv_lhs => rw [← hpw]
  exact List.count_map_of_injective _ _ (permWire_injective n σ) _

lemma permuteCircuit_wireFanOut_gate (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (k : ℕ) :
    wireFanOut n (permuteCircuit n σ C) (n + k) = wireFanOut n C (n + k) := by
  unfold wireFanOut
  have hsz : (permuteCircuit n σ C).size = C.size := permuteCircuit_size n σ C
  refine Finset.sum_bij (fun j _ => ⟨j.val, hsz ▸ j.isLt⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun j _ => ⟨⟨j.val, hsz.symm ▸ j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun j _ => ?_)
  simp only [permuteCircuit, List.getElem_map]
  split_ifs
  · have hpw : permWire n σ (n + k) = n + k := by
      unfold permWire
      split_ifs with h
      · omega
      · rfl
    conv_lhs => rw [← hpw]
    exact List.count_map_of_injective _ _ (permWire_injective n σ) _
  · rfl

def petersenFun (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def petersenRotFun (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0
  | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9 | _ => 5

def petersenRotInv (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3
  | 5 => 9 | 6 => 5 | 7 => 6 | 8 => 7 | _ => 8

def petersenRot : Equiv.Perm (Fin 10) :=
  ⟨petersenRotFun, petersenRotInv, by decide, by decide⟩

def petersenSwapFun (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 5 | 5 => 0
  | 1 => 7 | 7 => 1
  | 4 => 8 | 8 => 4
  | 6 => 9 | 9 => 6
  | 2 => 2 | _ => 3

def petersenSwap : Equiv.Perm (Fin 10) :=
  ⟨petersenSwapFun, petersenSwapFun, by decide, by decide⟩

lemma petersenFun_rot (x : Fin 10 → Bool) :
    petersenFun (x ∘ petersenRot) = petersenFun x := by
  unfold petersenFun
  simp only [Function.comp_apply, petersenRot, Equiv.coe_fn_mk, petersenRotFun]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;>
  cases x 5 <;> cases x 6 <;> cases x 7 <;> cases x 8 <;> cases x 9 <;> rfl

lemma petersenFun_swap (x : Fin 10 → Bool) :
    petersenFun (x ∘ petersenSwap) = petersenFun x := by
  unfold petersenFun
  simp only [Function.comp_apply, petersenSwap, Equiv.coe_fn_mk, petersenSwapFun]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;>
  cases x 5 <;> cases x 6 <;> cases x 7 <;> cases x 8 <;> cases x 9 <;> rfl

def petersenAut (v : Fin 10) : Equiv.Perm (Fin 10) :=
  match v.val with
  | 0 => 1
  | 1 => petersenRot.symm
  | 2 => petersenRot.symm * petersenRot.symm
  | 3 => petersenRot * petersenRot
  | 4 => petersenRot
  | 5 => petersenSwap
  | 6 => petersenSwap * petersenRot.symm
  | 7 => petersenSwap * (petersenRot.symm * petersenRot.symm)
  | 8 => petersenSwap * (petersenRot * petersenRot)
  | _ => petersenSwap * petersenRot

lemma petersenAut_apply (v : Fin 10) : petersenAut v v = 0 := by
  fin_cases v <;> decide

lemma petersenFun_rot_symm (x : Fin 10 → Bool) :
    petersenFun (x ∘ petersenRot.symm) = petersenFun x := by
  have h := petersenFun_rot (x ∘ petersenRot.symm)
  have hcomp : (x ∘ petersenRot.symm) ∘ petersenRot = x := by
    funext i; simp
  rw [hcomp] at h
  exact h.symm

lemma petersenFun_aut (v : Fin 10) (x : Fin 10 → Bool) :
    petersenFun (x ∘ petersenAut v) = petersenFun x := by
  fin_cases v
  · rfl
  · exact petersenFun_rot_symm x
  · change petersenFun ((x ∘ petersenRot.symm) ∘ petersenRot.symm) = petersenFun x
    rw [petersenFun_rot_symm, petersenFun_rot_symm]
  · change petersenFun ((x ∘ petersenRot) ∘ petersenRot) = petersenFun x
    rw [petersenFun_rot, petersenFun_rot]
  · exact petersenFun_rot x
  · exact petersenFun_swap x
  · change petersenFun ((x ∘ petersenSwap) ∘ petersenRot.symm) = petersenFun x
    rw [petersenFun_rot_symm, petersenFun_swap]
  · change petersenFun (((x ∘ petersenSwap) ∘ petersenRot.symm) ∘ petersenRot.symm) = petersenFun x
    rw [petersenFun_rot_symm, petersenFun_rot_symm, petersenFun_swap]
  · change petersenFun (((x ∘ petersenSwap) ∘ petersenRot) ∘ petersenRot) = petersenFun x
    rw [petersenFun_rot, petersenFun_rot, petersenFun_swap]
  · change petersenFun ((x ∘ petersenSwap) ∘ petersenRot) = petersenFun x
    rw [petersenFun_rot, petersenFun_swap]

def petersenNbr (v : Fin 10) : Fin 10 :=
  match v.val with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0
  | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 5 | _ => 6

lemma petersenFun_essential (v : Fin 10) :
    ∃ x : Fin 10 → Bool, petersenFun x ≠ petersenFun (Function.update x v (!x v)) := by
  refine ⟨fun i => decide (i = petersenNbr v), ?_⟩
  fin_cases v <;> decide

lemma petersenFun_not_false : ∃ x : Fin 10 → Bool, petersenFun x ≠ false :=
  ⟨fun i => decide (i = 0 ∨ i = 1), by decide⟩

lemma petersenFun_not_proj (i : Fin 10) : ∃ x : Fin 10 → Bool, petersenFun x ≠ x i := by
  refine ⟨fun j => decide (j = i), ?_⟩
  fin_cases i <;> decide

lemma minimal_circuit_exists (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n f s) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) ∧
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ C' : Circuit, FanInTwo C' → (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = f x) →
        C.size ≤ C'.size) := by
  classical
  have hex : ∃ m : ℕ, ∃ C : Circuit, FanInTwo C ∧ C.size = m ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
    obtain ⟨C, hF, hle, hev⟩ := h
    exact ⟨C.size, C, hF, rfl, hev⟩
  let m := Nat.find hex
  have hm_spec := Nat.find_spec hex
  have hm_le : m ≤ s := by
    obtain ⟨C, hF, hle, hev⟩ := h
    exact le_trans (Nat.find_min' hex ⟨C, hF, rfl, hev⟩) hle
  obtain ⟨C0, hF0, hsz0, hev0⟩ := hm_spec
  refine ⟨trimNots C0, trimNots_fanInTwo C0 hF0, by rw [trimNots_size, hsz0]; exact hm_le,
    fun x => by rw [trimNots_eval, hev0], trimNots_not_len C0, ?_⟩
  intro C' hF' hev'
  rw [trimNots_size, hsz0]
  exact Nat.find_min' hex ⟨C', hF', rfl, hev'⟩

lemma minimal_output_is_gate (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnotfalse : ∃ x : Fin n → Bool, f x ≠ false)
    (hnotproj : ∀ i : Fin n, ∃ x : Fin n → Bool, f x ≠ x i) :
    n ≤ C.output ∧ C.output < n + C.size := by
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨x, hx⟩ := hnotproj ⟨C.output, hlt⟩
    apply hx
    rw [← hev x]
    unfold Circuit.eval
    obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix C.gates (List.ofFn x)
    rw [wires_eq_foldl, hsuf]
    have hlt' : C.output < (List.ofFn x).length := by simp [hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt', List.getElem?_ofFn,
      hlt, ↓reduceDIte]
    rfl
  · by_contra hge
    push Not at hge
    obtain ⟨x, hx⟩ := hnotfalse
    apply hx
    rw [← hev x]
    unfold Circuit.eval
    have hlen : (C.wires (List.ofFn x)).length ≤ C.output := by
      rw [wires_length, List.length_ofFn]; exact hge
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

lemma minimal_no_dead_gate (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hF : FanInTwo C)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hmin : ∀ C' : Circuit, FanInTwo C' → (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = f x) →
      C.size ≤ C'.size)
    (j : Fin C.size) (hout : n + j.val ≠ C.output) :
    1 ≤ wireFanOut n C (n + j.val) := by
  by_contra hlt
  have hzero : wireFanOut n C (n + j.val) = 0 := by omega
  have hle := hmin (deleteGate n C j.val) (deleteGate_fanInTwo n C j.val hF) (fun x => by
    rw [deleteGate_eval n C j.val j.isLt (Ne.symm hout) hzero (List.ofFn x) (by simp), hev])
  rw [deleteGate_size n C j.val j.isLt] at hle
  have hjpos : 0 < C.size := Nat.zero_lt_of_lt j.isLt
  omega

lemma minimal_input_fanout_pos (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hout : n ≤ C.output)
    (hess : ∀ i : Fin n, ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))
    (i : Fin n) :
    1 ≤ wireFanOut n C i.val := by
  by_contra hlt
  have hzero : wireFanOut n C i.val = 0 := by omega
  obtain ⟨x, hx⟩ := hess i
  apply hx
  rw [← hev x, ← hev (Function.update x i (!x i))]
  exact unused_input_eval_eq n C i (by omega) hzero x

theorem wire_budget_minimal (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hF : FanInTwo C)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hmin : ∀ C' : Circuit, FanInTwo C' → (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = f x) →
      C.size ≤ C'.size)
    (hnotfalse : ∃ x : Fin n → Bool, f x ≠ false)
    (hnotproj : ∀ i : Fin n, ∃ x : Fin n → Bool, f x ≠ x i) :
    (∑ i : Fin n, wireFanOut n C i.val) +
    notCount C +
    (∑ j : Fin C.size, if n + j.val = C.output then 0 else wireFanOut n C (n + j.val) - 1) ≤
      C.size + 1 := by
  obtain ⟨hout_ge, hout_lt⟩ := minimal_output_is_gate n f C hev hnotfalse hnotproj
  have hraw := wire_budget_raw n C hF hNot
  have hgate_sum :
      (∑ j : Fin C.size, wireFanOut n C (n + j.val)) ≥
      (C.size - 1) +
      (∑ j : Fin C.size, if n + j.val = C.output then 0 else wireFanOut n C (n + j.val) - 1) := by
    have hcard : (∑ j : Fin C.size, if n + j.val = C.output then 0 else 1) = C.size - 1 := by
      have hout_j : C.output - n < C.size := by omega
      let j0 : Fin C.size := ⟨C.output - n, hout_j⟩
      have hite : ∀ j : Fin C.size,
          (if n + j.val = C.output then (0 : ℕ) else 1) = (if j = j0 then 0 else 1) := by
        intro j
        by_cases h : j = j0
        · subst h; simp [j0]; omega
        · have hne : n + j.val ≠ C.output := by
            intro heq; apply h; ext; dsimp [j0]; omega
          simp [h, hne]
      simp_rw [hite]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
      have hfilt : (Finset.univ.filter fun j : Fin C.size => ¬ j = j0) = Finset.univ.erase j0 := by
        ext j; simp
      rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
    rw [← hcard, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : n + j.val = C.output
    · simp [h]
    · have hpos := minimal_no_dead_gate n f C hF hev hmin j h
      simp only [h, ↓reduceIte]
      omega
  have hpos_sz : 1 ≤ C.size := by omega
  omega


-- Calibration facts for World 1.

/-- Cover circuit, cover {0,1,3,7,8,9}; x 0 appears only in gate 2 = x0 ∧ (x1 ∨ x4 ∨ x5). -/
def c20 : Circuit := ⟨[
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [10, 5]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [1, 13]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [15, 8]⟩,
    ⟨GateOp.and, [3, 16]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [18, 9]⟩,
    ⟨GateOp.and, [7, 19]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.and, [8, 21]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.and, [9, 23]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.or, [25, 17]⟩,
    ⟨GateOp.or, [26, 20]⟩,
    ⟨GateOp.or, [27, 22]⟩,
    ⟨GateOp.or, [28, 24]⟩], 29⟩

/-- Cover circuit for Petersen minus vertex 0, cover {1,3,7,8,9}. -/
def c16 : Circuit := ⟨[
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [1, 10]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [12, 8]⟩,
    ⟨GateOp.and, [3, 13]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [15, 9]⟩,
    ⟨GateOp.and, [7, 16]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.and, [8, 18]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.and, [9, 20]⟩,
    ⟨GateOp.or, [11, 14]⟩,
    ⟨GateOp.or, [22, 17]⟩,
    ⟨GateOp.or, [23, 19]⟩,
    ⟨GateOp.or, [24, 21]⟩], 25⟩

lemma ofFn10 (x : Fin 10 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
  simp [List.ofFn_succ]

set_option maxHeartbeats 4000000 in
lemma c20_eval_all : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
    c20.eval [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] =
      ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
       (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a4 && a9) ||
       (a5 && a7) || (a7 && a9) || (a9 && a6) || (a6 && a8) || (a8 && a5)) := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
    cases a5 <;> cases a6 <;> cases a7 <;> cases a8 <;> cases a9 <;> rfl

set_option maxHeartbeats 4000000 in
lemma c16_eval_all : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
    c16.eval [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] =
      ((false && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && false) ||
       (false && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a4 && a9) ||
       (a5 && a7) || (a7 && a9) || (a9 && a6) || (a6 && a8) || (a8 && a5)) := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
    cases a5 <;> cases a6 <;> cases a7 <;> cases a8 <;> cases a9 <;> rfl

lemma c20_fanInTwo : FanInTwo c20 := by
  intro g hg
  simp only [c20, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

lemma c16_fanInTwo : FanInTwo c16 := by
  intro g hg
  simp only [c16, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

/-- World 1 is inhabited at size 20. -/
theorem world1_tight :
    ∃ C : Circuit, FanInTwo C ∧ C.size = 20 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧
      wireFanOut 10 C 0 = 1 := by
  refine ⟨c20, c20_fanInTwo, rfl, ?_, by decide⟩
  intro x
  rw [ofFn10, c20_eval_all]
  rfl

/-- Fixing x 0 := false leaves a function with a 16-gate circuit. -/
theorem restrict0_upper16 :
    HasCircuitSize 10 (fun x => petersenFun (Function.update x 0 false)) 16 := by
  refine ⟨c16, c16_fanInTwo, le_refl _, ?_⟩
  intro x
  rw [ofFn10, c16_eval_all]
  simp [petersenFun, Function.update]


-- Part 2. Petersen minus vertex 0 (vertices 1..9 renamed 0..8), at size 15.

def p0Fun (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 5) || (x 1 && x 6) ||
  (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 6) || (x 6 && x 8) || (x 8 && x 5) ||
  (x 5 && x 7) || (x 7 && x 4)

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

/-- A circuit of at most 15 gates for Petersen minus a vertex, chosen of least size, reads at
least two distinct inputs exactly once: 9 essential inputs, each read at least once, with at
most 16 input reads in total, give k + 2(9 - k) ≤ 16, so k ≥ 2. -/
theorem p0_size15_two_read_once (h : HasCircuitSize 9 p0Fun 15) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 15 ∧
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = p0Fun x) ∧
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ C' : Circuit, FanInTwo C' → (∀ x : Fin 9 → Bool, C'.eval (List.ofFn x) = p0Fun x) →
        C.size ≤ C'.size) ∧
      ∃ u v : Fin 9, u ≠ v ∧ wireFanOut 9 C u.val = 1 ∧ wireFanOut 9 C v.val = 1 := by
  obtain ⟨C, hF, hle, hev, hNot, hmin⟩ := minimal_circuit_exists 9 15 p0Fun h
  have hbud := wire_budget_minimal 9 p0Fun C hF hNot hev hmin p0Fun_not_false p0Fun_not_proj
  obtain ⟨hout_ge, _⟩ := minimal_output_is_gate 9 p0Fun C hev p0Fun_not_false p0Fun_not_proj
  have hpos : ∀ i : Fin 9, 1 ≤ wireFanOut 9 C i.val :=
    minimal_input_fanout_pos 9 p0Fun C hev hout_ge p0Fun_essential
  have hsum : (∑ i : Fin 9, wireFanOut 9 C i.val) ≤ 16 := by omega
  have hlow : ∀ i : Fin 9,
      (if wireFanOut 9 C i.val = 1 then 1 else 2) ≤ wireFanOut 9 C i.val := by
    intro i
    have := hpos i
    split_ifs <;> omega
  have hge : (∑ i : Fin 9, (if wireFanOut 9 C i.val = 1 then 1 else 2)) ≤ 16 :=
    le_trans (Finset.sum_le_sum fun i _ => hlow i) hsum
  have hcalc : (∑ i : Fin 9, (if wireFanOut 9 C i.val = 1 then 1 else 2)) =
      (Finset.univ.filter (fun i : Fin 9 => wireFanOut 9 C i.val = 1)).card +
      2 * (Finset.univ.filter (fun i : Fin 9 => ¬ wireFanOut 9 C i.val = 1)).card := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    ring
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 9))) (fun i : Fin 9 => wireFanOut 9 C i.val = 1)
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have hcard : 1 < (Finset.univ.filter (fun i : Fin 9 => wireFanOut 9 C i.val = 1)).card := by
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_filter] at hu hv
  exact ⟨C, hF, hle, hev, hNot, hmin, u, v, huv, hu.2, hv.2⟩

-- Part 1. Fixing an input read by one gate.

def isBasis (op : GateOp) : Prop := op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not

lemma basis_of_mem {C : Circuit} (hF : FanInTwo C) {g : Gate} (hg : g ∈ C.gates) :
    isBasis g.op ∧ g.inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hF g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, h2⟩

lemma getD_append_left' (l1 l2 : List Bool) (w : ℕ) (h : w < l1.length) :
    (l1 ++ l2).getD w false = l1.getD w false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- The gate `g` with its reads of wire `w` replaced by the constant `c`. -/
def substGate (w : ℕ) (c : Bool) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
    if w ∈ g.inputs then
      (if c then ⟨GateOp.and, g.inputs.filter (fun v => v != w)⟩ else ⟨GateOp.or, []⟩)
    else g
  | GateOp.or =>
    if w ∈ g.inputs then
      (if c then ⟨GateOp.and, []⟩ else ⟨GateOp.or, g.inputs.filter (fun v => v != w)⟩)
    else g
  | GateOp.not =>
    if g.inputs.head? = some w then
      (if c then ⟨GateOp.or, []⟩ else ⟨GateOp.and, []⟩)
    else ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma all_filter_ne (l : List ℕ) (vals : ℕ → Bool) (w : ℕ) (hv : vals w = true) :
    ((l.filter (fun v => v != w)).map vals).all id = (l.map vals).all id := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = w
    · subst ha
      simp [List.filter_cons, hv, ih]
    · simp [List.filter_cons, ha, ih]

lemma any_filter_ne (l : List ℕ) (vals : ℕ → Bool) (w : ℕ) (hv : vals w = false) :
    ((l.filter (fun v => v != w)).map vals).any id = (l.map vals).any id := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = w
    · subst ha
      simp [List.filter_cons, hv, ih]
    · simp [List.filter_cons, ha, ih]

lemma substGate_eval (w : ℕ) (c : Bool) (g : Gate) (vals : ℕ → Bool) (hv : vals w = c)
    (hop : isBasis g.op) :
    (substGate w c g).op.eval ((substGate w c g).inputs.map vals) =
      g.op.eval (g.inputs.map vals) := by
  obtain ⟨op, l⟩ := g
  rcases hop with h | h | h <;> simp only at h <;> subst h
  · by_cases hw : w ∈ l
    · cases c
      · simp only [substGate, hw, if_true, Bool.false_eq_true, if_false, GateOp.eval,
          List.map_nil, List.any_nil]
        symm
        rw [Bool.eq_false_iff]
        intro hall
        rw [List.all_eq_true] at hall
        have := hall (vals w) (List.mem_map.mpr ⟨w, hw, rfl⟩)
        simp [hv] at this
      · simp only [substGate, hw, if_true, GateOp.eval]
        exact all_filter_ne l vals w hv
    · simp [substGate, hw]
  · by_cases hw : w ∈ l
    · cases c
      · simp only [substGate, hw, if_true, Bool.false_eq_true, if_false, GateOp.eval]
        exact any_filter_ne l vals w hv
      · simp only [substGate, hw, if_true, GateOp.eval, List.map_nil, List.all_nil]
        symm
        rw [List.any_eq_true]
        exact ⟨vals w, List.mem_map.mpr ⟨w, hw, rfl⟩, by simp [hv]⟩
    · simp [substGate, hw]
  · cases l with
    | nil => simp [substGate, GateOp.eval]
    | cons a t =>
      by_cases ha : a = w
      · subst ha
        cases c <;> simp [substGate, GateOp.eval, hv]
      · simp [substGate, GateOp.eval, ha]

lemma substGate_not_mem (w : ℕ) (c : Bool) (g : Gate) (hop : isBasis g.op) :
    w ∉ (substGate w c g).inputs := by
  obtain ⟨op, l⟩ := g
  rcases hop with h | h | h <;> simp only at h <;> subst h
  · by_cases hw : w ∈ l
    · cases c <;> simp [substGate, hw, List.mem_filter]
    · simp [substGate, hw]
  · by_cases hw : w ∈ l
    · cases c <;> simp [substGate, hw, List.mem_filter]
    · simp [substGate, hw]
  · cases l with
    | nil => simp [substGate]
    | cons a t =>
      by_cases ha : a = w
      · subst ha
        cases c <;> simp [substGate]
      · simp [substGate, ha, Ne.symm ha]

lemma substGate_basis (w : ℕ) (c : Bool) (g : Gate) (hop : isBasis g.op) :
    isBasis (substGate w c g).op ∧ (substGate w c g).inputs.length ≤ g.inputs.length := by
  obtain ⟨op, l⟩ := g
  rcases hop with h | h | h <;> simp only at h <;> subst h
  · by_cases hw : w ∈ l
    · cases c
      · simp [substGate, hw, isBasis]
      · simp only [substGate, hw, if_true]
        exact ⟨by simp [isBasis], List.length_filter_le _ _⟩
    · simp [substGate, hw, isBasis]
  · by_cases hw : w ∈ l
    · cases c
      · simp only [substGate, hw, if_true, Bool.false_eq_true, if_false]
        exact ⟨by simp [isBasis], List.length_filter_le _ _⟩
      · simp [substGate, hw, isBasis]
    · simp [substGate, hw, isBasis]
  · cases l with
    | nil => simp [substGate, isBasis]
    | cons a t =>
      by_cases ha : a = w
      · subst ha
        cases c <;> simp [substGate, isBasis]
      · simp [substGate, ha, isBasis]

/-- A gate of the basis that reads `w`, with at most two inputs (one for NOT), becomes an
AND or OR gate with at most one input after `w` is fixed. -/
lemma substGate_shape (w : ℕ) (c : Bool) (g : Gate) (hop : isBasis g.op)
    (hlen : g.inputs.length ≤ 2) (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (hw : w ∈ g.inputs) :
    ((substGate w c g).op = GateOp.and ∨ (substGate w c g).op = GateOp.or) ∧
      (substGate w c g).inputs.length ≤ 1 := by
  obtain ⟨op, l⟩ := g
  simp only at hlen hnot hw
  have hlt : (l.filter (fun v => v != w)).length < l.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨w, hw, by simp⟩
  rcases hop with h | h | h <;> simp only at h <;> subst h
  · cases c
    · simp [substGate, hw]
    · simp only [substGate, hw, if_true]
      exact ⟨by simp, by omega⟩
  · cases c
    · simp only [substGate, hw, if_true, Bool.false_eq_true, if_false]
      exact ⟨by simp, by omega⟩
    · simp [substGate, hw]
  · have h1 := hnot rfl
    cases l with
    | nil => simp at hw
    | cons a t =>
      have ht : t = [] := by
        cases t with
        | nil => rfl
        | cons _ _ => simp at h1
      subst ht
      have ha : a = w := by simp at hw; exact hw.symm
      subst ha
      cases c <;> simp [substGate]

lemma substGate_of_not_mem (w : ℕ) (c : Bool) (g : Gate) (hop : isBasis g.op)
    (hnot : g.op = GateOp.not → g.inputs.length ≤ 1) (hw : w ∉ g.inputs) :
    substGate w c g = g := by
  obtain ⟨op, l⟩ := g
  simp only at hnot hw
  rcases hop with h | h | h <;> simp only at h <;> subst h
  · simp [substGate, hw]
  · simp [substGate, hw]
  · have h1 := hnot rfl
    cases l with
    | nil => simp [substGate]
    | cons a t =>
      have ht : t = [] := by
        cases t with
        | nil => rfl
        | cons _ _ => simp at h1
      subst ht
      have ha : a ≠ w := by intro h; apply hw; simp [h]
      simp [substGate, ha]

/-- An AND gate reading `w` with `w` fixed to false, or an OR gate with `w` fixed to true,
becomes the constant `c`. -/
lemma substGate_const (w : ℕ) (c : Bool) (g : Gate) (hw : w ∈ g.inputs)
    (hab : (g.op = GateOp.and ∧ c = false) ∨ (g.op = GateOp.or ∧ c = true)) (vals : ℕ → Bool) :
    (substGate w c g).op.eval ((substGate w c g).inputs.map vals) = c := by
  obtain ⟨op, l⟩ := g
  simp only at hw hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [substGate, hw, GateOp.eval]

/-- Fix wire `w` to `c` in every gate that may read it (gate `k` reads only wires below `n + k`). -/
def substAt (n w : ℕ) (c : Bool) (C : Circuit) : Circuit :=
  ⟨C.gates.mapIdx (fun k g => if w < n + k then substGate w c g else g), C.output⟩

lemma substAt_size (n w : ℕ) (c : Bool) (C : Circuit) : (substAt n w c C).size = C.size := by
  simp [substAt, Circuit.size]

lemma substAt_getElem (n w : ℕ) (c : Bool) (C : Circuit) (k : ℕ)
    (h : k < (substAt n w c C).gates.length) :
    (substAt n w c C).gates[k]'h =
      if w < n + k then substGate w c (C.gates[k]'(by simpa [substAt] using h))
      else C.gates[k]'(by simpa [substAt] using h) := by
  simp [substAt]

lemma foldl_mapIdx_len (F : ℕ → Gate → Gate) (gs : List Gate) :
    ∀ (acc : List Bool) (m : ℕ) (f : ℕ → Gate → Gate), (∀ k g, f k g = F (m + k) g) →
      acc.length = m →
      (gs.mapIdx f).foldl stepWires acc = gs.foldl (fun a g => stepWires a (F a.length g)) acc := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro acc m f hf hm
    rw [List.mapIdx_cons, List.foldl_cons, List.foldl_cons]
    have h0 : f 0 g = F acc.length g := by rw [hf, hm, Nat.add_zero]
    rw [h0]
    apply ih (stepWires acc (F acc.length g)) (m + 1) (fun i => f (i + 1))
    · intro k g'
      rw [hf]
      congr 1
      omega
    · simp [stepWires, hm]

lemma foldl_subst_eq (w : ℕ) (c : Bool) (gs : List Gate) :
    ∀ acc : List Bool, (∀ g ∈ gs, isBasis g.op) →
      (gs.foldl stepWires acc).getD w false = c →
      gs.foldl (fun a g => stepWires a (if w < a.length then substGate w c g else g)) acc =
        gs.foldl stepWires acc := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro acc hb hfin
    simp only [List.foldl_cons] at hfin ⊢
    have hstep : stepWires acc (if w < acc.length then substGate w c g else g) =
        stepWires acc g := by
      split_ifs with hlt
      · obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix gs (stepWires acc g)
        have hacc : acc.getD w false = c := by
          rw [hsuf] at hfin
          unfold stepWires at hfin
          rwa [List.append_assoc, getD_append_left' _ _ _ hlt] at hfin
        unfold stepWires
        rw [substGate_eval w c g (fun i => acc.getD i false) hacc (hb g List.mem_cons_self)]
      · rfl
    rw [hstep]
    exact ih (stepWires acc g) (fun g' hg' => hb g' (List.mem_cons_of_mem _ hg')) hfin

lemma substAt_wires (n w : ℕ) (c : Bool) (C : Circuit) (hF : FanInTwo C) (x : List Bool)
    (hx : x.length = n) (hc : (C.wires x).getD w false = c) :
    (substAt n w c C).wires x = C.wires x := by
  have hb : ∀ g ∈ C.gates, isBasis g.op := fun g hg => (basis_of_mem hF hg).1
  rw [wires_eq_foldl, wires_eq_foldl]
  change (C.gates.mapIdx (fun k g => if w < n + k then substGate w c g else g)).foldl
    stepWires x = _
  rw [foldl_mapIdx_len (fun L g => if w < L then substGate w c g else g) C.gates x n _
    (fun k g => rfl) hx]
  exact foldl_subst_eq w c C.gates x hb (by rw [← wires_eq_foldl]; exact hc)

lemma substAt_fanInTwo (n w : ℕ) (c : Bool) (C : Circuit) (hF : FanInTwo C) :
    FanInTwo (substAt n w c C) := by
  intro g hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' : k < C.size := by simpa [substAt, Circuit.size] using hk
  rw [substAt_getElem n w c C k]
  have hm := basis_of_mem hF (List.getElem_mem hk')
  split_ifs
  · have hs := substGate_basis w c _ hm.1
    refine ⟨?_, by omega⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hs.1
  · exact hF _ (List.getElem_mem hk')

lemma substAt_dead (n w : ℕ) (c : Bool) (C : Circuit) (hF : FanInTwo C) :
    wireFanOut n (substAt n w c C) w = 0 := by
  unfold wireFanOut
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hlt
  · have hk' : k.val < C.size := by simpa [substAt_size] using k.isLt
    rw [substAt_getElem n w c C k.val, if_pos hlt]
    exact List.count_eq_zero.mpr
      (substGate_not_mem w c _ (basis_of_mem hF (List.getElem_mem hk')).1)
  · rfl

/-- The value of gate `j` from the values of the wires below it. -/
lemma wire_gate_value (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size) (x : List Bool)
    (hx : x.length = n) :
    (C.wires x).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun v =>
        if v < n + j then (C.wires x).getD v false else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm
  set w1 := (C.gates.take j).foldl stepWires x with hw1
  have hw1_len : w1.length = n + j := by
    rw [hw1, foldl_stepWires_length, hx, List.length_take_of_le (Nat.le_of_lt hj)]
  obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix (C.gates.drop (j + 1)) (stepWires w1 C.gates[j])
  have hwires : C.wires x = w1 ++ (C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
      w1.getD i false) :: suf) := by
    rw [wires_eq_foldl]
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [hsuf]
    simp [stepWires]
  have hval : (C.wires x).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => w1.getD i false) := by
    rw [hwires, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hw1_len,
      Nat.sub_self]
    rfl
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro v _
  split_ifs with hv
  · rw [hwires, getD_append_left' _ _ _ (by omega)]
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl

/-- An AND or OR gate with at most one input is constant, or a copy of a wire below it. -/
lemma gate_const_or_copy (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size)
    (hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or)
    (hlen : C.gates[j].inputs.length ≤ 1) :
    (∃ c : Bool, ∀ x : List Bool, x.length = n → (C.wires x).getD (n + j) false = c) ∨
    (∃ y, y < n + j ∧ ∀ x : List Bool, x.length = n →
      (C.wires x).getD (n + j) false = (C.wires x).getD y false) := by
  rcases hl : C.gates[j].inputs with _ | ⟨y, _ | ⟨z, t⟩⟩
  · left
    rcases hop with h | h
    · exact ⟨true, fun x hx => by rw [wire_gate_value n C j hj x hx, hl, h]; rfl⟩
    · exact ⟨false, fun x hx => by rw [wire_gate_value n C j hj x hx, hl, h]; rfl⟩
  · by_cases hy : y < n + j
    · right
      refine ⟨y, hy, fun x hx => ?_⟩
      rw [wire_gate_value n C j hj x hx, hl]
      rcases hop with h | h <;> simp [h, GateOp.eval, hy]
    · left
      refine ⟨false, fun x hx => ?_⟩
      rw [wire_gate_value n C j hj x hx, hl]
      rcases hop with h | h <;> simp [h, GateOp.eval, hy]
  · rw [hl] at hlen
    simp at hlen

/-- Wires below a deleted gate keep their values. -/
lemma deleteGate_prefix (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size) (x : List Bool)
    (hx : x.length = n) (m : ℕ) (hm : m < n + j) :
    ((deleteGate n C j).wires x).getD m false = (C.wires x).getD m false := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm
  have herase : C.gates.eraseIdx j = C.gates.take j ++ C.gates.drop (j + 1) := by
    rw [List.eraseIdx_eq_take_drop_succ]
  have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  set w1 := (C.gates.take j).foldl stepWires x with hw1
  have hw1_len : w1.length = n + j := by rw [hw1, foldl_stepWires_length, hx, htake_len]
  have hpref : ((C.gates.take j).map (shiftGate (n + j))).foldl stepWires x = w1 :=
    foldl_shift_prefix (C.gates.take j) x (n + j) (by rw [hx, htake_len])
  have hL : (deleteGate n C j).wires x =
      ((C.gates.drop (j + 1)).map (shiftGate (n + j))).foldl stepWires w1 := by
    simp only [wires_eq_foldl, deleteGate]
    rw [herase, List.map_append, List.foldl_append, hpref]
  have hR : C.wires x = (C.gates[j] :: C.gates.drop (j + 1)).foldl stepWires w1 := by
    rw [wires_eq_foldl]
    conv_lhs => rw [hsplit, List.foldl_append]
  obtain ⟨s1, hs1, _⟩ := foldl_stepWires_prefix ((C.gates.drop (j + 1)).map (shiftGate (n + j))) w1
  obtain ⟨s2, hs2, _⟩ := foldl_stepWires_prefix (C.gates[j] :: C.gates.drop (j + 1)) w1
  rw [hL, hR, hs1, hs2, getD_append_left' _ _ _ (by omega), getD_append_left' _ _ _ (by omega)]

/-- A gate that is constant on every input and is not the output can be removed. -/
theorem elim_const_gate (n : ℕ) (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.size)
    (c : Bool) (hout : C.output ≠ n + j)
    (hc : ∀ x : List Bool, x.length = n → (C.wires x).getD (n + j) false = c) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size - 1 ∧
      (∀ x : List Bool, x.length = n → C'.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = n → ∀ m < n + j,
        (C'.wires x).getD m false = (C.wires x).getD m false) := by
  have hw1 : ∀ x : List Bool, x.length = n → (substAt n (n + j) c C).wires x = C.wires x :=
    fun x hx => substAt_wires n (n + j) c C hF x hx (hc x hx)
  have hj1 : j < (substAt n (n + j) c C).size := by rw [substAt_size]; exact hj
  refine ⟨deleteGate n (substAt n (n + j) c C) j,
    deleteGate_fanInTwo n _ j (substAt_fanInTwo n (n + j) c C hF), ?_, ?_, ?_⟩
  · rw [deleteGate_size n _ j hj1, substAt_size]
  · intro x hx
    rw [deleteGate_eval n _ j hj1 hout (substAt_dead n (n + j) c C hF) x hx]
    unfold Circuit.eval
    rw [hw1 x hx]
    rfl
  · intro x hx m hm
    rw [deleteGate_prefix n _ j hj1 x hx m hm, hw1 x hx]

/-- Redirect every read of wire `w` (by gates above it, and by the output) to wire `y`. -/
def redirAt (n w y : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.mapIdx (fun k g => if w < n + k then
      (⟨g.op, g.inputs.map (fun v => if v = w then y else v)⟩ : Gate) else g),
    if C.output = w then y else C.output⟩

lemma redirAt_size (n w y : ℕ) (C : Circuit) : (redirAt n w y C).size = C.size := by
  simp [redirAt, Circuit.size]

lemma redirAt_getElem (n w y : ℕ) (C : Circuit) (k : ℕ)
    (h : k < (redirAt n w y C).gates.length) :
    (redirAt n w y C).gates[k]'h =
      if w < n + k then (⟨(C.gates[k]'(by simpa [redirAt] using h)).op,
        (C.gates[k]'(by simpa [redirAt] using h)).inputs.map
          (fun v => if v = w then y else v)⟩ : Gate)
      else C.gates[k]'(by simpa [redirAt] using h) := by
  simp [redirAt]

lemma foldl_redir_eq (w y : ℕ) (hy : y < w) (gs : List Gate) :
    ∀ acc : List Bool,
      (gs.foldl stepWires acc).getD w false = (gs.foldl stepWires acc).getD y false →
      gs.foldl (fun a g => stepWires a (if w < a.length then
          (⟨g.op, g.inputs.map (fun v => if v = w then y else v)⟩ : Gate) else g)) acc =
        gs.foldl stepWires acc := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro acc hfin
    simp only [List.foldl_cons] at hfin ⊢
    have hstep : stepWires acc (if w < acc.length then
        (⟨g.op, g.inputs.map (fun v => if v = w then y else v)⟩ : Gate) else g) =
        stepWires acc g := by
      split_ifs with hlt
      · obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix gs (stepWires acc g)
        have hacc : acc.getD w false = acc.getD y false := by
          rw [hsuf] at hfin
          unfold stepWires at hfin
          rwa [List.append_assoc, getD_append_left' _ _ _ hlt,
            getD_append_left' _ _ _ (by omega)] at hfin
        unfold stepWires
        simp only [List.map_map]
        congr 3
        apply List.map_congr_left
        intro v _
        simp only [Function.comp]
        split_ifs with hv
        · rw [hv, hacc]
        · rfl
      · rfl
    rw [hstep]
    exact ih (stepWires acc g) hfin

lemma redirAt_wires (n w y : ℕ) (hy : y < w) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hcopy : (C.wires x).getD w false = (C.wires x).getD y false) :
    (redirAt n w y C).wires x = C.wires x := by
  rw [wires_eq_foldl, wires_eq_foldl]
  change (C.gates.mapIdx (fun k g => if w < n + k then
      (⟨g.op, g.inputs.map (fun v => if v = w then y else v)⟩ : Gate) else g)).foldl
    stepWires x = _
  rw [foldl_mapIdx_len (fun L g => if w < L then
      (⟨g.op, g.inputs.map (fun v => if v = w then y else v)⟩ : Gate) else g) C.gates x n _
    (fun k g => rfl) hx]
  exact foldl_redir_eq w y hy C.gates x (by rw [← wires_eq_foldl]; exact hcopy)

lemma redirAt_fanInTwo (n w y : ℕ) (C : Circuit) (hF : FanInTwo C) :
    FanInTwo (redirAt n w y C) := by
  intro g hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' : k < C.size := by simpa [redirAt, Circuit.size] using hk
  rw [redirAt_getElem n w y C k]
  have hm := hF _ (List.getElem_mem hk')
  split_ifs
  · exact ⟨hm.1, by rw [List.length_map]; exact hm.2⟩
  · exact hm

lemma redirAt_dead (n w y : ℕ) (hy : y < w) (C : Circuit) :
    wireFanOut n (redirAt n w y C) w = 0 := by
  unfold wireFanOut
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hlt
  · have hk' : k.val < C.size := by simpa [redirAt_size] using k.isLt
    rw [redirAt_getElem n w y C k.val, if_pos hlt]
    apply List.count_eq_zero.mpr
    simp only [List.mem_map, not_exists, not_and]
    intro v _ hv
    split_ifs at hv with h
    · omega
    · exact h hv
  · rfl

/-- A gate that copies a wire below it can be removed. -/
theorem elim_copy_gate (n : ℕ) (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.size)
    (y : ℕ) (hy : y < n + j)
    (hcopy : ∀ x : List Bool, x.length = n →
      (C.wires x).getD (n + j) false = (C.wires x).getD y false) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size - 1 ∧
      (∀ x : List Bool, x.length = n → C'.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = n → ∀ m < n + j,
        (C'.wires x).getD m false = (C.wires x).getD m false) := by
  have hw1 : ∀ x : List Bool, x.length = n → (redirAt n (n + j) y C).wires x = C.wires x :=
    fun x hx => redirAt_wires n (n + j) y hy C x hx (hcopy x hx)
  have hj1 : j < (redirAt n (n + j) y C).size := by rw [redirAt_size]; exact hj
  have hout : (redirAt n (n + j) y C).output ≠ n + j := by
    simp only [redirAt]
    split_ifs <;> omega
  refine ⟨deleteGate n (redirAt n (n + j) y C) j,
    deleteGate_fanInTwo n _ j (redirAt_fanInTwo n (n + j) y C hF), ?_, ?_, ?_⟩
  · rw [deleteGate_size n _ j hj1, redirAt_size]
  · intro x hx
    rw [deleteGate_eval n _ j hj1 hout (redirAt_dead n (n + j) y hy C) x hx]
    unfold Circuit.eval
    rw [hw1 x hx]
    simp only [redirAt]
    split_ifs with h
    · rw [h, hcopy x hx]
    · rfl
  · intro x hx m hm
    rw [deleteGate_prefix n _ j hj1 x hx m hm, hw1 x hx]

/-- In a circuit whose function is not constant, an AND or OR gate with at most one input
can be removed. -/
theorem elim_small_gate (n : ℕ) (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.size)
    (hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or)
    (hlen : C.gates[j].inputs.length ≤ 1)
    (hnc : ∃ x x' : List Bool, x.length = n ∧ x'.length = n ∧ C.eval x ≠ C.eval x') :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size - 1 ∧
      (∀ x : List Bool, x.length = n → C'.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = n → ∀ m < n + j,
        (C'.wires x).getD m false = (C.wires x).getD m false) := by
  rcases gate_const_or_copy n C j hj hop hlen with ⟨c, hc⟩ | ⟨y, hy, hcopy⟩
  · have hout : C.output ≠ n + j := by
      intro h
      obtain ⟨x, x', hx, hx', hne⟩ := hnc
      apply hne
      unfold Circuit.eval
      rw [h, hc x hx, hc x' hx']
    exact elim_const_gate n C hF j hj c hout hc
  · exact elim_copy_gate n C hF j hj y hy hcopy

lemma exists_reader (n : ℕ) (C : Circuit) (w : ℕ) (h : 1 ≤ wireFanOut n C w) :
    ∃ k : Fin C.size, w < n + k.val ∧ w ∈ C.gates[k.val].inputs := by
  by_contra hne
  push Not at hne
  have hzero : wireFanOut n C w = 0 := by
    unfold wireFanOut
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with hlt
    · exact List.count_eq_zero.mpr (hne k hlt)
    · rfl
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (w : ℕ) (h : wireFanOut n C w = 1)
    (j k : Fin C.size) (hj : w < n + j.val) (hk : w < n + k.val)
    (hwj : w ∈ C.gates[j.val].inputs) (hwk : w ∈ C.gates[k.val].inputs) : j = k := by
  by_contra hne
  have hsub : (∑ m ∈ ({j, k} : Finset (Fin C.size)),
      (if w < n + m.val then C.gates[m.val].inputs.count w else 0)) ≤ wireFanOut n C w :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne, if_pos hj, if_pos hk] at hsub
  have h1 := List.count_pos_iff.mpr hwj
  have h2 := List.count_pos_iff.mpr hwk
  omega

/-- Fixing x_i: the circuit `substAt n i b C` no longer reads x_i and computes the restricted
function, with the same number of gates. -/
theorem substAt_input_eval (n : ℕ) (C : Circuit) (hF : FanInTwo C) (i : Fin n) (b : Bool)
    (hout : C.output ≠ i.val) (x : Fin n → Bool) :
    (substAt n i.val b C).eval (List.ofFn x) = C.eval (List.ofFn (Function.update x i b)) := by
  have hno : ∀ g ∈ (substAt n i.val b C).gates, i.val ∉ g.inputs := by
    intro g hg
    rw [List.mem_iff_getElem] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    have hk' : k < C.size := by simpa [substAt, Circuit.size] using hk
    rw [substAt_getElem n i.val b C k, if_pos (by omega)]
    exact substGate_not_mem _ _ _ (basis_of_mem hF (List.getElem_mem hk')).1
  have h1 := foldl_unused_input (substAt n i.val b C).gates (List.ofFn x)
    (List.ofFn (Function.update x i b)) i.val (by simp) (by
      intro k hki
      by_cases hk : k < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, ↓reduceDIte]
        have hne : (⟨k, hk⟩ : Fin n) ≠ i := by intro h; apply hki; exact congrArg Fin.val h
        simp [Function.update_of_ne hne]
      · simp [List.getD_eq_getElem?_getD, hk]) hno
  have hc : (C.wires (List.ofFn (Function.update x i b))).getD i.val false = b := by
    obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix C.gates (List.ofFn (Function.update x i b))
    rw [wires_eq_foldl, hsuf, getD_append_left' _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hw := substAt_wires n i.val b C hF (List.ofFn (Function.update x i b)) (by simp) hc
  show ((substAt n i.val b C).wires (List.ofFn x)).getD C.output false =
    (C.wires (List.ofFn (Function.update x i b))).getD C.output false
  rw [wires_eq_foldl, h1.2 C.output hout, ← wires_eq_foldl, hw]

/-- Restriction, minus one gate. If some gate reads input `i`, and the function with `x_i`
fixed to `b` is not constant, then that function has a circuit with at least one gate fewer.
(It covers `wireFanOut n C i = 1`; NOT gates must read at most one wire.) -/
theorem restrict_minus_one (n : ℕ) (C : Circuit) (hF : FanInTwo C)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (i : Fin n) (b : Bool) (hout : C.output ≠ i.val) (hread : 1 ≤ wireFanOut n C i.val)
    (hnc : ∃ x x' : Fin n → Bool, C.eval (List.ofFn (Function.update x i b)) ≠
      C.eval (List.ofFn (Function.update x' i b))) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x i b)) := by
  obtain ⟨j, hjlt, hji⟩ := exists_reader n C i.val hread
  have hj' : j.val < C.size := j.isLt
  have hmem := List.getElem_mem hj'
  have hb := basis_of_mem hF hmem
  have hshape := substGate_shape i.val b C.gates[j.val] hb.1 hb.2 (hNot _ hmem) hji
  have hj1 : j.val < (substAt n i.val b C).size := by rw [substAt_size]; exact hj'
  have hg1 : ∀ h, (substAt n i.val b C).gates[j.val]'h = substGate i.val b C.gates[j.val] :=
    fun h => (substAt_getElem n i.val b C j.val h).trans (if_pos hjlt)
  have hev1 := substAt_input_eval n C hF i b hout
  have hnc1 : ∃ x x' : List Bool, x.length = n ∧ x'.length = n ∧
      (substAt n i.val b C).eval x ≠ (substAt n i.val b C).eval x' := by
    obtain ⟨x, x', hne⟩ := hnc
    exact ⟨List.ofFn x, List.ofFn x', by simp, by simp, by rw [hev1, hev1]; exact hne⟩
  obtain ⟨C', hF', hsz, hev', _⟩ := elim_small_gate n (substAt n i.val b C)
    (substAt_fanInTwo n i.val b C hF) j.val hj1 (by have e := hg1 hj1; rw [e]; exact hshape.1)
    (by have e := hg1 hj1; rw [e]; exact hshape.2) hnc1
  refine ⟨C', hF', ?_, fun x => ?_⟩
  · rw [hsz, substAt_size]; omega
  · rw [hev' (List.ofFn x) (by simp), hev1]

/-- The request's form: input `i` read exactly once, fixed to false or to true. -/
theorem restrict_fanout_one (n : ℕ) (C : Circuit) (hF : FanInTwo C)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (i : Fin n) (hout : C.output ≠ i.val) (hfo : wireFanOut n C i.val = 1) (b : Bool)
    (hnc : ∃ x x' : Fin n → Bool, C.eval (List.ofFn (Function.update x i b)) ≠
      C.eval (List.ofFn (Function.update x' i b))) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size ≤ C.size - 1 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x i b)) := by
  obtain ⟨C', hF', hsz, hev⟩ := restrict_minus_one n C hF hNot i b hout (by omega) hnc
  exact ⟨C', hF', by omega, hev⟩

/-- Restriction, minus two gates: input `i` is read once, by an AND gate fixed to false or an
OR gate fixed to true, and that gate is read by some later gate. -/
theorem restrict_minus_two (n : ℕ) (C : Circuit) (hF : FanInTwo C)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (i : Fin n) (b : Bool) (hout : C.output ≠ i.val) (hfo : wireFanOut n C i.val = 1)
    (j : Fin C.size) (hji : i.val ∈ C.gates[j.val].inputs)
    (hab : (C.gates[j.val].op = GateOp.and ∧ b = false) ∨
      (C.gates[j.val].op = GateOp.or ∧ b = true))
    (hjread : 1 ≤ wireFanOut n C (n + j.val))
    (hnc : ∃ x x' : Fin n → Bool, C.eval (List.ofFn (Function.update x i b)) ≠
      C.eval (List.ofFn (Function.update x' i b))) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size ≤ C.size - 2 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x i b)) := by
  have hj' : j.val < C.size := j.isLt
  have hjlt : i.val < n + j.val := by omega
  have hb := basis_of_mem hF (List.getElem_mem hj')
  -- step 1: fix x_i; gate j becomes a constant gate with value b
  set C1 := substAt n i.val b C with hC1
  have hev1 := substAt_input_eval n C hF i b hout
  have hF1 : FanInTwo C1 := substAt_fanInTwo n i.val b C hF
  have hjC1 : j.val < C1.size := by rw [hC1, substAt_size]; exact hj'
  have hg1 : ∀ h, C1.gates[j.val]'h = substGate i.val b C.gates[j.val] :=
    fun h => (substAt_getElem n i.val b C j.val h).trans (if_pos hjlt)
  have hconst : ∀ x : List Bool, x.length = n → (C1.wires x).getD (n + j.val) false = b := by
    intro x hx
    rw [wire_gate_value n C1 j.val hjC1 x hx]
    have e := hg1 hjC1
    rw [e]
    exact substGate_const _ _ _ hji hab _
  -- step 2: a later gate k reads gate j; it does not read x_i
  obtain ⟨k, hjk, hkj⟩ := exists_reader n C (n + j.val) hjread
  have hk' : k.val < C.size := k.isLt
  have hkb := basis_of_mem hF (List.getElem_mem hk')
  have hki : i.val ∉ C.gates[k.val].inputs := by
    intro hin
    have := reader_unique n C i.val hfo j k hjlt (by omega) hji hin
    rw [this] at hjk
    omega
  have hg1k : ∀ h, C1.gates[k.val]'h = C.gates[k.val] := fun h =>
    (substAt_getElem n i.val b C k.val h).trans ((if_pos (by omega)).trans
      (substGate_of_not_mem _ _ _ hkb.1 (hNot _ (List.getElem_mem hk')) hki))
  -- step 3: fix gate j's wire to b; gate k becomes AND/OR with at most one input
  set C2 := substAt n (n + j.val) b C1 with hC2
  have hw2 : ∀ x : List Bool, x.length = n → C2.wires x = C1.wires x :=
    fun x hx => substAt_wires n (n + j.val) b C1 hF1 x hx (hconst x hx)
  have hF2 : FanInTwo C2 := substAt_fanInTwo n (n + j.val) b C1 hF1
  have hk2 : k.val < C2.size := by rw [hC2, substAt_size, hC1, substAt_size]; exact hk'
  have hg2k : ∀ h, C2.gates[k.val]'h = substGate (n + j.val) b C.gates[k.val] := fun h =>
    (substAt_getElem n (n + j.val) b C1 k.val h).trans ((if_pos hjk).trans
      (congrArg (substGate (n + j.val) b) (hg1k _)))
  have hshape := substGate_shape (n + j.val) b C.gates[k.val] hkb.1 hkb.2
    (hNot _ (List.getElem_mem hk')) hkj
  have hev2 : ∀ x : Fin n → Bool,
      C2.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x i b)) := by
    intro x
    have : C2.eval (List.ofFn x) = C1.eval (List.ofFn x) := by
      unfold Circuit.eval
      rw [hw2 _ (by simp)]
      rfl
    rw [this, hev1]
  have hnc2 : ∃ x x' : List Bool, x.length = n ∧ x'.length = n ∧ C2.eval x ≠ C2.eval x' := by
    obtain ⟨x, x', hne⟩ := hnc
    exact ⟨List.ofFn x, List.ofFn x', by simp, by simp, by rw [hev2, hev2]; exact hne⟩
  -- step 4: remove gate k
  obtain ⟨C3, hF3, hsz3, hev3, hpre3⟩ := elim_small_gate n C2 hF2 k.val hk2
    (by have e := hg2k hk2; rw [e]; exact hshape.1)
    (by have e := hg2k hk2; rw [e]; exact hshape.2) hnc2
  -- step 5: gate j is still constant in C3; remove it
  have hconst3 : ∀ x : List Bool, x.length = n → (C3.wires x).getD (n + j.val) false = b := by
    intro x hx
    rw [hpre3 x hx (n + j.val) hjk, hw2 x hx, hconst x hx]
  have hsz3' : C3.size = C.size - 1 := by rw [hsz3, hC2, substAt_size, hC1, substAt_size]
  have hj3 : j.val < C3.size := by omega
  have hev3' : ∀ x : Fin n → Bool,
      C3.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x i b)) := by
    intro x
    rw [hev3 _ (by simp), hev2]
  have hout3 : C3.output ≠ n + j.val := by
    intro h
    obtain ⟨x, x', hne⟩ := hnc
    apply hne
    rw [← hev3' x, ← hev3' x']
    unfold Circuit.eval
    rw [h, hconst3 _ (by simp), hconst3 _ (by simp)]
  obtain ⟨C4, hF4, hsz4, hev4, _⟩ := elim_const_gate n C3 hF3 j.val hj3 b hout3 hconst3
  refine ⟨C4, hF4, by omega, fun x => ?_⟩
  rw [hev4 _ (by simp), hev3']

-- Part 3. From a World 1 circuit for Petersen to a smaller circuit for Petersen minus vertex 0
-- (the function with x 0 fixed to false, on the same 10 inputs; it does not depend on x 0).

lemma petersen_restrict0_nonconst :
    ∃ x x' : Fin 10 → Bool, petersenFun (Function.update x 0 false) ≠
      petersenFun (Function.update x' 0 false) :=
  ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 2), by decide⟩

lemma and_gate_false (g : Gate) (hand : g.op = GateOp.and) (vals : ℕ → Bool) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vals w = false) : g.op.eval (g.inputs.map vals) = false := by
  obtain ⟨op, l⟩ := g
  simp only at hand hw
  subst hand
  simp only [GateOp.eval]
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  have := hall (vals w) (List.mem_map.mpr ⟨w, hw, rfl⟩)
  simp [hv] at this

/-- A World 1 circuit (at most 19 gates, x 0 read by exactly one gate) gives a circuit of at
most 18 gates for Petersen with x 0 fixed to false, and of at most 17 gates when the gate
reading x 0 is an AND. -/
theorem world1_restrict (C : Circuit) (hF : FanInTwo C) (hle : C.size ≤ 19)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x)
    (hNot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hdead : ∀ j : Fin C.size, 10 + j.val ≠ C.output → 1 ≤ wireFanOut 10 C (10 + j.val))
    (hf1 : wireFanOut 10 C 0 = 1) :
    HasCircuitSize 10 (fun x => petersenFun (Function.update x 0 false)) 18 ∧
    (∀ j : Fin C.size, (0 : ℕ) ∈ C.gates[j.val].inputs → C.gates[j.val].op = GateOp.and →
      HasCircuitSize 10 (fun x => petersenFun (Function.update x 0 false)) 17) := by
  obtain ⟨hout_ge, _⟩ := minimal_output_is_gate 10 petersenFun C hev
    petersenFun_not_false petersenFun_not_proj
  have hout0 : C.output ≠ (0 : Fin 10).val := by
    show C.output ≠ 0
    omega
  have hnc : ∃ x x' : Fin 10 → Bool, C.eval (List.ofFn (Function.update x 0 false)) ≠
      C.eval (List.ofFn (Function.update x' 0 false)) := by
    obtain ⟨x, x', h⟩ := petersen_restrict0_nonconst
    exact ⟨x, x', by rw [hev, hev]; exact h⟩
  constructor
  · obtain ⟨C', hF', hsz, hev'⟩ := restrict_fanout_one 10 C hF hNot 0 hout0 hf1 false hnc
    exact ⟨C', hF', by omega, fun x => by rw [hev', hev]⟩
  · intro j hj0 hand
    have hjout : 10 + j.val ≠ C.output := by
      intro heq
      let y : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
      have hy : petersenFun y = true := by decide
      have hv0 : (C.wires (List.ofFn y)).getD 0 false = false := by
        obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix C.gates (List.ofFn y)
        rw [wires_eq_foldl, hsuf, getD_append_left' _ _ _ (by simp)]
        decide
      have hw := wire_gate_value 10 C j.val j.isLt (List.ofFn y) (by simp)
      have hfalse : (C.wires (List.ofFn y)).getD (10 + j.val) false = false :=
        hw.trans (and_gate_false _ hand _ 0 hj0 (by
          show (if (0 : ℕ) < 10 + j.val then (C.wires (List.ofFn y)).getD 0 false else false) =
            false
          rw [if_pos (by omega)]
          exact hv0))
      have h1 := hev y
      rw [hy] at h1
      unfold Circuit.eval at h1
      rw [← heq, hfalse] at h1
      exact Bool.false_ne_true h1
    obtain ⟨C', hF', hsz, hev'⟩ := restrict_minus_two 10 C hF hNot 0 false hout0 hf1 j hj0
      (Or.inl ⟨hand, rfl⟩) (hdead j hjout) hnc
    exact ⟨C', hF', by omega, fun x => by rw [hev', hev]⟩


-- Glue to petersen_19_world1_only, whose World 1 circuit carries no condition on NOT gates and
-- no dead-gate condition: trim NOT gates first, then show the AND gate reading x 0 is read.

lemma wireFanOut_eq_range (n : ℕ) (C : Circuit) (w : ℕ) :
    wireFanOut n C w = ∑ j ∈ Finset.range C.size,
      (if w < n + j then (C.gates.getD j ⟨GateOp.and, []⟩).inputs.count w else 0) := by
  unfold wireFanOut
  rw [← Fin.sum_univ_eq_sum_range (fun j => if w < n + j then
    (C.gates.getD j ⟨GateOp.and, []⟩).inputs.count w else 0)]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val < C.gates.length := j.isLt
  show _ = (if w < n + j.val then (C.gates.getD j.val ⟨GateOp.and, []⟩).inputs.count w else 0)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

lemma trimNots_fanout_le (n : ℕ) (C : Circuit) (w : ℕ) :
    wireFanOut n (trimNots C) w ≤ wireFanOut n C w := by
  rw [wireFanOut_eq_range, wireFanOut_eq_range, trimNots_size]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · have hj' : j < C.gates.length := Finset.mem_range.mp hj
    have hget : (trimNots C).gates.getD j ⟨GateOp.and, []⟩ =
        trimNot (C.gates.getD j ⟨GateOp.and, []⟩) := by
      simp only [trimNots, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some]
    rw [hget]
    unfold trimNot
    split_ifs
    · exact (List.take_sublist 1 _).count_le _
    · exact le_refl _
  · exact le_refl _

lemma trimNot_of_ne (g : Gate) (h : g.op ≠ GateOp.not) : trimNot g = g := by
  unfold trimNot
  have : isNotOp g.op = false := by
    cases hg : g.op <;> simp_all [isNotOp]
  simp [this]

/-- A circuit for Petersen must read x 0. -/
lemma petersen_reads_x0 (D : Circuit)
    (hev : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersenFun x)
    (hno : ∀ g ∈ D.gates, (0 : ℕ) ∉ g.inputs) (hout : D.output ≠ 0) : False := by
  obtain ⟨x, hx⟩ := petersenFun_essential 0
  apply hx
  rw [← hev, ← hev]
  have h1 := foldl_unused_input D.gates (List.ofFn x) (List.ofFn (Function.update x 0 (!x 0))) 0
    (by simp) (by
      intro k hki
      by_cases hk : k < 10
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, ↓reduceDIte]
        have hne : (⟨k, hk⟩ : Fin 10) ≠ 0 := by intro h; apply hki; exact congrArg Fin.val h
        simp [Function.update_of_ne hne]
      · simp [List.getD_eq_getElem?_getD, hk]) hno
  unfold Circuit.eval
  rw [wires_eq_foldl, wires_eq_foldl]
  exact h1.2 D.output hout

/-- In a Petersen circuit reading x 0 once, the gate reading x 0 is not dead. -/
lemma world1_reader_not_dead (D : Circuit)
    (hev : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersenFun x)
    (hfo : wireFanOut 10 D 0 = 1) (j : Fin D.size) (hj0 : (0 : ℕ) ∈ D.gates[j.val].inputs)
    (hout : 10 + j.val ≠ D.output) (hD10 : 10 ≤ D.output) :
    1 ≤ wireFanOut 10 D (10 + j.val) := by
  by_contra hlt
  have hdead : wireFanOut 10 D (10 + j.val) = 0 := by omega
  have hev' : ∀ x : Fin 10 → Bool, (deleteGate 10 D j.val).eval (List.ofFn x) = petersenFun x := by
    intro x
    rw [deleteGate_eval 10 D j.val j.isLt (Ne.symm hout) hdead (List.ofFn x) (by simp), hev]
  have hno : ∀ g ∈ (deleteGate 10 D j.val).gates, (0 : ℕ) ∉ g.inputs := by
    intro g hg hin
    simp only [deleteGate, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [List.mem_eraseIdx_iff_getElem] at hg0
    obtain ⟨m, hm, hmj, rfl⟩ := hg0
    simp only [shiftGate, List.mem_map] at hin
    obtain ⟨v, hv, hv0⟩ := hin
    have hv' : v = 0 := by
      unfold shiftIdx at hv0
      split_ifs at hv0 <;> omega
    subst hv'
    have := reader_unique 10 D 0 hfo ⟨m, hm⟩ j (by omega) (by omega) hv hj0
    exact hmj (congrArg Fin.val this)
  have hout' : (deleteGate 10 D j.val).output ≠ 0 := by
    simp only [deleteGate, shiftIdx]
    split_ifs <;> omega
  exact petersen_reads_x0 _ hev' hno hout'

/-- From the World 1 form of `petersen_19_world1_only`: Petersen with x 0 fixed to false
(Gemini's `p0Fun10`) has a circuit of at most 18 gates, and of at most 17 when the gate
reading x 0 is an AND. -/
theorem world1_only_restrict (C : Circuit) (hF : FanInTwo C) (hle : C.size ≤ 19)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x)
    (hf1 : wireFanOut 10 C 0 = 1) :
    HasCircuitSize 10 (fun x => petersenFun (Function.update x 0 false)) 18 ∧
    (∀ j : Fin C.size, (0 : ℕ) ∈ C.gates[j.val].inputs → C.gates[j.val].op = GateOp.and →
      HasCircuitSize 10 (fun x => petersenFun (Function.update x 0 false)) 17) := by
  have hFD : FanInTwo (trimNots C) := trimNots_fanInTwo C hF
  have hszD : (trimNots C).size = C.size := trimNots_size C
  have hevD : ∀ x : Fin 10 → Bool, (trimNots C).eval (List.ofFn x) = petersenFun x := by
    intro x; rw [trimNots_eval, hev]
  have hNotD := trimNots_not_len C
  obtain ⟨houtD, _⟩ := minimal_output_is_gate 10 petersenFun (trimNots C) hevD
    petersenFun_not_false petersenFun_not_proj
  have hfD : wireFanOut 10 (trimNots C) 0 = 1 := by
    have h1 := trimNots_fanout_le 10 C 0
    have h2 := minimal_input_fanout_pos 10 petersenFun (trimNots C) hevD houtD
      petersenFun_essential 0
    have h2' : 1 ≤ wireFanOut 10 (trimNots C) 0 := h2
    omega
  have hout0 : (trimNots C).output ≠ (0 : Fin 10).val := by
    show (trimNots C).output ≠ 0
    omega
  have hnc : ∃ x x' : Fin 10 → Bool, (trimNots C).eval (List.ofFn (Function.update x 0 false)) ≠
      (trimNots C).eval (List.ofFn (Function.update x' 0 false)) := by
    obtain ⟨x, x', h⟩ := petersen_restrict0_nonconst
    exact ⟨x, x', by rw [hevD, hevD]; exact h⟩
  constructor
  · obtain ⟨C', hF', hsz, hev'⟩ :=
      restrict_fanout_one 10 (trimNots C) hFD hNotD 0 hout0 hfD false hnc
    exact ⟨C', hF', by omega, fun x => by rw [hev', hevD]⟩
  · intro j hj0 hand
    have hjD : j.val < (trimNots C).gates.length := by
      have := j.isLt
      simp only [trimNots, List.length_map]
      exact this
    have hne : C.gates[j.val].op ≠ GateOp.not := by
      intro h
      exact GateOp.noConfusion (hand.symm.trans h)
    have hDj : (trimNots C).gates[j.val]'hjD = C.gates[j.val] :=
      (List.getElem_map _).trans (trimNot_of_ne _ hne)
    have hDj0 : (0 : ℕ) ∈ ((trimNots C).gates[j.val]'hjD).inputs := by rw [hDj]; exact hj0
    have hDand : ((trimNots C).gates[j.val]'hjD).op = GateOp.and := by rw [hDj]; exact hand
    let jD : Fin (trimNots C).size := ⟨j.val, hjD⟩
    have hjout : 10 + jD.val ≠ (trimNots C).output := by
      intro heq
      let y : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
      have hy : petersenFun y = true := by decide
      have hv0 : ((trimNots C).wires (List.ofFn y)).getD 0 false = false := by
        obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix (trimNots C).gates (List.ofFn y)
        rw [wires_eq_foldl, hsuf, getD_append_left' _ _ _ (by simp)]
        decide
      have hw := wire_gate_value 10 (trimNots C) jD.val jD.isLt (List.ofFn y) (by simp)
      have hfalse : ((trimNots C).wires (List.ofFn y)).getD (10 + jD.val) false = false :=
        hw.trans (and_gate_false _ hDand _ 0 hDj0 (by
          show (if (0 : ℕ) < 10 + jD.val then
            ((trimNots C).wires (List.ofFn y)).getD 0 false else false) = false
          rw [if_pos (by omega)]
          exact hv0))
      have h1 := hevD y
      rw [hy] at h1
      unfold Circuit.eval at h1
      rw [← heq, hfalse] at h1
      exact Bool.false_ne_true h1
    have hjread := world1_reader_not_dead (trimNots C) hevD hfD jD hDj0 hjout houtD
    obtain ⟨C', hF', hsz, hev'⟩ := restrict_minus_two 10 (trimNots C) hFD hNotD 0 false hout0
      hfD jD hDj0 (Or.inl ⟨hDand, rfl⟩) hjread hnc
    exact ⟨C', hF', by omega, fun x => by rw [hev', hevD]⟩

/-- The conclusion of `petersen_19_world1_only` (Gemini, L_meta_651_step) gives a circuit of at
most 18 gates for `p0Fun10 x = petersenFun (Function.update x 0 false)`. -/
theorem world1_only_to_p0Fun10
    (hW1 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧ wireFanOut 10 C 0 = 1) :
    HasCircuitSize 10 (fun x => petersenFun (Function.update x 0 false)) 18 := by
  obtain ⟨C, hF, hle, hev, hf1⟩ := hW1
  exact (world1_only_restrict C hF hle hev hf1).1

end PEqualNP.Outside.L_meta_651_world1
