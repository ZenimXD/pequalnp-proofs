import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_651_step

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

theorem petersen_19_dichotomy (h : HasCircuitSize 10 petersenFun 19) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ j : Fin C.size, 10 + j.val ≠ C.output → 1 ≤ wireFanOut 10 C (10 + j.val)) ∧
      (wireFanOut 10 C 0 = 1 ∨
        (C.size = 19 ∧
         notCount C = 0 ∧
         (∀ j : Fin C.size, 10 + j.val ≠ C.output → wireFanOut 10 C (10 + j.val) = 1) ∧
         (∀ i : Fin 10, wireFanOut 10 C i.val = 2))) := by
  obtain ⟨C, hF, hle, hev, hNot, hmin⟩ := minimal_circuit_exists 10 19 petersenFun h
  obtain ⟨hout_ge, hout_lt⟩ := minimal_output_is_gate 10 petersenFun C hev
    petersenFun_not_false petersenFun_not_proj
  have hbud := wire_budget_minimal 10 petersenFun C hF hNot hev hmin
    petersenFun_not_false petersenFun_not_proj
  have hin_pos : ∀ i : Fin 10, 1 ≤ wireFanOut 10 C i.val :=
    minimal_input_fanout_pos 10 petersenFun C hev hout_ge petersenFun_essential
  by_cases h1 : ∃ v : Fin 10, wireFanOut 10 C v.val = 1
  · obtain ⟨v, hv⟩ := h1
    let σ := petersenAut v
    let C' := permuteCircuit 10 σ C
    refine ⟨C', permuteCircuit_fanInTwo 10 σ C hF, by rw [permuteCircuit_size]; exact hle,
      fun x => by rw [permuteCircuit_eval, hev, petersenFun_aut],
      permuteCircuit_not_len 10 σ C hNot, ?_, Or.inl ?_⟩
    · intro j hj
      have hj' : j.val < C.size := by simpa [C', permuteCircuit_size] using j.isLt
      have hout' : 10 + j.val ≠ C.output := by
        intro heq
        apply hj
        dsimp [C', permuteCircuit, permWire]
        rw [← heq]
        split_ifs with hlt
        · omega
        · rfl
      rw [permuteCircuit_wireFanOut_gate]
      exact minimal_no_dead_gate 10 petersenFun C hF hev hmin ⟨j.val, hj'⟩ hout'
    · have h0 : (σ v).val = 0 := congrArg Fin.val (petersenAut_apply v)
      rw [← h0, permuteCircuit_wireFanOut_input]
      exact hv
  · push Not at h1
    have hge2 : ∀ i : Fin 10, 2 ≤ wireFanOut 10 C i.val := by
      intro i
      have hpos := hin_pos i
      have hne := h1 i
      omega
    have hsum_ge20 : 20 ≤ ∑ i : Fin 10, wireFanOut 10 C i.val := by
      calc 20 = ∑ _i : Fin 10, 2 := by simp
        _ ≤ ∑ i : Fin 10, wireFanOut 10 C i.val := Finset.sum_le_sum fun i _ => hge2 i
    have hsz19 : C.size = 19 := by omega
    have hnot0 : notCount C = 0 := by omega
    have hgate_ex0 : (∑ j : Fin C.size,
        if 10 + j.val = C.output then 0 else wireFanOut 10 C (10 + j.val) - 1) = 0 := by omega
    have hsum_eq20 : (∑ i : Fin 10, wireFanOut 10 C i.val) = 20 := by omega
    refine ⟨C, hF, hle, hev, hNot,
      fun j hj => minimal_no_dead_gate 10 petersenFun C hF hev hmin j hj,
      Or.inr ⟨hsz19, hnot0, ?_, ?_⟩⟩
    · intro j hj
      have hzero := Finset.sum_eq_zero_iff.mp hgate_ex0 j (Finset.mem_univ _)
      simp only [hj, ↓reduceIte] at hzero
      have hpos := minimal_no_dead_gate 10 petersenFun C hF hev hmin j hj
      omega
    · intro i
      by_contra hne
      have hgt : 3 ≤ wireFanOut 10 C i.val := by have := hge2 i; omega
      have hlt : 20 < ∑ k : Fin 10, wireFanOut 10 C k.val := by
        calc 20 = ∑ _k : Fin 10, 2 := by simp
          _ < ∑ k : Fin 10, wireFanOut 10 C k.val :=
            Finset.sum_lt_sum (fun k _ => hge2 k) ⟨i, Finset.mem_univ i, by omega⟩
      omega

inductive MonoFormula (n : ℕ) where
  | var (i : Fin n)
  | and (l r : MonoFormula n)
  | or (l r : MonoFormula n)

def MonoFormula.eval {n : ℕ} : MonoFormula n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

def MonoFormula.leaves {n : ℕ} : MonoFormula n → ℕ
  | .var _ => 1
  | .and l r => l.leaves + r.leaves
  | .or l r => l.leaves + r.leaves

def MonoFormula.varCount {n : ℕ} (v : Fin n) : MonoFormula n → ℕ
  | .var i => if i = v then 1 else 0
  | .and l r => l.varCount v + r.varCount v
  | .or l r => l.varCount v + r.varCount v

def MonoFormula.andDepth {n : ℕ} : MonoFormula n → ℕ
  | .var _ => 0
  | .and l r => max l.andDepth r.andDepth + 1
  | .or l r => max l.andDepth r.andDepth

def MonoFormula.orVars {n : ℕ} : MonoFormula n → Finset (Fin n)
  | .var i => {i}
  | .and l r => l.orVars ∪ r.orVars
  | .or l r => l.orVars ∪ r.orVars

lemma MonoFormula.orVars_card_le {n : ℕ} (F : MonoFormula n) :
    F.orVars.card ≤ F.leaves := by
  induction F with
  | var i => simp [orVars, leaves]
  | and l r ihl ihr =>
    simp only [orVars, leaves]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihl ihr)
  | or l r ihl ihr =>
    simp only [orVars, leaves]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihl ihr)

lemma MonoFormula.eval_of_andDepth_zero {n : ℕ} (F : MonoFormula n) (h0 : F.andDepth = 0)
    (x : Fin n → Bool) :
    F.eval x = true ↔ ∃ v ∈ F.orVars, x v = true := by
  induction F with
  | var i => simp [eval, orVars]
  | and l r _ _ => simp [andDepth] at h0
  | or l r ihl ihr =>
    simp only [andDepth, Nat.max_eq_zero_iff] at h0
    simp only [eval, Bool.or_eq_true, ihl h0.1, ihr h0.2, orVars, Finset.mem_union]
    constructor
    · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
      · exact ⟨v, Or.inl hv, hx⟩
      · exact ⟨v, Or.inr hv, hx⟩
    · rintro ⟨v, hv | hv, hx⟩
      · exact Or.inl ⟨v, hv, hx⟩
      · exact Or.inr ⟨v, hv, hx⟩

def petersenEdgesList : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
   (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)]

def petersenEdges : Finset (Fin 10 × Fin 10) := petersenEdgesList.toFinset

def petersenAdj (u v : Fin 10) : Bool :=
  (u, v) ∈ petersenEdgesList || (v, u) ∈ petersenEdgesList

def pairInput (u v : Fin 10) : Fin 10 → Bool :=
  fun i => decide (i = u ∨ i = v)

def singleInput (u : Fin 10) : Fin 10 → Bool :=
  fun i => decide (i = u)

lemma petersenEdges_card : petersenEdges.card = 15 := by decide

lemma petersenEdges_lt : ∀ e ∈ petersenEdges, e.1 < e.2 := by decide

lemma petersenEdges_adj : ∀ e ∈ petersenEdges, petersenAdj e.1 e.2 = true := by decide

lemma petersenFun_single (u : Fin 10) : petersenFun (singleInput u) = false := by
  fin_cases u <;> decide

lemma petersenFun_pair_iff :
    ∀ u v : Fin 10, petersenFun (pairInput u v) = true ↔ petersenAdj u v = true := by
  decide

lemma petersenAdj_irrefl : ∀ u : Fin 10, petersenAdj u u = false := by
  decide

lemma petersenAdj_no_c4 : ∀ (u1 u2 v1 v2 : Fin 10), u1 ≠ u2 → v1 ≠ v2 →
    petersenAdj u1 v1 = true → petersenAdj u1 v2 = true →
    petersenAdj u2 v1 = true → petersenAdj u2 v2 = false := by
  decide

lemma petersen_biclique_star (A B : Finset (Fin 10))
    (h : ∀ u ∈ A, ∀ v ∈ B, petersenAdj u v = true) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hnot
  push Not at hnot
  obtain ⟨hA, hB⟩ := hnot
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hA
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp hB
  have h11 := h u1 hu1 v1 hv1
  have h12 := h u1 hu1 v2 hv2
  have h21 := h u2 hu2 v1 hv1
  have h22 := h u2 hu2 v2 hv2
  have hfalse := petersenAdj_no_c4 u1 u2 v1 v2 hune hvne h11 h12 h21
  rw [h22] at hfalse
  exact absurd hfalse (by decide)

lemma c5_bool_bound (b0 b1 b2 b3 b4 : Bool)
    (h01 : !(b0 && b1) = true) (h12 : !(b1 && b2) = true) (h23 : !(b2 && b3) = true)
    (h34 : !(b3 && b4) = true) (h40 : !(b4 && b0) = true) :
    (if b0 = true then 1 else 0) + (if b1 = true then 1 else 0) +
    (if b2 = true then 1 else 0) + (if b3 = true then 1 else 0) +
    (if b4 = true then 1 else 0) ≤ 2 := by
  revert b0 b1 b2 b3 b4 h01 h12 h23 h34 h40
  decide

lemma c5_indep_le_two (S : Finset (Fin 10))
    (a0 a1 a2 a3 a4 : Fin 10)
    (hsub : S ⊆ {a0, a1, a2, a3, a4})
    (h01 : ¬ (a0 ∈ S ∧ a1 ∈ S))
    (h12 : ¬ (a1 ∈ S ∧ a2 ∈ S))
    (h23 : ¬ (a2 ∈ S ∧ a3 ∈ S))
    (h34 : ¬ (a3 ∈ S ∧ a4 ∈ S))
    (h40 : ¬ (a4 ∈ S ∧ a0 ∈ S)) :
    S.card ≤ 2 := by
  let b : Fin 10 → Bool := fun x => decide (x ∈ S)
  let d : Fin 10 → ℕ := fun x => if b x = true then 1 else 0
  have hstep : ∀ (x : Fin 10) (s : Finset (Fin 10)),
      ((insert x s).filter (· ∈ S)).card ≤ d x + (s.filter (· ∈ S)).card := by
    intro x s
    rw [Finset.filter_insert]
    by_cases hx : x ∈ S
    · have hdx : d x = 1 := by simp [d, b, hx]
      rw [if_pos hx, hdx]
      exact le_trans (Finset.card_insert_le _ _) (by omega)
    · have hdx : d x = 0 := by simp [d, b, hx]
      rw [if_neg hx, hdx, zero_add]
  have h1 : S = ({a0, a1, a2, a3, a4} : Finset (Fin 10)).filter (· ∈ S) := by
    ext x; simp only [Finset.mem_filter]; exact ⟨fun hx => ⟨hsub hx, hx⟩, fun h => h.2⟩
  have hsum : S.card ≤ d a0 + d a1 + d a2 + d a3 + d a4 := by
    rw [h1]
    have c1 := hstep a0 {a1, a2, a3, a4}
    have c2 := hstep a1 {a2, a3, a4}
    have c3 := hstep a2 {a3, a4}
    have c4 := hstep a3 {a4}
    have c5 : (({a4} : Finset (Fin 10)).filter (· ∈ S)).card ≤ d a4 := by
      simpa using hstep a4 ∅
    have eq1 : ({a0, a1, a2, a3, a4} : Finset (Fin 10)) = insert a0 {a1, a2, a3, a4} := rfl
    have eq2 : ({a1, a2, a3, a4} : Finset (Fin 10)) = insert a1 {a2, a3, a4} := rfl
    have eq3 : ({a2, a3, a4} : Finset (Fin 10)) = insert a2 {a3, a4} := rfl
    have eq4 : ({a3, a4} : Finset (Fin 10)) = insert a3 {a4} := rfl
    rw [eq1]; rw [eq2] at c1; rw [eq3] at c2; rw [eq4] at c3
    omega
  have hb : d a0 + d a1 + d a2 + d a3 + d a4 ≤ 2 :=
    c5_bool_bound (b a0) (b a1) (b a2) (b a3) (b a4)
      (by simp [b, h01]) (by simp [b, h12]) (by simp [b, h23]) (by simp [b, h34]) (by simp [b, h40])
  omega

lemma petersen_tau_ge_6 (T : Finset (Fin 10))
    (hcov : ∀ e ∈ petersenEdges, e.1 ∈ T ∨ e.2 ∈ T) :
    6 ≤ T.card := by
  let I := Tᶜ
  have hind : ∀ e ∈ petersenEdges, ¬ (e.1 ∈ I ∧ e.2 ∈ I) := by
    intro e he ⟨h1, h2⟩
    simp only [I, Finset.mem_compl] at h1 h2
    rcases hcov e he with h | h
    · exact h1 h
    · exact h2 h
  let outer : Finset (Fin 10) := {0, 1, 2, 3, 4}
  let inner : Finset (Fin 10) := {5, 7, 9, 6, 8}
  have hout : (I ∩ outer).card ≤ 2 := by
    apply c5_indep_le_two (I ∩ outer) 0 1 2 3 4 Finset.inter_subset_right
    · intro ⟨h1, h2⟩; exact hind (0, 1) (by decide) ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · intro ⟨h1, h2⟩; exact hind (1, 2) (by decide) ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · intro ⟨h1, h2⟩; exact hind (2, 3) (by decide) ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · intro ⟨h1, h2⟩; exact hind (3, 4) (by decide) ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · intro ⟨h1, h2⟩; exact hind (0, 4) (by decide) ⟨(Finset.mem_inter.mp h2).1, (Finset.mem_inter.mp h1).1⟩
  have hinn : (I ∩ inner).card ≤ 2 := by
    apply c5_indep_le_two (I ∩ inner) 5 7 9 6 8 Finset.inter_subset_right
    · intro ⟨h1, h2⟩; exact hind (5, 7) (by decide) ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · intro ⟨h1, h2⟩; exact hind (7, 9) (by decide) ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · intro ⟨h1, h2⟩; exact hind (6, 9) (by decide) ⟨(Finset.mem_inter.mp h2).1, (Finset.mem_inter.mp h1).1⟩
    · intro ⟨h1, h2⟩; exact hind (6, 8) (by decide) ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
    · intro ⟨h1, h2⟩; exact hind (5, 8) (by decide) ⟨(Finset.mem_inter.mp h2).1, (Finset.mem_inter.mp h1).1⟩
  have hunion : I ⊆ (I ∩ outer) ∪ (I ∩ inner) := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
    have hpart : x ∈ outer ∨ x ∈ inner := by fin_cases x <;> decide
    rcases hpart with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hI_le : I.card ≤ 4 := by
    calc I.card ≤ ((I ∩ outer) ∪ (I ∩ inner)).card := Finset.card_le_card hunion
      _ ≤ (I ∩ outer).card + (I ∩ inner).card := Finset.card_union_le _ _
      _ ≤ 2 + 2 := Nat.add_le_add hout hinn
      _ = 4 := rfl
  have hcompl : T.card + I.card = 10 := by
    simpa [I] using Finset.card_add_card_compl T
  omega

lemma sigma3_subformula_bound (F : MonoFormula 10)
    (hd : F.andDepth ≤ 1)
    (hle : ∀ x : Fin 10 → Bool, F.eval x = true → petersenFun x = true) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, F.eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ F.leaves := by
  induction F with
  | var i =>
    exfalso
    have h1 := hle (singleInput i) (by simp [MonoFormula.eval, singleInput])
    rw [petersenFun_single] at h1
    exact absurd h1 (by decide)
  | or l r ihl ihr =>
    simp only [MonoFormula.andDepth, Nat.max_le] at hd
    have hle_l : ∀ x, l.eval x = true → petersenFun x = true :=
      fun x hx => hle x (by simp [MonoFormula.eval, hx])
    have hle_r : ∀ x, r.eval x = true → petersenFun x = true :=
      fun x hx => hle x (by simp [MonoFormula.eval, hx])
    obtain ⟨T1, E1, hE1, hcov1, hbd1⟩ := ihl hd.1 hle_l
    obtain ⟨T2, E2, hE2, hcov2, hbd2⟩ := ihr hd.2 hle_r
    refine ⟨T1 ∪ T2, E1 ∪ E2, ?_, ?_, ?_⟩
    · intro e he hev
      simp only [MonoFormula.eval, Bool.or_eq_true] at hev
      rw [Finset.mem_union]
      rcases hev with hl | hr
      · exact Or.inl (hE1 e he hl)
      · exact Or.inr (hE2 e he hr)
    · intro e he
      rw [Finset.mem_union] at he
      rcases he with h1 | h2
      · rcases hcov1 e h1 with hc | hc
        · exact Or.inl (Finset.mem_union_left _ hc)
        · exact Or.inr (Finset.mem_union_left _ hc)
      · rcases hcov2 e h2 with hc | hc
        · exact Or.inl (Finset.mem_union_right _ hc)
        · exact Or.inr (Finset.mem_union_right _ hc)
    · simp only [MonoFormula.leaves]
      have c1 := Finset.card_union_le E1 E2
      have c2 := Finset.card_union_le T1 T2
      omega
  | and l r _ _ =>
    simp only [MonoFormula.andDepth] at hd
    have hdl : l.andDepth = 0 := by omega
    have hdr : r.andDepth = 0 := by omega
    let A := l.orVars
    let B := r.orVars
    have hA_le : A.card ≤ l.leaves := l.orVars_card_le
    have hB_le : B.card ≤ r.leaves := r.orVars_card_le
    have hadj : ∀ u ∈ A, ∀ v ∈ B, petersenAdj u v = true := by
      intro u hu v hv
      rw [← petersenFun_pair_iff]
      apply hle (pairInput u v)
      simp only [MonoFormula.eval, Bool.and_eq_true]
      constructor
      · rw [l.eval_of_andDepth_zero hdl]
        exact ⟨u, hu, by simp [pairInput]⟩
      · rw [r.eval_of_andDepth_zero hdr]
        exact ⟨v, hv, by simp [pairInput]⟩
    rcases petersen_biclique_star A B hadj with hA1 | hB1
    · by_cases hAne : A.Nonempty
      · have hAeq : A.card = 1 := by
          have := Finset.card_pos.mpr hAne; omega
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hAeq
        let E := B.image fun v => if c < v then (c, v) else (v, c)
        refine ⟨{c}, E, ?_, ?_, ?_⟩
        · intro e he hev
          have hlt : e.1 < e.2 := petersenEdges_lt e he
          simp only [MonoFormula.eval, Bool.and_eq_true, l.eval_of_andDepth_zero hdl,
            r.eval_of_andDepth_zero hdr] at hev
          obtain ⟨⟨u, hu, hup⟩, ⟨v, hv, hvp⟩⟩ := hev
          have huc : u = c := by change u ∈ A at hu; rw [hc, Finset.mem_singleton] at hu; exact hu
          subst u
          simp only [pairInput, decide_eq_true_eq] at hup hvp
          have hne_cv : c ≠ v := by
            intro heq; subst heq
            have hfalse := petersenAdj_irrefl c
            have htrue := hadj c (by rw [hc]; simp) c hv
            rw [htrue] at hfalse; exact absurd hfalse (by decide)
          rcases hup with h1 | h1 <;> rcases hvp with h2 | h2
          · exact absurd (h1.trans h2.symm) hne_cv
          · refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
            subst h1; subst h2; simp [hlt]
          · refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
            subst h1; subst h2
            have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
            simp [hnot]
          · exact absurd (h1.trans h2.symm) hne_cv
        · intro e he
          obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
          split_ifs <;> simp
        · simp only [MonoFormula.leaves, Finset.card_singleton]
          have hE_le : E.card ≤ B.card := Finset.card_image_le
          omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hAne
        refine ⟨∅, ∅, ?_, by simp, by simp⟩
        intro e _ hev
        simp only [MonoFormula.eval, Bool.and_eq_true, l.eval_of_andDepth_zero hdl] at hev
        obtain ⟨⟨u, hu, _⟩, _⟩ := hev
        change u ∈ A at hu
        rw [hAne] at hu
        simp at hu
    · by_cases hBne : B.Nonempty
      · have hBeq : B.card = 1 := by
          have := Finset.card_pos.mpr hBne; omega
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hBeq
        let E := A.image fun u => if u < c then (u, c) else (c, u)
        refine ⟨{c}, E, ?_, ?_, ?_⟩
        · intro e he hev
          have hlt : e.1 < e.2 := petersenEdges_lt e he
          simp only [MonoFormula.eval, Bool.and_eq_true, l.eval_of_andDepth_zero hdl,
            r.eval_of_andDepth_zero hdr] at hev
          obtain ⟨⟨u, hu, hup⟩, ⟨v, hv, hvp⟩⟩ := hev
          have hvc : v = c := by change v ∈ B at hv; rw [hc, Finset.mem_singleton] at hv; exact hv
          subst v
          simp only [pairInput, decide_eq_true_eq] at hup hvp
          have hne_uc : u ≠ c := by
            intro heq; subst u
            have hfalse := petersenAdj_irrefl c
            have htrue := hadj c hu c (by rw [hc]; simp)
            rw [htrue] at hfalse; exact absurd hfalse (by decide)
          rcases hup with h1 | h1 <;> rcases hvp with h2 | h2
          · exact absurd (h1.trans h2.symm) hne_uc
          · refine Finset.mem_image.mpr ⟨u, hu, ?_⟩
            subst h1; subst h2; simp [hlt]
          · refine Finset.mem_image.mpr ⟨u, hu, ?_⟩
            subst h1; subst h2
            have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
            simp [hnot]
          · exact absurd (h1.trans h2.symm) hne_uc
        · intro e he
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
          split_ifs <;> simp
        · simp only [MonoFormula.leaves, Finset.card_singleton]
          have hE_le : E.card ≤ A.card := Finset.card_image_le
          omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hBne
        refine ⟨∅, ∅, ?_, by simp, by simp⟩
        intro e _ hev
        simp only [MonoFormula.eval, Bool.and_eq_true, r.eval_of_andDepth_zero hdr] at hev
        obtain ⟨_, ⟨v, hv, _⟩⟩ := hev
        change v ∈ B at hv
        rw [hBne] at hv
        simp at hv

theorem petersen_sigma3_leaves_ge_21 (F : MonoFormula 10)
    (hd : F.andDepth ≤ 1)
    (hev : ∀ x : Fin 10 → Bool, F.eval x = petersenFun x) :
    21 ≤ F.leaves := by
  obtain ⟨T, E, hE, hcov, hbd⟩ := sigma3_subformula_bound F hd (fun x hx => by rw [← hev x, hx])
  have hsub : petersenEdges ⊆ E := by
    intro e he
    apply hE e he
    rw [hev, petersenFun_pair_iff]
    exact petersenEdges_adj e he
  have hE15 : 15 ≤ E.card := by
    rw [← petersenEdges_card]
    exact Finset.card_le_card hsub
  have hT6 : 6 ≤ T.card := petersen_tau_ge_6 T (fun e he => hcov e (hsub he))
  omega

def wireToFormula (C : Circuit) : ℕ → MonoFormula 10
  | w =>
    if h : w < 10 then
      MonoFormula.var ⟨w, h⟩
    else if hg : w - 10 < C.gates.length then
      let g := C.gates[w - 10]
      match g.inputs with
      | [a, b] =>
        if ha : a < w then
          if hb : b < w then
            match g.op with
            | GateOp.and => MonoFormula.and (wireToFormula C a) (wireToFormula C b)
            | _ => MonoFormula.or (wireToFormula C a) (wireToFormula C b)
          else MonoFormula.var 0
        else MonoFormula.var 0
      | _ => MonoFormula.var 0
    else MonoFormula.var 0

lemma list_len_two_eq (l : List ℕ) (h : l.length = 2) : ∃ a b : ℕ, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

set_option maxHeartbeats 800000 in
lemma world2_gate_structure (C : Circuit) (hF : FanInTwo C) (hsz : C.size = 19)
    (hnot0 : notCount C = 0)
    (hout_ge : 10 ≤ C.output) (hout_lt : C.output < 10 + C.size)
    (hgate1 : ∀ j : Fin C.size, 10 + j.val ≠ C.output → wireFanOut 10 C (10 + j.val) = 1)
    (hin2 : ∀ i : Fin 10, wireFanOut 10 C i.val = 2) :
    wireFanOut 10 C C.output = 0 ∧
    ∀ j : Fin C.size,
      (C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C.gates[j.val].inputs = [a, b] ∧ a < 10 + j.val ∧ b < 10 + j.val := by
  have hsum_in : (∑ i : Fin 10, wireFanOut 10 C i.val) = 20 := by
    simp [hin2]
  have hout_j : C.output - 10 < C.size := by omega
  let j0 : Fin C.size := ⟨C.output - 10, hout_j⟩
  have hsum_gate : (∑ j : Fin C.size, wireFanOut 10 C (10 + j.val)) =
      18 + wireFanOut 10 C C.output := by
    have hsplit := Finset.add_sum_erase Finset.univ (fun j : Fin C.size => wireFanOut 10 C (10 + j.val))
      (Finset.mem_univ j0)
    rw [← hsplit]
    have hj0_eq : 10 + j0.val = C.output := by dsimp [j0]; omega
    rw [hj0_eq]
    have hrest : (∑ j ∈ Finset.univ.erase j0, wireFanOut 10 C (10 + j.val)) = 18 := by
      have hcongr : (∑ j ∈ Finset.univ.erase j0, wireFanOut 10 C (10 + j.val)) =
          ∑ _j ∈ Finset.univ.erase j0, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hne : 10 + j.val ≠ C.output := by
          intro heq
          apply (Finset.mem_erase.mp hj).1
          ext; dsimp [j0]; omega
        exact hgate1 j hne
      rw [hcongr, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
      omega
    omega
  have hno_not : ∀ j : Fin C.size, C.gates[j.val].op ≠ GateOp.not := by
    intro j hnot
    have hmem : C.gates[j.val] ∈ C.gates.filter (fun g => isNotOp g.op) := by
      rw [List.mem_filter]
      exact ⟨List.getElem_mem j.isLt, (isNotOp_eq_true _).mpr hnot⟩
    have hpos : 0 < (C.gates.filter fun g => isNotOp g.op).length := List.length_pos_of_mem hmem
    unfold notCount at hnot0
    omega
  have hraw : (∑ j : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
      if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) =
      38 + wireFanOut 10 C C.output := by
    have h1 : (∑ i : Fin 10, wireFanOut 10 C i.val) +
        (∑ j : Fin C.size, wireFanOut 10 C (10 + j.val)) =
        ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w := by
      rw [Finset.sum_range_add,
        Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C x),
        Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C (10 + x))]
    have h2 : ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w =
        ∑ j : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
          if w < 10 + j.val then C.gates[j.val].inputs.count w else 0 := by
      unfold wireFanOut; exact Finset.sum_comm
    omega
  have hterm_le : ∀ j : Fin C.size,
      (∑ w ∈ Finset.range (10 + C.size),
        if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) ≤ 2 := by
    intro j
    calc (∑ w ∈ Finset.range (10 + C.size),
            if w < 10 + j.val then C.gates[j.val].inputs.count w else 0)
        ≤ ∑ w ∈ Finset.range (10 + C.size), C.gates[j.val].inputs.count w :=
          Finset.sum_le_sum fun w _ => by split_ifs <;> omega
      _ ≤ C.gates[j.val].inputs.length := sum_count_range_le _ _
      _ ≤ 2 := (hF C.gates[j.val] (List.getElem_mem j.isLt)).2
  have hsum_le38 : (∑ j : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
      if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) ≤ 38 := by
    calc _ ≤ ∑ _j : Fin C.size, 2 := Finset.sum_le_sum fun j _ => hterm_le j
      _ = 38 := by simp [hsz]
  have hout0 : wireFanOut 10 C C.output = 0 := by omega
  refine ⟨hout0, ?_⟩
  intro j
  have hterm_eq2 : (∑ w ∈ Finset.range (10 + C.size),
      if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) = 2 := by
    by_contra hne
    have hlt : (∑ w ∈ Finset.range (10 + C.size),
        if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) < 2 := by
      have := hterm_le j; omega
    have hsum_lt : (∑ k : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
        if w < 10 + k.val then C.gates[k.val].inputs.count w else 0) < 38 := by
      calc _ < ∑ _k : Fin C.size, 2 :=
            Finset.sum_lt_sum (fun k _ => hterm_le k) ⟨j, Finset.mem_univ j, hlt⟩
        _ = 38 := by simp [hsz]
    omega
  have hop : C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or := by
    have hmem := (hF C.gates[j.val] (List.getElem_mem j.isLt)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hno_not j)
  have hlen2 : C.gates[j.val].inputs.length = 2 := by
    have h1 := sum_count_range_le C.gates[j.val].inputs (10 + C.size)
    have h2 : (∑ w ∈ Finset.range (10 + C.size),
        if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) ≤
        ∑ w ∈ Finset.range (10 + C.size), C.gates[j.val].inputs.count w :=
      Finset.sum_le_sum fun w _ => by split_ifs <;> omega
    have h3 := (hF C.gates[j.val] (List.getElem_mem j.isLt)).2
    omega
  obtain ⟨a, b, hin⟩ := list_len_two_eq C.gates[j.val].inputs hlen2
  refine ⟨hop, a, b, hin, ?_, ?_⟩
  · by_contra ha
    have hsum_le1 : (∑ w ∈ Finset.range (10 + C.size),
        if w < 10 + j.val then ([a, b] : List ℕ).count w else 0) ≤ 1 := by
      have hcongr : ∀ w ∈ Finset.range (10 + C.size),
          (if w < 10 + j.val then ([a, b] : List ℕ).count w else 0) ≤
          (if w = b then 1 else 0) := by
        intro w _
        split_ifs with hlt hwb
        · have hwa : w ≠ a := by omega
          have hba : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
          simp [List.count_cons, hba, hwb]; omega
        · have hwa : w ≠ a := by omega
          have hba : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
          have hbb : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
          simp [List.count_cons, hba, hbb]
        · omega
        · omega
      calc _ ≤ ∑ w ∈ Finset.range (10 + C.size), (if w = b then 1 else 0) :=
            Finset.sum_le_sum hcongr
        _ ≤ 1 := by rw [Finset.sum_ite_eq']; split_ifs <;> omega
    rw [hin] at hterm_eq2
    omega
  · by_contra hb
    have hsum_le1 : (∑ w ∈ Finset.range (10 + C.size),
        if w < 10 + j.val then ([a, b] : List ℕ).count w else 0) ≤ 1 := by
      have hcongr : ∀ w ∈ Finset.range (10 + C.size),
          (if w < 10 + j.val then ([a, b] : List ℕ).count w else 0) ≤
          (if w = a then 1 else 0) := by
        intro w _
        split_ifs with hlt hwa
        · have hwb : w ≠ b := by omega
          have hbb : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
          simp [List.count_cons, hbb, hwa]; omega
        · have hwb : w ≠ b := by omega
          have hba : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
          have hbb : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
          simp [List.count_cons, hba, hbb]
        · omega
        · omega
      calc _ ≤ ∑ w ∈ Finset.range (10 + C.size), (if w = a then 1 else 0) :=
            Finset.sum_le_sum hcongr
        _ ≤ 1 := by rw [Finset.sum_ite_eq']; split_ifs <;> omega
    rw [hin] at hterm_eq2
    omega

lemma wireToFormula_eval (C : Circuit)
    (hstruct : ∀ j : Fin C.size,
      (C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C.gates[j.val].inputs = [a, b] ∧ a < 10 + j.val ∧ b < 10 + j.val)
    (x : Fin 10 → Bool) :
    ∀ w : ℕ, w < 10 + C.size →
      (wireToFormula C w).eval x = (C.wires (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h10 : w < 10
    · rw [wireToFormula]
      simp only [h10, ↓reduceDIte, MonoFormula.eval]
      obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix C.gates (List.ofFn x)
      rw [wires_eq_foldl, hsuf]
      have hlt : w < (List.ofFn x).length := by simp [h10]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_ofFn,
        h10, ↓reduceDIte]
      rfl
    · have hj : w - 10 < C.size := by omega
      have hjlen : w - 10 < C.gates.length := hj
      have hw_eq : 10 + (w - 10) = w := by omega
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hstruct ⟨w - 10, hj⟩
      dsimp only at hop hin ha hb
      rw [hw_eq] at ha hb
      have heval_w : (C.wires (List.ofFn x)).getD w false =
          (C.gates[w - 10]'hjlen).op.eval
            [(C.wires (List.ofFn x)).getD a false, (C.wires (List.ofFn x)).getD b false] := by
        have hsplit : C.gates = C.gates.take (w - 10) ++ (C.gates[w - 10]'hjlen) :: C.gates.drop (w - 10 + 1) := by
          have h1 := List.take_append_drop (w - 10) C.gates
          have h2 : C.gates.drop (w - 10) = (C.gates[w - 10]'hjlen) :: C.gates.drop (w - 10 + 1) :=
            List.drop_eq_getElem_cons hjlen
          rw [h2] at h1; exact h1.symm
        set w1 := (C.gates.take (w - 10)).foldl stepWires (List.ofFn x)
        have hw1_len : w1.length = w := by
          rw [foldl_stepWires_length, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt hjlen)]
          omega
        obtain ⟨suf, hsuf, _⟩ := foldl_stepWires_prefix (C.gates.drop (w - 10 + 1)) (stepWires w1 (C.gates[w - 10]'hjlen))
        have hwires : C.wires (List.ofFn x) =
            w1 ++ [(C.gates[w - 10]'hjlen).op.eval ((C.gates[w - 10]'hjlen).inputs.map fun i => w1.getD i false)] ++ suf := by
          rw [wires_eq_foldl]
          conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
          exact hsuf
        have hget_lt : ∀ k < w, (C.wires (List.ofFn x)).getD k false = w1.getD k false := by
          intro k hk
          rw [hwires, List.append_assoc]
          have hkl : k < w1.length := by omega
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hkl]
        have hget_w : (C.wires (List.ofFn x)).getD w false =
            (C.gates[w - 10]'hjlen).op.eval ((C.gates[w - 10]'hjlen).inputs.map fun i => w1.getD i false) := by
          rw [hwires]
          have hlt1 : w < (w1 ++ [(C.gates[w - 10]'hjlen).op.eval ((C.gates[w - 10]'hjlen).inputs.map fun i => w1.getD i false)]).length := by
            simp [hw1_len]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
            List.getElem?_append_right (by omega : w1.length ≤ w)]
          simp [hw1_len]
        have hin' : (C.gates[w - 10]'hjlen).inputs = [a, b] := hin
        rw [hget_w, hin']
        simp only [List.map_cons, List.map_nil, hget_lt a ha, hget_lt b hb]
      rw [wireToFormula]
      have hin' : (C.gates[w - 10]'hjlen).inputs = [a, b] := hin
      simp only [h10, ↓reduceDIte, hjlen, hin', ha, hb]
      rw [heval_w]
      have hop' : (C.gates[w - 10]'hjlen).op = GateOp.and ∨ (C.gates[w - 10]'hjlen).op = GateOp.or := hop
      rcases hop' with hand | hor
      · simp only [hand, MonoFormula.eval, GateOp.eval, List.all_cons, List.all_nil, id_eq,
          Bool.and_true]
        rw [ih a ha (by omega), ih b hb (by omega)]
      · simp only [hor, MonoFormula.eval, GateOp.eval, List.any_cons, List.any_nil, id_eq,
          Bool.or_false]
        rw [ih a ha (by omega), ih b hb (by omega)]

lemma wireToFormula_leaves_telescoping (C : Circuit) (hsz : C.size = 19)
    (hout_ge : 10 ≤ C.output) (hout_lt : C.output < 10 + C.size)
    (hout0 : wireFanOut 10 C C.output = 0)
    (hgate1 : ∀ j : Fin C.size, 10 + j.val ≠ C.output → wireFanOut 10 C (10 + j.val) = 1)
    (hin2 : ∀ i : Fin 10, wireFanOut 10 C i.val = 2)
    (hstruct : ∀ j : Fin C.size,
      (C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C.gates[j.val].inputs = [a, b] ∧ a < 10 + j.val ∧ b < 10 + j.val) :
    (wireToFormula C C.output).leaves = 20 := by
  let L : ℕ → ℕ := fun w => (wireToFormula C w).leaves
  have hL_in : ∀ i : Fin 10, L i.val = 1 := by
    intro i
    dsimp [L]
    rw [wireToFormula]
    simp [i.isLt, MonoFormula.leaves]
  have hL_gate : ∀ j : Fin C.size,
      L (10 + j.val) = ∑ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w := by
    intro j
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hstruct j
    have hL_eq : L (10 + j.val) = L a + L b := by
      dsimp [L]
      rw [wireToFormula]
      have hnot10 : ¬ (10 + j.val < 10) := by omega
      have hsub : 10 + j.val - 10 = j.val := by omega
      have hjlen : j.val < C.gates.length := j.isLt
      simp only [hnot10, ↓reduceDIte, hsub, hjlen, hin, ha, hb]
      rcases hop with hand | hor
      · simp [hand, MonoFormula.leaves]
      · simp [hor, MonoFormula.leaves]
    rw [hL_eq, hin]
    have hsum_ab : ∀ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then ([a, b] : List ℕ).count w else 0) * L w =
        (if w = a then L a else 0) + (if w = b then L b else 0) := by
      intro w _
      by_cases hwa : w = a <;> by_cases hwb : w = b
      · subst hwa; subst hwb
        simp only [ha, ↓reduceIte, List.count_cons, beq_self_eq_true, List.count_nil]
        ring
      · subst hwa
        have hbb : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [ha, hwb, List.count_cons, hbb]
      · subst hwb
        have hba : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        simp [hb, hwa, List.count_cons, hba]
      · have hba : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        have hbb : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [hwa, hwb, List.count_cons, hba, hbb]
    rw [Finset.sum_congr rfl hsum_ab, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    have ha_mem : a ∈ Finset.range (10 + C.size) := Finset.mem_range.mpr (by omega)
    have hb_mem : b ∈ Finset.range (10 + C.size) := Finset.mem_range.mpr (by omega)
    simp [ha_mem, hb_mem]
  have hsum_eq : (∑ j : Fin C.size, L (10 + j.val)) =
      ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
    calc (∑ j : Fin C.size, L (10 + j.val))
        = ∑ j : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_congr rfl fun j _ => hL_gate j
      _ = ∑ w ∈ Finset.range (10 + C.size), ∑ j : Fin C.size,
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_comm
      _ = ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
          apply Finset.sum_congr rfl
          intro w _
          unfold wireFanOut
          rw [Finset.sum_mul]
  rw [Finset.sum_range_add,
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C x * L x),
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C (10 + x) * L (10 + x))] at hsum_eq
  have hpart1 : (∑ i : Fin 10, wireFanOut 10 C i.val * L i.val) = 20 := by
    simp [hin2, hL_in]
  let j0 : Fin C.size := ⟨C.output - 10, by omega⟩
  have hj0_eq : 10 + j0.val = C.output := by dsimp [j0]; omega
  have hsplit_lhs := Finset.add_sum_erase Finset.univ (fun j : Fin C.size => L (10 + j.val))
    (Finset.mem_univ j0)
  have hsplit_rhs := Finset.add_sum_erase Finset.univ
    (fun j : Fin C.size => wireFanOut 10 C (10 + j.val) * L (10 + j.val)) (Finset.mem_univ j0)
  have hrest_eq : (∑ j ∈ Finset.univ.erase j0, wireFanOut 10 C (10 + j.val) * L (10 + j.val)) =
      ∑ j ∈ Finset.univ.erase j0, L (10 + j.val) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : 10 + j.val ≠ C.output := by
      intro heq; apply (Finset.mem_erase.mp hj).1; ext; dsimp [j0]; omega
    rw [hgate1 j hne, one_mul]
  rw [← hsplit_lhs, ← hsplit_rhs, hpart1, hj0_eq, hout0, zero_mul, zero_add, hrest_eq] at hsum_eq
  dsimp [L] at hsum_eq
  omega

theorem petersen_19_dichotomy_v2 (h : HasCircuitSize 10 petersenFun 19) :
    (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧
      wireFanOut 10 C 0 = 1) ∨
    (∃ F : MonoFormula 10,
      (∀ x : Fin 10 → Bool, F.eval x = petersenFun x) ∧
      F.leaves = 20 ∧
      2 ≤ F.andDepth) := by
  obtain ⟨C, hF, hle, hev, _, hnoDead, hcases⟩ := petersen_19_dichotomy h
  rcases hcases with hf1 | ⟨hsz19, hnot0, hgate1, hin2⟩
  · exact Or.inl ⟨C, hF, hle, hev, hf1⟩
  · right
    obtain ⟨hout_ge, hout_lt⟩ := minimal_output_is_gate 10 petersenFun C hev
      petersenFun_not_false petersenFun_not_proj
    obtain ⟨hout0, hstruct⟩ := world2_gate_structure C hF hsz19 hnot0 hout_ge hout_lt hgate1 hin2
    let F := wireToFormula C C.output
    have hFeval : ∀ x : Fin 10 → Bool, F.eval x = petersenFun x := by
      intro x
      dsimp [F]
      rw [wireToFormula_eval C hstruct x C.output hout_lt]
      exact hev x
    have hFleaves : F.leaves = 20 :=
      wireToFormula_leaves_telescoping C hsz19 hout_ge hout_lt hout0 hgate1 hin2 hstruct
    have hFdepth : 2 ≤ F.andDepth := by
      by_contra hlt
      have hd1 : F.andDepth ≤ 1 := by omega
      have h21 := petersen_sigma3_leaves_ge_21 F hd1 hFeval
      omega
    exact ⟨F, hFeval, hFleaves, hFdepth⟩

lemma wireToFormula_varCount_telescoping (C : Circuit) (hsz : C.size = 19)
    (hout_ge : 10 ≤ C.output) (hout_lt : C.output < 10 + C.size)
    (hout0 : wireFanOut 10 C C.output = 0)
    (hgate1 : ∀ j : Fin C.size, 10 + j.val ≠ C.output → wireFanOut 10 C (10 + j.val) = 1)
    (hin2 : ∀ i : Fin 10, wireFanOut 10 C i.val = 2)
    (hstruct : ∀ j : Fin C.size,
      (C.gates[j.val].op = GateOp.and ∨ C.gates[j.val].op = GateOp.or) ∧
      ∃ a b : ℕ, C.gates[j.val].inputs = [a, b] ∧ a < 10 + j.val ∧ b < 10 + j.val)
    (v : Fin 10) :
    (wireToFormula C C.output).varCount v = 2 := by
  let L : ℕ → ℕ := fun w => (wireToFormula C w).varCount v
  have hL_in : ∀ i : Fin 10, L i.val = if i = v then 1 else 0 := by
    intro i
    dsimp [L]
    rw [wireToFormula]
    simp [i.isLt, MonoFormula.varCount]
  have hL_gate : ∀ j : Fin C.size,
      L (10 + j.val) = ∑ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w := by
    intro j
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hstruct j
    have hL_eq : L (10 + j.val) = L a + L b := by
      dsimp [L]
      rw [wireToFormula]
      have hnot10 : ¬ (10 + j.val < 10) := by omega
      have hsub : 10 + j.val - 10 = j.val := by omega
      have hjlen : j.val < C.gates.length := j.isLt
      simp only [hnot10, ↓reduceDIte, hsub, hjlen, hin, ha, hb]
      rcases hop with hand | hor
      · simp [hand, MonoFormula.varCount]
      · simp [hor, MonoFormula.varCount]
    rw [hL_eq, hin]
    have hsum_ab : ∀ w ∈ Finset.range (10 + C.size),
        (if w < 10 + j.val then ([a, b] : List ℕ).count w else 0) * L w =
        (if w = a then L a else 0) + (if w = b then L b else 0) := by
      intro w _
      by_cases hwa : w = a <;> by_cases hwb : w = b
      · subst hwa; subst hwb
        simp only [ha, ↓reduceIte, List.count_cons, beq_self_eq_true, List.count_nil]
        ring
      · subst hwa
        have hbb : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [ha, hwb, List.count_cons, hbb]
      · subst hwb
        have hba : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        simp [hb, hwa, List.count_cons, hba]
      · have hba : (a == w) = false := beq_false_of_ne (Ne.symm hwa)
        have hbb : (b == w) = false := beq_false_of_ne (Ne.symm hwb)
        simp [hwa, hwb, List.count_cons, hba, hbb]
    rw [Finset.sum_congr rfl hsum_ab, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    have ha_mem : a ∈ Finset.range (10 + C.size) := Finset.mem_range.mpr (by omega)
    have hb_mem : b ∈ Finset.range (10 + C.size) := Finset.mem_range.mpr (by omega)
    simp [ha_mem, hb_mem]
  have hsum_eq : (∑ j : Fin C.size, L (10 + j.val)) =
      ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
    calc (∑ j : Fin C.size, L (10 + j.val))
        = ∑ j : Fin C.size, ∑ w ∈ Finset.range (10 + C.size),
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_congr rfl fun j _ => hL_gate j
      _ = ∑ w ∈ Finset.range (10 + C.size), ∑ j : Fin C.size,
            (if w < 10 + j.val then C.gates[j.val].inputs.count w else 0) * L w :=
          Finset.sum_comm
      _ = ∑ w ∈ Finset.range (10 + C.size), wireFanOut 10 C w * L w := by
          apply Finset.sum_congr rfl
          intro w _
          unfold wireFanOut
          rw [Finset.sum_mul]
  rw [Finset.sum_range_add,
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C x * L x),
    ← Fin.sum_univ_eq_sum_range (fun x => wireFanOut 10 C (10 + x) * L (10 + x))] at hsum_eq
  have hpart1 : (∑ i : Fin 10, wireFanOut 10 C i.val * L i.val) = 2 := by
    have hcongr : ∀ i : Fin 10, wireFanOut 10 C i.val * L i.val = if i = v then 2 else 0 := by
      intro i
      rw [hin2 i, hL_in i]
      split_ifs <;> rfl
    simp [hcongr]
  let j0 : Fin C.size := ⟨C.output - 10, by omega⟩
  have hj0_eq : 10 + j0.val = C.output := by dsimp [j0]; omega
  have hsplit_lhs := Finset.add_sum_erase Finset.univ (fun j : Fin C.size => L (10 + j.val))
    (Finset.mem_univ j0)
  have hsplit_rhs := Finset.add_sum_erase Finset.univ
    (fun j : Fin C.size => wireFanOut 10 C (10 + j.val) * L (10 + j.val)) (Finset.mem_univ j0)
  have hrest_eq : (∑ j ∈ Finset.univ.erase j0, wireFanOut 10 C (10 + j.val) * L (10 + j.val)) =
      ∑ j ∈ Finset.univ.erase j0, L (10 + j.val) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : 10 + j.val ≠ C.output := by
      intro heq; apply (Finset.mem_erase.mp hj).1; ext; dsimp [j0]; omega
    rw [hgate1 j hne, one_mul]
  rw [← hsplit_lhs, ← hsplit_rhs, hpart1, hj0_eq, hout0, zero_mul, zero_add, hrest_eq] at hsum_eq
  dsimp [L] at hsum_eq
  omega

lemma MonoFormula.eval_false {n : ℕ} (F : MonoFormula n) :
    F.eval (fun _ => false) = false := by
  induction F with
  | var _ => rfl
  | and l r ihl ihr => simp [eval, ihl, ihr]
  | or l r ihl ihr => simp [eval, ihl, ihr]

lemma MonoFormula.eval_mono {n : ℕ} (F : MonoFormula n) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    F.eval x = true → F.eval y = true := by
  induction F with
  | var i => exact hxy i
  | and l r ihl ihr =>
    simp only [eval, Bool.and_eq_true]
    exact fun ⟨hl, hr⟩ => ⟨ihl hl, ihr hr⟩
  | or l r ihl ihr =>
    simp only [eval, Bool.or_eq_true]
    exact fun h => h.elim (fun hl => Or.inl (ihl hl)) (fun hr => Or.inr (ihr hr))

lemma MonoFormula.eval_congr_orVars {n : ℕ} (F : MonoFormula n) (x y : Fin n → Bool)
    (h : ∀ i ∈ F.orVars, x i = y i) :
    F.eval x = F.eval y := by
  induction F with
  | var i => exact h i (by simp [orVars])
  | and l r ihl ihr =>
    simp only [eval]
    rw [ihl (fun i hi => h i (Finset.mem_union_left _ hi)),
        ihr (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or l r ihl ihr =>
    simp only [eval]
    rw [ihl (fun i hi => h i (Finset.mem_union_left _ hi)),
        ihr (fun i hi => h i (Finset.mem_union_right _ hi))]

lemma MonoFormula.mem_orVars_iff_varCount_pos {n : ℕ} (F : MonoFormula n) (v : Fin n) :
    v ∈ F.orVars ↔ 0 < F.varCount v := by
  induction F with
  | var i =>
    simp only [orVars, Finset.mem_singleton, varCount]
    by_cases h : i = v
    · subst h; simp
    · have h' : v ≠ i := Ne.symm h; simp [h, h']
  | and l r ihl ihr =>
    simp only [orVars, Finset.mem_union, varCount, ihl, ihr]; omega
  | or l r ihl ihr =>
    simp only [orVars, Finset.mem_union, varCount, ihl, ihr]; omega

def MonoFormula.restrictFalse (S : Finset (Fin 10)) : MonoFormula 10 → Option (MonoFormula 10)
  | .var i => if i ∈ S then some (.var i) else none
  | .and l r =>
    match restrictFalse S l, restrictFalse S r with
    | some l', some r' => some (.and l' r')
    | _, _ => none
  | .or l r =>
    match restrictFalse S l, restrictFalse S r with
    | some l', some r' => some (.or l' r')
    | some l', none => some l'
    | none, some r' => some r'
    | none, none => none

lemma MonoFormula.restrictFalse_eval (S : Finset (Fin 10)) (F : MonoFormula 10) (x : Fin 10 → Bool) :
    (F.restrictFalse S).elim false (fun G => G.eval x) =
    F.eval (fun i => if i ∈ S then x i else false) := by
  induction F with
  | var i =>
    unfold restrictFalse
    split_ifs with h <;> simp [eval, h]
  | and l r ihl ihr =>
    unfold restrictFalse
    cases hl : l.restrictFalse S <;> cases hr : r.restrictFalse S <;>
      simp only [eval, ← ihl, ← ihr, hl, hr, Option.elim_none, Option.elim_some,
        Bool.false_and, Bool.and_false]
  | or l r ihl ihr =>
    unfold restrictFalse
    cases hl : l.restrictFalse S <;> cases hr : r.restrictFalse S <;>
      simp only [eval, ← ihl, ← ihr, hl, hr, Option.elim_none, Option.elim_some,
        Bool.false_or, Bool.or_false]

lemma MonoFormula.restrictFalse_orVars (S : Finset (Fin 10)) (F G : MonoFormula 10)
    (h : F.restrictFalse S = some G) : G.orVars ⊆ S := by
  induction F generalizing G with
  | var i =>
    unfold restrictFalse at h
    split_ifs at h with hi
    · cases h; simp [orVars, hi]
  | and l r ihl ihr =>
    unfold restrictFalse at h
    cases hl : l.restrictFalse S with
    | none => simp [hl] at h
    | some l' =>
      cases hr : r.restrictFalse S with
      | none => simp [hl, hr] at h
      | some r' =>
        simp [hl, hr] at h
        subst h
        exact Finset.union_subset (ihl l' hl) (ihr r' hr)
  | or l r ihl ihr =>
    unfold restrictFalse at h
    cases hl : l.restrictFalse S with
    | none =>
      cases hr : r.restrictFalse S with
      | none => simp [hl, hr] at h
      | some r' => simp [hl, hr] at h; subst h; exact ihr r' hr
    | some l' =>
      cases hr : r.restrictFalse S with
      | none => simp [hl, hr] at h; subst h; exact ihl l' hl
      | some r' =>
        simp [hl, hr] at h
        subst h
        exact Finset.union_subset (ihl l' hl) (ihr r' hr)

lemma MonoFormula.restrictFalse_varCount_le (S : Finset (Fin 10)) (F G : MonoFormula 10)
    (h : F.restrictFalse S = some G) (v : Fin 10) : G.varCount v ≤ F.varCount v := by
  induction F generalizing G with
  | var i =>
    unfold restrictFalse at h
    split_ifs at h with hi
    · cases h; exact le_refl _
  | and l r ihl ihr =>
    unfold restrictFalse at h
    cases hl : l.restrictFalse S with
    | none => simp [hl] at h
    | some l' =>
      cases hr : r.restrictFalse S with
      | none => simp [hl, hr] at h
      | some r' =>
        simp [hl, hr] at h; subst h
        exact Nat.add_le_add (ihl l' hl) (ihr r' hr)
  | or l r ihl ihr =>
    unfold restrictFalse at h
    cases hl : l.restrictFalse S with
    | none =>
      cases hr : r.restrictFalse S with
      | none => simp [hl, hr] at h
      | some r' =>
        simp [hl, hr] at h; subst h
        have := ihr r' hr; simp [varCount]; omega
    | some l' =>
      cases hr : r.restrictFalse S with
      | none =>
        simp [hl, hr] at h; subst h
        have := ihl l' hl; simp [varCount]; omega
      | some r' =>
        simp [hl, hr] at h; subst h
        exact Nat.add_le_add (ihl l' hl) (ihr r' hr)

lemma eval_pair_of_not_mem {n : ℕ} (F : MonoFormula n) (u v : Fin n)
    (hu : u ∉ F.orVars) :
    F.eval (fun i => decide (i = u ∨ i = v)) = F.eval (fun i => decide (i = v)) := by
  apply F.eval_congr_orVars
  intro i hi
  have hiu : i ≠ u := fun heq => hu (heq ▸ hi)
  simp [hiu]

lemma eval_pair_of_not_mem_both {n : ℕ} (F : MonoFormula n) (u v : Fin n)
    (hu : u ∉ F.orVars) (hv : v ∉ F.orVars) :
    F.eval (fun i => decide (i = u ∨ i = v)) = false := by
  rw [← F.eval_false]
  apply F.eval_congr_orVars
  intro i hi
  have hiu : i ≠ u := fun heq => hu (heq ▸ hi)
  have hiv : i ≠ v := fun heq => hv (heq ▸ hi)
  simp [hiu, hiv]

lemma read_once_no_p4 (a b c d : Fin 10)
    (G : MonoFormula 10)
    (hro : ∀ v : Fin 10, G.varCount v ≤ 1)
    (hs_a : G.eval (singleInput a) = false)
    (hs_b : G.eval (singleInput b) = false)
    (hs_c : G.eval (singleInput c) = false)
    (hs_d : G.eval (singleInput d) = false)
    (hab : G.eval (pairInput a b) = true)
    (hbc : G.eval (pairInput b c) = true)
    (hcd : G.eval (pairInput c d) = true)
    (had : G.eval (pairInput a d) = false) :
    False := by
  induction G with
  | var i =>
    simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at hab hbc
    rcases hab with rfl | rfl
    · simp [MonoFormula.eval, singleInput] at hs_a
    · simp [MonoFormula.eval, singleInput] at hs_b
  | or l r ihl ihr =>
    have hrol : ∀ v, l.varCount v ≤ 1 := fun v => by have := hro v; simp [MonoFormula.varCount] at this; omega
    have hror : ∀ v, r.varCount v ≤ 1 := fun v => by have := hro v; simp [MonoFormula.varCount] at this; omega
    have hdisj : ∀ v, ¬ (v ∈ l.orVars ∧ v ∈ r.orVars) := by
      intro v ⟨hl, hr⟩
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hl hr
      have := hro v; simp [MonoFormula.varCount] at this; omega
    have hsl : ∀ v, (l.or r).eval (singleInput v) = false → l.eval (singleInput v) = false ∧ r.eval (singleInput v) = false := by
      intro v hv; simp [MonoFormula.eval] at hv; exact hv
    have hpl : ∀ u v, (l.or r).eval (pairInput u v) = true →
        (l.eval (singleInput u) = false ∧ r.eval (singleInput u) = false) →
        (l.eval (singleInput v) = false ∧ r.eval (singleInput v) = false) →
        (u ∈ l.orVars ∧ v ∈ l.orVars ∧ l.eval (pairInput u v) = true) ∨
        (u ∈ r.orVars ∧ v ∈ r.orVars ∧ r.eval (pairInput u v) = true) := by
      intro u v huv ⟨hlu, hru⟩ ⟨hlv, hrv⟩
      simp only [MonoFormula.eval, Bool.or_eq_true] at huv
      rcases huv with hl | hr
      · left
        have hu : u ∈ l.orVars := by
          by_contra hnu
          have := eval_pair_of_not_mem l u v hnu
          change l.eval (pairInput u v) = l.eval (singleInput v) at this
          rw [this, hlv] at hl; exact absurd hl (by decide)
        have hv : v ∈ l.orVars := by
          by_contra hnv
          have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
          rw [hsym] at hl
          have := eval_pair_of_not_mem l v u hnv
          change l.eval (pairInput v u) = l.eval (singleInput u) at this
          rw [this, hlu] at hl; exact absurd hl (by decide)
        exact ⟨hu, hv, hl⟩
      · right
        have hu : u ∈ r.orVars := by
          by_contra hnu
          have := eval_pair_of_not_mem r u v hnu
          change r.eval (pairInput u v) = r.eval (singleInput v) at this
          rw [this, hrv] at hr; exact absurd hr (by decide)
        have hv : v ∈ r.orVars := by
          by_contra hnv
          have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
          rw [hsym] at hr
          have := eval_pair_of_not_mem r v u hnv
          change r.eval (pairInput v u) = r.eval (singleInput u) at this
          rw [this, hru] at hr; exact absurd hr (by decide)
        exact ⟨hu, hv, hr⟩
    have ha0 := hsl a hs_a
    have hb0 := hsl b hs_b
    have hc0 := hsl c hs_c
    have hd0 := hsl d hs_d
    have had0 : l.eval (pairInput a d) = false ∧ r.eval (pairInput a d) = false := by
      simp [MonoFormula.eval] at had; exact had
    rcases hpl a b hab ha0 hb0 with ⟨hal, hbl, habl⟩ | ⟨har, hbr, habr⟩
    · rcases hpl b c hbc hb0 hc0 with ⟨_, hcl, hbcl⟩ | ⟨hbr, _, _⟩
      · rcases hpl c d hcd hc0 hd0 with ⟨_, _, hcdl⟩ | ⟨hcr, _, _⟩
        · exact ihl hrol ha0.1 hb0.1 hc0.1 hd0.1 habl hbcl hcdl had0.1
        · exact hdisj c ⟨hcl, hcr⟩
      · exact hdisj b ⟨hbl, hbr⟩
    · rcases hpl b c hbc hb0 hc0 with ⟨hbl, _, _⟩ | ⟨_, hcr, hbcr⟩
      · exact hdisj b ⟨hbl, hbr⟩
      · rcases hpl c d hcd hc0 hd0 with ⟨hcl, _, _⟩ | ⟨_, _, hcdr⟩
        · exact hdisj c ⟨hcl, hcr⟩
        · exact ihr hror ha0.2 hb0.2 hc0.2 hd0.2 habr hbcr hcdr had0.2
  | and l r _ _ =>
    have hdisj : ∀ v, ¬ (v ∈ l.orVars ∧ v ∈ r.orVars) := by
      intro v ⟨hl, hr⟩
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hl hr
      have := hro v; simp [MonoFormula.varCount] at this; omega
    have hcross : ∀ u v, (l.and r).eval (pairInput u v) = true →
        (u ∈ l.orVars ∧ v ∈ r.orVars ∧ l.eval (singleInput u) = true ∧ r.eval (singleInput v) = true) ∨
        (u ∈ r.orVars ∧ v ∈ l.orVars ∧ r.eval (singleInput u) = true ∧ l.eval (singleInput v) = true) := by
      intro u v huv
      simp only [MonoFormula.eval, Bool.and_eq_true] at huv
      obtain ⟨hl, hr⟩ := huv
      have hul_or_vl : u ∈ l.orVars ∨ v ∈ l.orVars := by
        by_contra h
        push Not at h
        have hf := eval_pair_of_not_mem_both l u v h.1 h.2
        change l.eval (pairInput u v) = false at hf
        rw [hf] at hl; exact absurd hl (by decide)
      have hur_or_vr : u ∈ r.orVars ∨ v ∈ r.orVars := by
        by_contra h
        push Not at h
        have hf := eval_pair_of_not_mem_both r u v h.1 h.2
        change r.eval (pairInput u v) = false at hf
        rw [hf] at hr; exact absurd hr (by decide)
      rcases hul_or_vl with hul | hvl <;> rcases hur_or_vr with hur | hvr
      · exact absurd ⟨hul, hur⟩ (hdisj u)
      · left
        have hnv_l : v ∉ l.orVars := fun hv => hdisj v ⟨hv, hvr⟩
        have hnu_r : u ∉ r.orVars := fun hu => hdisj u ⟨hul, hu⟩
        have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
        have hl' : l.eval (singleInput u) = true := by
          have := eval_pair_of_not_mem l v u hnv_l
          change l.eval (pairInput v u) = l.eval (singleInput u) at this
          rw [← this, ← hsym]; exact hl
        have hr' : r.eval (singleInput v) = true := by
          have := eval_pair_of_not_mem r u v hnu_r
          change r.eval (pairInput u v) = r.eval (singleInput v) at this
          rw [← this]; exact hr
        exact ⟨hul, hvr, hl', hr'⟩
      · right
        have hnu_l : u ∉ l.orVars := fun hu => hdisj u ⟨hu, hur⟩
        have hnv_r : v ∉ r.orVars := fun hv => hdisj v ⟨hvl, hv⟩
        have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
        have hr' : r.eval (singleInput u) = true := by
          have := eval_pair_of_not_mem r v u hnv_r
          change r.eval (pairInput v u) = r.eval (singleInput u) at this
          rw [← this, ← hsym]; exact hr
        have hl' : l.eval (singleInput v) = true := by
          have := eval_pair_of_not_mem l u v hnu_l
          change l.eval (pairInput u v) = l.eval (singleInput v) at this
          rw [← this]; exact hl
        exact ⟨hur, hvl, hr', hl'⟩
      · exact absurd ⟨hvl, hvr⟩ (hdisj v)
    rcases hcross a b hab with ⟨hal, hbr, hla, _⟩ | ⟨har, hbl, hra, _⟩
    · rcases hcross b c hbc with ⟨hbl, _, _, _⟩ | ⟨_, hcl, _, _⟩
      · exact hdisj b ⟨hbl, hbr⟩
      · rcases hcross c d hcd with ⟨_, hdr, _, hrd⟩ | ⟨hcr, _, _, _⟩
        · have had1 : (l.and r).eval (pairInput a d) = true := by
            simp only [MonoFormula.eval, Bool.and_eq_true]
            exact ⟨l.eval_mono (singleInput a) (pairInput a d) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hla,
              r.eval_mono (singleInput d) (pairInput a d) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hrd⟩
          rw [had] at had1; exact absurd had1 (by decide)
        · exact hdisj c ⟨hcl, hcr⟩
    · rcases hcross b c hbc with ⟨_, hcr, _, _⟩ | ⟨hbr, _, _, _⟩
      · rcases hcross c d hcd with ⟨hcl, _, _, _⟩ | ⟨_, hdl, _, hld⟩
        · exact hdisj c ⟨hcl, hcr⟩
        · have had1 : (l.and r).eval (pairInput a d) = true := by
            simp only [MonoFormula.eval, Bool.and_eq_true]
            exact ⟨l.eval_mono (singleInput d) (pairInput a d) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hld,
              r.eval_mono (singleInput a) (pairInput a d) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hra⟩
          rw [had] at had1; exact absurd had1 (by decide)
      · exact hdisj b ⟨hbl, hbr⟩

lemma spider_no_1_read2 (u0 x1 y1 x2 y2 x3 y3 : Fin 10)
    (G : MonoFormula 10)
    (hcnt0 : G.varCount u0 ≤ 2)
    (hcnt_other : ∀ v : Fin 10, v ≠ u0 → G.varCount v ≤ 1)
    (hs : ∀ v ∈ ({u0, x1, y1, x2, y2, x3, y3} : Finset (Fin 10)), G.eval (singleInput v) = false)
    (he1 : G.eval (pairInput u0 x1) = true) (hf1 : G.eval (pairInput x1 y1) = true)
    (he2 : G.eval (pairInput u0 x2) = true) (hf2 : G.eval (pairInput x2 y2) = true)
    (he3 : G.eval (pairInput u0 x3) = true) (hf3 : G.eval (pairInput x3 y3) = true)
    (hne_x1x2 : G.eval (pairInput x1 x2) = false)
    (hne_x1y2 : G.eval (pairInput x1 y2) = false)
    (hne_y1x2 : G.eval (pairInput y1 x2) = false)
    (hne_y1y2 : G.eval (pairInput y1 y2) = false)
    (hne_u0y1 : G.eval (pairInput u0 y1) = false)
    (hne_u0y2 : G.eval (pairInput u0 y2) = false)
    (hne_u0y3 : G.eval (pairInput u0 y3) = false)
    (hne_y1x3 : G.eval (pairInput y1 x3) = false)
    (hne_y2x3 : G.eval (pairInput y2 x3) = false)
    (hdistinct : x1 ≠ u0 ∧ y1 ≠ u0 ∧ x2 ≠ u0 ∧ y2 ≠ u0 ∧ x3 ≠ u0 ∧ y3 ≠ u0) :
    False := by
  induction G with
  | var i =>
    simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at hf1
    rcases hf1 with h | h
    · have := hs x1 (by simp); rw [← h] at this; simp [MonoFormula.eval, singleInput] at this
    · have := hs y1 (by simp); rw [← h] at this; simp [MonoFormula.eval, singleInput] at this
  | and l r _ _ =>
    have hdisj : ∀ v : Fin 10, v ≠ u0 → ¬ (v ∈ l.orVars ∧ v ∈ r.orVars) := by
      intro v hvu ⟨hl, hr⟩
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hl hr
      have := hcnt_other v hvu; simp [MonoFormula.varCount] at this; omega
    have hcross : ∀ u v : Fin 10, u ≠ u0 → v ≠ u0 → (l.and r).eval (pairInput u v) = true →
        (l.eval (singleInput u) = true ∧ r.eval (singleInput v) = true) ∨
        (r.eval (singleInput u) = true ∧ l.eval (singleInput v) = true) := by
      intro u v hu hv huv
      simp only [MonoFormula.eval, Bool.and_eq_true] at huv
      obtain ⟨hl, hr⟩ := huv
      have hul_or_vl : u ∈ l.orVars ∨ v ∈ l.orVars := by
        by_contra h; push Not at h
        have hf := eval_pair_of_not_mem_both l u v h.1 h.2
        change l.eval (pairInput u v) = false at hf; rw [hf] at hl; exact absurd hl (by decide)
      have hur_or_vr : u ∈ r.orVars ∨ v ∈ r.orVars := by
        by_contra h; push Not at h
        have hf := eval_pair_of_not_mem_both r u v h.1 h.2
        change r.eval (pairInput u v) = false at hf; rw [hf] at hr; exact absurd hr (by decide)
      have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
      rcases hul_or_vl with hul | hvl <;> rcases hur_or_vr with hur | hvr
      · exact absurd ⟨hul, hur⟩ (hdisj u hu)
      · left
        have hnv_l : v ∉ l.orVars := fun h => hdisj v hv ⟨h, hvr⟩
        have hnu_r : u ∉ r.orVars := fun h => hdisj u hu ⟨hul, h⟩
        have hl' : l.eval (singleInput u) = true := by
          have := eval_pair_of_not_mem l v u hnv_l
          change l.eval (pairInput v u) = l.eval (singleInput u) at this
          rw [← this, ← hsym]; exact hl
        have hr' : r.eval (singleInput v) = true := by
          have := eval_pair_of_not_mem r u v hnu_r
          change r.eval (pairInput u v) = r.eval (singleInput v) at this
          rw [← this]; exact hr
        exact ⟨hl', hr'⟩
      · right
        have hnu_l : u ∉ l.orVars := fun h => hdisj u hu ⟨h, hur⟩
        have hnv_r : v ∉ r.orVars := fun h => hdisj v hv ⟨hvl, h⟩
        have hr' : r.eval (singleInput u) = true := by
          have := eval_pair_of_not_mem r v u hnv_r
          change r.eval (pairInput v u) = r.eval (singleInput u) at this
          rw [← this, ← hsym]; exact hr
        have hl' : l.eval (singleInput v) = true := by
          have := eval_pair_of_not_mem l u v hnu_l
          change l.eval (pairInput u v) = l.eval (singleInput v) at this
          rw [← this]; exact hl
        exact ⟨hr', hl'⟩
      · exact absurd ⟨hvl, hvr⟩ (hdisj v hv)
    have hcontra : ∀ u v : Fin 10, l.eval (singleInput u) = true → r.eval (singleInput v) = true →
        (l.and r).eval (pairInput u v) = false → False := by
      intro u v hlu hrv hfalse
      have ht : (l.and r).eval (pairInput u v) = true := by
        simp only [MonoFormula.eval, Bool.and_eq_true]
        exact ⟨l.eval_mono (singleInput u) (pairInput u v) (fun i hi => by
          simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hlu,
          r.eval_mono (singleInput v) (pairInput u v) (fun i hi => by
          simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hrv⟩
      rw [hfalse] at ht; exact absurd ht (by decide)
    rcases hcross x1 y1 hdistinct.1 hdistinct.2.1 hf1 with ⟨hlx1, hry1⟩ | ⟨hrx1, hly1⟩
    · rcases hcross x2 y2 hdistinct.2.2.1 hdistinct.2.2.2.1 hf2 with ⟨hlx2, hry2⟩ | ⟨hrx2, hly2⟩
      · exact hcontra x1 y2 hlx1 hry2 hne_x1y2
      · exact hcontra x1 x2 hlx1 hrx2 hne_x1x2
    · rcases hcross x2 y2 hdistinct.2.2.1 hdistinct.2.2.2.1 hf2 with ⟨hlx2, hry2⟩ | ⟨hrx2, hly2⟩
      · exact hcontra y1 y2 hly1 hry2 hne_y1y2
      · exact hcontra y1 x2 hly1 hrx2 hne_y1x2
  | or l r ihl ihr =>
    have hs_lr : ∀ v ∈ ({u0, x1, y1, x2, y2, x3, y3} : Finset (Fin 10)),
        l.eval (singleInput v) = false ∧ r.eval (singleInput v) = false := by
      intro v hv
      have h := hs v hv
      simp [MonoFormula.eval] at h
      exact h
    have hdisj : ∀ v : Fin 10, v ≠ u0 → ¬ (v ∈ l.orVars ∧ v ∈ r.orVars) := by
      intro v hvu ⟨hl, hr⟩
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hl hr
      have := hcnt_other v hvu; simp [MonoFormula.varCount] at this; omega
    have hleg : ∀ x y : Fin 10, x ≠ u0 → y ≠ u0 →
        x ∈ ({u0, x1, y1, x2, y2, x3, y3} : Finset (Fin 10)) →
        y ∈ ({u0, x1, y1, x2, y2, x3, y3} : Finset (Fin 10)) →
        (l.or r).eval (pairInput u0 x) = true → (l.or r).eval (pairInput x y) = true →
        (x ∈ l.orVars ∧ y ∈ l.orVars ∧ l.eval (pairInput u0 x) = true ∧ l.eval (pairInput x y) = true) ∨
        (x ∈ r.orVars ∧ y ∈ r.orVars ∧ r.eval (pairInput u0 x) = true ∧ r.eval (pairInput x y) = true) := by
      intro x y hxu hyu hxm hym hux hxy
      have hs0 := hs_lr u0 (by simp)
      have hsx := hs_lr x hxm
      have hsy := hs_lr y hym
      have hsym_ux : pairInput u0 x = pairInput x u0 := by funext i; simp [pairInput, or_comm]
      have hsym_xy : pairInput x y = pairInput y x := by funext i; simp [pairInput, or_comm]
      simp only [MonoFormula.eval, Bool.or_eq_true] at hxy
      rcases hxy with hlxy | hrxy
      · have hxl : x ∈ l.orVars := by
          by_contra hn
          have := eval_pair_of_not_mem l x y hn
          change l.eval (pairInput x y) = l.eval (singleInput y) at this
          rw [this, hsy.1] at hlxy; exact absurd hlxy (by decide)
        have hyl : y ∈ l.orVars := by
          by_contra hn
          rw [hsym_xy] at hlxy
          have := eval_pair_of_not_mem l y x hn
          change l.eval (pairInput y x) = l.eval (singleInput x) at this
          rw [this, hsx.1] at hlxy; exact absurd hlxy (by decide)
        have hxr_not : x ∉ r.orVars := fun h => hdisj x hxu ⟨hxl, h⟩
        have hrux : r.eval (pairInput u0 x) = false := by
          rw [hsym_ux]
          have := eval_pair_of_not_mem r x u0 hxr_not
          change r.eval (pairInput x u0) = r.eval (singleInput u0) at this
          rw [this]; exact hs0.2
        simp only [MonoFormula.eval, hrux, Bool.or_false] at hux
        exact Or.inl ⟨hxl, hyl, hux, hlxy⟩
      · have hxr : x ∈ r.orVars := by
          by_contra hn
          have := eval_pair_of_not_mem r x y hn
          change r.eval (pairInput x y) = r.eval (singleInput y) at this
          rw [this, hsy.2] at hrxy; exact absurd hrxy (by decide)
        have hyr : y ∈ r.orVars := by
          by_contra hn
          rw [hsym_xy] at hrxy
          have := eval_pair_of_not_mem r y x hn
          change r.eval (pairInput y x) = r.eval (singleInput x) at this
          rw [this, hsx.2] at hrxy; exact absurd hrxy (by decide)
        have hxl_not : x ∉ l.orVars := fun h => hdisj x hxu ⟨h, hxr⟩
        have hlux : l.eval (pairInput u0 x) = false := by
          rw [hsym_ux]
          have := eval_pair_of_not_mem l x u0 hxl_not
          change l.eval (pairInput x u0) = l.eval (singleInput u0) at this
          rw [this]; exact hs0.1
        simp only [MonoFormula.eval, hlux, Bool.false_or] at hux
        exact Or.inr ⟨hxr, hyr, hux, hrxy⟩
    have hl_false : ∀ u v, (l.or r).eval (pairInput u v) = false →
        l.eval (pairInput u v) = false ∧ r.eval (pairInput u v) = false := by
      intro u v h; simp [MonoFormula.eval] at h; exact h
    have hleg1 := hleg x1 y1 hdistinct.1 hdistinct.2.1 (by simp) (by simp) he1 hf1
    have hleg2 := hleg x2 y2 hdistinct.2.2.1 hdistinct.2.2.2.1 (by simp) (by simp) he2 hf2
    have hleg3 := hleg x3 y3 hdistinct.2.2.2.2.1 hdistinct.2.2.2.2.2 (by simp) (by simp) he3 hf3
    by_cases h0l : l.varCount u0 = 0
    · have hu0_not_l : u0 ∉ l.orVars := by rw [MonoFormula.mem_orVars_iff_varCount_pos]; omega
      have hno_l : ∀ x, x ∈ ({u0, x1, y1, x2, y2, x3, y3} : Finset (Fin 10)) →
          l.eval (pairInput u0 x) = false := by
        intro x hxm
        have := eval_pair_of_not_mem l u0 x hu0_not_l
        change l.eval (pairInput u0 x) = l.eval (singleInput x) at this
        rw [this]; exact (hs_lr x hxm).1
      rcases hleg1 with ⟨_, _, h1, _⟩ | ⟨_, _, he1r, hf1r⟩
      · rw [hno_l x1 (by simp)] at h1; exact absurd h1 (by decide)
      · rcases hleg2 with ⟨_, _, h2, _⟩ | ⟨_, _, he2r, hf2r⟩
        · rw [hno_l x2 (by simp)] at h2; exact absurd h2 (by decide)
        · rcases hleg3 with ⟨_, _, h3, _⟩ | ⟨_, _, he3r, hf3r⟩
          · rw [hno_l x3 (by simp)] at h3; exact absurd h3 (by decide)
          · exact ihr (by simp [MonoFormula.varCount] at hcnt0; omega)
              (fun v hv => by have := hcnt_other v hv; simp [MonoFormula.varCount] at this; omega)
              (fun v hv => (hs_lr v hv).2)
              he1r hf1r he2r hf2r he3r hf3r
              (hl_false _ _ hne_x1x2).2 (hl_false _ _ hne_x1y2).2
              (hl_false _ _ hne_y1x2).2 (hl_false _ _ hne_y1y2).2
              (hl_false _ _ hne_u0y1).2 (hl_false _ _ hne_u0y2).2
              (hl_false _ _ hne_u0y3).2 (hl_false _ _ hne_y1x3).2
              (hl_false _ _ hne_y2x3).2
    · by_cases h0r : r.varCount u0 = 0
      · have hu0_not_r : u0 ∉ r.orVars := by rw [MonoFormula.mem_orVars_iff_varCount_pos]; omega
        have hno_r : ∀ x, x ∈ ({u0, x1, y1, x2, y2, x3, y3} : Finset (Fin 10)) →
            r.eval (pairInput u0 x) = false := by
          intro x hxm
          have := eval_pair_of_not_mem r u0 x hu0_not_r
          change r.eval (pairInput u0 x) = r.eval (singleInput x) at this
          rw [this]; exact (hs_lr x hxm).2
        rcases hleg1 with ⟨_, _, he1l, hf1l⟩ | ⟨_, _, h1, _⟩
        · rcases hleg2 with ⟨_, _, he2l, hf2l⟩ | ⟨_, _, h2, _⟩
          · rcases hleg3 with ⟨_, _, he3l, hf3l⟩ | ⟨_, _, h3, _⟩
            · exact ihl (by simp [MonoFormula.varCount] at hcnt0; omega)
                (fun v hv => by have := hcnt_other v hv; simp [MonoFormula.varCount] at this; omega)
                (fun v hv => (hs_lr v hv).1)
                he1l hf1l he2l hf2l he3l hf3l
                (hl_false _ _ hne_x1x2).1 (hl_false _ _ hne_x1y2).1
                (hl_false _ _ hne_y1x2).1 (hl_false _ _ hne_y1y2).1
                (hl_false _ _ hne_u0y1).1 (hl_false _ _ hne_u0y2).1
                (hl_false _ _ hne_u0y3).1 (hl_false _ _ hne_y1x3).1
                (hl_false _ _ hne_y2x3).1
            · rw [hno_r x3 (by simp)] at h3; exact absurd h3 (by decide)
          · rw [hno_r x2 (by simp)] at h2; exact absurd h2 (by decide)
        · rw [hno_r x1 (by simp)] at h1; exact absurd h1 (by decide)
      · have hrol : ∀ v : Fin 10, l.varCount v ≤ 1 := by
          intro v
          by_cases hv : v = u0
          · subst hv; simp [MonoFormula.varCount] at hcnt0; omega
          · have := hcnt_other v hv; simp [MonoFormula.varCount] at this; omega
        have hror : ∀ v : Fin 10, r.varCount v ≤ 1 := by
          intro v
          by_cases hv : v = u0
          · subst hv; simp [MonoFormula.varCount] at hcnt0; omega
          · have := hcnt_other v hv; simp [MonoFormula.varCount] at this; omega
        have hsym_pair : ∀ a b : Fin 10, pairInput a b = pairInput b a :=
          fun a b => by funext i; simp [pairInput, or_comm]
        rcases hleg1 with ⟨_, _, he1l, hf1l⟩ | ⟨_, _, he1r, hf1r⟩ <;>
        rcases hleg2 with ⟨_, _, he2l, hf2l⟩ | ⟨_, _, he2r, hf2r⟩
        · exact read_once_no_p4 y1 x1 u0 x2 l hrol
            (hs_lr y1 (by simp)).1 (hs_lr x1 (by simp)).1 (hs_lr u0 (by simp)).1 (hs_lr x2 (by simp)).1
            (by rw [hsym_pair]; exact hf1l) (by rw [hsym_pair]; exact he1l) he2l (hl_false _ _ hne_y1x2).1
        · rcases hleg3 with ⟨_, _, he3l, hf3l⟩ | ⟨_, _, he3r, hf3r⟩
          · exact read_once_no_p4 y1 x1 u0 x3 l hrol
              (hs_lr y1 (by simp)).1 (hs_lr x1 (by simp)).1 (hs_lr u0 (by simp)).1 (hs_lr x3 (by simp)).1
              (by rw [hsym_pair]; exact hf1l) (by rw [hsym_pair]; exact he1l) he3l (hl_false _ _ hne_y1x3).1
          · exact read_once_no_p4 y2 x2 u0 x3 r hror
              (hs_lr y2 (by simp)).2 (hs_lr x2 (by simp)).2 (hs_lr u0 (by simp)).2 (hs_lr x3 (by simp)).2
              (by rw [hsym_pair]; exact hf2r) (by rw [hsym_pair]; exact he2r) he3r (hl_false _ _ hne_y2x3).2
        · rcases hleg3 with ⟨_, _, he3l, hf3l⟩ | ⟨_, _, he3r, hf3r⟩
          · exact read_once_no_p4 y2 x2 u0 x3 l hrol
              (hs_lr y2 (by simp)).1 (hs_lr x2 (by simp)).1 (hs_lr u0 (by simp)).1 (hs_lr x3 (by simp)).1
              (by rw [hsym_pair]; exact hf2l) (by rw [hsym_pair]; exact he2l) he3l (hl_false _ _ hne_y2x3).1
          · exact read_once_no_p4 y1 x1 u0 x3 r hror
              (hs_lr y1 (by simp)).2 (hs_lr x1 (by simp)).2 (hs_lr u0 (by simp)).2 (hs_lr x3 (by simp)).2
              (by rw [hsym_pair]; exact hf1r) (by rw [hsym_pair]; exact he1r) he3r (hl_false _ _ hne_y1x3).2
        · exact read_once_no_p4 y1 x1 u0 x2 r hror
            (hs_lr y1 (by simp)).2 (hs_lr x1 (by simp)).2 (hs_lr u0 (by simp)).2 (hs_lr x2 (by simp)).2
            (by rw [hsym_pair]; exact hf1r) (by rw [hsym_pair]; exact he1r) he2r (hl_false _ _ hne_y1x2).2

lemma read_once_bipartite (M : Finset (Fin 10)) (G : MonoFormula 10)
    (hro : ∀ v : Fin 10, G.varCount v ≤ 1)
    (hs : ∀ v ∈ M, G.eval (singleInput v) = false)
    (he : ∀ u ∈ M, ∀ v ∈ M, petersenAdj u v = true → G.eval (pairInput u v) = true) :
    ∃ col : Fin 10 → Bool, ∀ u ∈ M, ∀ v ∈ M, petersenAdj u v = true → col u ≠ col v := by
  induction G generalizing M with
  | var i =>
    refine ⟨fun _ => false, ?_⟩
    intro u hu v hv hadj
    have h1 := he u hu v hv hadj
    simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at h1
    rcases h1 with h | h
    · have := hs u hu; rw [← h] at this; simp [MonoFormula.eval, singleInput] at this
    · have := hs v hv; rw [← h] at this; simp [MonoFormula.eval, singleInput] at this
  | and l r _ _ =>
    have hdisj : ∀ v, ¬ (v ∈ l.orVars ∧ v ∈ r.orVars) := by
      intro v ⟨hl, hr⟩
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hl hr
      have := hro v; simp [MonoFormula.varCount] at this; omega
    refine ⟨fun v => decide (v ∈ l.orVars), ?_⟩
    intro u hu v hv hadj
    have h1 := he u hu v hv hadj
    simp only [MonoFormula.eval, Bool.and_eq_true] at h1
    have hul_or_vl : u ∈ l.orVars ∨ v ∈ l.orVars := by
      by_contra h; push Not at h
      have hf := eval_pair_of_not_mem_both l u v h.1 h.2
      change l.eval (pairInput u v) = false at hf; rw [hf] at h1; exact absurd h1.1 (by decide)
    have hur_or_vr : u ∈ r.orVars ∨ v ∈ r.orVars := by
      by_contra h; push Not at h
      have hf := eval_pair_of_not_mem_both r u v h.1 h.2
      change r.eval (pairInput u v) = false at hf; rw [hf] at h1; exact absurd h1.2 (by decide)
    rcases hul_or_vl with hul | hvl <;> rcases hur_or_vr with hur | hvr
    · exact absurd ⟨hul, hur⟩ (hdisj u)
    · have hnv : v ∉ l.orVars := fun h => hdisj v ⟨h, hvr⟩
      simp [hul, hnv]
    · have hnu : u ∉ l.orVars := fun h => hdisj u ⟨h, hur⟩
      simp [hnu, hvl]
    · exact absurd ⟨hvl, hvr⟩ (hdisj v)
  | or l r ihl ihr =>
    have hrol : ∀ v, l.varCount v ≤ 1 := fun v => by have := hro v; simp [MonoFormula.varCount] at this; omega
    have hror : ∀ v, r.varCount v ≤ 1 := fun v => by have := hro v; simp [MonoFormula.varCount] at this; omega
    have hdisj : ∀ v, ¬ (v ∈ l.orVars ∧ v ∈ r.orVars) := by
      intro v ⟨hl, hr⟩
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hl hr
      have := hro v; simp [MonoFormula.varCount] at this; omega
    have hs_lr : ∀ v ∈ M, l.eval (singleInput v) = false ∧ r.eval (singleInput v) = false := by
      intro v hv; have h := hs v hv; simp [MonoFormula.eval] at h; exact h
    have hsplit_e : ∀ u ∈ M, ∀ v ∈ M, petersenAdj u v = true →
        (u ∈ l.orVars ∧ v ∈ l.orVars ∧ l.eval (pairInput u v) = true) ∨
        (u ∈ r.orVars ∧ v ∈ r.orVars ∧ r.eval (pairInput u v) = true) := by
      intro u hu v hv hadj
      have h1 := he u hu v hv hadj
      simp only [MonoFormula.eval, Bool.or_eq_true] at h1
      have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
      rcases h1 with hl | hr
      · left
        have hul : u ∈ l.orVars := by
          by_contra hn
          have := eval_pair_of_not_mem l u v hn
          change l.eval (pairInput u v) = l.eval (singleInput v) at this
          rw [this, (hs_lr v hv).1] at hl; exact absurd hl (by decide)
        have hvl : v ∈ l.orVars := by
          by_contra hn
          rw [hsym] at hl
          have := eval_pair_of_not_mem l v u hn
          change l.eval (pairInput v u) = l.eval (singleInput u) at this
          rw [this, (hs_lr u hu).1] at hl; exact absurd hl (by decide)
        exact ⟨hul, hvl, hl⟩
      · right
        have hur : u ∈ r.orVars := by
          by_contra hn
          have := eval_pair_of_not_mem r u v hn
          change r.eval (pairInput u v) = r.eval (singleInput v) at this
          rw [this, (hs_lr v hv).2] at hr; exact absurd hr (by decide)
        have hvr : v ∈ r.orVars := by
          by_contra hn
          rw [hsym] at hr
          have := eval_pair_of_not_mem r v u hn
          change r.eval (pairInput v u) = r.eval (singleInput u) at this
          rw [this, (hs_lr u hu).2] at hr; exact absurd hr (by decide)
        exact ⟨hur, hvr, hr⟩
    obtain ⟨col1, hcol1⟩ := ihl (M ∩ l.orVars) hrol
      (fun v hv => (hs_lr v (Finset.mem_inter.mp hv).1).1)
      (fun u hu v hv hadj => by
        rcases hsplit_e u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1 hadj with
          ⟨_, _, hl⟩ | ⟨hur, _, _⟩
        · exact hl
        · exact absurd ⟨(Finset.mem_inter.mp hu).2, hur⟩ (hdisj u))
    obtain ⟨col2, hcol2⟩ := ihr (M ∩ r.orVars) hror
      (fun v hv => (hs_lr v (Finset.mem_inter.mp hv).1).2)
      (fun u hu v hv hadj => by
        rcases hsplit_e u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1 hadj with
          ⟨hul, _, _⟩ | ⟨_, _, hr⟩
        · exact absurd ⟨hul, (Finset.mem_inter.mp hu).2⟩ (hdisj u)
        · exact hr)
    refine ⟨fun v => if v ∈ l.orVars then col1 v else col2 v, ?_⟩
    intro u hu v hv hadj
    rcases hsplit_e u hu v hv hadj with ⟨hul, hvl, _⟩ | ⟨hur, hvr, _⟩
    · simp only [hul, hvl, ↓reduceIte]
      exact hcol1 u (Finset.mem_inter.mpr ⟨hu, hul⟩) v (Finset.mem_inter.mpr ⟨hv, hvl⟩) hadj
    · have hnu : u ∉ l.orVars := fun h => hdisj u ⟨h, hur⟩
      have hnv : v ∉ l.orVars := fun h => hdisj v ⟨h, hvr⟩
      simp only [hnu, hnv, ↓reduceIte]
      exact hcol2 u (Finset.mem_inter.mpr ⟨hu, hur⟩) v (Finset.mem_inter.mpr ⟨hv, hvr⟩) hadj

def petersenC5s : List (Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10) :=
  [(0, 1, 2, 3, 4), (0, 1, 2, 7, 5), (0, 1, 6, 8, 5), (0, 1, 6, 9, 4),
   (0, 4, 9, 7, 5), (0, 4, 3, 8, 5), (1, 2, 3, 8, 6), (1, 2, 7, 9, 6),
   (2, 3, 8, 5, 7), (2, 3, 4, 9, 7), (3, 4, 9, 6, 8), (5, 7, 9, 6, 8)]

lemma petersenC5s_valid :
    ∀ c ∈ petersenC5s,
      petersenAdj c.1 c.2.1 = true ∧ petersenAdj c.2.1 c.2.2.1 = true ∧
      petersenAdj c.2.2.1 c.2.2.2.1 = true ∧ petersenAdj c.2.2.2.1 c.2.2.2.2 = true ∧
      petersenAdj c.2.2.2.2 c.1 = true := by
  decide

lemma petersen_del2_has_c5 :
    ∀ u v : Fin 10, petersenAdj u v = false →
      ∃ c ∈ petersenC5s,
        u ≠ c.1 ∧ u ≠ c.2.1 ∧ u ≠ c.2.2.1 ∧ u ≠ c.2.2.2.1 ∧ u ≠ c.2.2.2.2 ∧
        v ≠ c.1 ∧ v ≠ c.2.1 ∧ v ≠ c.2.2.1 ∧ v ≠ c.2.2.2.1 ∧ v ≠ c.2.2.2.2 := by
  decide

lemma c5_not_bipartite (a b c d e : Fin 10) (col : Fin 10 → Bool)
    (h1 : col a ≠ col b) (h2 : col b ≠ col c) (h3 : col c ≠ col d)
    (h4 : col d ≠ col e) (h5 : col e ≠ col a) : False := by
  cases ha : col a <;> cases hb : col b <;> cases hc : col c <;>
  cases hd : col d <;> cases he : col e <;> simp_all

def petersenInd3Witness : List ((Fin 10 × Fin 10 × Fin 10) × (Fin 10 × Fin 10 × Fin 10 × Fin 10)) :=
  [((0, 2, 6), (3, 4, 9, 7)), ((0, 2, 8), (1, 6, 9, 4)), ((0, 2, 9), (1, 6, 8, 3)),
   ((0, 3, 6), (1, 2, 7, 5)), ((0, 3, 7), (1, 6, 8, 5)), ((0, 3, 9), (1, 2, 7, 5)),
   ((0, 6, 7), (1, 2, 3, 4)), ((0, 7, 8), (1, 2, 3, 4)), ((0, 8, 9), (1, 2, 3, 4)),
   ((1, 3, 5), (0, 4, 9, 6)), ((1, 3, 7), (0, 4, 9, 6)), ((1, 3, 9), (0, 5, 7, 2)),
   ((1, 4, 5), (2, 3, 8, 6)), ((1, 4, 7), (0, 5, 8, 3)), ((1, 4, 8), (0, 5, 7, 2)),
   ((1, 5, 9), (0, 4, 3, 2)), ((1, 7, 8), (0, 4, 3, 2)), ((1, 8, 9), (0, 4, 3, 2)),
   ((2, 4, 5), (0, 1, 6, 8)), ((2, 4, 6), (0, 5, 7, 9)), ((2, 4, 8), (0, 1, 6, 9)),
   ((2, 5, 6), (0, 4, 3, 8)), ((2, 5, 9), (0, 1, 6, 8)), ((2, 8, 9), (1, 0, 4, 3)),
   ((3, 5, 6), (0, 1, 2, 7)), ((3, 5, 9), (0, 1, 2, 7)), ((3, 6, 7), (1, 0, 4, 9)),
   ((4, 5, 6), (0, 1, 2, 3)), ((4, 6, 7), (0, 1, 2, 3)), ((4, 7, 8), (0, 1, 2, 3))]

lemma petersen_ind3_cover_and_p4 :
    ∀ u1 u2 u3 : Fin 10, u1 < u2 → u2 < u3 →
      petersenAdj u1 u2 = false → petersenAdj u1 u3 = false → petersenAdj u2 u3 = false →
      ∃ w ∈ petersenInd3Witness,
        w.1 = (u1, u2, u3) ∧
        (let a := w.2.1; let b := w.2.2.1; let c := w.2.2.2.1; let d := w.2.2.2.2;
         a ≠ u1 ∧ a ≠ u2 ∧ a ≠ u3 ∧ b ≠ u1 ∧ b ≠ u2 ∧ b ≠ u3 ∧
         c ≠ u1 ∧ c ≠ u2 ∧ c ≠ u3 ∧ d ≠ u1 ∧ d ≠ u2 ∧ d ≠ u3 ∧
         petersenAdj a b = true ∧ petersenAdj b c = true ∧ petersenAdj c d = true ∧
         petersenAdj a d = false ∧
         (petersenAdj u1 a = true ∨ petersenAdj u2 a = true ∨ petersenAdj u3 a = true ∨
          petersenAdj u1 d = true ∨ petersenAdj u2 d = true ∨ petersenAdj u3 d = true)) := by
  decide

def petersenInd4Witness : List ((Fin 10 × Fin 10 × Fin 10 × Fin 10) ×
    (Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10)) :=
  [((0, 2, 8, 9), (0, 1, 6, 4, 3, 5, 7)),
   ((0, 3, 6, 7), (0, 1, 2, 4, 9, 5, 8)),
   ((1, 3, 5, 9), (1, 0, 4, 2, 7, 6, 8)),
   ((1, 4, 7, 8), (1, 0, 5, 2, 3, 6, 9)),
   ((2, 4, 5, 6), (2, 1, 0, 3, 8, 7, 9))]

lemma petersen_ind4_mem :
    ∀ u1 u2 u3 u4 : Fin 10, u1 < u2 → u2 < u3 → u3 < u4 →
      petersenAdj u1 u2 = false → petersenAdj u1 u3 = false → petersenAdj u1 u4 = false →
      petersenAdj u2 u3 = false → petersenAdj u2 u4 = false → petersenAdj u3 u4 = false →
      ∃ w ∈ petersenInd4Witness, w.1 = (u1, u2, u3, u4) := by
  decide

lemma petersen_ind4_valid :
    ∀ w ∈ petersenInd4Witness,
      let u1 := w.1.1; let u2 := w.1.2.1; let u3 := w.1.2.2.1; let u4 := w.1.2.2.2
      let u0 := w.2.1; let x1 := w.2.2.1; let y1 := w.2.2.2.1
      let x2 := w.2.2.2.2.1; let y2 := w.2.2.2.2.2.1
      let x3 := w.2.2.2.2.2.2.1; let y3 := w.2.2.2.2.2.2.2
      u0 = u1 ∧
      x1 ≠ u1 ∧ x1 ≠ u2 ∧ x1 ≠ u3 ∧ x1 ≠ u4 ∧
      y1 ≠ u1 ∧ y1 ≠ u2 ∧ y1 ≠ u3 ∧ y1 ≠ u4 ∧
      x2 ≠ u1 ∧ x2 ≠ u2 ∧ x2 ≠ u3 ∧ x2 ≠ u4 ∧
      y2 ≠ u1 ∧ y2 ≠ u2 ∧ y2 ≠ u3 ∧ y2 ≠ u4 ∧
      x3 ≠ u1 ∧ x3 ≠ u2 ∧ x3 ≠ u3 ∧ x3 ≠ u4 ∧
      y3 ≠ u1 ∧ y3 ≠ u2 ∧ y3 ≠ u3 ∧ y3 ≠ u4 ∧
      (∀ v : Fin 10, v ≠ u1 → v ≠ u2 → v ≠ u3 → v ≠ u4 →
        petersenAdj u1 v = true ∨ petersenAdj u2 v = true ∨
        petersenAdj u3 v = true ∨ petersenAdj u4 v = true) ∧
      petersenAdj u0 x1 = true ∧ petersenAdj x1 y1 = true ∧
      petersenAdj u0 x2 = true ∧ petersenAdj x2 y2 = true ∧
      petersenAdj u0 x3 = true ∧ petersenAdj x3 y3 = true ∧
      petersenAdj x1 x2 = false ∧ petersenAdj x1 y2 = false ∧
      petersenAdj y1 x2 = false ∧ petersenAdj y1 y2 = false ∧
      petersenAdj u0 y1 = false ∧ petersenAdj u0 y2 = false ∧
      petersenAdj u0 y3 = false ∧ petersenAdj y1 x3 = false ∧ petersenAdj y2 x3 = false := by
  intro w hw
  simp only [petersenInd4Witness, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (repeat' constructor) <;> decide

lemma petersen_ind4_spider
    (u1 u2 u3 u4 : Fin 10) (h12 : u1 < u2) (h23 : u2 < u3) (h34 : u3 < u4)
    (a12 : petersenAdj u1 u2 = false) (a13 : petersenAdj u1 u3 = false)
    (a14 : petersenAdj u1 u4 = false) (a23 : petersenAdj u2 u3 = false)
    (a24 : petersenAdj u2 u4 = false) (a34 : petersenAdj u3 u4 = false) :
    ∃ w ∈ petersenInd4Witness,
      w.1 = (u1, u2, u3, u4) ∧
      (let u0 := w.2.1; let x1 := w.2.2.1; let y1 := w.2.2.2.1;
       let x2 := w.2.2.2.2.1; let y2 := w.2.2.2.2.2.1;
       let x3 := w.2.2.2.2.2.2.1; let y3 := w.2.2.2.2.2.2.2;
       u0 = u1 ∧
       x1 ≠ u1 ∧ x1 ≠ u2 ∧ x1 ≠ u3 ∧ x1 ≠ u4 ∧
       y1 ≠ u1 ∧ y1 ≠ u2 ∧ y1 ≠ u3 ∧ y1 ≠ u4 ∧
       x2 ≠ u1 ∧ x2 ≠ u2 ∧ x2 ≠ u3 ∧ x2 ≠ u4 ∧
       y2 ≠ u1 ∧ y2 ≠ u2 ∧ y2 ≠ u3 ∧ y2 ≠ u4 ∧
       x3 ≠ u1 ∧ x3 ≠ u2 ∧ x3 ≠ u3 ∧ x3 ≠ u4 ∧
       y3 ≠ u1 ∧ y3 ≠ u2 ∧ y3 ≠ u3 ∧ y3 ≠ u4 ∧
       (∀ v : Fin 10, v ≠ u1 → v ≠ u2 → v ≠ u3 → v ≠ u4 →
         petersenAdj u1 v = true ∨ petersenAdj u2 v = true ∨
         petersenAdj u3 v = true ∨ petersenAdj u4 v = true) ∧
       petersenAdj u0 x1 = true ∧ petersenAdj x1 y1 = true ∧
       petersenAdj u0 x2 = true ∧ petersenAdj x2 y2 = true ∧
       petersenAdj u0 x3 = true ∧ petersenAdj x3 y3 = true ∧
       petersenAdj x1 x2 = false ∧ petersenAdj x1 y2 = false ∧
       petersenAdj y1 x2 = false ∧ petersenAdj y1 y2 = false ∧
       petersenAdj u0 y1 = false ∧ petersenAdj u0 y2 = false ∧
       petersenAdj u0 y3 = false ∧ petersenAdj y1 x3 = false ∧ petersenAdj y2 x3 = false) := by
  obtain ⟨w, hw, hw1⟩ := petersen_ind4_mem u1 u2 u3 u4 h12 h23 h34 a12 a13 a14 a23 a24 a34
  have hv := petersen_ind4_valid w hw
  rw [hw1] at hv
  exact ⟨w, hw, hw1, hv⟩

lemma petersen_no_common_3nbrs :
    ∀ u c : Fin 10, u ≠ c →
      ∃ w : Fin 10, petersenAdj u w = true ∧ petersenAdj c w = false := by
  decide

lemma petersen_deg3 :
    ∀ u : Fin 10, ∃ v1 v2 : Fin 10, v1 ≠ v2 ∧ petersenAdj u v1 = true ∧ petersenAdj u v2 = true := by
  decide

lemma petersen_no_ind5 (U : Finset (Fin 10))
    (hind : ∀ u ∈ U, ∀ v ∈ U, petersenAdj u v = false) :
    U.card ≤ 4 := by
  have hT : 6 ≤ Uᶜ.card := by
    apply petersen_tau_ge_6 Uᶜ
    intro e he
    by_contra h
    push Not at h
    simp only [Finset.mem_compl, not_not] at h
    have h1 := hind e.1 h.1 e.2 h.2
    have h2 := petersenEdges_adj e he
    rw [h1] at h2; exact absurd h2 (by decide)
  have hsum : U.card + Uᶜ.card = 10 := by simpa using Finset.card_add_card_compl U
  omega

lemma root_and_ul_empty_contra (l r : MonoFormula 10)
    (hro_l : ∀ v : Fin 10, l.varCount v ≤ 1)
    (hro_r : ∀ v : Fin 10, r.varCount v ≤ 1)
    (hev : ∀ x : Fin 10 → Bool, (l.and r).eval x = petersenFun x) :
    False := by
  let SL := Finset.univ.filter fun v : Fin 10 => l.eval (singleInput v) = true
  let SR := Finset.univ.filter fun v : Fin 10 => r.eval (singleInput v) = true
  have hbic : ∀ u ∈ SL, ∀ v ∈ SR, petersenAdj u v = true := by
    intro u hu v hv
    rw [Finset.mem_filter] at hu hv
    rw [← petersenFun_pair_iff, ← hev]
    simp only [MonoFormula.eval, Bool.and_eq_true]
    exact ⟨l.eval_mono (singleInput u) (pairInput u v) (fun i hi => by
      simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hu.2,
      r.eval_mono (singleInput v) (pairInput u v) (fun i hi => by
      simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hv.2⟩
  have haux : ∀ (G : MonoFormula 10) (SG : Finset (Fin 10)),
      (∀ v, G.varCount v ≤ 1) →
      (∀ v, v ∈ SG ↔ G.eval (singleInput v) = true) →
      (∀ u v, petersenAdj u v = true → G.eval (pairInput u v) = true) →
      SG.card ≤ 1 → False := by
    intro G SG hroG hSG hGe hcard
    let M := SGᶜ
    obtain ⟨col, hcol⟩ := read_once_bipartite M G hroG
      (fun v hv => by
        have hnot : v ∉ SG := Finset.mem_compl.mp hv
        cases hvG : G.eval (singleInput v)
        · rfl
        · exact absurd ((hSG v).mpr hvG) hnot)
      (fun u _ v _ hadj => hGe u v hadj)
    have hex_u : ∃ u : Fin 10, SG ⊆ {u} := by
      by_cases hne : SG.Nonempty
      · have h1 : SG.card = 1 := by have := Finset.card_pos.mpr hne; omega
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        exact ⟨u, by rw [hu]⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        exact ⟨0, by rw [hne]; simp⟩
    obtain ⟨u, hu⟩ := hex_u
    obtain ⟨c, hc, hu1, hu2, hu3, hu4, hu5, _⟩ := petersen_del2_has_c5 u u (petersenAdj_irrefl u)
    have hval := petersenC5s_valid c hc
    have hmem : ∀ w : Fin 10, u ≠ w → w ∈ M := by
      intro w hne; simp only [M, Finset.mem_compl]
      intro hw; have := hu hw; simp at this; exact hne this.symm
    exact c5_not_bipartite c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 col
      (hcol _ (hmem _ hu1) _ (hmem _ hu2) hval.1)
      (hcol _ (hmem _ hu2) _ (hmem _ hu3) hval.2.1)
      (hcol _ (hmem _ hu3) _ (hmem _ hu4) hval.2.2.1)
      (hcol _ (hmem _ hu4) _ (hmem _ hu5) hval.2.2.2.1)
      (hcol _ (hmem _ hu5) _ (hmem _ hu1) hval.2.2.2.2)
  rcases petersen_biclique_star SL SR hbic with hL1 | hR1
  · exact haux l SL hro_l (fun v => by simp [SL])
      (fun u v hadj => by
        have h := hev (pairInput u v)
        rw [(petersenFun_pair_iff u v).mpr hadj] at h
        simp [MonoFormula.eval] at h; exact h.1) hL1
  · exact haux r SR hro_r (fun v => by simp [SR])
      (fun u v hadj => by
        have h := hev (pairInput u v)
        rw [(petersenFun_pair_iff u v).mpr hadj] at h
        simp [MonoFormula.eval] at h; exact h.2) hR1

lemma root_and_ul_nonempty_contra (l r : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, (l.and r).varCount v = 2)
    (hev : ∀ x : Fin 10 → Bool, (l.and r).eval x = petersenFun x)
    (UL : Finset (Fin 10))
    (hUL_def : UL = Finset.univ.filter fun v : Fin 10 => r.varCount v = 0)
    (hUL_ne : UL.Nonempty) :
    False := by
  have hUL_indep : ∀ u ∈ UL, ∀ v ∈ UL, petersenAdj u v = false := by
    intro u hu v hv
    rw [hUL_def, Finset.mem_filter] at hu hv
    have hun : u ∉ r.orVars := by rw [MonoFormula.mem_orVars_iff_varCount_pos]; omega
    have hvn : v ∉ r.orVars := by rw [MonoFormula.mem_orVars_iff_varCount_pos]; omega
    have hr0 : r.eval (pairInput u v) = false := eval_pair_of_not_mem_both r u v hun hvn
    have hf0 : petersenFun (pairInput u v) = false := by
      rw [← hev]; simp [MonoFormula.eval, hr0]
    cases hadj : petersenAdj u v
    · rfl
    · rw [(petersenFun_pair_iff u v).mpr hadj] at hf0; exact absurd hf0 (by decide)
  have hnbr_SR : ∀ u ∈ UL, ∀ w : Fin 10, petersenAdj u w = true → r.eval (singleInput w) = true := by
    intro u hu w hadj
    rw [hUL_def, Finset.mem_filter] at hu
    have hun : u ∉ r.orVars := by rw [MonoFormula.mem_orVars_iff_varCount_pos]; omega
    have h1 := hev (pairInput u w)
    rw [(petersenFun_pair_iff u w).mpr hadj] at h1
    simp only [MonoFormula.eval, Bool.and_eq_true] at h1
    have h2 := eval_pair_of_not_mem r u w hun
    change r.eval (pairInput u w) = r.eval (singleInput w) at h2
    rw [← h2]; exact h1.2
  have hSL_not_M : ∀ c : Fin 10, c ∉ UL → l.eval (singleInput c) = false := by
    intro c hc
    cases hlc : l.eval (singleInput c)
    · rfl
    · exfalso
      obtain ⟨u, hu⟩ := hUL_ne
      have hne : u ≠ c := fun heq => hc (heq ▸ hu)
      obtain ⟨w, huw, hcw⟩ := petersen_no_common_3nbrs u c hne
      have hrw := hnbr_SR u hu w huw
      have h1 : (l.and r).eval (pairInput c w) = true := by
        simp only [MonoFormula.eval, Bool.and_eq_true]
        exact ⟨l.eval_mono (singleInput c) (pairInput c w) (fun i hi => by
          simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hlc,
          r.eval_mono (singleInput w) (pairInput c w) (fun i hi => by
          simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hrw⟩
      rw [hev, petersenFun_pair_iff] at h1
      rw [hcw] at h1; exact absurd h1 (by decide)
  let M := ULᶜ
  have hro_M : ∀ v ∈ M, l.varCount v ≤ 1 := by
    intro v hv
    have hnot : v ∉ UL := Finset.mem_compl.mp hv
    rw [hUL_def, Finset.mem_filter] at hnot
    have hrpos : 1 ≤ r.varCount v := by
      have : r.varCount v ≠ 0 := fun h => hnot ⟨Finset.mem_univ v, h⟩
      omega
    have h2 := hr2 v; simp [MonoFormula.varCount] at h2; omega
  have hcard_le4 : UL.card ≤ 4 := petersen_no_ind5 UL hUL_indep
  by_cases hle2 : UL.card ≤ 2
  · obtain ⟨u, hu⟩ := hUL_ne
    have hex_uv : ∃ v : Fin 10, petersenAdj u v = false ∧ UL ⊆ {u, v} := by
      by_cases h1 : UL.card = 1
      · obtain ⟨u', hu'⟩ := Finset.card_eq_one.mp h1
        have huu : u = u' := by rw [hu', Finset.mem_singleton] at hu; exact hu
        subst huu
        exact ⟨u, petersenAdj_irrefl u, by rw [hu']; simp⟩
      · have hpos : 0 < UL.card := Finset.card_pos.mpr ⟨u, hu⟩
        have h2 : UL.card = 2 := by omega
        obtain ⟨a, b, hab, hULab⟩ := Finset.card_eq_two.mp h2
        have hua : u = a ∨ u = b := by rw [hULab] at hu; simpa using hu
        rcases hua with rfl | rfl
        · exact ⟨b, hUL_indep u (by rw [hULab]; simp) b (by rw [hULab]; simp), by rw [hULab]⟩
        · exact ⟨a, hUL_indep u (by rw [hULab]; simp) a (by rw [hULab]; simp), by rw [hULab]; intro x hx; simp at hx ⊢; tauto⟩
    obtain ⟨v, huv, hUL_sub⟩ := hex_uv
    cases hlM : l.restrictFalse M with
    | none =>
      obtain ⟨c, hc, hu1, hu2, _, _, _, hv1, hv2, _, _, _⟩ := petersen_del2_has_c5 u v huv
      have hval := petersenC5s_valid c hc
      have hc1M : c.1 ∈ M := by simp only [M, Finset.mem_compl]; intro h; have := hUL_sub h; simp at this; rcases this with rfl | rfl <;> contradiction
      have hc2M : c.2.1 ∈ M := by simp only [M, Finset.mem_compl]; intro h; have := hUL_sub h; simp at this; rcases this with rfl | rfl <;> contradiction
      have h0 := l.restrictFalse_eval M (pairInput c.1 c.2.1)
      rw [hlM] at h0; simp only [Option.elim_none] at h0
      have hfeq : (fun i => if i ∈ M then pairInput c.1 c.2.1 i else false) = pairInput c.1 c.2.1 := by
        funext i; unfold pairInput; split_ifs with hi
        · rfl
        · simp only [Bool.false_eq, decide_eq_false_iff_not, not_or]
          exact ⟨fun h => hi (h ▸ hc1M), fun h => hi (h ▸ hc2M)⟩
      rw [hfeq] at h0
      have ht := hev (pairInput c.1 c.2.1)
      rw [(petersenFun_pair_iff c.1 c.2.1).mpr hval.1] at ht
      simp [MonoFormula.eval, ← h0] at ht
    | some G =>
      have hGro : ∀ w : Fin 10, G.varCount w ≤ 1 := by
        intro w
        by_cases hwM : w ∈ M
        · exact le_trans (l.restrictFalse_varCount_le M G hlM w) (hro_M w hwM)
        · have hnot : w ∉ G.orVars := fun h => hwM (l.restrictFalse_orVars M G hlM h)
          rw [MonoFormula.mem_orVars_iff_varCount_pos] at hnot; omega
      have hGeval_M : ∀ x : Fin 10 → Bool, (∀ i, x i = true → i ∈ M) → G.eval x = l.eval x := by
        intro x hx
        have h0 := l.restrictFalse_eval M x
        rw [hlM] at h0; simp only [Option.elim_some] at h0
        rw [h0]
        congr 1; funext i; split_ifs with hi
        · rfl
        · cases hxi : x i
          · rfl
          · exact absurd (hx i hxi) hi
      obtain ⟨col, hcol⟩ := read_once_bipartite M G hGro
        (fun w hw => by
          rw [hGeval_M (singleInput w) (fun i hi => by
            simp only [singleInput, decide_eq_true_eq] at hi; exact hi ▸ hw)]
          exact hSL_not_M w (Finset.mem_compl.mp hw))
        (fun a ha b hb hadj => by
          rw [hGeval_M (pairInput a b) (fun i hi => by
            simp only [pairInput, decide_eq_true_eq] at hi; rcases hi with rfl | rfl <;> assumption)]
          have ht := hev (pairInput a b)
          rw [(petersenFun_pair_iff a b).mpr hadj] at ht
          simp [MonoFormula.eval] at ht; exact ht.1)
      obtain ⟨c, hc, hu1, hu2, hu3, hu4, hu5, hv1, hv2, hv3, hv4, hv5⟩ := petersen_del2_has_c5 u v huv
      have hval := petersenC5s_valid c hc
      have hmem : ∀ w : Fin 10, u ≠ w → v ≠ w → w ∈ M := by
        intro w hnu hnv; simp only [M, Finset.mem_compl]
        intro hw; have := hUL_sub hw; simp at this; rcases this with rfl | rfl <;> contradiction
      exact c5_not_bipartite c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 col
        (hcol _ (hmem _ hu1 hv1) _ (hmem _ hu2 hv2) hval.1)
        (hcol _ (hmem _ hu2 hv2) _ (hmem _ hu3 hv3) hval.2.1)
        (hcol _ (hmem _ hu3 hv3) _ (hmem _ hu4 hv4) hval.2.2.1)
        (hcol _ (hmem _ hu4 hv4) _ (hmem _ hu5 hv5) hval.2.2.2.1)
        (hcol _ (hmem _ hu5 hv5) _ (hmem _ hu1 hv1) hval.2.2.2.2)
  · by_cases h3 : UL.card = 3
    · have hsort : ∃ u1 u2 u3 : Fin 10, u1 < u2 ∧ u2 < u3 ∧ UL = {u1, u2, u3} := by
        have hlen : (UL.sort (· ≤ ·)).length = 3 := by rw [Finset.length_sort, h3]
        match hs : UL.sort (· ≤ ·), hlen with
        | [u1, u2, u3], _ =>
          have hp := UL.pairwise_sort (· ≤ ·)
          have hnd' := UL.sort_nodup (· ≤ ·)
          rw [hs] at hp hnd'
          simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, List.nodup_cons, not_or] at hp hnd'
          refine ⟨u1, u2, u3,
            lt_of_le_of_ne hp.1.1 hnd'.1.1,
            lt_of_le_of_ne hp.2.1 hnd'.2.1, ?_⟩
          ext x
          rw [← Finset.mem_sort (· ≤ ·), hs]
          simp
      obtain ⟨u1, u2, u3, h12, h23, hUL_eq⟩ := hsort
      have hu1 : u1 ∈ UL := by rw [hUL_eq]; simp
      have hu2 : u2 ∈ UL := by rw [hUL_eq]; simp
      have hu3 : u3 ∈ UL := by rw [hUL_eq]; simp
      obtain ⟨w, _, hw1, ha1, ha2, ha3, hb1, hb2, hb3, hc1, hc2, hc3, hd1, hd2, hd3,
        hab, hbc, hcd, had, hSR⟩ :=
        petersen_ind3_cover_and_p4 u1 u2 u3 h12 h23
          (hUL_indep u1 hu1 u2 hu2) (hUL_indep u1 hu1 u3 hu3) (hUL_indep u2 hu2 u3 hu3)
      let a := w.2.1; let b := w.2.2.1; let c := w.2.2.2.1; let d := w.2.2.2.2
      have haM : a ∈ M := by dsimp only [a]; simp [M, hUL_eq, ha1, ha2, ha3]
      have hbM : b ∈ M := by dsimp only [b]; simp [M, hUL_eq, hb1, hb2, hb3]
      have hcM : c ∈ M := by dsimp only [c]; simp [M, hUL_eq, hc1, hc2, hc3]
      have hdM : d ∈ M := by dsimp only [d]; simp [M, hUL_eq, hd1, hd2, hd3]
      have hrad : r.eval (pairInput a d) = true := by
        rcases hSR with h | h | h | h | h | h
        · exact r.eval_mono (singleInput a) (pairInput a d) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (hnbr_SR u1 hu1 a h)
        · exact r.eval_mono (singleInput a) (pairInput a d) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (hnbr_SR u2 hu2 a h)
        · exact r.eval_mono (singleInput a) (pairInput a d) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (hnbr_SR u3 hu3 a h)
        · exact r.eval_mono (singleInput d) (pairInput a d) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (hnbr_SR u1 hu1 d h)
        · exact r.eval_mono (singleInput d) (pairInput a d) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (hnbr_SR u2 hu2 d h)
        · exact r.eval_mono (singleInput d) (pairInput a d) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (hnbr_SR u3 hu3 d h)
      have hlad : l.eval (pairInput a d) = false := by
        have h := hev (pairInput a d)
        have hf : petersenFun (pairInput a d) = false := by
          cases hp : petersenFun (pairInput a d)
          · rfl
          · rw [petersenFun_pair_iff] at hp; rw [had] at hp; exact absurd hp (by decide)
        rw [hf] at h; simp [MonoFormula.eval, hrad] at h; exact h
      cases hlM : l.restrictFalse M with
      | none =>
        have h0 := l.restrictFalse_eval M (pairInput a b)
        rw [hlM] at h0; simp only [Option.elim_none] at h0
        have hfeq : (fun i => if i ∈ M then pairInput a b i else false) = pairInput a b := by
          funext i; unfold pairInput; split_ifs with hi
          · rfl
          · simp only [Bool.false_eq, decide_eq_false_iff_not, not_or]
            exact ⟨fun h => hi (h ▸ haM), fun h => hi (h ▸ hbM)⟩
        rw [hfeq] at h0
        have ht := hev (pairInput a b)
        rw [(petersenFun_pair_iff a b).mpr hab] at ht; simp [MonoFormula.eval, ← h0] at ht
      | some G =>
        have hGro : ∀ v : Fin 10, G.varCount v ≤ 1 := by
          intro v
          by_cases hvM : v ∈ M
          · exact le_trans (l.restrictFalse_varCount_le M G hlM v) (hro_M v hvM)
          · have hnot : v ∉ G.orVars := fun h => hvM (l.restrictFalse_orVars M G hlM h)
            rw [MonoFormula.mem_orVars_iff_varCount_pos] at hnot; omega
        have hGeval_M : ∀ x : Fin 10 → Bool, (∀ i, x i = true → i ∈ M) → G.eval x = l.eval x := by
          intro x hx
          have h0 := l.restrictFalse_eval M x
          rw [hlM] at h0; simp only [Option.elim_some] at h0; rw [h0]
          congr 1; funext i; split_ifs with hi
          · rfl
          · cases hxi : x i
            · rfl
            · exact absurd (hx i hxi) hi
        have hGpair : ∀ x y, x ∈ M → y ∈ M → G.eval (pairInput x y) = l.eval (pairInput x y) :=
          fun x y hx hy => hGeval_M (pairInput x y) (fun i hi => by
            simp only [pairInput, decide_eq_true_eq] at hi; rcases hi with rfl | rfl <;> assumption)
        have hGsing : ∀ x, x ∈ M → G.eval (singleInput x) = false := fun x hx => by
          rw [hGeval_M (singleInput x) (fun i hi => by
            simp only [singleInput, decide_eq_true_eq] at hi; exact hi ▸ hx)]
          exact hSL_not_M x (Finset.mem_compl.mp hx)
        have hle_p : ∀ x y, petersenAdj x y = true → l.eval (pairInput x y) = true := by
          intro x y hxy
          have ht := hev (pairInput x y); rw [(petersenFun_pair_iff x y).mpr hxy] at ht
          simp [MonoFormula.eval] at ht; exact ht.1
        exact read_once_no_p4 a b c d G hGro
          (hGsing a haM) (hGsing b hbM) (hGsing c hcM) (hGsing d hdM)
          (by rw [hGpair a b haM hbM]; exact hle_p a b hab)
          (by rw [hGpair b c hbM hcM]; exact hle_p b c hbc)
          (by rw [hGpair c d hcM hdM]; exact hle_p c d hcd)
          (by rw [hGpair a d haM hdM]; exact hlad)
    · have h4 : UL.card = 4 := by omega
      have hsort : ∃ u1 u2 u3 u4 : Fin 10, u1 < u2 ∧ u2 < u3 ∧ u3 < u4 ∧ UL = {u1, u2, u3, u4} := by
        have hlen : (UL.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, h4]
        match hs : UL.sort (· ≤ ·), hlen with
        | [u1, u2, u3, u4], _ =>
          have hp := UL.pairwise_sort (· ≤ ·)
          have hnd' := UL.sort_nodup (· ≤ ·)
          rw [hs] at hp hnd'
          simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, List.nodup_cons, not_or] at hp hnd'
          refine ⟨u1, u2, u3, u4,
            lt_of_le_of_ne hp.1.1 hnd'.1.1,
            lt_of_le_of_ne hp.2.1.1 hnd'.2.1.1,
            lt_of_le_of_ne hp.2.2.1 hnd'.2.2.1, ?_⟩
          ext x
          rw [← Finset.mem_sort (· ≤ ·), hs]
          simp
      obtain ⟨u1, u2, u3, u4, h12, h23, h34, hUL_eq⟩ := hsort
      have hu1 : u1 ∈ UL := by rw [hUL_eq]; simp
      have hu2 : u2 ∈ UL := by rw [hUL_eq]; simp
      have hu3 : u3 ∈ UL := by rw [hUL_eq]; simp
      have hu4 : u4 ∈ UL := by rw [hUL_eq]; simp
      obtain ⟨w, _, _, hu0_eq, hx1_1, hx1_2, hx1_3, hx1_4, hy1_1, hy1_2, hy1_3, hy1_4,
        hx2_1, hx2_2, hx2_3, hx2_4, hy2_1, hy2_2, hy2_3, hy2_4,
        hx3_1, hx3_2, hx3_3, hx3_4, hy3_1, hy3_2, hy3_3, hy3_4,
        hSR_all, he1, hf1, he2, hf2, he3, hf3,
        hne_x1x2, hne_x1y2, hne_y1x2, hne_y1y2, hne_u0y1, hne_u0y2, hne_u0y3, hne_y1x3, hne_y2x3⟩ :=
        petersen_ind4_spider u1 u2 u3 u4 h12 h23 h34
          (hUL_indep u1 hu1 u2 hu2) (hUL_indep u1 hu1 u3 hu3) (hUL_indep u1 hu1 u4 hu4)
          (hUL_indep u2 hu2 u3 hu3) (hUL_indep u2 hu2 u4 hu4) (hUL_indep u3 hu3 u4 hu4)
      let u0 := w.2.1; let x1 := w.2.2.1; let y1 := w.2.2.2.1
      let x2 := w.2.2.2.2.1; let y2 := w.2.2.2.2.2.1
      let x3 := w.2.2.2.2.2.2.1; let y3 := w.2.2.2.2.2.2.2
      have hSR_M : ∀ v ∈ M, r.eval (singleInput v) = true := by
        intro v hv
        have hnot : v ∉ UL := Finset.mem_compl.mp hv
        rw [hUL_eq] at hnot; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        rcases hSR_all v hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2 with h | h | h | h
        · exact hnbr_SR u1 hu1 v h
        · exact hnbr_SR u2 hu2 v h
        · exact hnbr_SR u3 hu3 v h
        · exact hnbr_SR u4 hu4 v h
      let S := insert u0 M
      have hu0_ne_y1 : u0 ≠ y1 := by dsimp only [u0, y1]; rw [hu0_eq]; exact Ne.symm hy1_1
      have hy1M : y1 ∈ M := by dsimp only [y1]; simp [M, hUL_eq, hy1_1, hy1_2, hy1_3, hy1_4]
      have hx1M : x1 ∈ M := by dsimp only [x1]; simp [M, hUL_eq, hx1_1, hx1_2, hx1_3, hx1_4]
      have hx2M : x2 ∈ M := by dsimp only [x2]; simp [M, hUL_eq, hx2_1, hx2_2, hx2_3, hx2_4]
      have hy2M : y2 ∈ M := by dsimp only [y2]; simp [M, hUL_eq, hy2_1, hy2_2, hy2_3, hy2_4]
      have hx3M : x3 ∈ M := by dsimp only [x3]; simp [M, hUL_eq, hx3_1, hx3_2, hx3_3, hx3_4]
      have hy3M : y3 ∈ M := by dsimp only [y3]; simp [M, hUL_eq, hy3_1, hy3_2, hy3_3, hy3_4]
      have hl_nonedge : ∀ a b : Fin 10, (a ∈ M ∨ b ∈ M) → petersenAdj a b = false → l.eval (pairInput a b) = false := by
        intro a b habM hadj
        have hr1 : r.eval (pairInput a b) = true := by
          rcases habM with ha | hb
          · exact r.eval_mono (singleInput a) (pairInput a b) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (hSR_M a ha)
          · exact r.eval_mono (singleInput b) (pairInput a b) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (hSR_M b hb)
        have hf : petersenFun (pairInput a b) = false := by
          cases hp : petersenFun (pairInput a b)
          · rfl
          · rw [petersenFun_pair_iff] at hp; rw [hadj] at hp; exact absurd hp (by decide)
        have h := hev (pairInput a b); rw [hf] at h; simp [MonoFormula.eval, hr1] at h; exact h
      have hlu0 : l.eval (singleInput u0) = false := by
        have h := hl_nonedge u0 y1 (Or.inr hy1M) hne_u0y1
        cases hu0l : l.eval (singleInput u0)
        · rfl
        · have ht := l.eval_mono (singleInput u0) (pairInput u0 y1) (fun i hi => by
            simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hu0l
          rw [h] at ht; exact absurd ht (by decide)
      cases hlS : l.restrictFalse S with
      | none =>
        have h0 := l.restrictFalse_eval S (pairInput x1 y1)
        rw [hlS] at h0; simp only [Option.elim_none] at h0
        have hfeq : (fun i => if i ∈ S then pairInput x1 y1 i else false) = pairInput x1 y1 := by
          funext i; unfold pairInput; split_ifs with hi
          · rfl
          · simp only [Bool.false_eq, decide_eq_false_iff_not, not_or]
            exact ⟨fun h => hi (h ▸ Finset.mem_insert_of_mem hx1M), fun h => hi (h ▸ Finset.mem_insert_of_mem hy1M)⟩
        rw [hfeq] at h0
        have ht := hev (pairInput x1 y1); rw [(petersenFun_pair_iff x1 y1).mpr hf1] at ht
        simp [MonoFormula.eval, ← h0] at ht
      | some G =>
        have hGcnt0 : G.varCount u0 ≤ 2 := by
          have h1 := l.restrictFalse_varCount_le S G hlS u0
          have h2 := hr2 u0; simp [MonoFormula.varCount] at h2; omega
        have hGcnt_other : ∀ v : Fin 10, v ≠ u0 → G.varCount v ≤ 1 := by
          intro v hvu
          by_cases hvM : v ∈ M
          · exact le_trans (l.restrictFalse_varCount_le S G hlS v) (hro_M v hvM)
          · have hvS : v ∉ S := by simp [S, hvu, hvM]
            have hnot : v ∉ G.orVars := fun h => hvS (l.restrictFalse_orVars S G hlS h)
            rw [MonoFormula.mem_orVars_iff_varCount_pos] at hnot; omega
        have hGeval_S : ∀ x : Fin 10 → Bool, (∀ i, x i = true → i ∈ S) → G.eval x = l.eval x := by
          intro x hx
          have h0 := l.restrictFalse_eval S x
          rw [hlS] at h0; simp only [Option.elim_some] at h0; rw [h0]
          congr 1; funext i; split_ifs with hi
          · rfl
          · cases hxi : x i
            · rfl
            · exact absurd (hx i hxi) hi
        have hGpair : ∀ a b, a ∈ S → b ∈ S → G.eval (pairInput a b) = l.eval (pairInput a b) :=
          fun a b ha hb => hGeval_S (pairInput a b) (fun i hi => by
            simp only [pairInput, decide_eq_true_eq] at hi; rcases hi with rfl | rfl <;> assumption)
        have hu0S : u0 ∈ S := Finset.mem_insert_self u0 M
        have hx1S : x1 ∈ S := Finset.mem_insert_of_mem hx1M
        have hy1S : y1 ∈ S := Finset.mem_insert_of_mem hy1M
        have hx2S : x2 ∈ S := Finset.mem_insert_of_mem hx2M
        have hy2S : y2 ∈ S := Finset.mem_insert_of_mem hy2M
        have hx3S : x3 ∈ S := Finset.mem_insert_of_mem hx3M
        have hy3S : y3 ∈ S := Finset.mem_insert_of_mem hy3M
        have hle_p : ∀ a b, petersenAdj a b = true → l.eval (pairInput a b) = true := by
          intro a b hab
          have ht := hev (pairInput a b); rw [(petersenFun_pair_iff a b).mpr hab] at ht
          simp [MonoFormula.eval] at ht; exact ht.1
        exact spider_no_1_read2 u0 x1 y1 x2 y2 x3 y3 G hGcnt0 hGcnt_other
          (fun v hv => by
            have hvS : v ∈ S := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
            rw [hGeval_S (singleInput v) (fun i hi => by
              simp only [singleInput, decide_eq_true_eq] at hi; exact hi ▸ hvS)]
            by_cases hvu : v = u0
            · rw [hvu]; exact hlu0
            · have hvM : v ∈ M := by simp [S, hvu] at hvS; exact hvS
              exact hSL_not_M v (Finset.mem_compl.mp hvM))
          (by rw [hGpair u0 x1 hu0S hx1S]; exact hle_p u0 x1 he1)
          (by rw [hGpair x1 y1 hx1S hy1S]; exact hle_p x1 y1 hf1)
          (by rw [hGpair u0 x2 hu0S hx2S]; exact hle_p u0 x2 he2)
          (by rw [hGpair x2 y2 hx2S hy2S]; exact hle_p x2 y2 hf2)
          (by rw [hGpair u0 x3 hu0S hx3S]; exact hle_p u0 x3 he3)
          (by rw [hGpair x3 y3 hx3S hy3S]; exact hle_p x3 y3 hf3)
          (by rw [hGpair x1 x2 hx1S hx2S]; exact hl_nonedge x1 x2 (Or.inl hx1M) hne_x1x2)
          (by rw [hGpair x1 y2 hx1S hy2S]; exact hl_nonedge x1 y2 (Or.inl hx1M) hne_x1y2)
          (by rw [hGpair y1 x2 hy1S hx2S]; exact hl_nonedge y1 x2 (Or.inl hy1M) hne_y1x2)
          (by rw [hGpair y1 y2 hy1S hy2S]; exact hl_nonedge y1 y2 (Or.inl hy1M) hne_y1y2)
          (by rw [hGpair u0 y1 hu0S hy1S]; exact hl_nonedge u0 y1 (Or.inr hy1M) hne_u0y1)
          (by rw [hGpair u0 y2 hu0S hy2S]; exact hl_nonedge u0 y2 (Or.inr hy2M) hne_u0y2)
          (by rw [hGpair u0 y3 hu0S hy3S]; exact hl_nonedge u0 y3 (Or.inr hy3M) hne_u0y3)
          (by rw [hGpair y1 x3 hy1S hx3S]; exact hl_nonedge y1 x3 (Or.inl hy1M) hne_y1x3)
          (by rw [hGpair y2 x3 hy2S hx3S]; exact hl_nonedge y2 x3 (Or.inl hy2M) hne_y2x3)
          ⟨by dsimp only [u0, x1]; rw [hu0_eq]; exact hx1_1,
           by dsimp only [u0, y1]; rw [hu0_eq]; exact hy1_1,
           by dsimp only [u0, x2]; rw [hu0_eq]; exact hx2_1,
           by dsimp only [u0, y2]; rw [hu0_eq]; exact hy2_1,
           by dsimp only [u0, x3]; rw [hu0_eq]; exact hx3_1,
           by dsimp only [u0, y3]; rw [hu0_eq]; exact hy3_1⟩

theorem petersen_read2_not_root_and (l r : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, (l.and r).varCount v = 2)
    (hev : ∀ x : Fin 10 → Bool, (l.and r).eval x = petersenFun x) :
    False := by
  let UL := Finset.univ.filter fun v : Fin 10 => r.varCount v = 0
  let UR := Finset.univ.filter fun v : Fin 10 => l.varCount v = 0
  by_cases hUL : UL.Nonempty
  · exact root_and_ul_nonempty_contra l r hr2 hev UL rfl hUL
  · by_cases hUR : UR.Nonempty
    · have hr2' : ∀ v : Fin 10, (r.and l).varCount v = 2 := by
        intro v; have := hr2 v; simp [MonoFormula.varCount] at this ⊢; omega
      have hev' : ∀ x : Fin 10 → Bool, (r.and l).eval x = petersenFun x := by
        intro x; rw [← hev x]; simp [MonoFormula.eval, Bool.and_comm]
      exact root_and_ul_nonempty_contra r l hr2' hev' UR rfl hUR
    · rw [Finset.not_nonempty_iff_eq_empty] at hUL hUR
      have hro_l : ∀ v : Fin 10, l.varCount v ≤ 1 := by
        intro v
        have hnot : v ∉ UL := by rw [hUL]; simp
        simp only [UL, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        have h2 := hr2 v; simp [MonoFormula.varCount] at h2; omega
      have hro_r : ∀ v : Fin 10, r.varCount v ≤ 1 := by
        intro v
        have hnot : v ∉ UR := by rw [hUR]; simp
        simp only [UR, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        have h2 := hr2 v; simp [MonoFormula.varCount] at h2; omega
      exact root_and_ul_empty_contra l r hro_l hro_r hev

theorem petersen_19_dichotomy_v3 (h : HasCircuitSize 10 petersenFun 19) :
    (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧
      wireFanOut 10 C 0 = 1) ∨
    (∃ l r : MonoFormula 10,
      (∀ x : Fin 10 → Bool, (l.or r).eval x = petersenFun x) ∧
      (l.or r).leaves = 20 ∧
      (∀ v : Fin 10, (l.or r).varCount v = 2) ∧
      2 ≤ (l.or r).andDepth) := by
  obtain ⟨C, hF, hle, hev, _, _, hcases⟩ := petersen_19_dichotomy h
  rcases hcases with hf1 | ⟨hsz19, hnot0, hgate1, hin2⟩
  · exact Or.inl ⟨C, hF, hle, hev, hf1⟩
  · right
    obtain ⟨hout_ge, hout_lt⟩ := minimal_output_is_gate 10 petersenFun C hev
      petersenFun_not_false petersenFun_not_proj
    obtain ⟨hout0, hstruct⟩ := world2_gate_structure C hF hsz19 hnot0 hout_ge hout_lt hgate1 hin2
    let F := wireToFormula C C.output
    have hFeval : ∀ x : Fin 10 → Bool, F.eval x = petersenFun x := by
      intro x; dsimp [F]; rw [wireToFormula_eval C hstruct x C.output hout_lt]; exact hev x
    have hFleaves : F.leaves = 20 :=
      wireToFormula_leaves_telescoping C hsz19 hout_ge hout_lt hout0 hgate1 hin2 hstruct
    have hFcnt : ∀ v : Fin 10, F.varCount v = 2 :=
      wireToFormula_varCount_telescoping C hsz19 hout_ge hout_lt hout0 hgate1 hin2 hstruct
    have hFdepth : 2 ≤ F.andDepth := by
      by_contra hlt
      have hd1 : F.andDepth ≤ 1 := by omega
      have h21 := petersen_sigma3_leaves_ge_21 F hd1 hFeval
      omega
    cases hF : F with
    | var i =>
      rw [hF] at hFleaves; simp [MonoFormula.leaves] at hFleaves
    | and l r =>
      rw [hF] at hFcnt hFeval
      exact absurd (petersen_read2_not_root_and l r hFcnt hFeval) id
    | or l r =>
      rw [hF] at hFeval hFleaves hFcnt hFdepth
      exact ⟨l, r, hFeval, hFleaves, hFcnt, hFdepth⟩

def singleSet (L : MonoFormula 10) : Finset (Fin 10) :=
  Finset.univ.filter fun v : Fin 10 => L.eval (singleInput v) = true

def edgesM0 (M0 : Finset (Fin 10)) (L : MonoFormula 10) : Finset (Fin 10 × Fin 10) :=
  petersenEdges.filter fun e =>
    (e.1 ∈ M0 ∨ e.2 ∈ M0) ∧
    L.eval (pairInput e.1 e.2) = true ∧
    e.1 ∉ singleSet L ∧
    e.2 ∉ singleSet L

def bipEdges (A B : Finset (Fin 10)) : Finset (Fin 10 × Fin 10) :=
  petersenEdges.filter fun e => (e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.1 ∈ B ∧ e.2 ∈ A)

lemma singleSet_subset_orVars (L : MonoFormula 10) : singleSet L ⊆ L.orVars := by
  intro v hv
  simp only [singleSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  by_contra hnot
  have h0 : L.eval (singleInput v) = L.eval (fun _ => false) := by
    apply L.eval_congr_orVars
    intro i hi
    have hne : i ≠ v := fun heq => hnot (heq ▸ hi)
    simp [singleInput, hne]
  rw [h0, L.eval_false] at hv
  exact absurd hv (by decide)

lemma petersen_deg_le_3 : ∀ u : Fin 10, (Finset.univ.filter fun v : Fin 10 => petersenAdj u v = true).card ≤ 3 := by
  decide

lemma petersenAdj_symm : ∀ u v : Fin 10, petersenAdj u v = true → petersenAdj v u = true := by
  decide

lemma bipEdges_comm (A B : Finset (Fin 10)) : bipEdges A B = bipEdges B A := by
  ext e; simp [bipEdges, or_comm]

lemma bipEdges_le_three_left (A B : Finset (Fin 10)) (hdisj : Disjoint A B) :
    (bipEdges A B).card ≤ 3 * A.card := by
  have hsub : bipEdges A B ⊆ A.biUnion fun a =>
      (Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).image
        (fun b => if a < b then (a, b) else (b, a)) := by
    intro e he
    simp only [bipEdges, Finset.mem_filter] at he
    have hlt := petersenEdges_lt e he.1
    have hadj := petersenEdges_adj e he.1
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he.2 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨e.1, h1, e.2, hadj, by simp [hlt]⟩
    · have hadj' : petersenAdj e.2 e.1 = true := by
        revert hadj; generalize e.1 = x; generalize e.2 = y
        revert x y; decide
      have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact ⟨e.2, h2, e.1, hadj', by simp [hnot]⟩
  calc (bipEdges A B).card
      ≤ (A.biUnion fun a =>
          (Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).image
            (fun b => if a < b then (a, b) else (b, a))).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A, ((Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).image
          (fun b => if a < b then (a, b) else (b, a))).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).card :=
        Finset.sum_le_sum fun a _ => Finset.card_image_le
    _ ≤ ∑ _a ∈ A, 3 := Finset.sum_le_sum fun a _ => petersen_deg_le_3 a
    _ = 3 * A.card := by simp [mul_comm]

lemma bipEdges_le_add_two (A B : Finset (Fin 10)) (hdisj : Disjoint A B) :
    (bipEdges A B).card ≤ A.card + 2 * B.card := by
  have h1 := bipEdges_le_three_left A B hdisj
  have h2 := bipEdges_le_three_left B A hdisj.symm
  rw [bipEdges_comm] at h2
  omega

lemma bipEdges_le_add_two_of_ext (x x2 : Fin 10) (Y B : Finset (Fin 10))
    (hxY : x ∉ Y) (hx2B : x2 ∉ B) (hadj_xx2 : petersenAdj x x2 = true)
    (hdisj : Disjoint (insert x Y) B) :
    (bipEdges (insert x Y) B).card ≤ Y.card + 2 * B.card := by
  have h2 : (bipEdges (insert x Y) B).card ≤ 3 * B.card := by
    rw [bipEdges_comm]; exact bipEdges_le_three_left B (insert x Y) hdisj.symm
  have hsub : bipEdges (insert x Y) B ⊆ bipEdges {x} B ∪ bipEdges Y B := by
    intro e he
    simp only [bipEdges, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
      Finset.mem_singleton] at he ⊢
    rcases he.2 with ⟨h1 | h1, h2⟩ | ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨he.1, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr ⟨he.1, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inl ⟨he.1, Or.inr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨he.1, Or.inr ⟨h1, h2⟩⟩
  have hY_disj : Disjoint Y B := Disjoint.mono_left (Finset.subset_insert x Y) hdisj
  have hY_le : (bipEdges Y B).card ≤ 3 * Y.card := bipEdges_le_three_left Y B hY_disj
  have hx_le2 : (bipEdges {x} B).card ≤ 2 := by
    let N := Finset.univ.filter fun b : Fin 10 => petersenAdj x b = true
    have hx2N : x2 ∈ N := by simp [N, hadj_xx2]
    have hsubx : bipEdges {x} B ⊆ (N.erase x2).image (fun b => if x < b then (x, b) else (b, x)) := by
      intro e he
      simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
      have hlt := petersenEdges_lt e he.1
      have hadj := petersenEdges_adj e he.1
      simp only [Finset.mem_image, Finset.mem_erase, N, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases he.2 with ⟨rfl, hb⟩ | ⟨hb, rfl⟩
      · exact ⟨e.2, ⟨fun h => hx2B (h ▸ hb), hadj⟩, by simp [hlt]⟩
      · have hadj' : petersenAdj e.2 e.1 = true := by
          revert hadj; generalize e.1 = u; generalize e.2 = v; revert u v; decide
        have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
        exact ⟨e.1, ⟨fun h => hx2B (h ▸ hb), hadj'⟩, by simp [hnot]⟩
    calc (bipEdges {x} B).card
        ≤ ((N.erase x2).image (fun b => if x < b then (x, b) else (b, x))).card := Finset.card_le_card hsubx
      _ ≤ (N.erase x2).card := Finset.card_image_le
      _ = N.card - 1 := Finset.card_erase_of_mem hx2N
      _ ≤ 2 := by have hN : N.card ≤ 3 := petersen_deg_le_3 x; omega
  have h1 : (bipEdges (insert x Y) B).card ≤ 2 + 3 * Y.card := by
    calc (bipEdges (insert x Y) B).card
        ≤ (bipEdges {x} B ∪ bipEdges Y B).card := Finset.card_le_card hsub
      _ ≤ (bipEdges {x} B).card + (bipEdges Y B).card := Finset.card_union_le _ _
      _ ≤ 2 + 3 * Y.card := Nat.add_le_add hx_le2 hY_le
  omega

lemma bipEdges_le_right_of_card_le_one (A B : Finset (Fin 10)) (hA : A.card ≤ 1) :
    (bipEdges A B).card ≤ B.card := by
  by_cases hAne : A.Nonempty
  · have hA1 : A.card = 1 := by have := Finset.card_pos.mpr hAne; omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA1
    have hsub : bipEdges {a} B ⊆ B.image fun b => if a < b then (a, b) else (b, a) := by
      intro e he
      simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
      have hlt := petersenEdges_lt e he.1
      simp only [Finset.mem_image]
      rcases he.2 with ⟨rfl, hb⟩ | ⟨hb, rfl⟩
      · exact ⟨e.2, hb, by simp [hlt]⟩
      · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
        exact ⟨e.1, hb, by simp [hnot]⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  · rw [Finset.not_nonempty_iff_eq_empty] at hAne
    subst hAne
    have : bipEdges ∅ B = ∅ := by ext e; simp [bipEdges]
    rw [this]; simp

set_option maxHeartbeats 800000 in
theorem golden_read2_bound (M0 : Finset (Fin 10)) (L : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, L.varCount v ≤ 2)
    (hM0 : ∀ m ∈ M0, L.varCount m ≤ 1)
    (hno : ∀ u v : Fin 10, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → L.eval (pairInput u v) = false) :
    (singleSet L).card + (edgesM0 M0 L).card ≤ L.leaves := by
  induction L with
  | var i =>
    have hS : singleSet (MonoFormula.var i) = {i} := by
      ext v; simp [singleSet, MonoFormula.eval, singleInput, eq_comm]
    have hE : edgesM0 M0 (MonoFormula.var i) = ∅ := by
      ext e
      simp only [edgesM0, Finset.mem_filter, hS, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨_, _, hev, h1, h2⟩
      simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at hev
      rcases hev with h | h
      · exact h1 h.symm
      · exact h2 h.symm
    rw [hS, hE]; simp [MonoFormula.leaves]
  | or l r ihl ihr =>
    have hr2l : ∀ v, l.varCount v ≤ 2 := fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega
    have hr2r : ∀ v, r.varCount v ≤ 2 := fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega
    have hM0l : ∀ m ∈ M0, l.varCount m ≤ 1 := fun m hm => by have := hM0 m hm; simp [MonoFormula.varCount] at this; omega
    have hM0r : ∀ m ∈ M0, r.varCount m ≤ 1 := fun m hm => by have := hM0 m hm; simp [MonoFormula.varCount] at this; omega
    have hnol : ∀ u v, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → l.eval (pairInput u v) = false := by
      intro u v hm hadj; have h := hno u v hm hadj; simp [MonoFormula.eval] at h; exact h.1
    have hnor : ∀ u v, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → r.eval (pairInput u v) = false := by
      intro u v hm hadj; have h := hno u v hm hadj; simp [MonoFormula.eval] at h; exact h.2
    have hS_sub : singleSet (l.or r) ⊆ singleSet l ∪ singleSet r := by
      intro v hv
      simp only [singleSet, Finset.mem_filter, Finset.mem_univ, true_and, MonoFormula.eval,
        Bool.or_eq_true, Finset.mem_union] at hv ⊢
      exact hv
    have hE_sub : edgesM0 M0 (l.or r) ⊆ edgesM0 M0 l ∪ edgesM0 M0 r := by
      intro e he
      simp only [edgesM0, Finset.mem_filter, Finset.mem_union, singleSet, Finset.mem_univ,
        true_and, MonoFormula.eval, Bool.or_eq_true, not_or] at he ⊢
      rcases he.2.2.1 with hl | hr
      · exact Or.inl ⟨he.1, he.2.1, hl, he.2.2.2.1.1, he.2.2.2.2.1⟩
      · exact Or.inr ⟨he.1, he.2.1, hr, he.2.2.2.1.2, he.2.2.2.2.2⟩
    have c1 := Finset.card_le_card hS_sub
    have c2 := Finset.card_union_le (singleSet l) (singleSet r)
    have c3 := Finset.card_le_card hE_sub
    have c4 := Finset.card_union_le (edgesM0 M0 l) (edgesM0 M0 r)
    have b1 := ihl hr2l hM0l hnol
    have b2 := ihr hr2r hM0r hnor
    simp only [MonoFormula.leaves]
    omega
  | and l r _ _ =>
    let S1 := singleSet l
    let S2 := singleSet r
    let S := singleSet (l.and r)
    have hS_eq : S = S1 ∩ S2 := by
      ext v; simp [S, S1, S2, singleSet, MonoFormula.eval]
    let A0 := M0 ∩ l.orVars
    let B0 := M0 ∩ r.orVars
    have hAB_disj : Disjoint A0 B0 := by
      rw [Finset.disjoint_left]
      intro m hmA hmB
      have hm0 : m ∈ M0 := (Finset.mem_inter.mp hmA).1
      have hml : m ∈ l.orVars := (Finset.mem_inter.mp hmA).2
      have hmr : m ∈ r.orVars := (Finset.mem_inter.mp hmB).2
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hml hmr
      have h1 := hM0 m hm0; simp [MonoFormula.varCount] at h1; omega
    let W1 := (l.orVars ∩ S2) \ S
    let W2 := (r.orVars ∩ S1) \ S
    let S1' := S1 \ r.orVars
    let S2' := S2 \ l.orVars
    let X1 := A0 ∩ S1'
    let Y1 := A0 \ S1'
    let Z1 := S1' \ A0
    let X2 := B0 ∩ S2'
    let Y2 := B0 \ S2'
    let Z2 := S2' \ B0
    have hS1_sub : S1 ⊆ l.orVars := singleSet_subset_orVars l
    have hS2_sub : S2 ⊆ r.orVars := singleSet_subset_orVars r
    have hA0_not_r : ∀ v ∈ A0, v ∉ r.orVars := fun v hv hr =>
      Finset.disjoint_left.mp hAB_disj hv (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hr⟩)
    have hB0_not_l : ∀ v ∈ B0, v ∉ l.orVars := fun v hv hl =>
      Finset.disjoint_left.mp hAB_disj (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hl⟩) hv
    have hl_budget : S.card + W1.card + W2.card + X1.card + Y1.card + Z1.card ≤ l.leaves := by
      have hpart1 : S.card + W1.card + W2.card + X1.card + Y1.card + Z1.card =
          (S ∪ W1 ∪ W2 ∪ X1 ∪ Y1 ∪ Z1).card := by
        have d1 : Disjoint S W1 := by
          rw [Finset.disjoint_left]; intro x hx h2; exact (Finset.mem_sdiff.mp h2).2 hx
        have d2 : Disjoint (S ∪ W1) W2 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have h2' := Finset.mem_sdiff.mp h2
          rw [Finset.mem_union] at hx
          rcases hx with hs | hw1
          · exact h2'.2 hs
          · have hxs2 : x ∈ S2 := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2
            have hxs1 : x ∈ S1 := (Finset.mem_inter.mp h2'.1).2
            exact h2'.2 (hS_eq ▸ Finset.mem_inter.mpr ⟨hxs1, hxs2⟩)
        have d3 : Disjoint (S ∪ W1 ∪ W2) X1 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have hnr : x ∉ r.orVars := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).2).2
          simp only [Finset.mem_union] at hx
          rcases hx with (hs | hw1) | hw2
          · exact hnr (hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2)
          · exact hnr (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2)
          · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
        have d4 : Disjoint (S ∪ W1 ∪ W2 ∪ X1) Y1 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have hnr : x ∉ r.orVars := hA0_not_r x (Finset.mem_sdiff.mp h2).1
          have hns : x ∉ S1' := (Finset.mem_sdiff.mp h2).2
          simp only [Finset.mem_union] at hx
          rcases hx with ((hs | hw1) | hw2) | hx1
          · exact hnr (hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2)
          · exact hnr (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2)
          · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
          · exact hns (Finset.mem_inter.mp hx1).2
        have d5 : Disjoint (S ∪ W1 ∪ W2 ∪ X1 ∪ Y1) Z1 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have hnr : x ∉ r.orVars := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2
          have hna : x ∉ A0 := (Finset.mem_sdiff.mp h2).2
          simp only [Finset.mem_union] at hx
          rcases hx with (((hs | hw1) | hw2) | hx1) | hy1
          · exact hnr (hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2)
          · exact hnr (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2)
          · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
          · exact hna (Finset.mem_inter.mp hx1).1
          · exact hna (Finset.mem_sdiff.mp hy1).1
        rw [Finset.card_union_of_disjoint d5, Finset.card_union_of_disjoint d4,
          Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
          Finset.card_union_of_disjoint d1]
      have hsub : S ∪ W1 ∪ W2 ∪ X1 ∪ Y1 ∪ Z1 ⊆ l.orVars := by
        intro x hx
        simp only [Finset.mem_union] at hx
        rcases hx with ((((hs | hw1) | hw2) | hx1) | hy1) | hz1
        · exact hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
        · exact hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx1).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy1).1).2
        · exact hS1_sub (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz1).1).1
      rw [hpart1]
      exact le_trans (Finset.card_le_card hsub) l.orVars_card_le
    have hr_budget : S.card + W1.card + W2.card + X2.card + Y2.card + Z2.card ≤ r.leaves := by
      have hpart2 : S.card + W1.card + W2.card + X2.card + Y2.card + Z2.card =
          (S ∪ W1 ∪ W2 ∪ X2 ∪ Y2 ∪ Z2).card := by
        have d1 : Disjoint S W1 := by
          rw [Finset.disjoint_left]; intro x hx h2; exact (Finset.mem_sdiff.mp h2).2 hx
        have d2 : Disjoint (S ∪ W1) W2 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have h2' := Finset.mem_sdiff.mp h2
          rw [Finset.mem_union] at hx
          rcases hx with hs | hw1
          · exact h2'.2 hs
          · have hxs2 : x ∈ S2 := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2
            have hxs1 : x ∈ S1 := (Finset.mem_inter.mp h2'.1).2
            exact h2'.2 (hS_eq ▸ Finset.mem_inter.mpr ⟨hxs1, hxs2⟩)
        have d3 : Disjoint (S ∪ W1 ∪ W2) X2 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have hnl : x ∉ l.orVars := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).2).2
          simp only [Finset.mem_union] at hx
          rcases hx with (hs | hw1) | hw2
          · exact hnl (hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1)
          · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
          · exact hnl (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2)
        have d4 : Disjoint (S ∪ W1 ∪ W2 ∪ X2) Y2 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have hnl : x ∉ l.orVars := hB0_not_l x (Finset.mem_sdiff.mp h2).1
          have hns : x ∉ S2' := (Finset.mem_sdiff.mp h2).2
          simp only [Finset.mem_union] at hx
          rcases hx with ((hs | hw1) | hw2) | hx2
          · exact hnl (hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1)
          · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
          · exact hnl (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2)
          · exact hns (Finset.mem_inter.mp hx2).2
        have d5 : Disjoint (S ∪ W1 ∪ W2 ∪ X2 ∪ Y2) Z2 := by
          rw [Finset.disjoint_left]; intro x hx h2
          have hnl : x ∉ l.orVars := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2
          have hnb : x ∉ B0 := (Finset.mem_sdiff.mp h2).2
          simp only [Finset.mem_union] at hx
          rcases hx with (((hs | hw1) | hw2) | hx2) | hy2
          · exact hnl (hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1)
          · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
          · exact hnl (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2)
          · exact hnb (Finset.mem_inter.mp hx2).1
          · exact hnb (Finset.mem_sdiff.mp hy2).1
        rw [Finset.card_union_of_disjoint d5, Finset.card_union_of_disjoint d4,
          Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
          Finset.card_union_of_disjoint d1]
      have hsub : S ∪ W1 ∪ W2 ∪ X2 ∪ Y2 ∪ Z2 ⊆ r.orVars := by
        intro x hx
        simp only [Finset.mem_union] at hx
        rcases hx with ((((hs | hw1) | hw2) | hx2) | hy2) | hz2
        · exact hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2
        · exact hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx2).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy2).1).2
        · exact hS2_sub (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz2).1).1
      rw [hpart2]
      exact le_trans (Finset.card_le_card hsub) r.orVars_card_le
    have hE_sub : edgesM0 M0 (l.and r) ⊆
        bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2 ∪ bipEdges X2 Z1 := by
      have hdir : ∀ u v : Fin 10, (u, v) ∈ petersenEdges → u ∈ M0 →
          (l.and r).eval (pairInput u v) = true → u ∉ S → v ∉ S →
          (u, v) ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2 ∪ bipEdges X2 Z1 := by
        intro u v he hum huv hus hvs
        simp only [MonoFormula.eval, Bool.and_eq_true] at huv
        by_cases hul : u ∈ l.orVars
        · have huA : u ∈ A0 := Finset.mem_inter.mpr ⟨hum, hul⟩
          have hunr : u ∉ r.orVars := hA0_not_r u huA
          have hrv : r.eval (singleInput v) = true := by
            have h1 := eval_pair_of_not_mem r u v hunr
            change r.eval (pairInput u v) = r.eval (singleInput v) at h1
            rw [← h1]; exact huv.2
          have hvS2 : v ∈ S2 := by simp [S2, singleSet, hrv]
          by_cases hvl : v ∈ l.orVars
          · have hvW1 : v ∈ W1 := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvl, hvS2⟩, hvs⟩
            simp only [Finset.mem_union]
            exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he, Or.inl ⟨huA, hvW1⟩⟩))))
          · have hvS2' : v ∈ S2' := Finset.mem_sdiff.mpr ⟨hvS2, hvl⟩
            have hlu : l.eval (singleInput u) = true := by
              have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
              have h1 := eval_pair_of_not_mem l v u hvl
              change l.eval (pairInput v u) = l.eval (singleInput u) at h1
              rw [← h1, ← hsym]; exact huv.1
            have huX1 : u ∈ X1 := Finset.mem_inter.mpr ⟨huA, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hlu], hunr⟩⟩
            by_cases hvB0 : v ∈ B0
            · have hvX2 : v ∈ X2 := Finset.mem_inter.mpr ⟨hvB0, hvS2'⟩
              simp only [Finset.mem_union]
              exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he, Or.inl ⟨huX1, hvX2⟩⟩)))
            · have hvZ2 : v ∈ Z2 := Finset.mem_sdiff.mpr ⟨hvS2', hvB0⟩
              simp only [Finset.mem_union]
              exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he, Or.inl ⟨huX1, hvZ2⟩⟩))
        · by_cases hur : u ∈ r.orVars
          · have huB : u ∈ B0 := Finset.mem_inter.mpr ⟨hum, hur⟩
            have hlv : l.eval (singleInput v) = true := by
              have h1 := eval_pair_of_not_mem l u v hul
              change l.eval (pairInput u v) = l.eval (singleInput v) at h1
              rw [← h1]; exact huv.1
            have hvS1 : v ∈ S1 := by simp [S1, singleSet, hlv]
            by_cases hvr : v ∈ r.orVars
            · have hvW2 : v ∈ W2 := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvr, hvS1⟩, hvs⟩
              simp only [Finset.mem_union]
              exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he, Or.inl ⟨huB, hvW2⟩⟩))))
            · have hvS1' : v ∈ S1' := Finset.mem_sdiff.mpr ⟨hvS1, hvr⟩
              have hru : r.eval (singleInput u) = true := by
                have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                have h1 := eval_pair_of_not_mem r v u hvr
                change r.eval (pairInput v u) = r.eval (singleInput u) at h1
                rw [← h1, ← hsym]; exact huv.2
              have huX2 : u ∈ X2 := Finset.mem_inter.mpr ⟨huB, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hru], hul⟩⟩
              by_cases hvA0 : v ∈ A0
              · have hvX1 : v ∈ X1 := Finset.mem_inter.mpr ⟨hvA0, hvS1'⟩
                simp only [Finset.mem_union]
                exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he, Or.inr ⟨huX2, hvX1⟩⟩)))
              · have hvZ1 : v ∈ Z1 := Finset.mem_sdiff.mpr ⟨hvS1', hvA0⟩
                simp only [Finset.mem_union]
                exact Or.inr (Finset.mem_filter.mpr ⟨he, Or.inl ⟨huX2, hvZ1⟩⟩)
          · exfalso
            have hlv : l.eval (singleInput v) = true := by
              have h1 := eval_pair_of_not_mem l u v hul
              change l.eval (pairInput u v) = l.eval (singleInput v) at h1
              rw [← h1]; exact huv.1
            have hrv : r.eval (singleInput v) = true := by
              have h1 := eval_pair_of_not_mem r u v hur
              change r.eval (pairInput u v) = r.eval (singleInput v) at h1
              rw [← h1]; exact huv.2
            exact hvs (by simp [S, singleSet, MonoFormula.eval, hlv, hrv])
      intro e he
      simp only [edgesM0, Finset.mem_filter] at he
      rcases he.2.1 with h1 | h2
      · exact hdir e.1 e.2 he.1 h1 he.2.2.1 he.2.2.2.1 he.2.2.2.2
      · have hsym : pairInput e.2 e.1 = pairInput e.1 e.2 := by funext i; simp [pairInput, or_comm]
        have hdir' : ∀ u v : Fin 10, (v, u) ∈ petersenEdges → u ∈ M0 →
            (l.and r).eval (pairInput u v) = true → u ∉ S → v ∉ S →
            (v, u) ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2 ∪ bipEdges X2 Z1 := by
          intro u v he' hum huv hus hvs
          simp only [MonoFormula.eval, Bool.and_eq_true] at huv
          by_cases hul : u ∈ l.orVars
          · have huA : u ∈ A0 := Finset.mem_inter.mpr ⟨hum, hul⟩
            have hunr : u ∉ r.orVars := hA0_not_r u huA
            have hrv : r.eval (singleInput v) = true := by
              have h1 := eval_pair_of_not_mem r u v hunr
              change r.eval (pairInput u v) = r.eval (singleInput v) at h1
              rw [← h1]; exact huv.2
            have hvS2 : v ∈ S2 := by simp [S2, singleSet, hrv]
            by_cases hvl : v ∈ l.orVars
            · have hvW1 : v ∈ W1 := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvl, hvS2⟩, hvs⟩
              simp only [Finset.mem_union]
              exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he', Or.inr ⟨hvW1, huA⟩⟩))))
            · have hvS2' : v ∈ S2' := Finset.mem_sdiff.mpr ⟨hvS2, hvl⟩
              have hlu : l.eval (singleInput u) = true := by
                have hsym2 : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                have h1 := eval_pair_of_not_mem l v u hvl
                change l.eval (pairInput v u) = l.eval (singleInput u) at h1
                rw [← h1, ← hsym2]; exact huv.1
              have huX1 : u ∈ X1 := Finset.mem_inter.mpr ⟨huA, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hlu], hunr⟩⟩
              by_cases hvB0 : v ∈ B0
              · have hvX2 : v ∈ X2 := Finset.mem_inter.mpr ⟨hvB0, hvS2'⟩
                simp only [Finset.mem_union]
                exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨hvX2, huX1⟩⟩)))
              · have hvZ2 : v ∈ Z2 := Finset.mem_sdiff.mpr ⟨hvS2', hvB0⟩
                simp only [Finset.mem_union]
                exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨hvZ2, huX1⟩⟩))
          · by_cases hur : u ∈ r.orVars
            · have huB : u ∈ B0 := Finset.mem_inter.mpr ⟨hum, hur⟩
              have hlv : l.eval (singleInput v) = true := by
                have h1 := eval_pair_of_not_mem l u v hul
                change l.eval (pairInput u v) = l.eval (singleInput v) at h1
                rw [← h1]; exact huv.1
              have hvS1 : v ∈ S1 := by simp [S1, singleSet, hlv]
              by_cases hvr : v ∈ r.orVars
              · have hvW2 : v ∈ W2 := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvr, hvS1⟩, hvs⟩
                simp only [Finset.mem_union]
                exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨hvW2, huB⟩⟩))))
              · have hvS1' : v ∈ S1' := Finset.mem_sdiff.mpr ⟨hvS1, hvr⟩
                have hru : r.eval (singleInput u) = true := by
                  have hsym2 : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                  have h1 := eval_pair_of_not_mem r v u hvr
                  change r.eval (pairInput v u) = r.eval (singleInput u) at h1
                  rw [← h1, ← hsym2]; exact huv.2
                have huX2 : u ∈ X2 := Finset.mem_inter.mpr ⟨huB, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hru], hul⟩⟩
                by_cases hvA0 : v ∈ A0
                · have hvX1 : v ∈ X1 := Finset.mem_inter.mpr ⟨hvA0, hvS1'⟩
                  simp only [Finset.mem_union]
                  exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨hvX1, huX2⟩⟩)))
                · have hvZ1 : v ∈ Z1 := Finset.mem_sdiff.mpr ⟨hvS1', hvA0⟩
                  simp only [Finset.mem_union]
                  exact Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨hvZ1, huX2⟩⟩)
            · exfalso
              have hlv : l.eval (singleInput v) = true := by
                have h1 := eval_pair_of_not_mem l u v hul
                change l.eval (pairInput u v) = l.eval (singleInput v) at h1
                rw [← h1]; exact huv.1
              have hrv : r.eval (singleInput v) = true := by
                have h1 := eval_pair_of_not_mem r u v hur
                change r.eval (pairInput u v) = r.eval (singleInput v) at h1
                rw [← h1]; exact huv.2
              exact hvs (by simp [S, singleSet, MonoFormula.eval, hlv, hrv])
        exact hdir' e.2 e.1 he.1 h2 (by rw [hsym]; exact he.2.2.1) he.2.2.2.2 he.2.2.2.1
    have hdisj_A0W1 : Disjoint A0 W1 := by
      rw [Finset.disjoint_left]; intro x hxA hxW
      exact hA0_not_r x hxA (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).2)
    have hdisj_B0W2 : Disjoint B0 W2 := by
      rw [Finset.disjoint_left]; intro x hxB hxW
      exact hB0_not_l x hxB (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).2)
    have hA0_card : A0.card = X1.card + Y1.card := (Finset.card_inter_add_card_sdiff A0 S1').symm
    have hB0_card : B0.card = X2.card + Y2.card := (Finset.card_inter_add_card_sdiff B0 S2').symm
    have hbic1 : X1.card ≤ 1 ∨ (W1 ∪ X2 ∪ Z2).card ≤ 1 := by
      apply petersen_biclique_star
      intro x hx v hv
      have hxM0 : x ∈ M0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      have hxS1 : x ∈ S1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
      have hvS2 : v ∈ S2 := by
        simp only [Finset.mem_union] at hv
        rcases hv with (hw1 | hx2) | hz2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz2).1).1
      have hl1 : l.eval (singleInput x) = true := (Finset.mem_filter.mp hxS1).2
      have hr1 : r.eval (singleInput v) = true := (Finset.mem_filter.mp hvS2).2
      cases hadj : petersenAdj x v
      · exfalso
        have hf := hno x v (Or.inl hxM0) hadj
        have ht : (l.and r).eval (pairInput x v) = true := by
          simp only [MonoFormula.eval, Bool.and_eq_true]
          exact ⟨l.eval_mono (singleInput x) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hl1,
            r.eval_mono (singleInput v) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hr1⟩
        rw [hf] at ht; exact absurd ht (by decide)
      · rfl
    have hbic2 : X2.card ≤ 1 ∨ (W2 ∪ X1 ∪ Z1).card ≤ 1 := by
      apply petersen_biclique_star
      intro x hx v hv
      have hxM0 : x ∈ M0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      have hxS2 : x ∈ S2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
      have hvS1 : v ∈ S1 := by
        simp only [Finset.mem_union] at hv
        rcases hv with (hw2 | hx1) | hz1
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx1).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz1).1).1
      have hr1 : r.eval (singleInput x) = true := (Finset.mem_filter.mp hxS2).2
      have hl1 : l.eval (singleInput v) = true := (Finset.mem_filter.mp hvS1).2
      cases hadj : petersenAdj x v
      · exfalso
        have hf := hno x v (Or.inl hxM0) hadj
        have ht : (l.and r).eval (pairInput x v) = true := by
          simp only [MonoFormula.eval, Bool.and_eq_true]
          exact ⟨l.eval_mono (singleInput v) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hl1,
            r.eval_mono (singleInput x) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hr1⟩
        rw [hf] at ht; exact absurd ht (by decide)
      · rfl
    have hE_union : (edgesM0 M0 (l.and r)).card ≤
        (bipEdges A0 W1).card + (bipEdges B0 W2).card + (bipEdges X1 X2).card +
        (bipEdges X1 Z2).card + (bipEdges X2 Z1).card := by
      calc (edgesM0 M0 (l.and r)).card
          ≤ (bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2 ∪ bipEdges X2 Z1).card :=
            Finset.card_le_card hE_sub
        _ ≤ _ := by
            have u1 := Finset.card_union_le (bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2) (bipEdges X2 Z1)
            have u2 := Finset.card_union_le (bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2) (bipEdges X1 Z2)
            have u3 := Finset.card_union_le (bipEdges A0 W1 ∪ bipEdges B0 W2) (bipEdges X1 X2)
            have u4 := Finset.card_union_le (bipEdges A0 W1) (bipEdges B0 W2)
            omega
    have hE_bound : (edgesM0 M0 (l.and r)).card ≤
        2 * W1.card + 2 * W2.card + X1.card + Y1.card + Z1.card + X2.card + Y2.card + Z2.card := by
      rcases hbic1 with hX1 | hR1
      · rcases hbic2 with hX2 | hL1
        · have bZ2 := bipEdges_le_right_of_card_le_one X1 Z2 hX1
          have bZ1 := bipEdges_le_right_of_card_le_one X2 Z1 hX2
          by_cases hX12 : (bipEdges X1 X2).Nonempty
          · obtain ⟨e, he⟩ := hX12
            have he_adj := petersenEdges_adj e (Finset.mem_filter.mp he).1
            have hex_x : ∃ x1 x2, X1 = {x1} ∧ X2 = {x2} ∧ petersenAdj x1 x2 = true := by
              have hX1ne : X1.Nonempty := by
                rcases (Finset.mem_filter.mp he).2 with ⟨h1, _⟩ | ⟨_, h2⟩
                · exact ⟨e.1, h1⟩
                · exact ⟨e.2, h2⟩
              have hX2ne : X2.Nonempty := by
                rcases (Finset.mem_filter.mp he).2 with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact ⟨e.2, h2⟩
                · exact ⟨e.1, h1⟩
              obtain ⟨x1, hx1⟩ := Finset.card_eq_one.mp (le_antisymm hX1 (Finset.card_pos.mpr hX1ne))
              obtain ⟨x2, hx2⟩ := Finset.card_eq_one.mp (le_antisymm hX2 (Finset.card_pos.mpr hX2ne))
              refine ⟨x1, x2, hx1, hx2, ?_⟩
              rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [hx1, Finset.mem_singleton] at h1; rw [hx2, Finset.mem_singleton] at h2
                rw [← h1, ← h2]; exact he_adj
              · rw [hx2, Finset.mem_singleton] at h1; rw [hx1, Finset.mem_singleton] at h2
                rw [← h1, ← h2]; exact petersenAdj_symm e.1 e.2 he_adj
            obtain ⟨x1, x2, hX1eq, hX2eq, hx12_adj⟩ := hex_x
            have hA0_ins : A0 = insert x1 Y1 := by
              ext z; simp only [Finset.mem_insert, Y1, Finset.mem_sdiff]
              constructor
              · intro hz
                by_cases hzs : z ∈ S1'
                · left; have : z ∈ X1 := Finset.mem_inter.mpr ⟨hz, hzs⟩
                  rw [hX1eq, Finset.mem_singleton] at this; exact this
                · exact Or.inr ⟨hz, hzs⟩
              · rintro (hz | ⟨hz, _⟩)
                · subst z
                  have : x1 ∈ X1 := by rw [hX1eq]; simp
                  exact (Finset.mem_inter.mp this).1
                · exact hz
            have hB0_ins : B0 = insert x2 Y2 := by
              ext z; simp only [Finset.mem_insert, Y2, Finset.mem_sdiff]
              constructor
              · intro hz
                by_cases hzs : z ∈ S2'
                · left; have : z ∈ X2 := Finset.mem_inter.mpr ⟨hz, hzs⟩
                  rw [hX2eq, Finset.mem_singleton] at this; exact this
                · exact Or.inr ⟨hz, hzs⟩
              · rintro (hz | ⟨hz, _⟩)
                · subst z
                  have : x2 ∈ X2 := by rw [hX2eq]; simp
                  exact (Finset.mem_inter.mp this).1
                · exact hz
            have hx1Y1 : x1 ∉ Y1 := by
              intro h; have h1 : x1 ∈ X1 := by rw [hX1eq]; simp
              exact (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp h1).2
            have hx2Y2 : x2 ∉ Y2 := by
              intro h; have h2 : x2 ∈ X2 := by rw [hX2eq]; simp
              exact (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp h2).2
            have hx2W1 : x2 ∉ W1 := by
              intro h; have h2 : x2 ∈ X2 := by rw [hX2eq]; simp
              have hnl : x2 ∉ l.orVars := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).2).2
              exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
            have hx1W2 : x1 ∉ W2 := by
              intro h; have h1 : x1 ∈ X1 := by rw [hX1eq]; simp
              have hnr : x1 ∉ r.orVars := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h1).2).2
              exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
            have bAW := bipEdges_le_add_two_of_ext x1 x2 Y1 W1 hx1Y1 hx2W1 hx12_adj (hA0_ins ▸ hdisj_A0W1)
            rw [← hA0_ins] at bAW
            have hx21_adj : petersenAdj x2 x1 = true := petersenAdj_symm x1 x2 hx12_adj
            have bBW := bipEdges_le_add_two_of_ext x2 x1 Y2 W2 hx2Y2 hx1W2 hx21_adj (hB0_ins ▸ hdisj_B0W2)
            rw [← hB0_ins] at bBW
            have bX12 := bipEdges_le_right_of_card_le_one X1 X2 hX1
            omega
          · rw [Finset.not_nonempty_iff_eq_empty] at hX12
            have bAW := bipEdges_le_add_two A0 W1 hdisj_A0W1
            have bBW := bipEdges_le_add_two B0 W2 hdisj_B0W2
            rw [hX12, Finset.card_empty] at hE_union
            omega
        · have hW2_le : W2.card ≤ 1 := le_trans (Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)) hL1
          have hZ1_le : Z1.card ≤ 1 := le_trans (Finset.card_le_card Finset.subset_union_right) hL1
          have hdisj_W2X1 : Disjoint W2 X1 := by
            rw [Finset.disjoint_left]; intro x hxW hxX
            exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxX).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).1
          have hdisj_W2X1_Z1 : Disjoint (W2 ∪ X1) Z1 := by
            rw [Finset.disjoint_left]; intro x hx hxZ
            have hnr : x ∉ r.orVars := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxZ).1).2
            have hna : x ∉ A0 := (Finset.mem_sdiff.mp hxZ).2
            rw [Finset.mem_union] at hx
            rcases hx with hw2 | hx1
            · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
            · exact hna (Finset.mem_inter.mp hx1).1
          have hsum1 : W2.card + X1.card + Z1.card ≤ 1 := by
            rw [← Finset.card_union_of_disjoint hdisj_W2X1, ← Finset.card_union_of_disjoint hdisj_W2X1_Z1]
            exact hL1
          have bAW := bipEdges_le_add_two A0 W1 hdisj_A0W1
          have bBW := bipEdges_le_add_two B0 W2 hdisj_B0W2
          have bZ2 := bipEdges_le_right_of_card_le_one X1 Z2 hX1
          have bX12 := bipEdges_le_right_of_card_le_one X1 X2 hX1
          have bZ1 : (bipEdges X2 Z1).card ≤ X2.card := by
            rw [bipEdges_comm]; exact bipEdges_le_right_of_card_le_one Z1 X2 hZ1_le
          by_cases hX10 : X1.card = 0
          · have eX12 : bipEdges X1 X2 = ∅ := by
              rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdges]
            have eZ2 : bipEdges X1 Z2 = ∅ := by
              rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdges]
            rw [eX12, eZ2, Finset.card_empty] at hE_union
            by_cases hZ10 : Z1.card = 0
            · have eZ1 : bipEdges X2 Z1 = ∅ := by
                rw [Finset.card_eq_zero.mp hZ10]; ext e; simp [bipEdges]
              rw [eZ1, Finset.card_empty] at hE_union; omega
            · have hW20 : W2.card = 0 := by omega
              have eBW : bipEdges B0 W2 = ∅ := by
                rw [Finset.card_eq_zero.mp hW20]; ext e; simp [bipEdges]
              rw [eBW, Finset.card_empty] at hE_union; omega
          · have hW20 : W2.card = 0 := by omega
            have hZ10 : Z1.card = 0 := by omega
            have eBW : bipEdges B0 W2 = ∅ := by
              rw [Finset.card_eq_zero.mp hW20]; ext e; simp [bipEdges]
            have eZ1 : bipEdges X2 Z1 = ∅ := by
              rw [Finset.card_eq_zero.mp hZ10]; ext e; simp [bipEdges]
            rw [eBW, eZ1, Finset.card_empty] at hE_union; omega
      · have hW1_le : W1.card ≤ 1 := le_trans (Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)) hR1
        have hX2_le : X2.card ≤ 1 := le_trans (Finset.card_le_card (Finset.subset_union_right.trans Finset.subset_union_left)) hR1
        have hZ2_le : Z2.card ≤ 1 := le_trans (Finset.card_le_card Finset.subset_union_right) hR1
        have hdisj_W1X2 : Disjoint W1 X2 := by
          rw [Finset.disjoint_left]; intro x hxW hxX
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxX).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).1
        have hdisj_W1X2_Z2 : Disjoint (W1 ∪ X2) Z2 := by
          rw [Finset.disjoint_left]; intro x hx hxZ
          have hnl : x ∉ l.orVars := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxZ).1).2
          have hnb : x ∉ B0 := (Finset.mem_sdiff.mp hxZ).2
          rw [Finset.mem_union] at hx
          rcases hx with hw1 | hx2
          · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
          · exact hnb (Finset.mem_inter.mp hx2).1
        have hsum1 : W1.card + X2.card + Z2.card ≤ 1 := by
          rw [← Finset.card_union_of_disjoint hdisj_W1X2, ← Finset.card_union_of_disjoint hdisj_W1X2_Z2]
          exact hR1
        have bAW := bipEdges_le_add_two A0 W1 hdisj_A0W1
        have bBW := bipEdges_le_add_two B0 W2 hdisj_B0W2
        have bZ1 := bipEdges_le_right_of_card_le_one X2 Z1 hX2_le
        have bX12 : (bipEdges X1 X2).card ≤ X1.card := by
          rw [bipEdges_comm]; exact bipEdges_le_right_of_card_le_one X2 X1 hX2_le
        have bZ2 : (bipEdges X1 Z2).card ≤ X1.card := by
          rw [bipEdges_comm]; exact bipEdges_le_right_of_card_le_one Z2 X1 hZ2_le
        by_cases hX20 : X2.card = 0
        · have eX12 : bipEdges X1 X2 = ∅ := by
            rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdges]
          have eZ1 : bipEdges X2 Z1 = ∅ := by
            rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdges]
          rw [eX12, eZ1, Finset.card_empty] at hE_union
          by_cases hZ20 : Z2.card = 0
          · have eZ2 : bipEdges X1 Z2 = ∅ := by
              rw [Finset.card_eq_zero.mp hZ20]; ext e; simp [bipEdges]
            rw [eZ2, Finset.card_empty] at hE_union; omega
          · have hW10 : W1.card = 0 := by omega
            have eAW : bipEdges A0 W1 = ∅ := by
              rw [Finset.card_eq_zero.mp hW10]; ext e; simp [bipEdges]
            rw [eAW, Finset.card_empty] at hE_union; omega
        · have hW10 : W1.card = 0 := by omega
          have hZ20 : Z2.card = 0 := by omega
          have eAW : bipEdges A0 W1 = ∅ := by
            rw [Finset.card_eq_zero.mp hW10]; ext e; simp [bipEdges]
          have eZ2 : bipEdges X1 Z2 = ∅ := by
            rw [Finset.card_eq_zero.mp hZ20]; ext e; simp [bipEdges]
          rw [eAW, eZ2, Finset.card_empty] at hE_union; omega
    change S.card + (edgesM0 M0 (l.and r)).card ≤ l.leaves + r.leaves
    omega

theorem read2_and_clean_bound (l r : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, (l.and r).varCount v ≤ 2)
    (hle : ∀ x : Fin 10 → Bool, (l.and r).eval x = true → petersenFun x = true)
    (hSl : singleSet l = ∅)
    (hMr : l.orVars ∩ r.orVars ⊆ singleSet r) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, (l.and r).eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ (l.and r).leaves := by
  let M := l.orVars ∩ r.orVars
  refine ⟨M, edgesM0 M l, ?_, ?_, ?_⟩
  · intro e he hev
    simp only [MonoFormula.eval, Bool.and_eq_true] at hev
    have hnotS : ∀ v : Fin 10, v ∉ singleSet l := by rw [hSl]; simp
    have hmemM : e.1 ∈ M ∨ e.2 ∈ M := by
      have hl_or : e.1 ∈ l.orVars ∨ e.2 ∈ l.orVars := by
        by_contra h; push Not at h
        have hf := eval_pair_of_not_mem_both l e.1 e.2 h.1 h.2
        change l.eval (pairInput e.1 e.2) = false at hf; rw [hf] at hev; exact absurd hev.1 (by decide)
      have hr_or : e.1 ∈ r.orVars ∨ e.2 ∈ r.orVars := by
        by_contra h; push Not at h
        have hf := eval_pair_of_not_mem_both r e.1 e.2 h.1 h.2
        change r.eval (pairInput e.1 e.2) = false at hf; rw [hf] at hev; exact absurd hev.2 (by decide)
      have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
      rcases hl_or with h1l | h2l <;> rcases hr_or with h1r | h2r
      · exact Or.inl (Finset.mem_inter.mpr ⟨h1l, h1r⟩)
      · by_cases h2l' : e.2 ∈ l.orVars
        · exact Or.inr (Finset.mem_inter.mpr ⟨h2l', h2r⟩)
        · exfalso
          have h1 := eval_pair_of_not_mem l e.2 e.1 h2l'
          change l.eval (pairInput e.2 e.1) = l.eval (singleInput e.1) at h1
          rw [← hsym] at h1
          have hs : e.1 ∈ singleSet l := by simp [singleSet, ← h1, hev.1]
          exact hnotS e.1 hs
      · by_cases h1l' : e.1 ∈ l.orVars
        · exact Or.inl (Finset.mem_inter.mpr ⟨h1l', h1r⟩)
        · exfalso
          have h1 := eval_pair_of_not_mem l e.1 e.2 h1l'
          change l.eval (pairInput e.1 e.2) = l.eval (singleInput e.2) at h1
          have hs : e.2 ∈ singleSet l := by simp [singleSet, ← h1, hev.1]
          exact hnotS e.2 hs
      · exact Or.inr (Finset.mem_inter.mpr ⟨h2l, h2r⟩)
    exact Finset.mem_filter.mpr ⟨he, hmemM, hev.1, hnotS e.1, hnotS e.2⟩
  · intro e he
    exact (Finset.mem_filter.mp he).2.1
  · have hgolden : (singleSet l).card + (edgesM0 M l).card ≤ l.leaves := by
      apply golden_read2_bound M l
      · intro v; have := hr2 v; simp [MonoFormula.varCount] at this; omega
      · intro m hm
        have hmr : m ∈ r.orVars := (Finset.mem_inter.mp hm).2
        rw [MonoFormula.mem_orVars_iff_varCount_pos] at hmr
        have := hr2 m; simp [MonoFormula.varCount] at this; omega
      · intro u v hm hadj
        have hr1 : r.eval (pairInput u v) = true := by
          rcases hm with hu | hv
          · have hru : r.eval (singleInput u) = true := (Finset.mem_filter.mp (hMr hu)).2
            exact r.eval_mono (singleInput u) (pairInput u v) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hru
          · have hrv : r.eval (singleInput v) = true := (Finset.mem_filter.mp (hMr hv)).2
            exact r.eval_mono (singleInput v) (pairInput u v) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hrv
        cases hluv : l.eval (pairInput u v)
        · rfl
        · exfalso
          have hp := hle (pairInput u v) (by simp [MonoFormula.eval, hluv, hr1])
          rw [petersenFun_pair_iff] at hp
          rw [hadj] at hp; exact absurd hp (by decide)
    have hM_le : M.card ≤ r.leaves :=
      le_trans (Finset.card_le_card Finset.inter_subset_right) r.orVars_card_le
    simp only [MonoFormula.leaves]
    omega

def isCleanOrTree : MonoFormula 10 → Prop
  | .var _ => True
  | .or l r => isCleanOrTree l ∧ isCleanOrTree r
  | .and l r =>
      (l.andDepth = 0 ∧ r.andDepth = 0) ∨
      (singleSet l = ∅ ∧ l.orVars ∩ r.orVars ⊆ singleSet r) ∨
      (singleSet r = ∅ ∧ l.orVars ∩ r.orVars ⊆ singleSet l)

lemma clean_or_tree_bound (F : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, F.varCount v ≤ 2)
    (hclean : isCleanOrTree F)
    (hle : ∀ x : Fin 10 → Bool, F.eval x = true → petersenFun x = true) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, F.eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ F.leaves := by
  induction F with
  | var i =>
    exfalso
    have h1 := hle (singleInput i) (by simp [MonoFormula.eval, singleInput])
    rw [petersenFun_single] at h1; exact absurd h1 (by decide)
  | or l r ihl ihr =>
    obtain ⟨hlc, hrc⟩ := hclean
    obtain ⟨T1, E1, hE1, hcov1, hbd1⟩ := ihl
      (fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega)
      hlc (fun x hx => hle x (by simp [MonoFormula.eval, hx]))
    obtain ⟨T2, E2, hE2, hcov2, hbd2⟩ := ihr
      (fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega)
      hrc (fun x hx => hle x (by simp [MonoFormula.eval, hx]))
    refine ⟨T1 ∪ T2, E1 ∪ E2, ?_, ?_, ?_⟩
    · intro e he hev
      simp only [MonoFormula.eval, Bool.or_eq_true] at hev
      rw [Finset.mem_union]
      rcases hev with hl | hr
      · exact Or.inl (hE1 e he hl)
      · exact Or.inr (hE2 e he hr)
    · intro e he
      rw [Finset.mem_union] at he
      rcases he with h1 | h2
      · rcases hcov1 e h1 with hc | hc
        · exact Or.inl (Finset.mem_union_left _ hc)
        · exact Or.inr (Finset.mem_union_left _ hc)
      · rcases hcov2 e h2 with hc | hc
        · exact Or.inl (Finset.mem_union_right _ hc)
        · exact Or.inr (Finset.mem_union_right _ hc)
    · simp only [MonoFormula.leaves]
      have c1 := Finset.card_union_le E1 E2
      have c2 := Finset.card_union_le T1 T2
      omega
  | and l r _ _ =>
    rcases hclean with ⟨hdl, hdr⟩ | ⟨hSl, hMr⟩ | ⟨hSr, hMl⟩
    · exact sigma3_subformula_bound (l.and r) (by simp [MonoFormula.andDepth, hdl, hdr]) hle
    · exact read2_and_clean_bound l r hr2 hle hSl hMr
    · have hr2' : ∀ v, (r.and l).varCount v ≤ 2 := fun v => by
        have := hr2 v; simp [MonoFormula.varCount] at this ⊢; omega
      have hle' : ∀ x, (r.and l).eval x = true → petersenFun x = true := fun x hx =>
        hle x (by simpa [MonoFormula.eval, Bool.and_comm] using hx)
      have hMl' : r.orVars ∩ l.orVars ⊆ singleSet l := by rwa [Finset.inter_comm]
      obtain ⟨T, E, hE, hcov, hbd⟩ := read2_and_clean_bound r l hr2' hle' hSr hMl'
      refine ⟨T, E, ?_, hcov, ?_⟩
      · intro e he hev
        exact hE e he (by simpa [MonoFormula.eval, Bool.and_comm] using hev)
      · simpa [MonoFormula.leaves, Nat.add_comm] using hbd

theorem petersen_clean_read2_leaves_ge_21 (F : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, F.varCount v ≤ 2)
    (hclean : isCleanOrTree F)
    (hev : ∀ x : Fin 10 → Bool, F.eval x = petersenFun x) :
    21 ≤ F.leaves := by
  obtain ⟨T, E, hE, hcov, hbd⟩ := clean_or_tree_bound F hr2 hclean (fun x hx => by rw [← hev x, hx])
  have hsub : petersenEdges ⊆ E := by
    intro e he
    apply hE e he
    rw [hev, petersenFun_pair_iff]
    exact petersenEdges_adj e he
  have hE15 : 15 ≤ E.card := by
    rw [← petersenEdges_card]; exact Finset.card_le_card hsub
  have hT6 : 6 ≤ T.card := petersen_tau_ge_6 T (fun e he => hcov e (hsub he))
  omega

theorem petersen_19_dichotomy_v4 (h : HasCircuitSize 10 petersenFun 19) :
    (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧
      wireFanOut 10 C 0 = 1) ∨
    (∃ l r : MonoFormula 10,
      (∀ x : Fin 10 → Bool, (l.or r).eval x = petersenFun x) ∧
      (l.or r).leaves = 20 ∧
      (∀ v : Fin 10, (l.or r).varCount v = 2) ∧
      2 ≤ (l.or r).andDepth ∧
      ¬ isCleanOrTree (l.or r)) := by
  rcases petersen_19_dichotomy_v3 h with h1 | ⟨l, r, hev, hleaves, hcnt, hdepth⟩
  · exact Or.inl h1
  · right
    refine ⟨l, r, hev, hleaves, hcnt, hdepth, ?_⟩
    intro hclean
    have h21 := petersen_clean_read2_leaves_ge_21 (l.or r) (fun v => by rw [hcnt v]) hclean hev
    omega

lemma bipartite_edges_add_tau_le_two_card (M : Finset (Fin 10))
    (col : Fin 10 → Bool)
    (hcol : ∀ u ∈ M, ∀ v ∈ M, petersenAdj u v = true → col u ≠ col v) :
    ∃ T : Finset (Fin 10),
      (∀ e ∈ petersenEdges, e.1 ∈ M → e.2 ∈ M → e.1 ∈ T ∨ e.2 ∈ T) ∧
      (petersenEdges.filter fun e => e.1 ∈ M ∧ e.2 ∈ M).card + T.card ≤ 2 * M.card := by
  let M0 := M.filter fun v => col v = false
  let M1 := M.filter fun v => col v = true
  have hpart : M0.card + M1.card = M.card := by
    have hd : Disjoint M0 M1 := by
      rw [Finset.disjoint_left]; intro v h0 h1
      simp only [M0, M1, Finset.mem_filter] at h0 h1
      rw [h0.2] at h1; exact absurd h1.2 (by decide)
    have hu : M0 ∪ M1 = M := by
      ext v; simp only [M0, M1, Finset.mem_union, Finset.mem_filter]
      cases hcv : col v <;> simp
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hdisj : Disjoint M0 M1 := by
    rw [Finset.disjoint_left]; intro v h0 h1
    simp only [M0, M1, Finset.mem_filter] at h0 h1
    rw [h0.2] at h1; exact absurd h1.2 (by decide)
  have hE_sub : (petersenEdges.filter fun e => e.1 ∈ M ∧ e.2 ∈ M) ⊆ bipEdges M0 M1 := by
    intro e he
    simp only [Finset.mem_filter] at he
    have hadj := petersenEdges_adj e he.1
    have hne := hcol e.1 he.2.1 e.2 he.2.2 hadj
    simp only [bipEdges, Finset.mem_filter, M0, M1]
    refine ⟨he.1, ?_⟩
    cases h1 : col e.1 <;> cases h2 : col e.2 <;> simp_all
  have hE_le : (petersenEdges.filter fun e => e.1 ∈ M ∧ e.2 ∈ M).card ≤ (bipEdges M0 M1).card :=
    Finset.card_le_card hE_sub
  have h30 := bipEdges_le_three_left M0 M1 hdisj
  have h31 : (bipEdges M0 M1).card ≤ 3 * M1.card := by
    rw [bipEdges_comm]; exact bipEdges_le_three_left M1 M0 hdisj.symm
  by_cases h01 : M0.card ≤ M1.card
  · refine ⟨M0, ?_, by omega⟩
    intro e he h1 h2
    have hmem := hE_sub (Finset.mem_filter.mpr ⟨he, h1, h2⟩)
    simp only [bipEdges, Finset.mem_filter] at hmem
    rcases hmem.2 with ⟨ha, _⟩ | ⟨_, hb⟩
    · exact Or.inl ha
    · exact Or.inr hb
  · refine ⟨M1, ?_, by omega⟩
    intro e he h1 h2
    have hmem := hE_sub (Finset.mem_filter.mpr ⟨he, h1, h2⟩)
    simp only [bipEdges, Finset.mem_filter] at hmem
    rcases hmem.2 with ⟨_, hb⟩ | ⟨ha, _⟩
    · exact Or.inr hb
    · exact Or.inl ha

theorem read2_and_m0_empty_bound (l r : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, (l.and r).varCount v ≤ 2)
    (hSl : singleSet l = ∅)
    (hM0 : l.orVars ∩ r.orVars ∩ singleSet r = ∅) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, (l.and r).eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ (l.and r).leaves := by
  let M := l.orVars ∩ r.orVars
  have hnotSl : ∀ v : Fin 10, v ∉ singleSet l := by rw [hSl]; simp
  have hnotSrM : ∀ v ∈ M, v ∉ singleSet r := by
    intro v hv hvr
    have : v ∈ M ∩ singleSet r := Finset.mem_inter.mpr ⟨hv, hvr⟩
    rw [hM0] at this; simp at this
  have hmemM_of_eval : ∀ e ∈ petersenEdges, (l.and r).eval (pairInput e.1 e.2) = true →
      e.1 ∈ M ∧ e.2 ∈ M := by
    intro e he hev
    simp only [MonoFormula.eval, Bool.and_eq_true] at hev
    have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
    have h1l : e.1 ∈ l.orVars := by
      by_contra h
      have h0 := eval_pair_of_not_mem l e.1 e.2 h
      change l.eval (pairInput e.1 e.2) = l.eval (singleInput e.2) at h0
      exact hnotSl e.2 (by simp [singleSet, ← h0, hev.1])
    have h2l : e.2 ∈ l.orVars := by
      by_contra h
      have h0 := eval_pair_of_not_mem l e.2 e.1 h
      change l.eval (pairInput e.2 e.1) = l.eval (singleInput e.1) at h0
      rw [← hsym] at h0
      exact hnotSl e.1 (by simp [singleSet, ← h0, hev.1])
    have h1r : e.1 ∈ r.orVars := by
      by_contra h
      have h0 := eval_pair_of_not_mem r e.1 e.2 h
      change r.eval (pairInput e.1 e.2) = r.eval (singleInput e.2) at h0
      have h2r : e.2 ∈ r.orVars := singleSet_subset_orVars r (by simp [singleSet, ← h0, hev.2])
      exact hnotSrM e.2 (Finset.mem_inter.mpr ⟨h2l, h2r⟩) (by simp [singleSet, ← h0, hev.2])
    have h2r : e.2 ∈ r.orVars := by
      by_contra h
      have h0 := eval_pair_of_not_mem r e.2 e.1 h
      change r.eval (pairInput e.2 e.1) = r.eval (singleInput e.1) at h0
      rw [← hsym] at h0
      exact hnotSrM e.1 (Finset.mem_inter.mpr ⟨h1l, h1r⟩) (by simp [singleSet, ← h0, hev.2])
    exact ⟨Finset.mem_inter.mpr ⟨h1l, h1r⟩, Finset.mem_inter.mpr ⟨h2l, h2r⟩⟩
  let E := petersenEdges.filter fun e => (l.and r).eval (pairInput e.1 e.2) = true
  by_cases hEne : E.Nonempty
  · cases hrM : r.restrictFalse M with
    | none =>
      exfalso
      obtain ⟨e, he⟩ := hEne
      simp only [E, Finset.mem_filter] at he
      have hm := hmemM_of_eval e he.1 he.2
      have h0 := r.restrictFalse_eval M (pairInput e.1 e.2)
      rw [hrM] at h0; simp only [Option.elim_none] at h0
      have hfeq : (fun i => if i ∈ M then pairInput e.1 e.2 i else false) = pairInput e.1 e.2 := by
        funext i; unfold pairInput; split_ifs with hi
        · rfl
        · simp only [Bool.false_eq, decide_eq_false_iff_not, not_or]
          exact ⟨fun h => hi (h ▸ hm.1), fun h => hi (h ▸ hm.2)⟩
      rw [hfeq] at h0
      simp only [MonoFormula.eval, Bool.and_eq_true] at he
      rw [← h0] at he; exact absurd he.2.2 (by decide)
    | some G =>
      have hGro : ∀ v : Fin 10, G.varCount v ≤ 1 := by
        intro v
        by_cases hvM : v ∈ M
        · have hvl : v ∈ l.orVars := (Finset.mem_inter.mp hvM).1
          rw [MonoFormula.mem_orVars_iff_varCount_pos] at hvl
          have h2 := hr2 v; simp [MonoFormula.varCount] at h2
          exact le_trans (r.restrictFalse_varCount_le M G hrM v) (by omega)
        · have hnot : v ∉ G.orVars := fun h => hvM (r.restrictFalse_orVars M G hrM h)
          rw [MonoFormula.mem_orVars_iff_varCount_pos] at hnot; omega
      have hGeval_M : ∀ x : Fin 10 → Bool, (∀ i, x i = true → i ∈ M) → G.eval x = r.eval x := by
        intro x hx
        have h0 := r.restrictFalse_eval M x
        rw [hrM] at h0; simp only [Option.elim_some] at h0; rw [h0]
        congr 1; funext i; split_ifs with hi
        · rfl
        · cases hxi : x i
          · rfl
          · exact absurd (hx i hxi) hi
      have hE_bip : ∃ col : Fin 10 → Bool, ∀ e ∈ E, col e.1 ≠ col e.2 := by
        have hGsing : ∀ v ∈ M, G.eval (singleInput v) = false := by
          intro v hv
          rw [hGeval_M (singleInput v) (fun i hi => by
            simp only [singleInput, decide_eq_true_eq] at hi; exact hi ▸ hv)]
          cases hrv : r.eval (singleInput v)
          · rfl
          · exact absurd (by simp [singleSet, hrv]) (hnotSrM v hv)
        have hGe_bip : ∀ (F' : MonoFormula 10) (E' : Finset (Fin 10 × Fin 10)),
            (∀ v, F'.varCount v ≤ 1) →
            (∀ e ∈ E', F'.eval (singleInput e.1) = false ∧ F'.eval (singleInput e.2) = false) →
            (∀ e ∈ E', F'.eval (pairInput e.1 e.2) = true) →
            ∃ col : Fin 10 → Bool, ∀ e ∈ E', col e.1 ≠ col e.2 := by
          intro F'
          induction F' with
          | var i =>
            intro E' _ hs he
            refine ⟨fun _ => false, fun e heE => ?_⟩
            have h1 := he e heE
            simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at h1
            rcases h1 with h | h
            · have := (hs e heE).1; rw [← h] at this; simp [MonoFormula.eval, singleInput] at this
            · have := (hs e heE).2; rw [← h] at this; simp [MonoFormula.eval, singleInput] at this
          | and a b _ _ =>
            intro E' hro _ he
            have hdisj : ∀ v, ¬ (v ∈ a.orVars ∧ v ∈ b.orVars) := by
              intro v ⟨ha, hb⟩
              rw [MonoFormula.mem_orVars_iff_varCount_pos] at ha hb
              have := hro v; simp [MonoFormula.varCount] at this; omega
            refine ⟨fun v => decide (v ∈ a.orVars), fun e heE => ?_⟩
            have h1 := he e heE; simp only [MonoFormula.eval, Bool.and_eq_true] at h1
            have ha : e.1 ∈ a.orVars ∨ e.2 ∈ a.orVars := by
              by_contra h; push Not at h
              have hf := eval_pair_of_not_mem_both a e.1 e.2 h.1 h.2
              change a.eval (pairInput e.1 e.2) = false at hf; rw [hf] at h1; exact absurd h1.1 (by decide)
            have hb : e.1 ∈ b.orVars ∨ e.2 ∈ b.orVars := by
              by_contra h; push Not at h
              have hf := eval_pair_of_not_mem_both b e.1 e.2 h.1 h.2
              change b.eval (pairInput e.1 e.2) = false at hf; rw [hf] at h1; exact absurd h1.2 (by decide)
            rcases ha with h1a | h2a <;> rcases hb with h1b | h2b
            · exact absurd ⟨h1a, h1b⟩ (hdisj e.1)
            · have hn2 : e.2 ∉ a.orVars := fun h => hdisj e.2 ⟨h, h2b⟩
              simp [h1a, hn2]
            · have hn1 : e.1 ∉ a.orVars := fun h => hdisj e.1 ⟨h, h1b⟩
              simp [hn1, h2a]
            · exact absurd ⟨h2a, h2b⟩ (hdisj e.2)
          | or a b iha ihb =>
            intro E' hro hs he
            have hroa : ∀ v, a.varCount v ≤ 1 := fun v => by have := hro v; simp [MonoFormula.varCount] at this; omega
            have hrob : ∀ v, b.varCount v ≤ 1 := fun v => by have := hro v; simp [MonoFormula.varCount] at this; omega
            have hdisj : ∀ v, ¬ (v ∈ a.orVars ∧ v ∈ b.orVars) := by
              intro v ⟨ha, hb⟩
              rw [MonoFormula.mem_orVars_iff_varCount_pos] at ha hb
              have := hro v; simp [MonoFormula.varCount] at this; omega
            have hsplit : ∀ e ∈ E',
                (e.1 ∈ a.orVars ∧ e.2 ∈ a.orVars ∧ a.eval (pairInput e.1 e.2) = true) ∨
                (e.1 ∈ b.orVars ∧ e.2 ∈ b.orVars ∧ b.eval (pairInput e.1 e.2) = true) := by
              intro e heE
              have h1 := he e heE; simp only [MonoFormula.eval, Bool.or_eq_true] at h1
              have hs1 := (hs e heE).1; have hs2 := (hs e heE).2
              simp only [MonoFormula.eval, Bool.or_eq_false_iff] at hs1 hs2
              have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
              rcases h1 with ha | hb
              · left
                have h1a : e.1 ∈ a.orVars := by
                  by_contra hn
                  have h0 := eval_pair_of_not_mem a e.1 e.2 hn
                  change a.eval (pairInput e.1 e.2) = a.eval (singleInput e.2) at h0
                  rw [h0, hs2.1] at ha; exact absurd ha (by decide)
                have h2a : e.2 ∈ a.orVars := by
                  by_contra hn; rw [hsym] at ha
                  have h0 := eval_pair_of_not_mem a e.2 e.1 hn
                  change a.eval (pairInput e.2 e.1) = a.eval (singleInput e.1) at h0
                  rw [h0, hs1.1] at ha; exact absurd ha (by decide)
                exact ⟨h1a, h2a, ha⟩
              · right
                have h1b : e.1 ∈ b.orVars := by
                  by_contra hn
                  have h0 := eval_pair_of_not_mem b e.1 e.2 hn
                  change b.eval (pairInput e.1 e.2) = b.eval (singleInput e.2) at h0
                  rw [h0, hs2.2] at hb; exact absurd hb (by decide)
                have h2b : e.2 ∈ b.orVars := by
                  by_contra hn; rw [hsym] at hb
                  have h0 := eval_pair_of_not_mem b e.2 e.1 hn
                  change b.eval (pairInput e.2 e.1) = b.eval (singleInput e.1) at h0
                  rw [h0, hs1.2] at hb; exact absurd hb (by decide)
                exact ⟨h1b, h2b, hb⟩
            let Ea := E'.filter fun e => e.1 ∈ a.orVars ∧ e.2 ∈ a.orVars
            let Eb := E'.filter fun e => e.1 ∈ b.orVars ∧ e.2 ∈ b.orVars
            obtain ⟨ca, hca⟩ := iha Ea hroa
              (fun e heE => by
                have hm := (Finset.mem_filter.mp heE).1
                have hs1 := (hs e hm).1; have hs2 := (hs e hm).2
                simp only [MonoFormula.eval, Bool.or_eq_false_iff] at hs1 hs2
                exact ⟨hs1.1, hs2.1⟩)
              (fun e heE => by
                have hf := Finset.mem_filter.mp heE
                rcases hsplit e hf.1 with ⟨_, _, ha⟩ | ⟨h1b, _, _⟩
                · exact ha
                · exact absurd ⟨hf.2.1, h1b⟩ (hdisj e.1))
            obtain ⟨cb, hcb⟩ := ihb Eb hrob
              (fun e heE => by
                have hm := (Finset.mem_filter.mp heE).1
                have hs1 := (hs e hm).1; have hs2 := (hs e hm).2
                simp only [MonoFormula.eval, Bool.or_eq_false_iff] at hs1 hs2
                exact ⟨hs1.2, hs2.2⟩)
              (fun e heE => by
                have hf := Finset.mem_filter.mp heE
                rcases hsplit e hf.1 with ⟨h1a, _, _⟩ | ⟨_, _, hb⟩
                · exact absurd ⟨h1a, hf.2.1⟩ (hdisj e.1)
                · exact hb)
            refine ⟨fun v => if v ∈ a.orVars then ca v else cb v, fun e heE => ?_⟩
            rcases hsplit e heE with ⟨h1a, h2a, _⟩ | ⟨h1b, h2b, _⟩
            · simp only [h1a, h2a, ↓reduceIte]
              exact hca e (Finset.mem_filter.mpr ⟨heE, h1a, h2a⟩)
            · have hn1 : e.1 ∉ a.orVars := fun h => hdisj e.1 ⟨h, h1b⟩
              have hn2 : e.2 ∉ a.orVars := fun h => hdisj e.2 ⟨h, h2b⟩
              simp only [hn1, hn2, ↓reduceIte]
              exact hcb e (Finset.mem_filter.mpr ⟨heE, h1b, h2b⟩)
        exact hGe_bip G E hGro
          (fun e heE => by
            have hf := Finset.mem_filter.mp heE
            have hm := hmemM_of_eval e hf.1 hf.2
            exact ⟨hGsing e.1 hm.1, hGsing e.2 hm.2⟩)
          (fun e heE => by
            have hf := Finset.mem_filter.mp heE
            have hm := hmemM_of_eval e hf.1 hf.2
            rw [hGeval_M (pairInput e.1 e.2) (fun i hi => by
              simp only [pairInput, decide_eq_true_eq] at hi; rcases hi with rfl | rfl <;> [exact hm.1; exact hm.2])]
            simp only [MonoFormula.eval, Bool.and_eq_true] at hf; exact hf.2.2)
      obtain ⟨col, hcol⟩ := hE_bip
      let M0 := M.filter fun v => col v = false
      let M1 := M.filter fun v => col v = true
      have hdisj : Disjoint M0 M1 := by
        rw [Finset.disjoint_left]; intro v h0 h1
        simp only [M0, M1, Finset.mem_filter] at h0 h1
        rw [h0.2] at h1; exact absurd h1.2 (by decide)
      have hpart : M0.card + M1.card = M.card := by
        have hu : M0 ∪ M1 = M := by
          ext v; simp only [M0, M1, Finset.mem_union, Finset.mem_filter]
          cases hcv : col v <;> simp
        rw [← Finset.card_union_of_disjoint hdisj, hu]
      have hE_sub : E ⊆ bipEdges M0 M1 := by
        intro e he
        have hf := Finset.mem_filter.mp he
        have hm := hmemM_of_eval e hf.1 hf.2
        have hne := hcol e he
        simp only [bipEdges, Finset.mem_filter, M0, M1]
        refine ⟨hf.1, ?_⟩
        cases h1 : col e.1 <;> cases h2 : col e.2 <;> simp_all
      have hE_le := Finset.card_le_card hE_sub
      have h30 := bipEdges_le_three_left M0 M1 hdisj
      have h31 : (bipEdges M0 M1).card ≤ 3 * M1.card := by
        rw [bipEdges_comm]; exact bipEdges_le_three_left M1 M0 hdisj.symm
      have hMl : M.card ≤ l.leaves := le_trans (Finset.card_le_card Finset.inter_subset_left) l.orVars_card_le
      have hMr : M.card ≤ r.leaves := le_trans (Finset.card_le_card Finset.inter_subset_right) r.orVars_card_le
      by_cases h01 : M0.card ≤ M1.card
      · refine ⟨M0, E, fun e he hev => Finset.mem_filter.mpr ⟨he, hev⟩, ?_, by simp only [MonoFormula.leaves]; omega⟩
        intro e he
        have hm := hE_sub he; simp only [bipEdges, Finset.mem_filter] at hm
        rcases hm.2 with ⟨ha, _⟩ | ⟨_, hb⟩
        · exact Or.inl ha
        · exact Or.inr hb
      · refine ⟨M1, E, fun e he hev => Finset.mem_filter.mpr ⟨he, hev⟩, ?_, by simp only [MonoFormula.leaves]; omega⟩
        intro e he
        have hm := hE_sub he; simp only [bipEdges, Finset.mem_filter] at hm
        rcases hm.2 with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact Or.inr hb
        · exact Or.inl ha
  · rw [Finset.not_nonempty_iff_eq_empty] at hEne
    refine ⟨∅, ∅, ?_, by simp, by simp⟩
    intro e he hev
    have : e ∈ E := Finset.mem_filter.mpr ⟨he, hev⟩
    rw [hEne] at this; simp at this

def edgesM0NoC (c : Fin 10) (M0 : Finset (Fin 10)) (L : MonoFormula 10) : Finset (Fin 10 × Fin 10) :=
  (edgesM0 M0 L).filter fun e => e.1 ≠ c ∧ e.2 ≠ c

def bipEdgesNoC (c : Fin 10) (A B : Finset (Fin 10)) : Finset (Fin 10 × Fin 10) :=
  (bipEdges A B).filter fun e => e.1 ≠ c ∧ e.2 ≠ c

lemma petersen_common_nbr_le_1 :
    ∀ u v : Fin 10, u ≠ v →
      (Finset.univ.filter fun w : Fin 10 => petersenAdj u w = true ∧ petersenAdj v w = true).card ≤ 1 := by
  decide

lemma bipEdgesNoC_nc_le_right (c : Fin 10) (A1 B : Finset (Fin 10))
    (hA1 : ∀ u ∈ A1, petersenAdj c u = true)
    (hdisj : Disjoint A1 B) :
    (bipEdgesNoC c A1 B).card ≤ B.card := by
  have hsub : bipEdgesNoC c A1 B ⊆ B.biUnion fun b =>
      if b = c then ∅ else
      (Finset.univ.filter fun a : Fin 10 => petersenAdj c a = true ∧ petersenAdj b a = true).image
        (fun a => if a < b then (a, b) else (b, a)) := by
    intro e he
    simp only [bipEdgesNoC, bipEdges, Finset.mem_filter] at he
    have hlt := petersenEdges_lt e he.1.1
    have hadj := petersenEdges_adj e he.1.1
    simp only [Finset.mem_biUnion]
    rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨e.2, h2, ?_⟩
      simp only [he.2.2, ↓reduceIte, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e.1, ⟨hA1 e.1 h1, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hlt]⟩
    · refine ⟨e.1, h1, ?_⟩
      simp only [he.2.1, ↓reduceIte, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact ⟨e.2, ⟨hA1 e.2 h2, hadj⟩, by simp [hnot]⟩
  calc (bipEdgesNoC c A1 B).card
      ≤ (B.biUnion fun b => if b = c then ∅ else
          (Finset.univ.filter fun a : Fin 10 => petersenAdj c a = true ∧ petersenAdj b a = true).image
            (fun a => if a < b then (a, b) else (b, a))).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ B, (if b = c then (∅ : Finset (Fin 10 × Fin 10)) else
          (Finset.univ.filter fun a : Fin 10 => petersenAdj c a = true ∧ petersenAdj b a = true).image
            (fun a => if a < b then (a, b) else (b, a))).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ B, 1 := by
        apply Finset.sum_le_sum; intro b _
        split_ifs with hbc
        · simp
        · exact le_trans Finset.card_image_le (petersen_common_nbr_le_1 c b (Ne.symm hbc))
    _ = B.card := by simp

lemma bipEdgesNoC_nc_le_two_left (c : Fin 10) (A1 B : Finset (Fin 10))
    (hA1 : ∀ u ∈ A1, petersenAdj c u = true)
    (hdisj : Disjoint A1 B) :
    (bipEdgesNoC c A1 B).card ≤ 2 * A1.card := by
  have hsub : bipEdgesNoC c A1 B ⊆ A1.biUnion fun a =>
      ((Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).erase c).image
        (fun b => if a < b then (a, b) else (b, a)) := by
    intro e he
    simp only [bipEdgesNoC, bipEdges, Finset.mem_filter] at he
    have hlt := petersenEdges_lt e he.1.1
    have hadj := petersenEdges_adj e he.1.1
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rcases he.1.2 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨e.1, h1, e.2, ⟨he.2.2, hadj⟩, by simp [hlt]⟩
    · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact ⟨e.2, h2, e.1, ⟨he.2.1, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
  calc (bipEdgesNoC c A1 B).card
      ≤ (A1.biUnion fun a =>
          ((Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).erase c).image
            (fun b => if a < b then (a, b) else (b, a))).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A1, (((Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).erase c).image
          (fun b => if a < b then (a, b) else (b, a))).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A1, 2 := by
        apply Finset.sum_le_sum; intro a ha
        have hcN : c ∈ Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true := by
          simp [petersenAdj_symm c a (hA1 a ha)]
        calc (((Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).erase c).image _).card
            ≤ ((Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).erase c).card := Finset.card_image_le
          _ = (Finset.univ.filter fun b : Fin 10 => petersenAdj a b = true).card - 1 := Finset.card_erase_of_mem hcN
          _ ≤ 2 := by have := petersen_deg_le_3 a; omega
    _ = 2 * A1.card := by simp [mul_comm]

lemma bipEdges_c4free_card2 (A2 B : Finset (Fin 10)) (hdisj : Disjoint A2 B) (h2 : A2.card = 2) :
    (bipEdges A2 B).card ≤ B.card + 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
  let Na := B.filter fun w => petersenAdj a w = true
  let Nb := B.filter fun w => petersenAdj b w = true
  have hsub : bipEdges {a, b} B ⊆ (Na.image fun w => if a < w then (a, w) else (w, a)) ∪
      (Nb.image fun w => if b < w then (b, w) else (w, b)) := by
    intro e he
    simp only [bipEdges, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at he
    have hlt := petersenEdges_lt e he.1
    have hadj := petersenEdges_adj e he.1
    rw [Finset.mem_union]
    rcases he.2 with ⟨rfl | rfl, hw⟩ | ⟨hw, rfl | rfl⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨hw, hadj⟩, by simp [hlt]⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨hw, hadj⟩, by simp [hlt]⟩)
    · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact Or.inl (Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨hw, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩)
    · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact Or.inr (Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨hw, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩)
  have hinter : (Na ∩ Nb).card ≤ 1 := by
    have hsubi : Na ∩ Nb ⊆ Finset.univ.filter fun w => petersenAdj a w = true ∧ petersenAdj b w = true := by
      intro w hw; simp only [Na, Nb, Finset.mem_inter, Finset.mem_filter] at hw
      simp [hw.1.2, hw.2.2]
    exact le_trans (Finset.card_le_card hsubi) (petersen_common_nbr_le_1 a b hab)
  have hunion : (Na ∪ Nb).card ≤ B.card := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hsum := Finset.card_union_add_card_inter Na Nb
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Na.image fun w => if a < w then (a, w) else (w, a))
    (Nb.image fun w => if b < w then (b, w) else (w, b))
  have h3 : (Na.image fun w => if a < w then (a, w) else (w, a)).card ≤ Na.card := Finset.card_image_le
  have h4 : (Nb.image fun w => if b < w then (b, w) else (w, b)).card ≤ Nb.card := Finset.card_image_le
  omega

lemma bipEdges_c4free_card3 (A2 B : Finset (Fin 10)) (hdisj : Disjoint A2 B) (h3 : A2.card = 3) :
    (bipEdges A2 B).card ≤ B.card + 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
  let Na := B.filter fun w => petersenAdj a w = true
  let Nb := B.filter fun w => petersenAdj b w = true
  let Nc := B.filter fun w => petersenAdj c w = true
  have hsub : bipEdges {a, b, c} B ⊆
      (Na.image fun w => if a < w then (a, w) else (w, a)) ∪
      (Nb.image fun w => if b < w then (b, w) else (w, b)) ∪
      (Nc.image fun w => if c < w then (c, w) else (w, c)) := by
    intro e he
    simp only [bipEdges, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at he
    have hlt := petersenEdges_lt e he.1
    have hadj := petersenEdges_adj e he.1
    simp only [Finset.mem_union]
    rcases he.2 with ⟨rfl | rfl | rfl, hw⟩ | ⟨hw, rfl | rfl | rfl⟩
    · exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨hw, hadj⟩, by simp [hlt]⟩))
    · exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨hw, hadj⟩, by simp [hlt]⟩))
    · exact Or.inr (Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨hw, hadj⟩, by simp [hlt]⟩)
    · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨hw, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩))
    · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨hw, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩))
    · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
      exact Or.inr (Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨hw, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩)
  have hint : ∀ x y : Fin 10, x ≠ y →
      ((B.filter fun w => petersenAdj x w = true) ∩ (B.filter fun w => petersenAdj y w = true)).card ≤ 1 := by
    intro x y hxy
    have hs : (B.filter fun w => petersenAdj x w = true) ∩ (B.filter fun w => petersenAdj y w = true) ⊆
        Finset.univ.filter fun w => petersenAdj x w = true ∧ petersenAdj y w = true := by
      intro w hw; simp only [Finset.mem_inter, Finset.mem_filter] at hw; simp [hw.1.2, hw.2.2]
    exact le_trans (Finset.card_le_card hs) (petersen_common_nbr_le_1 x y hxy)
  have hab_i : (Na ∩ Nb).card ≤ 1 := hint a b hab
  have hac_i : (Na ∩ Nc).card ≤ 1 := hint a c hac
  have hbc_i : (Nb ∩ Nc).card ≤ 1 := hint b c hbc
  have h12 := Finset.card_union_add_card_inter Na Nb
  have h123 := Finset.card_union_add_card_inter (Na ∪ Nb) Nc
  have hint123 : ((Na ∪ Nb) ∩ Nc).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    exact le_trans (Finset.card_union_le _ _) (by omega)
  have hun : (Na ∪ Nb ∪ Nc).card ≤ B.card :=
    Finset.card_le_card (Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) (Finset.filter_subset _ _))
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le ((Na.image fun w => if a < w then (a, w) else (w, a)) ∪ (Nb.image fun w => if b < w then (b, w) else (w, b)))
    (Nc.image fun w => if c < w then (c, w) else (w, c))
  have hc3 := Finset.card_union_le (Na.image fun w => if a < w then (a, w) else (w, a))
    (Nb.image fun w => if b < w then (b, w) else (w, b))
  have hi1 : (Na.image fun w => if a < w then (a, w) else (w, a)).card ≤ Na.card := Finset.card_image_le
  have hi2 : (Nb.image fun w => if b < w then (b, w) else (w, b)).card ≤ Nb.card := Finset.card_image_le
  have hi3 : (Nc.image fun w => if c < w then (c, w) else (w, c)).card ≤ Nc.card := Finset.card_image_le
  omega

lemma bipEdgesNoC_add_nc_le (c : Fin 10) (A B : Finset (Fin 10))
    (hcA : c ∉ A) (hdisj : Disjoint A B) :
    (bipEdgesNoC c A B).card + (A.filter fun u => petersenAdj c u = true).card ≤ A.card + 2 * B.card := by
  let A1 := A.filter fun u => petersenAdj c u = true
  let A2 := A.filter fun u => petersenAdj c u = false
  change (bipEdgesNoC c A B).card + A1.card ≤ A.card + 2 * B.card
  have hA_part : A1.card + A2.card = A.card := by
    have hd : Disjoint A1 A2 := by
      rw [Finset.disjoint_left]; intro u h1 h2
      simp only [A1, A2, Finset.mem_filter] at h1 h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)
    have hu : A1 ∪ A2 = A := by
      ext u; simp only [A1, A2, Finset.mem_union, Finset.mem_filter]
      cases hcu : petersenAdj c u <;> simp
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hsub : bipEdgesNoC c A B ⊆ bipEdgesNoC c A1 B ∪ bipEdgesNoC c A2 B := by
    intro e he
    simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_union, A1, A2] at he ⊢
    rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · cases hcu : petersenAdj c e.1
      · exact Or.inr ⟨⟨he.1.1, Or.inl ⟨⟨h1, rfl⟩, h2⟩⟩, he.2⟩
      · exact Or.inl ⟨⟨he.1.1, Or.inl ⟨⟨h1, rfl⟩, h2⟩⟩, he.2⟩
    · cases hcu : petersenAdj c e.2
      · exact Or.inr ⟨⟨he.1.1, Or.inr ⟨h1, ⟨h2, rfl⟩⟩⟩, he.2⟩
      · exact Or.inl ⟨⟨he.1.1, Or.inr ⟨h1, ⟨h2, rfl⟩⟩⟩, he.2⟩
  have hdisj1 : Disjoint A1 B := Disjoint.mono_left (Finset.filter_subset _ _) hdisj
  have hdisj2 : Disjoint A2 B := Disjoint.mono_left (Finset.filter_subset _ _) hdisj
  have he1_B := bipEdgesNoC_nc_le_right c A1 B (fun u hu => (Finset.mem_filter.mp hu).2) hdisj1
  have he1_2A1 := bipEdgesNoC_nc_le_two_left c A1 B (fun u hu => (Finset.mem_filter.mp hu).2) hdisj1
  have he2_sub : (bipEdgesNoC c A2 B).card ≤ (bipEdges A2 B).card := Finset.card_le_card (Finset.filter_subset _ _)
  have he2_3A2 := le_trans he2_sub (bipEdges_le_three_left A2 B hdisj2)
  have he_3B : (bipEdgesNoC c A B).card ≤ 3 * B.card :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by rw [bipEdges_comm]; exact bipEdges_le_three_left B A hdisj.symm)
  have hsplit : (bipEdgesNoC c A B).card ≤ (bipEdgesNoC c A1 B).card + (bipEdgesNoC c A2 B).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have htot10 : A.card + B.card ≤ 10 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact le_trans (Finset.card_le_univ _) (by simp)
  by_cases h0 : A2.card = 0
  · have hA2e : A2 = ∅ := Finset.card_eq_zero.mp h0
    have he20 : (bipEdgesNoC c A2 B).card = 0 := by
      have : bipEdgesNoC c A2 B = ∅ := by rw [hA2e]; ext e; simp [bipEdgesNoC, bipEdges]
      rw [this]; simp
    omega
  · by_cases h1 : A2.card = 1
    · have he2_B := le_trans he2_sub (bipEdges_le_right_of_card_le_one A2 B (by omega))
      omega
    · by_cases h2 : A2.card = 2
      · have he2_B1 := le_trans he2_sub (bipEdges_c4free_card2 A2 B hdisj2 h2)
        omega
      · by_cases h3 : A2.card = 3
        · have he2_B3 := le_trans he2_sub (bipEdges_c4free_card3 A2 B hdisj2 h3)
          omega
        · by_cases hB4 : B.card ≤ 4
          · omega
          · omega

lemma petersenAut_adj : ∀ (c u v : Fin 10),
    petersenAdj (petersenAut c u) (petersenAut c v) = petersenAdj u v := by
  decide

lemma petersen_y2_b3_zero :
    ∀ (x1 x2 w1 w2 w3 a b : Fin 10),
      x1 ≠ 0 → x2 ≠ 0 → petersenAdj 0 x2 = false → petersenAdj x1 x2 = true →
      w1 < w2 → w2 < w3 →
      w1 ≠ x1 → w1 ≠ x2 → w2 ≠ x1 → w2 ≠ x2 → w3 ≠ x1 → w3 ≠ x2 →
      a < b → a ≠ 0 → b ≠ 0 → petersenAdj 0 a = false → petersenAdj 0 b = false →
      a ≠ x1 → a ≠ x2 → a ≠ w1 → a ≠ w2 → a ≠ w3 →
      b ≠ x1 → b ≠ x2 → b ≠ w1 → b ≠ w2 → b ≠ w3 →
      (w1 ≠ 0 ∧ w2 ≠ 0 ∧ w3 ≠ 0 ∧
       (∃ u ∈ ({1, 4, 5} : List (Fin 10)), u ≠ x1 ∧ u ≠ w1 ∧ u ≠ w2 ∧ u ≠ w3 ∧ petersenAdj u w1 = true) ∧
       (∃ u ∈ ({1, 4, 5} : List (Fin 10)), u ≠ x1 ∧ u ≠ w1 ∧ u ≠ w2 ∧ u ≠ w3 ∧ petersenAdj u w2 = true) ∧
       (∃ u ∈ ({1, 4, 5} : List (Fin 10)), u ≠ x1 ∧ u ≠ w1 ∧ u ≠ w2 ∧ u ≠ w3 ∧ petersenAdj u w3 = true) ∧
       (if petersenAdj x2 w1 then 1 else 0) + (if petersenAdj x2 w2 then 1 else 0) + (if petersenAdj x2 w3 then 1 else 0) +
       (if petersenAdj a w1 then 1 else 0) + (if petersenAdj a w2 then 1 else 0) + (if petersenAdj a w3 then 1 else 0) +
       (if petersenAdj b w1 then 1 else 0) + (if petersenAdj b w2 then 1 else 0) + (if petersenAdj b w3 then 1 else 0) = 6) →
      False := by
  intro x1 x2 w1 w2 w3 a b hx10 hx20 h0x2 hx12 hw12 hw23 hw1x1 hw1x2 hw2x1 hw2x2 hw3x1 hw3x2 hab ha0 hb0 h0a h0b hax1 hax2 haw1 haw2 haw3 hbx1 hbx2 hbw1 hbw2 hbw3 hbad
  obtain ⟨hw10, hw20, hw30, ⟨u1, hu1m, hu1x1, hu1w1, hu1w2, hu1w3, hu1adj⟩,
    ⟨u2, hu2m, hu2x1, hu2w1, hu2w2, hu2w3, hu2adj⟩,
    ⟨u3, hu3m, hu3x1, hu3w1, hu3w2, hu3w3, hu3adj⟩, he2eq⟩ := hbad
  have hmem6 : ∀ z : Fin 10, z ≠ 0 → petersenAdj 0 z = false →
      z ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := by
    decide
  have hnotN0 : ∀ u ∈ ({1, 4, 5} : List (Fin 10)), ∀ w : Fin 10, w ≠ 0 → petersenAdj u w = true →
      petersenAdj 0 w = false := by
    decide
  have hw1_6 : w1 ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := hmem6 w1 hw10 (hnotN0 u1 hu1m w1 hw10 hu1adj)
  have hw2_6 : w2 ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := hmem6 w2 hw20 (hnotN0 u2 hu2m w2 hw20 hu2adj)
  have hw3_6 : w3 ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := hmem6 w3 hw30 (hnotN0 u3 hu3m w3 hw30 hu3adj)
  have hx2_6 : x2 ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := hmem6 x2 hx20 h0x2
  have ha_6 : a ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := hmem6 a ha0 h0a
  have hb_6 : b ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := hmem6 b hb0 h0b
  have hpart6 : ({w1, w2, w3, x2, a, b} : Finset (Fin 10)) = {2, 3, 6, 7, 8, 9} := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · have hc : ({w1, w2, w3, x2, a, b} : Finset (Fin 10)).card = 6 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [ne_of_lt hab]
        · simp [Ne.symm hax2, Ne.symm hbx2]
        · simp [hw3x2, Ne.symm haw3, Ne.symm hbw3]
        · simp [ne_of_lt hw23, hw2x2, Ne.symm haw2, Ne.symm hbw2]
        · simp [ne_of_lt hw12, ne_of_lt (lt_trans hw12 hw23), hw1x2, Ne.symm haw1, Ne.symm hbw1]
      rw [hc]; decide
  have hx1_N0 : x1 ∈ ([1, 4, 5] : List (Fin 10)) := by
    have hx12_ne : x1 ≠ x2 := by
      intro h; subst h; rw [petersenAdj_irrefl] at hx12; exact absurd hx12 (by decide)
    have hx1_not6 : x1 ∉ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) := by
      rw [← hpart6]; simp [Ne.symm hw1x1, Ne.symm hw2x1, Ne.symm hw3x1, hx12_ne, Ne.symm hax1, Ne.symm hbx1]
    revert hx10 hx1_not6; generalize x1 = z; revert z; decide
  have hcheck : (([1, 4, 5] : List (Fin 10)).all fun z1 =>
      ([2, 3, 6, 7, 8, 9] : List (Fin 10)).all fun z2 =>
        !petersenAdj z1 z2 ||
        ([2, 3, 6, 7, 8, 9] : List (Fin 10)).all fun v1 =>
          ([2, 3, 6, 7, 8, 9] : List (Fin 10)).all fun v2 =>
            !decide (v1 < v2) ||
            ([2, 3, 6, 7, 8, 9] : List (Fin 10)).all fun v3 =>
              !decide (v2 < v3) ||
              decide (v1 = z2) || decide (v2 = z2) || decide (v3 = z2) ||
              !(([1, 4, 5] : List (Fin 10)).any fun u => u != z1 && petersenAdj u v1) ||
              !(([1, 4, 5] : List (Fin 10)).any fun u => u != z1 && petersenAdj u v2) ||
              !(([1, 4, 5] : List (Fin 10)).any fun u => u != z1 && petersenAdj u v3) ||
              (([2, 3, 6, 7, 8, 9] : List (Fin 10)).map fun y =>
                 if y == v1 || y == v2 || y == v3 then 0
                 else (if petersenAdj y v1 then 1 else 0) + (if petersenAdj y v2 then 1 else 0) + (if petersenAdj y v3 then 1 else 0)).sum != 6) = true := by
    decide
  have hmem_list : ∀ z : Fin 10, z ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)) → z ∈ ([2, 3, 6, 7, 8, 9] : List (Fin 10)) := by
    decide
  have hstep := List.all_eq_true.mp hcheck x1 hx1_N0
  have hstep := List.all_eq_true.mp hstep x2 (hmem_list x2 hx2_6)
  rw [hx12] at hstep; simp only [Bool.not_true, Bool.false_or] at hstep
  have hstep := List.all_eq_true.mp hstep w1 (hmem_list w1 hw1_6)
  have hstep := List.all_eq_true.mp hstep w2 (hmem_list w2 hw2_6)
  rw [decide_eq_true hw12] at hstep; simp only [Bool.not_true, Bool.false_or] at hstep
  have hstep := List.all_eq_true.mp hstep w3 (hmem_list w3 hw3_6)
  rw [decide_eq_true hw23, decide_eq_false hw1x2, decide_eq_false hw2x2, decide_eq_false hw3x2] at hstep
  simp only [Bool.not_true, Bool.false_or] at hstep
  have hu1_any : (([1, 4, 5] : List (Fin 10)).any fun u => u != x1 && petersenAdj u w1) = true :=
    List.any_eq_true.mpr ⟨u1, hu1m, by simp [hu1x1, hu1adj]⟩
  have hu2_any : (([1, 4, 5] : List (Fin 10)).any fun u => u != x1 && petersenAdj u w2) = true :=
    List.any_eq_true.mpr ⟨u2, hu2m, by simp [hu2x1, hu2adj]⟩
  have hu3_any : (([1, 4, 5] : List (Fin 10)).any fun u => u != x1 && petersenAdj u w3) = true :=
    List.any_eq_true.mpr ⟨u3, hu3m, by simp [hu3x1, hu3adj]⟩
  rw [hu1_any, hu2_any, hu3_any] at hstep
  simp only [Bool.not_true, Bool.false_or, bne_iff_ne] at hstep
  apply hstep
  let f : Fin 10 → ℕ := fun y =>
    if y == w1 || y == w2 || y == w3 then 0
    else (if petersenAdj y w1 then 1 else 0) + (if petersenAdj y w2 then 1 else 0) + (if petersenAdj y w3 then 1 else 0)
  have hlist_eq : (([2, 3, 6, 7, 8, 9] : List (Fin 10)).map f).sum =
      ∑ y ∈ ({2, 3, 6, 7, 8, 9} : Finset (Fin 10)), f y := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  change (([2, 3, 6, 7, 8, 9] : List (Fin 10)).map f).sum = 6
  rw [hlist_eq, ← hpart6]
  rw [Finset.sum_insert (by simp [ne_of_lt hw12, ne_of_lt (lt_trans hw12 hw23), hw1x2, Ne.symm haw1, Ne.symm hbw1]),
    Finset.sum_insert (by simp [ne_of_lt hw23, hw2x2, Ne.symm haw2, Ne.symm hbw2]),
    Finset.sum_insert (by simp [hw3x2, Ne.symm haw3, Ne.symm hbw3]),
    Finset.sum_insert (by simp [Ne.symm hax2, Ne.symm hbx2]),
    Finset.sum_insert (by simp [ne_of_lt hab]),
    Finset.sum_singleton]
  have fw1 : f w1 = 0 := by simp [f]
  have fw2 : f w2 = 0 := by simp [f]
  have fw3 : f w3 = 0 := by simp [f]
  have fx2 : f x2 = (if petersenAdj x2 w1 then 1 else 0) + (if petersenAdj x2 w2 then 1 else 0) + (if petersenAdj x2 w3 then 1 else 0) := by
    simp [f, Ne.symm hw1x2, Ne.symm hw2x2, Ne.symm hw3x2]
  have fa : f a = (if petersenAdj a w1 then 1 else 0) + (if petersenAdj a w2 then 1 else 0) + (if petersenAdj a w3 then 1 else 0) := by
    simp [f, haw1, haw2, haw3]
  have fb : f b = (if petersenAdj b w1 then 1 else 0) + (if petersenAdj b w2 then 1 else 0) + (if petersenAdj b w3 then 1 else 0) := by
    simp [f, hbw1, hbw2, hbw3]
  rw [fw1, fw2, fw3, fx2, fa, fb]
  omega

lemma bipEdgesNoC_of_ext (c x1 x2 : Fin 10) (Y2 W2 : Finset (Fin 10))
    (hcY : c ∉ insert x2 Y2)
    (hx1c : x1 ≠ c) (hx2N : petersenAdj c x2 = false) (hx12 : petersenAdj x1 x2 = true)
    (hx2Y : x2 ∉ Y2) (hx1Y : x1 ∉ insert x2 Y2) (hx1W : x1 ∉ W2)
    (hdisj : Disjoint (insert x2 Y2) W2) :
    (bipEdgesNoC c (insert x2 Y2) W2).card + ((insert x2 Y2).filter fun u => petersenAdj c u = true).card ≤
      Y2.card + 2 * W2.card := by
  let B0 := insert x2 Y2
  let B1 := Y2.filter fun u => petersenAdj c u = true
  let Y2n := Y2.filter fun u => petersenAdj c u = false
  let B2 := insert x2 Y2n
  have hB1_eq : B0.filter (fun u => petersenAdj c u = true) = B1 := by
    ext u; simp only [B0, B1, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | h, ha⟩
      · rw [hx2N] at ha; exact absurd ha (by decide)
      · exact ⟨h, ha⟩
    · rintro ⟨h, ha⟩; exact ⟨Or.inr h, ha⟩
  rw [hB1_eq]
  change (bipEdgesNoC c B0 W2).card + B1.card ≤ Y2.card + 2 * W2.card
  change c ∉ B0 at hcY
  change x1 ∉ B0 at hx1Y
  change Disjoint B0 W2 at hdisj
  have hY2_part : B1.card + Y2n.card = Y2.card := by
    have hd : Disjoint B1 Y2n := by
      rw [Finset.disjoint_left]; intro u h1 h2
      simp only [B1, Y2n, Finset.mem_filter] at h1 h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)
    have hu : B1 ∪ Y2n = Y2 := by
      ext u; simp only [B1, Y2n, Finset.mem_union, Finset.mem_filter]
      cases hcu : petersenAdj c u <;> simp
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hx2_not_Y2n : x2 ∉ Y2n := fun h => hx2Y (Finset.mem_filter.mp h).1
  have hB2_card : B2.card = Y2n.card + 1 := by
    rw [Finset.card_insert_of_notMem hx2_not_Y2n]
  have hB0_eq : B0 = B1 ∪ B2 := by
    ext u; simp only [B0, B1, B2, Y2n, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    cases hcu : petersenAdj c u <;> tauto
  have hsub : bipEdgesNoC c B0 W2 ⊆ bipEdgesNoC c B1 W2 ∪ bipEdgesNoC c B2 W2 := by
    intro e he
    simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_union] at he ⊢
    rw [hB0_eq] at he
    simp only [Finset.mem_union] at he
    rcases he.1.2 with ⟨h1 | h1, h2⟩ | ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨⟨he.1.1, Or.inl ⟨h1, h2⟩⟩, he.2⟩
    · exact Or.inr ⟨⟨he.1.1, Or.inl ⟨h1, h2⟩⟩, he.2⟩
    · exact Or.inl ⟨⟨he.1.1, Or.inr ⟨h1, h2⟩⟩, he.2⟩
    · exact Or.inr ⟨⟨he.1.1, Or.inr ⟨h1, h2⟩⟩, he.2⟩
  have hdisj1 : Disjoint B1 W2 := Disjoint.mono_left (by rw [hB0_eq]; exact Finset.subset_union_left) hdisj
  have hdisj2 : Disjoint B2 W2 := Disjoint.mono_left (by rw [hB0_eq]; exact Finset.subset_union_right) hdisj
  have he1_W := bipEdgesNoC_nc_le_right c B1 W2 (fun u hu => (Finset.mem_filter.mp hu).2) hdisj1
  have he1_2B1 := bipEdgesNoC_nc_le_two_left c B1 W2 (fun u hu => (Finset.mem_filter.mp hu).2) hdisj1
  have he2_sub : (bipEdgesNoC c B2 W2).card ≤ (bipEdges B2 W2).card := Finset.card_le_card (Finset.filter_subset _ _)
  have he2_ext := le_trans he2_sub (bipEdges_le_add_two_of_ext x2 x1 Y2n W2 hx2_not_Y2n hx1W (petersenAdj_symm x1 x2 hx12) hdisj2)
  have he_3W : (bipEdgesNoC c B0 W2).card ≤ 3 * W2.card :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by rw [bipEdges_comm]; exact bipEdges_le_three_left W2 B0 hdisj.symm)
  have hsplit : (bipEdgesNoC c B0 W2).card ≤ (bipEdgesNoC c B1 W2).card + (bipEdgesNoC c B2 W2).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have htot9 : B0.card + W2.card ≤ 9 := by
    have hx1_not : x1 ∉ B0 ∪ W2 := by simp [hx1Y, hx1W]
    have hsub9 : B0 ∪ W2 ⊆ Finset.univ.erase x1 := by
      intro z hz; exact Finset.mem_erase.mpr ⟨fun h => hx1_not (h ▸ hz), Finset.mem_univ z⟩
    rw [← Finset.card_union_of_disjoint hdisj]
    exact le_trans (Finset.card_le_card hsub9) (by simp)
  have hB0_card : B0.card = B1.card + Y2n.card + 1 := by
    rw [Finset.card_insert_of_notMem hx2Y]; omega
  have he2_deg : (bipEdgesNoC c B2 W2).card ≤ 3 * Y2n.card + 2 := by
    have hx2_le2 : (bipEdges {x2} W2).card ≤ 2 := by
      let N := Finset.univ.filter fun w : Fin 10 => petersenAdj x2 w = true
      have hx1N : x1 ∈ N := by simp [N, petersenAdj_symm x1 x2 hx12]
      have hs : bipEdges {x2} W2 ⊆ (N.erase x1).image (fun w => if x2 < w then (x2, w) else (w, x2)) := by
        intro e he
        simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
        have hlt := petersenEdges_lt e he.1; have hadj := petersenEdges_adj e he.1
        simp only [Finset.mem_image, Finset.mem_erase, N, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases he.2 with ⟨rfl, hw⟩ | ⟨hw, rfl⟩
        · exact ⟨e.2, ⟨fun h => hx1W (h ▸ hw), hadj⟩, by simp [hlt]⟩
        · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
          exact ⟨e.1, ⟨fun h => hx1W (h ▸ hw), petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
      calc (bipEdges {x2} W2).card
          ≤ ((N.erase x1).image _).card := Finset.card_le_card hs
        _ ≤ (N.erase x1).card := Finset.card_image_le
        _ = N.card - 1 := Finset.card_erase_of_mem hx1N
        _ ≤ 2 := by have hN : N.card ≤ 3 := petersen_deg_le_3 x2; omega
    have hY2n_le : (bipEdges Y2n W2).card ≤ 3 * Y2n.card :=
      bipEdges_le_three_left Y2n W2 (Disjoint.mono_left (Finset.subset_insert x2 Y2n) hdisj2)
    have hsub2 : bipEdges B2 W2 ⊆ bipEdges {x2} W2 ∪ bipEdges Y2n W2 := by
      intro e he; simp only [B2, bipEdges, Finset.mem_filter, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at he ⊢
      rcases he.2 with ⟨h1 | h1, h2⟩ | ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨he.1, Or.inl ⟨h1, h2⟩⟩
      · exact Or.inr ⟨he.1, Or.inl ⟨h1, h2⟩⟩
      · exact Or.inl ⟨he.1, Or.inr ⟨h1, h2⟩⟩
      · exact Or.inr ⟨he.1, Or.inr ⟨h1, h2⟩⟩
    have := le_trans he2_sub (le_trans (Finset.card_le_card hsub2) (Finset.card_union_le _ _))
    omega
  by_cases hy0 : Y2n.card = 0
  · have hB2_1 : B2.card = 1 := by omega
    have he2_W := le_trans he2_sub (bipEdges_le_right_of_card_le_one B2 W2 (by omega))
    omega
  · by_cases hy1 : Y2n.card = 1
    · have hB2_2 : B2.card = 2 := by omega
      have he2_W1 := le_trans he2_sub (bipEdges_c4free_card2 B2 W2 hdisj2 hB2_2)
      omega
    · by_cases hy2 : Y2n.card = 2
      · by_cases hW2 : W2.card ≤ 2
        · omega
        · by_cases hW3 : W2.card = 3
          · by_contra hgt
            have he_ge9 : 9 ≤ (bipEdgesNoC c B0 W2).card := by omega
            have he2_le6 : (bipEdgesNoC c B2 W2).card ≤ 6 := by
              have hx2_le2 : (bipEdges {x2} W2).card ≤ 2 := by
                let N := Finset.univ.filter fun w : Fin 10 => petersenAdj x2 w = true
                have hx1N : x1 ∈ N := by simp [N, petersenAdj_symm x1 x2 hx12]
                have hs : bipEdges {x2} W2 ⊆ (N.erase x1).image (fun w => if x2 < w then (x2, w) else (w, x2)) := by
                  intro e he
                  simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
                  have hlt := petersenEdges_lt e he.1; have hadj := petersenEdges_adj e he.1
                  simp only [Finset.mem_image, Finset.mem_erase, N, Finset.mem_filter, Finset.mem_univ, true_and]
                  rcases he.2 with ⟨rfl, hw⟩ | ⟨hw, rfl⟩
                  · exact ⟨e.2, ⟨fun h => hx1W (h ▸ hw), hadj⟩, by simp [hlt]⟩
                  · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
                    exact ⟨e.1, ⟨fun h => hx1W (h ▸ hw), petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
                calc (bipEdges {x2} W2).card
                    ≤ ((N.erase x1).image _).card := Finset.card_le_card hs
                  _ ≤ (N.erase x1).card := Finset.card_image_le
                  _ = N.card - 1 := Finset.card_erase_of_mem hx1N
                  _ ≤ 2 := by have hN : N.card ≤ 3 := petersen_deg_le_3 x2; omega
              have hY2n_le4 : (bipEdges Y2n W2).card ≤ 4 := by
                have := bipEdges_c4free_card2 Y2n W2 (Disjoint.mono_left (Finset.subset_insert x2 Y2n) hdisj2) hy2
                omega
              have hsub2 : bipEdges B2 W2 ⊆ bipEdges {x2} W2 ∪ bipEdges Y2n W2 := by
                intro e he; simp only [B2, bipEdges, Finset.mem_filter, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at he ⊢
                rcases he.2 with ⟨h1 | h1, h2⟩ | ⟨h1, h2 | h2⟩
                · exact Or.inl ⟨he.1, Or.inl ⟨h1, h2⟩⟩
                · exact Or.inr ⟨he.1, Or.inl ⟨h1, h2⟩⟩
                · exact Or.inl ⟨he.1, Or.inr ⟨h1, h2⟩⟩
                · exact Or.inr ⟨he.1, Or.inr ⟨h1, h2⟩⟩
              have := le_trans he2_sub (le_trans (Finset.card_le_card hsub2) (Finset.card_union_le _ _))
              omega
            have he1_eq3 : (bipEdgesNoC c B1 W2).card = 3 := by omega
            have he2_eq6 : (bipEdgesNoC c B2 W2).card = 6 := by omega
            let σ := petersenAut c
            have hσc : σ c = 0 := petersenAut_apply c
            have hσadj : ∀ u v : Fin 10, petersenAdj (σ u) (σ v) = petersenAdj u v := petersenAut_adj c
            let W2' := W2.image σ
            let Y2n' := Y2n.image σ
            have hW2'card : W2'.card = 3 := by rw [Finset.card_image_of_injective W2 σ.injective, hW3]
            have hY2n'card : Y2n'.card = 2 := by rw [Finset.card_image_of_injective Y2n σ.injective, hy2]
            have hWsort : ∃ w1 w2 w3 : Fin 10, w1 < w2 ∧ w2 < w3 ∧ W2' = {w1, w2, w3} := by
              have hlen : (W2'.sort (· ≤ ·)).length = 3 := by rw [Finset.length_sort, hW2'card]
              match hs : W2'.sort (· ≤ ·), hlen with
              | [w1, w2, w3], _ =>
                have hp := W2'.pairwise_sort (· ≤ ·); have hnd := W2'.sort_nodup (· ≤ ·)
                rw [hs] at hp hnd
                simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
                  forall_eq_or_imp, forall_eq, List.nodup_cons, not_or] at hp hnd
                refine ⟨w1, w2, w3, lt_of_le_of_ne hp.1.1 hnd.1.1, lt_of_le_of_ne hp.2.1 hnd.2.1, ?_⟩
                ext z; rw [← Finset.mem_sort (· ≤ ·), hs]; simp
            have hYsort : ∃ a b : Fin 10, a < b ∧ Y2n' = {a, b} := by
              have hlen : (Y2n'.sort (· ≤ ·)).length = 2 := by rw [Finset.length_sort, hY2n'card]
              match hs : Y2n'.sort (· ≤ ·), hlen with
              | [a, b], _ =>
                have hp := Y2n'.pairwise_sort (· ≤ ·); have hnd := Y2n'.sort_nodup (· ≤ ·)
                rw [hs] at hp hnd
                simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
                  forall_eq, List.nodup_cons] at hp hnd
                refine ⟨a, b, lt_of_le_of_ne hp.1 hnd.1, ?_⟩
                ext z; rw [← Finset.mem_sort (· ≤ ·), hs]; simp
            obtain ⟨w1, w2, w3, hw12, hw23, hW2'eq⟩ := hWsort
            obtain ⟨a, b, hab, hY2n'eq⟩ := hYsort
            have hmemW2' : ∀ z, z ∈ W2' ↔ σ.symm z ∈ W2 := by
              intro z; simp only [W2', Finset.mem_image]; constructor
              · rintro ⟨y, hy, rfl⟩; simpa using hy
              · intro hz; exact ⟨σ.symm z, hz, σ.apply_symm_apply z⟩
            have hmemY2n' : ∀ z, z ∈ Y2n' ↔ σ.symm z ∈ Y2n := by
              intro z; simp only [Y2n', Finset.mem_image]; constructor
              · rintro ⟨y, hy, rfl⟩; simpa using hy
              · intro hz; exact ⟨σ.symm z, hz, σ.apply_symm_apply z⟩
            have hw_in_W2 : ∀ z ∈ ({w1, w2, w3} : Finset (Fin 10)), σ.symm z ∈ W2 :=
              fun z hz => (hmemW2' z).mp (hW2'eq ▸ hz)
            have hab_in_Y2n : ∀ z ∈ ({a, b} : Finset (Fin 10)), σ.symm z ∈ Y2n :=
              fun z hz => (hmemY2n' z).mp (hY2n'eq ▸ hz)
            have hw_ne_0_and_nbr : ∀ z ∈ ({w1, w2, w3} : Finset (Fin 10)),
                z ≠ 0 ∧ ∃ u ∈ ({1, 4, 5} : List (Fin 10)), u ≠ σ x1 ∧ u ≠ w1 ∧ u ≠ w2 ∧ u ≠ w3 ∧ petersenAdj u z = true := by
              intro z hz
              have hzeq : ∀ w ∈ W2, (bipEdgesNoC c B1 {w}).card ≤ 1 := fun w _ =>
                bipEdgesNoC_nc_le_right c B1 {w} (fun u hu => (Finset.mem_filter.mp hu).2)
                  (Disjoint.mono_right (by intro y hy; simp at hy; subst hy; assumption) hdisj1)
              have hsub_w : bipEdgesNoC c B1 W2 ⊆ W2.biUnion fun w => bipEdgesNoC c B1 {w} := by
                intro e he; simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_singleton] at he ⊢
                rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact ⟨e.2, h2, ⟨he.1.1, Or.inl ⟨h1, rfl⟩⟩, he.2⟩
                · exact ⟨e.1, h1, ⟨he.1.1, Or.inr ⟨rfl, h2⟩⟩, he.2⟩
              have hcard_pos : 1 ≤ (bipEdgesNoC c B1 {σ.symm z}).card := by
                by_contra h0
                have hzero : (bipEdgesNoC c B1 {σ.symm z}).card = 0 := by omega
                have hle2 : (bipEdgesNoC c B1 W2).card ≤ 2 := by
                  calc (bipEdgesNoC c B1 W2).card
                      ≤ (W2.biUnion fun w => bipEdgesNoC c B1 {w}).card := Finset.card_le_card hsub_w
                    _ ≤ ∑ w ∈ W2, (bipEdgesNoC c B1 {w}).card := Finset.card_biUnion_le
                    _ = (bipEdgesNoC c B1 {σ.symm z}).card + ∑ w ∈ W2.erase (σ.symm z), (bipEdgesNoC c B1 {w}).card :=
                        (Finset.add_sum_erase W2 _ (hw_in_W2 z hz)).symm
                    _ ≤ 0 + ∑ _w ∈ W2.erase (σ.symm z), 1 := by
                        rw [hzero]; exact Nat.add_le_add_left (Finset.sum_le_sum fun w hw => hzeq w (Finset.mem_of_mem_erase hw)) 0
                    _ = 2 := by rw [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (hw_in_W2 z hz), hW3]
                omega
              obtain ⟨e, he⟩ := Finset.card_pos.mp hcard_pos
              simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
              have hadj := petersenEdges_adj e he.1.1
              have hex_u : ∃ u0 ∈ B1, σ.symm z ≠ c ∧ petersenAdj u0 (σ.symm z) = true := by
                rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact ⟨e.1, h1, h2 ▸ he.2.2, h2 ▸ hadj⟩
                · exact ⟨e.2, h2, h1 ▸ he.2.1, h1 ▸ petersenAdj_symm e.1 e.2 hadj⟩
              obtain ⟨u0, hu0B1, hzc, hu0adj⟩ := hex_u
              have hz0 : z ≠ 0 := by intro h; apply hzc; exact σ.injective (by rw [σ.apply_symm_apply, h, hσc])
              refine ⟨hz0, σ u0, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · have h0u : petersenAdj 0 (σ u0) = true := by
                  rw [← hσc, hσadj]; exact (Finset.mem_filter.mp hu0B1).2
                revert h0u; generalize σ u0 = y; revert y; decide
              · intro h; apply hx1Y; rw [← σ.injective h]; exact Finset.mem_insert_of_mem (Finset.mem_filter.mp hu0B1).1
              · intro h; exact Finset.disjoint_left.mp hdisj1 hu0B1 (by rw [← σ.symm_apply_apply u0, h]; exact hw_in_W2 w1 (by simp))
              · intro h; exact Finset.disjoint_left.mp hdisj1 hu0B1 (by rw [← σ.symm_apply_apply u0, h]; exact hw_in_W2 w2 (by simp))
              · intro h; exact Finset.disjoint_left.mp hdisj1 hu0B1 (by rw [← σ.symm_apply_apply u0, h]; exact hw_in_W2 w3 (by simp))
              · have := hσadj u0 (σ.symm z); rw [σ.apply_symm_apply] at this; rw [this]; exact hu0adj
            have he2_cnt : (if petersenAdj (σ x2) w1 then 1 else 0) + (if petersenAdj (σ x2) w2 then 1 else 0) + (if petersenAdj (σ x2) w3 then 1 else 0) +
                (if petersenAdj a w1 then 1 else 0) + (if petersenAdj a w2 then 1 else 0) + (if petersenAdj a w3 then 1 else 0) +
                (if petersenAdj b w1 then 1 else 0) + (if petersenAdj b w2 then 1 else 0) + (if petersenAdj b w3 then 1 else 0) = 6 := by
              let B2' := B2.image σ
              have hB2'eq : B2' = {σ x2, a, b} := by
                change (insert x2 Y2n).image σ = {σ x2, a, b}
                rw [Finset.image_insert]
                change insert (σ x2) Y2n' = {σ x2, a, b}
                rw [hY2n'eq]
              have h6le : 6 ≤ (if petersenAdj (σ x2) w1 then 1 else 0) + (if petersenAdj (σ x2) w2 then 1 else 0) + (if petersenAdj (σ x2) w3 then 1 else 0) +
                  (if petersenAdj a w1 then 1 else 0) + (if petersenAdj a w2 then 1 else 0) + (if petersenAdj a w3 then 1 else 0) +
                  (if petersenAdj b w1 then 1 else 0) + (if petersenAdj b w2 then 1 else 0) + (if petersenAdj b w3 then 1 else 0) := by
                have hmap : (bipEdgesNoC c B2 W2).card ≤ ((B2' ×ˢ W2').filter fun p => petersenAdj p.1 p.2 = true).card := by
                  have hsub_p : (bipEdgesNoC c B2 W2).image (fun e => if e.1 ∈ B2 then (σ e.1, σ e.2) else (σ e.2, σ e.1)) ⊆
                      (B2' ×ˢ W2').filter fun p => petersenAdj p.1 p.2 = true := by
                    intro p hp
                    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
                    simp only [bipEdgesNoC, bipEdges, Finset.mem_filter] at he
                    have hadj := petersenEdges_adj e he.1.1
                    simp only [Finset.mem_filter, Finset.mem_product, B2', W2', Finset.mem_image]
                    split_ifs with h1
                    · rcases he.1.2 with ⟨_, h2⟩ | ⟨h1W, _⟩
                      · exact ⟨⟨⟨e.1, h1, rfl⟩, ⟨e.2, h2, rfl⟩⟩, by rw [hσadj]; exact hadj⟩
                      · exact absurd h1W (Finset.disjoint_left.mp hdisj2 h1)
                    · rcases he.1.2 with ⟨h1B, _⟩ | ⟨h1W, h2B⟩
                      · exact absurd h1B h1
                      · exact ⟨⟨⟨e.2, h2B, rfl⟩, ⟨e.1, h1W, rfl⟩⟩, by rw [hσadj]; exact petersenAdj_symm e.1 e.2 hadj⟩
                  have hinj : Set.InjOn (fun e : Fin 10 × Fin 10 => if e.1 ∈ B2 then (σ e.1, σ e.2) else (σ e.2, σ e.1)) (bipEdgesNoC c B2 W2) := by
                    intro e1 he1 e2 he2 heq
                    simp only [Finset.mem_coe, bipEdgesNoC, bipEdges, Finset.mem_filter] at he1 he2
                    have hlt1 := petersenEdges_lt e1 he1.1.1
                    have hlt2 := petersenEdges_lt e2 he2.1.1
                    dsimp only at heq
                    split_ifs at heq with h1 h2 h2
                    · have e11 := σ.injective (Prod.mk.inj heq).1
                      have e12 := σ.injective (Prod.mk.inj heq).2
                      exact Prod.ext e11 e12
                    · have e11 := σ.injective (Prod.mk.inj heq).1
                      have e12 := σ.injective (Prod.mk.inj heq).2
                      omega
                    · have e11 := σ.injective (Prod.mk.inj heq).1
                      have e12 := σ.injective (Prod.mk.inj heq).2
                      omega
                    · have e11 := σ.injective (Prod.mk.inj heq).1
                      have e12 := σ.injective (Prod.mk.inj heq).2
                      exact Prod.ext e12 e11
                  rw [← Finset.card_image_of_injOn hinj]
                  exact Finset.card_le_card hsub_p
                have hsum_prod : ((B2' ×ˢ W2').filter fun p => petersenAdj p.1 p.2 = true).card =
                    (if petersenAdj (σ x2) w1 then 1 else 0) + (if petersenAdj (σ x2) w2 then 1 else 0) + (if petersenAdj (σ x2) w3 then 1 else 0) +
                    (if petersenAdj a w1 then 1 else 0) + (if petersenAdj a w2 then 1 else 0) + (if petersenAdj a w3 then 1 else 0) +
                    (if petersenAdj b w1 then 1 else 0) + (if petersenAdj b w2 then 1 else 0) + (if petersenAdj b w3 then 1 else 0) := by
                  rw [hB2'eq, hW2'eq, Finset.card_filter, Finset.sum_product]
                  have ha_ne_x2 : σ x2 ≠ a := fun h => hx2_not_Y2n (by rw [← σ.symm_apply_apply x2, h]; exact hab_in_Y2n a (by simp))
                  have hb_ne_x2 : σ x2 ≠ b := fun h => hx2_not_Y2n (by rw [← σ.symm_apply_apply x2, h]; exact hab_in_Y2n b (by simp))
                  rw [Finset.sum_insert (by simp [ha_ne_x2, hb_ne_x2] : σ x2 ∉ ({a, b} : Finset (Fin 10))),
                    Finset.sum_insert (by simp [ne_of_lt hab] : a ∉ ({b} : Finset (Fin 10))), Finset.sum_singleton]
                  simp only [Finset.sum_insert (by simp [ne_of_lt hw12, ne_of_lt (lt_trans hw12 hw23)] : w1 ∉ ({w2, w3} : Finset (Fin 10))),
                    Finset.sum_insert (by simp [ne_of_lt hw23] : w2 ∉ ({w3} : Finset (Fin 10))),
                    Finset.sum_singleton]
                  omega
                omega
              have hle6 : (if petersenAdj (σ x2) w1 then 1 else 0) + (if petersenAdj (σ x2) w2 then 1 else 0) + (if petersenAdj (σ x2) w3 then 1 else 0) +
                  (if petersenAdj a w1 then 1 else 0) + (if petersenAdj a w2 then 1 else 0) + (if petersenAdj a w3 then 1 else 0) +
                  (if petersenAdj b w1 then 1 else 0) + (if petersenAdj b w2 then 1 else 0) + (if petersenAdj b w3 then 1 else 0) ≤ 6 := by
                have h_x2_2 : (if petersenAdj (σ x2) w1 then 1 else 0) + (if petersenAdj (σ x2) w2 then 1 else 0) + (if petersenAdj (σ x2) w3 then 1 else 0) ≤ 2 := by
                  have hsubx : ({w1, w2, w3} : Finset (Fin 10)).filter (fun w => petersenAdj (σ x2) w = true) ⊆
                      (Finset.univ.filter fun w => petersenAdj (σ x2) w = true).erase (σ x1) := by
                    intro w hw; simp only [Finset.mem_filter] at hw
                    refine Finset.mem_erase.mpr ⟨fun h => ?_, by simp [hw.2]⟩
                    exact hx1W (by rw [← σ.symm_apply_apply x1, ← h]; exact hw_in_W2 w hw.1)
                  have hx1in : σ x1 ∈ Finset.univ.filter fun w => petersenAdj (σ x2) w = true := by
                    simp [hσadj, petersenAdj_symm x1 x2 hx12]
                  have hc := Finset.card_le_card hsubx
                  rw [Finset.card_erase_of_mem hx1in] at hc
                  have hd3 := petersen_deg_le_3 (σ x2)
                  rw [Finset.card_filter, Finset.sum_insert (by simp [ne_of_lt hw12, ne_of_lt (lt_trans hw12 hw23)]),
                    Finset.sum_insert (by simp [ne_of_lt hw23]), Finset.sum_singleton] at hc
                  omega
                have h_ab_4 : (if petersenAdj a w1 then 1 else 0) + (if petersenAdj a w2 then 1 else 0) + (if petersenAdj a w3 then 1 else 0) +
                    (if petersenAdj b w1 then 1 else 0) + (if petersenAdj b w2 then 1 else 0) + (if petersenAdj b w3 then 1 else 0) ≤ 4 := by
                  have hcm := petersen_common_nbr_le_1 a b (ne_of_lt hab)
                  have h1 : (({w1, w2, w3} : Finset (Fin 10)).filter fun w => petersenAdj a w = true ∧ petersenAdj b w = true).card ≤ 1 :=
                    le_trans (Finset.card_le_card (fun w hw => by simp only [Finset.mem_filter] at hw; simp [hw.2])) hcm
                  rw [Finset.card_filter, Finset.sum_insert (by simp [ne_of_lt hw12, ne_of_lt (lt_trans hw12 hw23)]),
                    Finset.sum_insert (by simp [ne_of_lt hw23]), Finset.sum_singleton] at h1
                  cases ha1 : petersenAdj a w1 <;> cases hb1 : petersenAdj b w1 <;>
                  cases ha2 : petersenAdj a w2 <;> cases hb2 : petersenAdj b w2 <;>
                  cases ha3 : petersenAdj a w3 <;> cases hb3 : petersenAdj b w3 <;>
                  simp [ha1, hb1, ha2, hb2, ha3, hb3] at h1 ⊢ <;> omega
                omega
              omega
            have hw1p := hw_ne_0_and_nbr w1 (by simp)
            have hw2p := hw_ne_0_and_nbr w2 (by simp)
            have hw3p := hw_ne_0_and_nbr w3 (by simp)
            exact petersen_y2_b3_zero (σ x1) (σ x2) w1 w2 w3 a b
              (fun h => hx1c (σ.injective (by rw [hσc, h])))
              (fun h => hcY (by have hxc : x2 = c := σ.injective (by rw [hσc, h]); exact hxc ▸ Finset.mem_insert_self x2 Y2))
              (by rw [← hσc, hσadj]; exact hx2N)
              (by rw [hσadj]; exact hx12)
              hw12 hw23
              (fun h => hx1W (by rw [← σ.symm_apply_apply x1, ← h]; exact hw_in_W2 w1 (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj (Finset.mem_insert_self x2 Y2) (by rw [← σ.symm_apply_apply x2, ← h]; exact hw_in_W2 w1 (by simp)))
              (fun h => hx1W (by rw [← σ.symm_apply_apply x1, ← h]; exact hw_in_W2 w2 (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj (Finset.mem_insert_self x2 Y2) (by rw [← σ.symm_apply_apply x2, ← h]; exact hw_in_W2 w2 (by simp)))
              (fun h => hx1W (by rw [← σ.symm_apply_apply x1, ← h]; exact hw_in_W2 w3 (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj (Finset.mem_insert_self x2 Y2) (by rw [← σ.symm_apply_apply x2, ← h]; exact hw_in_W2 w3 (by simp)))
              hab
              (fun h => hcY (by have hac : σ.symm a = c := σ.injective (by rw [σ.apply_symm_apply, hσc, h]); exact hac ▸ Finset.mem_insert_of_mem (Finset.mem_filter.mp (hab_in_Y2n a (by simp))).1))
              (fun h => hcY (by have hbc : σ.symm b = c := σ.injective (by rw [σ.apply_symm_apply, hσc, h]); exact hbc ▸ Finset.mem_insert_of_mem (Finset.mem_filter.mp (hab_in_Y2n b (by simp))).1))
              (by rw [← hσc, ← σ.apply_symm_apply a, hσadj]; exact (Finset.mem_filter.mp (hab_in_Y2n a (by simp))).2)
              (by rw [← hσc, ← σ.apply_symm_apply b, hσadj]; exact (Finset.mem_filter.mp (hab_in_Y2n b (by simp))).2)
              (fun h => hx1Y (by have hax : σ.symm a = x1 := σ.injective (by rw [σ.apply_symm_apply, h]); exact hax ▸ Finset.mem_insert_of_mem (Finset.mem_filter.mp (hab_in_Y2n a (by simp))).1))
              (fun h => hx2_not_Y2n (by rw [← σ.symm_apply_apply x2, ← h]; exact hab_in_Y2n a (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (hab_in_Y2n a (by simp))) (h ▸ hw_in_W2 w1 (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (hab_in_Y2n a (by simp))) (h ▸ hw_in_W2 w2 (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (hab_in_Y2n a (by simp))) (h ▸ hw_in_W2 w3 (by simp)))
              (fun h => hx1Y (by have hbx : σ.symm b = x1 := σ.injective (by rw [σ.apply_symm_apply, h]); exact hbx ▸ Finset.mem_insert_of_mem (Finset.mem_filter.mp (hab_in_Y2n b (by simp))).1))
              (fun h => hx2_not_Y2n (by rw [← σ.symm_apply_apply x2, ← h]; exact hab_in_Y2n b (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (hab_in_Y2n b (by simp))) (h ▸ hw_in_W2 w1 (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (hab_in_Y2n b (by simp))) (h ▸ hw_in_W2 w2 (by simp)))
              (fun h => Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (hab_in_Y2n b (by simp))) (h ▸ hw_in_W2 w3 (by simp)))
              ⟨hw1p.1, hw2p.1, hw3p.1, hw1p.2, hw2p.2, hw3p.2, he2_cnt⟩
          · have hW4 : 4 ≤ W2.card := by omega
            by_cases hcW : c ∈ W2
            · have he_3Wm1 : (bipEdgesNoC c B0 W2).card ≤ 3 * (W2.card - 1) := by
                have hsubW : bipEdgesNoC c B0 W2 ⊆ bipEdges B0 (W2.erase c) := by
                  intro e he; simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_erase] at he ⊢
                  rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact ⟨he.1.1, Or.inl ⟨h1, he.2.2, h2⟩⟩
                  · exact ⟨he.1.1, Or.inr ⟨⟨he.2.1, h1⟩, h2⟩⟩
                have hdW : Disjoint (W2.erase c) B0 := Disjoint.mono_left (Finset.erase_subset _ _) hdisj.symm
                calc (bipEdgesNoC c B0 W2).card
                    ≤ (bipEdges B0 (W2.erase c)).card := Finset.card_le_card hsubW
                  _ = (bipEdges (W2.erase c) B0).card := by rw [bipEdges_comm]
                  _ ≤ 3 * (W2.erase c).card := bipEdges_le_three_left _ _ hdW
                  _ = 3 * (W2.card - 1) := by rw [Finset.card_erase_of_mem hcW]
              by_cases hW4' : W2.card = 4
              · omega
              · have hB1_le1 : B1.card ≤ 1 := by omega
                have he2_le8 : (bipEdgesNoC c B2 W2).card ≤ 8 := by omega
                omega
            · have htot8 : B0.card + W2.card ≤ 8 := by
                have hc_not : c ∉ B0 ∪ W2 := by simp [hcY, hcW]
                have hx1_not : x1 ∉ B0 ∪ W2 := by simp [hx1Y, hx1W]
                have hsub8 : B0 ∪ W2 ⊆ (Finset.univ.erase c).erase x1 := by
                  intro z hz
                  exact Finset.mem_erase.mpr ⟨fun h => hx1_not (h ▸ hz),
                    Finset.mem_erase.mpr ⟨fun h => hc_not (h ▸ hz), Finset.mem_univ z⟩⟩
                rw [← Finset.card_union_of_disjoint hdisj]
                have hx1_in : x1 ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hx1c, Finset.mem_univ x1⟩
                exact le_trans (Finset.card_le_card hsub8) (by rw [Finset.card_erase_of_mem hx1_in]; simp)
              have hB1_le1 : B1.card ≤ 1 := by omega
              have he2_le8 : (bipEdgesNoC c B2 W2).card ≤ 8 := by omega
              omega
      · by_cases hW3 : W2.card ≤ 3
        · omega
        · by_cases hcW : c ∈ W2
          · have he_3Wm1 : (bipEdgesNoC c B0 W2).card ≤ 3 * (W2.card - 1) := by
              have hsubW : bipEdgesNoC c B0 W2 ⊆ bipEdges B0 (W2.erase c) := by
                intro e he; simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_erase] at he ⊢
                rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact ⟨he.1.1, Or.inl ⟨h1, he.2.2, h2⟩⟩
                · exact ⟨he.1.1, Or.inr ⟨⟨he.2.1, h1⟩, h2⟩⟩
              have hdW : Disjoint (W2.erase c) B0 := Disjoint.mono_left (Finset.erase_subset _ _) hdisj.symm
              calc (bipEdgesNoC c B0 W2).card
                  ≤ (bipEdges B0 (W2.erase c)).card := Finset.card_le_card hsubW
                _ = (bipEdges (W2.erase c) B0).card := by rw [bipEdges_comm]
                _ ≤ 3 * (W2.erase c).card := bipEdges_le_three_left _ _ hdW
                _ = 3 * (W2.card - 1) := by rw [Finset.card_erase_of_mem hcW]
            by_cases hB1_0 : B1.card = 0
            · have he10 : (bipEdgesNoC c B1 W2).card = 0 := by omega
              omega
            · omega
          · have htot8 : B0.card + W2.card ≤ 8 := by
              have hc_not : c ∉ B0 ∪ W2 := by simp [hcY, hcW]
              have hx1_not : x1 ∉ B0 ∪ W2 := by simp [hx1Y, hx1W]
              have hsub8 : B0 ∪ W2 ⊆ (Finset.univ.erase c).erase x1 := by
                intro z hz
                exact Finset.mem_erase.mpr ⟨fun h => hx1_not (h ▸ hz),
                  Finset.mem_erase.mpr ⟨fun h => hc_not (h ▸ hz), Finset.mem_univ z⟩⟩
              rw [← Finset.card_union_of_disjoint hdisj]
              have hx1_in : x1 ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hx1c, Finset.mem_univ x1⟩
              exact le_trans (Finset.card_le_card hsub8) (by rw [Finset.card_erase_of_mem hx1_in]; simp)
            have hB1_0 : B1.card = 0 := by omega
            have he10 : (bipEdgesNoC c B1 W2).card = 0 := by omega
            omega

lemma petersen_no_triangle : ∀ c u v : Fin 10,
    petersenAdj c u = true → petersenAdj u v = true → petersenAdj c v = false := by
  decide

set_option maxHeartbeats 1200000 in
theorem golden_read2_bound_with_c (c : Fin 10) (M0 : Finset (Fin 10)) (L : MonoFormula 10)
    (hcM0 : c ∉ M0)
    (hr2 : ∀ v : Fin 10, L.varCount v ≤ 2)
    (hM0 : ∀ m ∈ M0, L.varCount m ≤ 1)
    (hno : ∀ u v : Fin 10, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → L.eval (pairInput u v) = false) :
    (singleSet L).card + (edgesM0NoC c M0 L).card +
      (((M0 ∩ L.orVars) \ singleSet L).filter fun u => petersenAdj c u = true).card ≤ L.leaves := by
  induction L with
  | var i =>
    have hS : singleSet (MonoFormula.var i) = {i} := by
      ext v; simp [singleSet, MonoFormula.eval, singleInput, eq_comm]
    have hE : edgesM0NoC c M0 (MonoFormula.var i) = ∅ := by
      ext e
      simp only [edgesM0NoC, edgesM0, Finset.mem_filter, hS, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, _, hev, h1, h2⟩, _⟩
      simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at hev
      rcases hev with h | h
      · exact h1 h.symm
      · exact h2 h.symm
    have hN : (((M0 ∩ (MonoFormula.var i).orVars) \ singleSet (MonoFormula.var i)).filter
        fun u => petersenAdj c u = true) = ∅ := by
      ext u; simp [hS, MonoFormula.orVars]
    rw [hN, hS, hE]; simp [MonoFormula.leaves]
  | or l r ihl ihr =>
    have hr2l : ∀ v, l.varCount v ≤ 2 := fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega
    have hr2r : ∀ v, r.varCount v ≤ 2 := fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega
    have hM0l : ∀ m ∈ M0, l.varCount m ≤ 1 := fun m hm => by have := hM0 m hm; simp [MonoFormula.varCount] at this; omega
    have hM0r : ∀ m ∈ M0, r.varCount m ≤ 1 := fun m hm => by have := hM0 m hm; simp [MonoFormula.varCount] at this; omega
    have hnol : ∀ u v, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → l.eval (pairInput u v) = false := by
      intro u v hm hadj; have h := hno u v hm hadj; simp [MonoFormula.eval] at h; exact h.1
    have hnor : ∀ u v, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → r.eval (pairInput u v) = false := by
      intro u v hm hadj; have h := hno u v hm hadj; simp [MonoFormula.eval] at h; exact h.2
    have hS_sub : singleSet (l.or r) ⊆ singleSet l ∪ singleSet r := by
      intro v hv; simp only [singleSet, Finset.mem_filter, Finset.mem_univ, true_and,
        MonoFormula.eval, Bool.or_eq_true, Finset.mem_union] at hv ⊢; exact hv
    have hE_sub : edgesM0NoC c M0 (l.or r) ⊆ edgesM0NoC c M0 l ∪ edgesM0NoC c M0 r := by
      intro e he
      simp only [edgesM0NoC, edgesM0, Finset.mem_filter, Finset.mem_union, singleSet, Finset.mem_univ,
        true_and, MonoFormula.eval, Bool.or_eq_true, not_or] at he ⊢
      rcases he.1.2.2.1 with hl | hr
      · exact Or.inl ⟨⟨he.1.1, he.1.2.1, hl, he.1.2.2.2.1.1, he.1.2.2.2.2.1⟩, he.2⟩
      · exact Or.inr ⟨⟨he.1.1, he.1.2.1, hr, he.1.2.2.2.1.2, he.1.2.2.2.2.2⟩, he.2⟩
    have hN_sub : (((M0 ∩ (l.or r).orVars) \ singleSet (l.or r)).filter fun u => petersenAdj c u = true) ⊆
        (((M0 ∩ l.orVars) \ singleSet l).filter fun u => petersenAdj c u = true) ∪
        (((M0 ∩ r.orVars) \ singleSet r).filter fun u => petersenAdj c u = true) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter, MonoFormula.orVars,
        Finset.mem_union, singleSet, Finset.mem_univ, true_and, MonoFormula.eval, Bool.or_eq_true, not_or] at hu ⊢
      rcases hu.1.1.2 with hl | hr
      · exact Or.inl ⟨⟨⟨hu.1.1.1, hl⟩, hu.1.2.1⟩, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1.1.1, hr⟩, hu.1.2.2⟩, hu.2⟩
    have c1 := le_trans (Finset.card_le_card hS_sub) (Finset.card_union_le _ _)
    have c2 := le_trans (Finset.card_le_card hE_sub) (Finset.card_union_le _ _)
    have c3 := le_trans (Finset.card_le_card hN_sub) (Finset.card_union_le _ _)
    have b1 := ihl hr2l hM0l hnol
    have b2 := ihr hr2r hM0r hnor
    simp only [MonoFormula.leaves]
    omega
  | and l r _ _ =>
    let S1 := singleSet l
    let S2 := singleSet r
    let S := singleSet (l.and r)
    have hS_eq : S = S1 ∩ S2 := by ext v; simp [S, S1, S2, singleSet, MonoFormula.eval]
    let A0 := M0 ∩ l.orVars
    let B0 := M0 ∩ r.orVars
    have hAB_disj : Disjoint A0 B0 := by
      rw [Finset.disjoint_left]; intro m hmA hmB
      have hm0 := (Finset.mem_inter.mp hmA).1
      have hml := (Finset.mem_inter.mp hmA).2
      have hmr := (Finset.mem_inter.mp hmB).2
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hml hmr
      have h1 := hM0 m hm0; simp [MonoFormula.varCount] at h1; omega
    let W1 := (l.orVars ∩ S2) \ S
    let W2 := (r.orVars ∩ S1) \ S
    let S1' := S1 \ r.orVars
    let S2' := S2 \ l.orVars
    let X1 := A0 ∩ S1'
    let Y1 := A0 \ S1'
    let Z1 := S1' \ A0
    let X2 := B0 ∩ S2'
    let Y2 := B0 \ S2'
    let Z2 := S2' \ B0
    have hS1_sub : S1 ⊆ l.orVars := singleSet_subset_orVars l
    have hS2_sub : S2 ⊆ r.orVars := singleSet_subset_orVars r
    have hA0_not_r : ∀ v ∈ A0, v ∉ r.orVars := fun v hv hr =>
      Finset.disjoint_left.mp hAB_disj hv (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hr⟩)
    have hB0_not_l : ∀ v ∈ B0, v ∉ l.orVars := fun v hv hl =>
      Finset.disjoint_left.mp hAB_disj (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hl⟩) hv
    have hcA0 : c ∉ A0 := fun h => hcM0 (Finset.mem_inter.mp h).1
    have hcB0 : c ∉ B0 := fun h => hcM0 (Finset.mem_inter.mp h).1
    have hl_budget : S.card + W1.card + W2.card + X1.card + Y1.card + Z1.card ≤ l.leaves := by
      have d1 : Disjoint S W1 := by rw [Finset.disjoint_left]; intro x hx h2; exact (Finset.mem_sdiff.mp h2).2 hx
      have d2 : Disjoint (S ∪ W1) W2 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have h2' := Finset.mem_sdiff.mp h2; rw [Finset.mem_union] at hx
        rcases hx with hs | hw1
        · exact h2'.2 hs
        · exact h2'.2 (hS_eq ▸ Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h2'.1).2, (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2⟩)
      have d3 : Disjoint (S ∪ W1 ∪ W2) X1 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have hnr := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).2).2
        simp only [Finset.mem_union] at hx
        rcases hx with (hs | hw1) | hw2
        · exact hnr (hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2)
        · exact hnr (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2)
        · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
      have d4 : Disjoint (S ∪ W1 ∪ W2 ∪ X1) Y1 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have hnr := hA0_not_r x (Finset.mem_sdiff.mp h2).1
        have hns := (Finset.mem_sdiff.mp h2).2
        simp only [Finset.mem_union] at hx
        rcases hx with ((hs | hw1) | hw2) | hx1
        · exact hnr (hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2)
        · exact hnr (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2)
        · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
        · exact hns (Finset.mem_inter.mp hx1).2
      have d5 : Disjoint (S ∪ W1 ∪ W2 ∪ X1 ∪ Y1) Z1 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have hnr := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2
        have hna := (Finset.mem_sdiff.mp h2).2
        simp only [Finset.mem_union] at hx
        rcases hx with (((hs | hw1) | hw2) | hx1) | hy1
        · exact hnr (hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2)
        · exact hnr (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2)
        · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
        · exact hna (Finset.mem_inter.mp hx1).1
        · exact hna (Finset.mem_sdiff.mp hy1).1
      have hsub : S ∪ W1 ∪ W2 ∪ X1 ∪ Y1 ∪ Z1 ⊆ l.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with ((((hs | hw1) | hw2) | hx1) | hy1) | hz1
        · exact hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
        · exact hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx1).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy1).1).2
        · exact hS1_sub (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz1).1).1
      rw [← Finset.card_union_of_disjoint d1, ← Finset.card_union_of_disjoint d2,
        ← Finset.card_union_of_disjoint d3, ← Finset.card_union_of_disjoint d4,
        ← Finset.card_union_of_disjoint d5]
      exact le_trans (Finset.card_le_card hsub) l.orVars_card_le
    have hr_budget : S.card + W1.card + W2.card + X2.card + Y2.card + Z2.card ≤ r.leaves := by
      have d1 : Disjoint S W1 := by rw [Finset.disjoint_left]; intro x hx h2; exact (Finset.mem_sdiff.mp h2).2 hx
      have d2 : Disjoint (S ∪ W1) W2 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have h2' := Finset.mem_sdiff.mp h2; rw [Finset.mem_union] at hx
        rcases hx with hs | hw1
        · exact h2'.2 hs
        · exact h2'.2 (hS_eq ▸ Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h2'.1).2, (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2⟩)
      have d3 : Disjoint (S ∪ W1 ∪ W2) X2 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have hnl := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).2).2
        simp only [Finset.mem_union] at hx
        rcases hx with (hs | hw1) | hw2
        · exact hnl (hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1)
        · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
        · exact hnl (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2)
      have d4 : Disjoint (S ∪ W1 ∪ W2 ∪ X2) Y2 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have hnl := hB0_not_l x (Finset.mem_sdiff.mp h2).1
        have hns := (Finset.mem_sdiff.mp h2).2
        simp only [Finset.mem_union] at hx
        rcases hx with ((hs | hw1) | hw2) | hx2
        · exact hnl (hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1)
        · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
        · exact hnl (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2)
        · exact hns (Finset.mem_inter.mp hx2).2
      have d5 : Disjoint (S ∪ W1 ∪ W2 ∪ X2 ∪ Y2) Z2 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have hnl := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2
        have hnb := (Finset.mem_sdiff.mp h2).2
        simp only [Finset.mem_union] at hx
        rcases hx with (((hs | hw1) | hw2) | hx2) | hy2
        · exact hnl (hS1_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).1)
        · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
        · exact hnl (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2)
        · exact hnb (Finset.mem_inter.mp hx2).1
        · exact hnb (Finset.mem_sdiff.mp hy2).1
      have hsub : S ∪ W1 ∪ W2 ∪ X2 ∪ Y2 ∪ Z2 ⊆ r.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with ((((hs | hw1) | hw2) | hx2) | hy2) | hz2
        · exact hS2_sub (Finset.mem_inter.mp (hS_eq ▸ hs)).2
        · exact hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx2).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy2).1).2
        · exact hS2_sub (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz2).1).1
      rw [← Finset.card_union_of_disjoint d1, ← Finset.card_union_of_disjoint d2,
        ← Finset.card_union_of_disjoint d3, ← Finset.card_union_of_disjoint d4,
        ← Finset.card_union_of_disjoint d5]
      exact le_trans (Finset.card_le_card hsub) r.orVars_card_le
    have hNc_le : (((M0 ∩ (l.and r).orVars) \ S).filter fun u => petersenAdj c u = true).card ≤
        (A0.filter fun u => petersenAdj c u = true).card + (B0.filter fun u => petersenAdj c u = true).card := by
      have hsub : (((M0 ∩ (l.and r).orVars) \ S).filter fun u => petersenAdj c u = true) ⊆
          (A0.filter fun u => petersenAdj c u = true) ∪ (B0.filter fun u => petersenAdj c u = true) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter, MonoFormula.orVars,
          Finset.mem_union, A0, B0] at hu ⊢
        rcases hu.1.1.2 with hl | hr
        · exact Or.inl ⟨⟨hu.1.1.1, hl⟩, hu.2⟩
        · exact Or.inr ⟨⟨hu.1.1.1, hr⟩, hu.2⟩
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hE_sub : edgesM0NoC c M0 (l.and r) ⊆
        bipEdgesNoC c A0 W1 ∪ bipEdgesNoC c B0 W2 ∪ bipEdgesNoC c X1 X2 ∪ bipEdgesNoC c X1 Z2 ∪ bipEdgesNoC c X2 Z1 := by
      intro e he
      simp only [edgesM0NoC, Finset.mem_filter] at he
      have h1 : e ∈ edgesM0 M0 (l.and r) := he.1
      have hnc := he.2
      simp only [edgesM0, Finset.mem_filter] at h1
      have hmem_raw : e ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2 ∪ bipEdges X2 Z1 := by
        have hdir : ∀ u v : Fin 10, (u, v) ∈ petersenEdges → u ∈ M0 →
            (l.and r).eval (pairInput u v) = true → u ∉ S → v ∉ S →
            (u, v) ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2 ∪ bipEdges X2 Z1 := by
          intro u v he' hum huv hus hvs
          simp only [MonoFormula.eval, Bool.and_eq_true] at huv
          simp only [Finset.mem_union]
          by_cases hul : u ∈ l.orVars
          · have huA : u ∈ A0 := Finset.mem_inter.mpr ⟨hum, hul⟩
            have hunr : u ∉ r.orVars := hA0_not_r u huA
            have hrv : r.eval (singleInput v) = true := by
              have h0 := eval_pair_of_not_mem r u v hunr
              change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
            have hvS2 : v ∈ S2 := by simp [S2, singleSet, hrv]
            by_cases hvl : v ∈ l.orVars
            · have hvW1 : v ∈ W1 := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvl, hvS2⟩, hvs⟩
              exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huA, hvW1⟩⟩))))
            · have hvS2' : v ∈ S2' := Finset.mem_sdiff.mpr ⟨hvS2, hvl⟩
              have hlu : l.eval (singleInput u) = true := by
                have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                have h0 := eval_pair_of_not_mem l v u hvl
                change l.eval (pairInput v u) = l.eval (singleInput u) at h0; rw [← h0, ← hsym]; exact huv.1
              have huX1 : u ∈ X1 := Finset.mem_inter.mpr ⟨huA, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hlu], hunr⟩⟩
              by_cases hvB0 : v ∈ B0
              · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX1, Finset.mem_inter.mpr ⟨hvB0, hvS2'⟩⟩⟩)))
              · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX1, Finset.mem_sdiff.mpr ⟨hvS2', hvB0⟩⟩⟩))
          · by_cases hur : u ∈ r.orVars
            · have huB : u ∈ B0 := Finset.mem_inter.mpr ⟨hum, hur⟩
              have hlv : l.eval (singleInput v) = true := by
                have h0 := eval_pair_of_not_mem l u v hul
                change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
              have hvS1 : v ∈ S1 := by simp [S1, singleSet, hlv]
              by_cases hvr : v ∈ r.orVars
              · exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huB, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvr, hvS1⟩, hvs⟩⟩⟩))))
              · have hvS1' : v ∈ S1' := Finset.mem_sdiff.mpr ⟨hvS1, hvr⟩
                have hru : r.eval (singleInput u) = true := by
                  have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                  have h0 := eval_pair_of_not_mem r v u hvr
                  change r.eval (pairInput v u) = r.eval (singleInput u) at h0; rw [← h0, ← hsym]; exact huv.2
                have huX2 : u ∈ X2 := Finset.mem_inter.mpr ⟨huB, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hru], hul⟩⟩
                by_cases hvA0 : v ∈ A0
                · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨huX2, Finset.mem_inter.mpr ⟨hvA0, hvS1'⟩⟩⟩)))
                · exact Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX2, Finset.mem_sdiff.mpr ⟨hvS1', hvA0⟩⟩⟩)
            · exfalso
              have hlv : l.eval (singleInput v) = true := by
                have h0 := eval_pair_of_not_mem l u v hul
                change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
              have hrv : r.eval (singleInput v) = true := by
                have h0 := eval_pair_of_not_mem r u v hur
                change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
              exact hvs (by simp [S, singleSet, MonoFormula.eval, hlv, hrv])
        rcases h1.2.1 with hm1 | hm2
        · exact hdir e.1 e.2 h1.1 hm1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2
        · have hsym : pairInput e.2 e.1 = pairInput e.1 e.2 := by funext i; simp [pairInput, or_comm]
          have hrev : ∀ u v : Fin 10, (v, u) ∈ petersenEdges → u ∈ M0 →
              (l.and r).eval (pairInput u v) = true → u ∉ S → v ∉ S →
              (v, u) ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪ bipEdges X1 Z2 ∪ bipEdges X2 Z1 := by
            intro u v he' hum huv hus hvs
            simp only [MonoFormula.eval, Bool.and_eq_true] at huv
            simp only [Finset.mem_union]
            by_cases hul : u ∈ l.orVars
            · have huA : u ∈ A0 := Finset.mem_inter.mpr ⟨hum, hul⟩
              have hunr : u ∉ r.orVars := hA0_not_r u huA
              have hrv : r.eval (singleInput v) = true := by
                have h0 := eval_pair_of_not_mem r u v hunr
                change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
              have hvS2 : v ∈ S2 := by simp [S2, singleSet, hrv]
              by_cases hvl : v ∈ l.orVars
              · exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvl, hvS2⟩, hvs⟩, huA⟩⟩))))
              · have hvS2' : v ∈ S2' := Finset.mem_sdiff.mpr ⟨hvS2, hvl⟩
                have hlu : l.eval (singleInput u) = true := by
                  have hsym2 : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                  have h0 := eval_pair_of_not_mem l v u hvl
                  change l.eval (pairInput v u) = l.eval (singleInput u) at h0; rw [← h0, ← hsym2]; exact huv.1
                have huX1 : u ∈ X1 := Finset.mem_inter.mpr ⟨huA, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hlu], hunr⟩⟩
                by_cases hvB0 : v ∈ B0
                · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_inter.mpr ⟨hvB0, hvS2'⟩, huX1⟩⟩)))
                · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨hvS2', hvB0⟩, huX1⟩⟩))
            · by_cases hur : u ∈ r.orVars
              · have huB : u ∈ B0 := Finset.mem_inter.mpr ⟨hum, hur⟩
                have hlv : l.eval (singleInput v) = true := by
                  have h0 := eval_pair_of_not_mem l u v hul
                  change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
                have hvS1 : v ∈ S1 := by simp [S1, singleSet, hlv]
                by_cases hvr : v ∈ r.orVars
                · exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvr, hvS1⟩, hvs⟩, huB⟩⟩))))
                · have hvS1' : v ∈ S1' := Finset.mem_sdiff.mpr ⟨hvS1, hvr⟩
                  have hru : r.eval (singleInput u) = true := by
                    have hsym2 : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                    have h0 := eval_pair_of_not_mem r v u hvr
                    change r.eval (pairInput v u) = r.eval (singleInput u) at h0; rw [← h0, ← hsym2]; exact huv.2
                  have huX2 : u ∈ X2 := Finset.mem_inter.mpr ⟨huB, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hru], hul⟩⟩
                  by_cases hvA0 : v ∈ A0
                  · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨Finset.mem_inter.mpr ⟨hvA0, hvS1'⟩, huX2⟩⟩)))
                  · exact Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨hvS1', hvA0⟩, huX2⟩⟩)
              · exfalso
                have hlv : l.eval (singleInput v) = true := by
                  have h0 := eval_pair_of_not_mem l u v hul
                  change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
                have hrv : r.eval (singleInput v) = true := by
                  have h0 := eval_pair_of_not_mem r u v hur
                  change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
                exact hvs (by simp [S, singleSet, MonoFormula.eval, hlv, hrv])
          exact hrev e.2 e.1 h1.1 hm2 (by rw [hsym]; exact h1.2.2.1) h1.2.2.2.2 h1.2.2.2.1
      simp only [Finset.mem_union] at hmem_raw ⊢
      rcases hmem_raw with (((h | h) | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨h, hnc⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩))))
      · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩)))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩))
      · exact Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩)
    have hdisj_A0W1 : Disjoint A0 W1 := by
      rw [Finset.disjoint_left]; intro x hxA hxW
      exact hA0_not_r x hxA (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).2)
    have hdisj_B0W2 : Disjoint B0 W2 := by
      rw [Finset.disjoint_left]; intro x hxB hxW
      exact hB0_not_l x hxB (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).2)
    have hA0_card : A0.card = X1.card + Y1.card := (Finset.card_inter_add_card_sdiff A0 S1').symm
    have hB0_card : B0.card = X2.card + Y2.card := (Finset.card_inter_add_card_sdiff B0 S2').symm
    have hbic1 : X1.card ≤ 1 ∨ (W1 ∪ X2 ∪ Z2).card ≤ 1 := by
      apply petersen_biclique_star
      intro x hx v hv
      have hxM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      have hxS1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
      have hvS2 : v ∈ S2 := by
        simp only [Finset.mem_union] at hv
        rcases hv with (hw1 | hx2) | hz2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz2).1).1
      cases hadj : petersenAdj x v
      · exfalso
        have hf := hno x v (Or.inl hxM0) hadj
        have ht : (l.and r).eval (pairInput x v) = true := by
          simp only [MonoFormula.eval, Bool.and_eq_true]
          exact ⟨l.eval_mono (singleInput x) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hxS1).2,
            r.eval_mono (singleInput v) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp hvS2).2⟩
        rw [hf] at ht; exact absurd ht (by decide)
      · rfl
    have hbic2 : X2.card ≤ 1 ∨ (W2 ∪ X1 ∪ Z1).card ≤ 1 := by
      apply petersen_biclique_star
      intro x hx v hv
      have hxM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      have hxS2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
      have hvS1 : v ∈ S1 := by
        simp only [Finset.mem_union] at hv
        rcases hv with (hw2 | hx1) | hz1
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).2
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx1).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz1).1).1
      cases hadj : petersenAdj x v
      · exfalso
        have hf := hno x v (Or.inl hxM0) hadj
        have ht : (l.and r).eval (pairInput x v) = true := by
          simp only [MonoFormula.eval, Bool.and_eq_true]
          exact ⟨l.eval_mono (singleInput v) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp hvS1).2,
            r.eval_mono (singleInput x) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hxS2).2⟩
        rw [hf] at ht; exact absurd ht (by decide)
      · rfl
    have hE_union : (edgesM0NoC c M0 (l.and r)).card ≤
        (bipEdgesNoC c A0 W1).card + (bipEdgesNoC c B0 W2).card + (bipEdgesNoC c X1 X2).card +
        (bipEdgesNoC c X1 Z2).card + (bipEdgesNoC c X2 Z1).card := by
      calc (edgesM0NoC c M0 (l.and r)).card
          ≤ (bipEdgesNoC c A0 W1 ∪ bipEdgesNoC c B0 W2 ∪ bipEdgesNoC c X1 X2 ∪ bipEdgesNoC c X1 Z2 ∪ bipEdgesNoC c X2 Z1).card :=
            Finset.card_le_card hE_sub
        _ ≤ _ := by
            have u1 := Finset.card_union_le (bipEdgesNoC c A0 W1 ∪ bipEdgesNoC c B0 W2 ∪ bipEdgesNoC c X1 X2 ∪ bipEdgesNoC c X1 Z2) (bipEdgesNoC c X2 Z1)
            have u2 := Finset.card_union_le (bipEdgesNoC c A0 W1 ∪ bipEdgesNoC c B0 W2 ∪ bipEdgesNoC c X1 X2) (bipEdgesNoC c X1 Z2)
            have u3 := Finset.card_union_le (bipEdgesNoC c A0 W1 ∪ bipEdgesNoC c B0 W2) (bipEdgesNoC c X1 X2)
            have u4 := Finset.card_union_le (bipEdgesNoC c A0 W1) (bipEdgesNoC c B0 W2)
            omega
    have hEN_bound : (edgesM0NoC c M0 (l.and r)).card +
        (A0.filter fun u => petersenAdj c u = true).card +
        (B0.filter fun u => petersenAdj c u = true).card ≤
        2 * W1.card + 2 * W2.card + X1.card + Y1.card + Z1.card + X2.card + Y2.card + Z2.card := by
      have bAW := bipEdgesNoC_add_nc_le c A0 W1 hcA0 hdisj_A0W1
      have bBW := bipEdgesNoC_add_nc_le c B0 W2 hcB0 hdisj_B0W2
      rcases hbic1 with hX1 | hR1
      · rcases hbic2 with hX2 | hL1
        · have bZ2 : (bipEdgesNoC c X1 Z2).card ≤ Z2.card :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (bipEdges_le_right_of_card_le_one X1 Z2 hX1)
          have bZ1 : (bipEdgesNoC c X2 Z1).card ≤ Z1.card :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (bipEdges_le_right_of_card_le_one X2 Z1 hX2)
          by_cases hX12 : (bipEdgesNoC c X1 X2).Nonempty
          · obtain ⟨e, he⟩ := hX12
            have he_adj := petersenEdges_adj e (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
            have hex_x : ∃ x1 x2, X1 = {x1} ∧ X2 = {x2} ∧ petersenAdj x1 x2 = true := by
              have hX1ne : X1.Nonempty := by
                rcases (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2 with ⟨h1, _⟩ | ⟨_, h2⟩
                · exact ⟨e.1, h1⟩
                · exact ⟨e.2, h2⟩
              have hX2ne : X2.Nonempty := by
                rcases (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2 with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact ⟨e.2, h2⟩
                · exact ⟨e.1, h1⟩
              obtain ⟨x1, hx1⟩ := Finset.card_eq_one.mp (le_antisymm hX1 (Finset.card_pos.mpr hX1ne))
              obtain ⟨x2, hx2⟩ := Finset.card_eq_one.mp (le_antisymm hX2 (Finset.card_pos.mpr hX2ne))
              refine ⟨x1, x2, hx1, hx2, ?_⟩
              rcases (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [hx1, Finset.mem_singleton] at h1; rw [hx2, Finset.mem_singleton] at h2
                rw [← h1, ← h2]; exact he_adj
              · rw [hx2, Finset.mem_singleton] at h1; rw [hx1, Finset.mem_singleton] at h2
                rw [← h1, ← h2]; exact petersenAdj_symm e.1 e.2 he_adj
            obtain ⟨x1, x2, hX1eq, hX2eq, hx12_adj⟩ := hex_x
            have hA0_ins : A0 = insert x1 Y1 := by
              ext z; simp only [Finset.mem_insert, Y1, Finset.mem_sdiff]; constructor
              · intro hz; by_cases hzs : z ∈ S1'
                · left; have : z ∈ X1 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hX1eq, Finset.mem_singleton] at this; exact this
                · exact Or.inr ⟨hz, hzs⟩
              · rintro (hz | ⟨hz, _⟩)
                · subst z; exact (Finset.mem_inter.mp (by rw [hX1eq]; simp : x1 ∈ X1)).1
                · exact hz
            have hB0_ins : B0 = insert x2 Y2 := by
              ext z; simp only [Finset.mem_insert, Y2, Finset.mem_sdiff]; constructor
              · intro hz; by_cases hzs : z ∈ S2'
                · left; have : z ∈ X2 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hX2eq, Finset.mem_singleton] at this; exact this
                · exact Or.inr ⟨hz, hzs⟩
              · rintro (hz | ⟨hz, _⟩)
                · subst z; exact (Finset.mem_inter.mp (by rw [hX2eq]; simp : x2 ∈ X2)).1
                · exact hz
            have hx1Y1 : x1 ∉ Y1 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp (by rw [hX1eq]; simp : x1 ∈ X1)).2
            have hx2Y2 : x2 ∉ Y2 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp (by rw [hX2eq]; simp : x2 ∈ X2)).2
            have hx1A0 : x1 ∈ A0 := by rw [hA0_ins]; simp
            have hx2B0 : x2 ∈ B0 := by rw [hB0_ins]; simp
            have hx1c : x1 ≠ c := fun h => hcA0 (h ▸ hx1A0)
            have hx2c : x2 ≠ c := fun h => hcB0 (h ▸ hx2B0)
            have hx1_not_B0 : x1 ∉ B0 := Finset.disjoint_left.mp hAB_disj hx1A0
            have hx2_not_A0 : x2 ∉ A0 := Finset.disjoint_right.mp hAB_disj hx2B0
            have hx2W1 : x2 ∉ W1 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by rw [hX2eq]; simp : x2 ∈ X2)).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
            have hx1W2 : x1 ∉ W2 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by rw [hX1eq]; simp : x1 ∈ X1)).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
            have hX1c : X1.card = 1 := by rw [hX1eq]; simp
            have hX2c : X2.card = 1 := by rw [hX2eq]; simp
            have bX12 : (bipEdgesNoC c X1 X2).card ≤ X2.card :=
              le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (bipEdges_le_right_of_card_le_one X1 X2 hX1)
            cases hc1 : petersenAdj c x1
            · have bAW' := bipEdgesNoC_of_ext c x2 x1 Y1 W1 (hA0_ins ▸ hcA0) hx2c hc1 (petersenAdj_symm x1 x2 hx12_adj) hx1Y1 (hA0_ins ▸ hx2_not_A0) hx2W1 (hA0_ins ▸ hdisj_A0W1)
              rw [← hA0_ins] at bAW'
              omega
            · have hc2 : petersenAdj c x2 = false := petersen_no_triangle c x1 x2 hc1 hx12_adj
              have bBW' := bipEdgesNoC_of_ext c x1 x2 Y2 W2 (hB0_ins ▸ hcB0) hx1c hc2 hx12_adj hx2Y2 (hB0_ins ▸ hx1_not_B0) hx1W2 (hB0_ins ▸ hdisj_B0W2)
              rw [← hB0_ins] at bBW'
              omega
          · rw [Finset.not_nonempty_iff_eq_empty] at hX12
            rw [hX12, Finset.card_empty] at hE_union
            omega
        · have hW2_le : W2.card ≤ 1 := le_trans (Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)) hL1
          have hZ1_le : Z1.card ≤ 1 := le_trans (Finset.card_le_card Finset.subset_union_right) hL1
          have hdisj_W2X1 : Disjoint W2 X1 := by
            rw [Finset.disjoint_left]; intro x hxW hxX
            exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxX).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).1
          have hdisj_W2X1_Z1 : Disjoint (W2 ∪ X1) Z1 := by
            rw [Finset.disjoint_left]; intro x hx hxZ
            have hnr := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxZ).1).2
            have hna := (Finset.mem_sdiff.mp hxZ).2
            rw [Finset.mem_union] at hx
            rcases hx with hw2 | hx1
            · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
            · exact hna (Finset.mem_inter.mp hx1).1
          have hsum1 : W2.card + X1.card + Z1.card ≤ 1 := by
            rw [← Finset.card_union_of_disjoint hdisj_W2X1, ← Finset.card_union_of_disjoint hdisj_W2X1_Z1]; exact hL1
          have bZ2 : (bipEdgesNoC c X1 Z2).card ≤ Z2.card :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (bipEdges_le_right_of_card_le_one X1 Z2 hX1)
          have bX12 : (bipEdgesNoC c X1 X2).card ≤ X2.card :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (bipEdges_le_right_of_card_le_one X1 X2 hX1)
          have bZ1 : (bipEdgesNoC c X2 Z1).card ≤ X2.card :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by rw [bipEdges_comm]; exact bipEdges_le_right_of_card_le_one Z1 X2 hZ1_le)
          by_cases hX10 : X1.card = 0
          · have eX12 : bipEdgesNoC c X1 X2 = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesNoC, bipEdges]
            have eZ2 : bipEdgesNoC c X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesNoC, bipEdges]
            rw [eX12, eZ2, Finset.card_empty] at hE_union
            by_cases hZ10 : Z1.card = 0
            · have eZ1 : bipEdgesNoC c X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hZ10]; ext e; simp [bipEdgesNoC, bipEdges]
              rw [eZ1, Finset.card_empty] at hE_union; omega
            · have hW20 : W2.card = 0 := by omega
              have eBW : bipEdgesNoC c B0 W2 = ∅ := by rw [Finset.card_eq_zero.mp hW20]; ext e; simp [bipEdgesNoC, bipEdges]
              have hZ1eq : Z1.card = 1 := by omega
              obtain ⟨z1, hz1⟩ := Finset.card_eq_one.mp hZ1eq
              by_cases hzc : z1 = c
              · have eZ1 : bipEdgesNoC c X2 Z1 = ∅ := by
                  rw [hz1, hzc]; ext e; simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
                  rintro ⟨⟨_, ⟨_, rfl⟩ | ⟨rfl, _⟩⟩, h1, h2⟩ <;> contradiction
                rw [eZ1, eBW, Finset.card_empty] at hE_union
                have : (B0.filter fun u => petersenAdj c u = true).card ≤ B0.card := Finset.card_le_card (Finset.filter_subset _ _)
                omega
              · have hX2_nc : (X2.filter fun u => petersenAdj c u = true).card ≤ 1 := by
                  have hsub_c : X2.filter (fun u => petersenAdj c u = true) ⊆
                      Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj z1 u = true := by
                    intro u hu; simp only [Finset.mem_filter] at hu
                    have hadj_z : petersenAdj z1 u = true := by
                      have huM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hu.1).1).1
                      have huS2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu.1).2).1
                      have hzS1 : z1 ∈ S1 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (by rw [hz1]; simp : z1 ∈ Z1)).1).1
                      cases ha : petersenAdj z1 u
                      · exfalso; have hf := hno z1 u (Or.inr huM0) ha
                        have ht : (l.and r).eval (pairInput z1 u) = true := by
                          simp only [MonoFormula.eval, Bool.and_eq_true]
                          exact ⟨l.eval_mono (singleInput z1) (pairInput z1 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hzS1).2,
                            r.eval_mono (singleInput u) (pairInput z1 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp huS2).2⟩
                        rw [hf] at ht; exact absurd ht (by decide)
                      · rfl
                    simp [hu.2, hadj_z]
                  exact le_trans (Finset.card_le_card hsub_c) (petersen_common_nbr_le_1 c z1 (Ne.symm hzc))
                have hB0_nc : (B0.filter fun u => petersenAdj c u = true).card ≤
                    (X2.filter fun u => petersenAdj c u = true).card + Y2.card := by
                  have hs : B0.filter (fun u => petersenAdj c u = true) ⊆
                      (X2.filter fun u => petersenAdj c u = true) ∪ Y2 := by
                    intro u hu; simp only [Finset.mem_filter, Finset.mem_union, X2, Y2, Finset.mem_inter, Finset.mem_sdiff] at hu ⊢
                    by_cases h : u ∈ S2'
                    · exact Or.inl ⟨⟨hu.1, h⟩, hu.2⟩
                    · exact Or.inr ⟨hu.1, h⟩
                  exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
                rw [eBW, Finset.card_empty] at hE_union
                omega
          · have hW20 : W2.card = 0 := by omega
            have hZ10 : Z1.card = 0 := by omega
            have eBW : bipEdgesNoC c B0 W2 = ∅ := by rw [Finset.card_eq_zero.mp hW20]; ext e; simp [bipEdgesNoC, bipEdges]
            have eZ1 : bipEdgesNoC c X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hZ10]; ext e; simp [bipEdgesNoC, bipEdges]
            rw [eBW, eZ1, Finset.card_empty] at hE_union
            have hX1eq : X1.card = 1 := by omega
            obtain ⟨x1, hx1⟩ := Finset.card_eq_one.mp hX1eq
            have hx1c : x1 ≠ c := fun h => hcA0 (h ▸ (Finset.mem_inter.mp (by rw [hx1]; simp : x1 ∈ X1)).1)
            have hX2_nc : (X2.filter fun u => petersenAdj c u = true).card ≤ 1 := by
              have hsub_c : X2.filter (fun u => petersenAdj c u = true) ⊆
                  Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj x1 u = true := by
                intro u hu; simp only [Finset.mem_filter] at hu
                have hadj_x : petersenAdj x1 u = true := by
                  have huM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hu.1).1).1
                  have huS2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu.1).2).1
                  have hxS1 : x1 ∈ S1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by rw [hx1]; simp : x1 ∈ X1)).2).1
                  cases ha : petersenAdj x1 u
                  · exfalso; have hf := hno x1 u (Or.inr huM0) ha
                    have ht : (l.and r).eval (pairInput x1 u) = true := by
                      simp only [MonoFormula.eval, Bool.and_eq_true]
                      exact ⟨l.eval_mono (singleInput x1) (pairInput x1 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hxS1).2,
                        r.eval_mono (singleInput u) (pairInput x1 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp huS2).2⟩
                    rw [hf] at ht; exact absurd ht (by decide)
                  · rfl
                simp [hu.2, hadj_x]
              exact le_trans (Finset.card_le_card hsub_c) (petersen_common_nbr_le_1 c x1 (Ne.symm hx1c))
            have hB0_nc : (B0.filter fun u => petersenAdj c u = true).card ≤
                (X2.filter fun u => petersenAdj c u = true).card + Y2.card := by
              have hs : B0.filter (fun u => petersenAdj c u = true) ⊆
                  (X2.filter fun u => petersenAdj c u = true) ∪ Y2 := by
                intro u hu; simp only [Finset.mem_filter, Finset.mem_union, X2, Y2, Finset.mem_inter, Finset.mem_sdiff] at hu ⊢
                by_cases h : u ∈ S2'
                · exact Or.inl ⟨⟨hu.1, h⟩, hu.2⟩
                · exact Or.inr ⟨hu.1, h⟩
              exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
            by_cases hX2_nc0 : (X2.filter fun u => petersenAdj c u = true).card = 0
            · omega
            · obtain ⟨x2, hx2f⟩ := Finset.card_pos.mp (by omega : 0 < (X2.filter fun u => petersenAdj c u = true).card)
              have hx2X2 : x2 ∈ X2 := (Finset.mem_filter.mp hx2f).1
              have hcx2 : petersenAdj c x2 = true := (Finset.mem_filter.mp hx2f).2
              have hx12_adj : petersenAdj x1 x2 = true := by
                have hx2M0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx2X2).1).1
                have hx2S2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2X2).2).1
                have hx1S1 : x1 ∈ S1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by rw [hx1]; simp : x1 ∈ X1)).2).1
                cases ha : petersenAdj x1 x2
                · exfalso; have hf := hno x1 x2 (Or.inr hx2M0) ha
                  have ht : (l.and r).eval (pairInput x1 x2) = true := by
                    simp only [MonoFormula.eval, Bool.and_eq_true]
                    exact ⟨l.eval_mono (singleInput x1) (pairInput x1 x2) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hx1S1).2,
                      r.eval_mono (singleInput x2) (pairInput x1 x2) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp hx2S2).2⟩
                  rw [hf] at ht; exact absurd ht (by decide)
                · rfl
              have hcx1 : petersenAdj c x1 = false := petersen_no_triangle c x2 x1 hcx2 (petersenAdj_symm x1 x2 hx12_adj)
              have hA0_ins : A0 = insert x1 Y1 := by
                ext z; simp only [Finset.mem_insert, Y1, Finset.mem_sdiff]; constructor
                · intro hz; by_cases hzs : z ∈ S1'
                  · left; have : z ∈ X1 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hx1, Finset.mem_singleton] at this; exact this
                  · exact Or.inr ⟨hz, hzs⟩
                · rintro (hz | ⟨hz, _⟩)
                  · subst z; exact (Finset.mem_inter.mp (by rw [hx1]; simp : x1 ∈ X1)).1
                  · exact hz
              have hx1Y1 : x1 ∉ Y1 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp (by rw [hx1]; simp : x1 ∈ X1)).2
              have hx2B0 : x2 ∈ B0 := (Finset.mem_inter.mp hx2X2).1
              have hx2c : x2 ≠ c := fun h => hcB0 (h ▸ hx2B0)
              have hx2_not_A0 : x2 ∉ A0 := Finset.disjoint_right.mp hAB_disj hx2B0
              have hx2W1 : x2 ∉ W1 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2X2).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
              have bAW' := bipEdgesNoC_of_ext c x2 x1 Y1 W1 (hA0_ins ▸ hcA0) hx2c hcx1 (petersenAdj_symm x1 x2 hx12_adj) hx1Y1 (hA0_ins ▸ hx2_not_A0) hx2W1 (hA0_ins ▸ hdisj_A0W1)
              rw [← hA0_ins] at bAW'
              omega
      · have hW1_le : W1.card ≤ 1 := le_trans (Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)) hR1
        have hX2_le : X2.card ≤ 1 := le_trans (Finset.card_le_card (Finset.subset_union_right.trans Finset.subset_union_left)) hR1
        have hZ2_le : Z2.card ≤ 1 := le_trans (Finset.card_le_card Finset.subset_union_right) hR1
        have hdisj_W1X2 : Disjoint W1 X2 := by
          rw [Finset.disjoint_left]; intro x hxW hxX
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxX).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).1
        have hdisj_W1X2_Z2 : Disjoint (W1 ∪ X2) Z2 := by
          rw [Finset.disjoint_left]; intro x hx hxZ
          have hnl := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxZ).1).2
          have hnb := (Finset.mem_sdiff.mp hxZ).2
          rw [Finset.mem_union] at hx
          rcases hx with hw1 | hx2
          · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
          · exact hnb (Finset.mem_inter.mp hx2).1
        have hsum1 : W1.card + X2.card + Z2.card ≤ 1 := by
          rw [← Finset.card_union_of_disjoint hdisj_W1X2, ← Finset.card_union_of_disjoint hdisj_W1X2_Z2]; exact hR1
        have bZ1 : (bipEdgesNoC c X2 Z1).card ≤ Z1.card :=
          le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (bipEdges_le_right_of_card_le_one X2 Z1 hX2_le)
        have bX12 : (bipEdgesNoC c X1 X2).card ≤ X1.card :=
          le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by rw [bipEdges_comm]; exact bipEdges_le_right_of_card_le_one X2 X1 hX2_le)
        have bZ2 : (bipEdgesNoC c X1 Z2).card ≤ X1.card :=
          le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by rw [bipEdges_comm]; exact bipEdges_le_right_of_card_le_one Z2 X1 hZ2_le)
        by_cases hX20 : X2.card = 0
        · have eX12 : bipEdgesNoC c X1 X2 = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesNoC, bipEdges]
          have eZ1 : bipEdgesNoC c X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesNoC, bipEdges]
          rw [eX12, eZ1, Finset.card_empty] at hE_union
          by_cases hZ20 : Z2.card = 0
          · have eZ2 : bipEdgesNoC c X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hZ20]; ext e; simp [bipEdgesNoC, bipEdges]
            rw [eZ2, Finset.card_empty] at hE_union; omega
          · have hW10 : W1.card = 0 := by omega
            have eAW : bipEdgesNoC c A0 W1 = ∅ := by rw [Finset.card_eq_zero.mp hW10]; ext e; simp [bipEdgesNoC, bipEdges]
            have hZ2eq : Z2.card = 1 := by omega
            obtain ⟨z2, hz2⟩ := Finset.card_eq_one.mp hZ2eq
            by_cases hzc : z2 = c
            · have eZ2 : bipEdgesNoC c X1 Z2 = ∅ := by
                rw [hz2, hzc]; ext e; simp only [bipEdgesNoC, bipEdges, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
                rintro ⟨⟨_, ⟨_, rfl⟩ | ⟨rfl, _⟩⟩, h1, h2⟩ <;> contradiction
              rw [eZ2, eAW, Finset.card_empty] at hE_union
              have : (A0.filter fun u => petersenAdj c u = true).card ≤ A0.card := Finset.card_le_card (Finset.filter_subset _ _)
              omega
            · have hX1_nc : (X1.filter fun u => petersenAdj c u = true).card ≤ 1 := by
                have hsub_c : X1.filter (fun u => petersenAdj c u = true) ⊆
                    Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj z2 u = true := by
                  intro u hu; simp only [Finset.mem_filter] at hu
                  have hadj_z : petersenAdj z2 u = true := by
                    have huM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hu.1).1).1
                    have huS1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu.1).2).1
                    have hzS2 : z2 ∈ S2 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (by rw [hz2]; simp : z2 ∈ Z2)).1).1
                    cases ha : petersenAdj z2 u
                    · exfalso; have hf := hno z2 u (Or.inr huM0) ha
                      have ht : (l.and r).eval (pairInput z2 u) = true := by
                        simp only [MonoFormula.eval, Bool.and_eq_true]
                        exact ⟨l.eval_mono (singleInput u) (pairInput z2 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp huS1).2,
                          r.eval_mono (singleInput z2) (pairInput z2 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hzS2).2⟩
                      rw [hf] at ht; exact absurd ht (by decide)
                    · rfl
                  simp [hu.2, hadj_z]
                exact le_trans (Finset.card_le_card hsub_c) (petersen_common_nbr_le_1 c z2 (Ne.symm hzc))
              have hA0_nc : (A0.filter fun u => petersenAdj c u = true).card ≤
                  (X1.filter fun u => petersenAdj c u = true).card + Y1.card := by
                have hs : A0.filter (fun u => petersenAdj c u = true) ⊆
                    (X1.filter fun u => petersenAdj c u = true) ∪ Y1 := by
                  intro u hu; simp only [Finset.mem_filter, Finset.mem_union, X1, Y1, Finset.mem_inter, Finset.mem_sdiff] at hu ⊢
                  by_cases h : u ∈ S1'
                  · exact Or.inl ⟨⟨hu.1, h⟩, hu.2⟩
                  · exact Or.inr ⟨hu.1, h⟩
                exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
              rw [eAW, Finset.card_empty] at hE_union
              omega
        · have hW10 : W1.card = 0 := by omega
          have hZ20 : Z2.card = 0 := by omega
          have eAW : bipEdgesNoC c A0 W1 = ∅ := by rw [Finset.card_eq_zero.mp hW10]; ext e; simp [bipEdgesNoC, bipEdges]
          have eZ2 : bipEdgesNoC c X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hZ20]; ext e; simp [bipEdgesNoC, bipEdges]
          rw [eAW, eZ2, Finset.card_empty] at hE_union
          have hX2eq : X2.card = 1 := by omega
          obtain ⟨x2, hx2⟩ := Finset.card_eq_one.mp hX2eq
          have hx2c : x2 ≠ c := fun h => hcB0 (h ▸ (Finset.mem_inter.mp (by rw [hx2]; simp : x2 ∈ X2)).1)
          have hX1_nc : (X1.filter fun u => petersenAdj c u = true).card ≤ 1 := by
            have hsub_c : X1.filter (fun u => petersenAdj c u = true) ⊆
                Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj x2 u = true := by
              intro u hu; simp only [Finset.mem_filter] at hu
              have hadj_x : petersenAdj x2 u = true := by
                have huM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hu.1).1).1
                have huS1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu.1).2).1
                have hxS2 : x2 ∈ S2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by rw [hx2]; simp : x2 ∈ X2)).2).1
                cases ha : petersenAdj x2 u
                · exfalso; have hf := hno x2 u (Or.inr huM0) ha
                  have ht : (l.and r).eval (pairInput x2 u) = true := by
                    simp only [MonoFormula.eval, Bool.and_eq_true]
                    exact ⟨l.eval_mono (singleInput u) (pairInput x2 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp huS1).2,
                      r.eval_mono (singleInput x2) (pairInput x2 u) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hxS2).2⟩
                  rw [hf] at ht; exact absurd ht (by decide)
                · rfl
              simp [hu.2, hadj_x]
            exact le_trans (Finset.card_le_card hsub_c) (petersen_common_nbr_le_1 c x2 (Ne.symm hx2c))
          have hA0_nc : (A0.filter fun u => petersenAdj c u = true).card ≤
              (X1.filter fun u => petersenAdj c u = true).card + Y1.card := by
            have hs : A0.filter (fun u => petersenAdj c u = true) ⊆
                (X1.filter fun u => petersenAdj c u = true) ∪ Y1 := by
              intro u hu; simp only [Finset.mem_filter, Finset.mem_union, X1, Y1, Finset.mem_inter, Finset.mem_sdiff] at hu ⊢
              by_cases h : u ∈ S1'
              · exact Or.inl ⟨⟨hu.1, h⟩, hu.2⟩
              · exact Or.inr ⟨hu.1, h⟩
            exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
          by_cases hX1_nc0 : (X1.filter fun u => petersenAdj c u = true).card = 0
          · omega
          · obtain ⟨x1, hx1f⟩ := Finset.card_pos.mp (by omega : 0 < (X1.filter fun u => petersenAdj c u = true).card)
            have hx1X1 : x1 ∈ X1 := (Finset.mem_filter.mp hx1f).1
            have hcx1 : petersenAdj c x1 = true := (Finset.mem_filter.mp hx1f).2
            have hx12_adj : petersenAdj x1 x2 = true := by
              have hx1M0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx1X1).1).1
              have hx1S1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx1X1).2).1
              have hx2S2 : x2 ∈ S2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by rw [hx2]; simp : x2 ∈ X2)).2).1
              cases ha : petersenAdj x1 x2
              · exfalso; have hf := hno x1 x2 (Or.inl hx1M0) ha
                have ht : (l.and r).eval (pairInput x1 x2) = true := by
                  simp only [MonoFormula.eval, Bool.and_eq_true]
                  exact ⟨l.eval_mono (singleInput x1) (pairInput x1 x2) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hx1S1).2,
                    r.eval_mono (singleInput x2) (pairInput x1 x2) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp hx2S2).2⟩
                rw [hf] at ht; exact absurd ht (by decide)
              · rfl
            have hcx2 : petersenAdj c x2 = false := petersen_no_triangle c x1 x2 hcx1 hx12_adj
            have hB0_ins : B0 = insert x2 Y2 := by
              ext z; simp only [Finset.mem_insert, Y2, Finset.mem_sdiff]; constructor
              · intro hz; by_cases hzs : z ∈ S2'
                · left; have : z ∈ X2 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hx2, Finset.mem_singleton] at this; exact this
                · exact Or.inr ⟨hz, hzs⟩
              · rintro (hz | ⟨hz, _⟩)
                · subst z; exact (Finset.mem_inter.mp (by rw [hx2]; simp : x2 ∈ X2)).1
                · exact hz
            have hx2Y2 : x2 ∉ Y2 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp (by rw [hx2]; simp : x2 ∈ X2)).2
            have hx1A0 : x1 ∈ A0 := (Finset.mem_inter.mp hx1X1).1
            have hx1c : x1 ≠ c := fun h => hcA0 (h ▸ hx1A0)
            have hx1_not_B0 : x1 ∉ B0 := Finset.disjoint_left.mp hAB_disj hx1A0
            have hx1W2 : x1 ∉ W2 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx1X1).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
            have bBW' := bipEdgesNoC_of_ext c x1 x2 Y2 W2 (hB0_ins ▸ hcB0) hx1c hcx2 hx12_adj hx2Y2 (hB0_ins ▸ hx1_not_B0) hx1W2 (hB0_ins ▸ hdisj_B0W2)
            rw [← hB0_ins] at bBW'
            omega
    change S.card + (edgesM0NoC c M0 (l.and r)).card +
      (((M0 ∩ (l.and r).orVars) \ S).filter fun u => petersenAdj c u = true).card ≤ l.leaves + r.leaves
    omega

theorem read2_and_sing1_bound (c : Fin 10) (l r : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, (l.and r).varCount v ≤ 2)
    (hle : ∀ x : Fin 10 → Bool, (l.and r).eval x = true → petersenFun x = true)
    (hSl : singleSet l = {c})
    (hMr : l.orVars ∩ r.orVars ⊆ singleSet r) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, (l.and r).eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ (l.and r).leaves := by
  let M := l.orVars ∩ r.orVars
  let Ur := r.orVars \ l.orVars
  have hcM : c ∉ M := by
    intro hc
    have hlc : l.eval (singleInput c) = true := (Finset.mem_filter.mp (by rw [hSl]; simp : c ∈ singleSet l)).2
    have hrc : r.eval (singleInput c) = true := (Finset.mem_filter.mp (hMr hc)).2
    have hp := hle (singleInput c) (by simp [MonoFormula.eval, hlc, hrc])
    rw [petersenFun_single] at hp; exact absurd hp (by decide)
  let E := edgesM0NoC c M l ∪ bipEdges {c} Ur ∪ bipEdges {c} M
  refine ⟨insert c M, E, ?_, ?_, ?_⟩
  · intro e he hev
    simp only [MonoFormula.eval, Bool.and_eq_true] at hev
    by_cases h1c : e.1 = c
    · subst h1c
      have h2r : e.2 ∈ r.orVars := by
        by_contra h
        have h0 := eval_pair_of_not_mem r e.1 e.2 (by
          intro hc_r; exact hcM (Finset.mem_inter.mpr ⟨singleSet_subset_orVars l (by rw [hSl]; simp), hc_r⟩))
        have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
        have h1 := eval_pair_of_not_mem r e.2 e.1 h
        change r.eval (pairInput e.2 e.1) = r.eval (singleInput e.1) at h1
        rw [← hsym] at h1
        have hrc : r.eval (singleInput e.1) = true := by rw [← h1]; exact hev.2
        exact hcM (Finset.mem_inter.mpr ⟨singleSet_subset_orVars l (by rw [hSl]; simp), singleSet_subset_orVars r (by simp [singleSet, hrc])⟩)
      by_cases h2l : e.2 ∈ l.orVars
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inl ⟨by simp, Finset.mem_inter.mpr ⟨h2l, h2r⟩⟩⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inl ⟨by simp, Finset.mem_sdiff.mpr ⟨h2r, h2l⟩⟩⟩))
    · by_cases h2c : e.2 = c
      · subst h2c
        have h1r : e.1 ∈ r.orVars := by
          by_contra h
          have h1 := eval_pair_of_not_mem r e.1 e.2 h
          change r.eval (pairInput e.1 e.2) = r.eval (singleInput e.2) at h1
          have hrc : r.eval (singleInput e.2) = true := by rw [← h1]; exact hev.2
          exact hcM (Finset.mem_inter.mpr ⟨singleSet_subset_orVars l (by rw [hSl]; simp), singleSet_subset_orVars r (by simp [singleSet, hrc])⟩)
        by_cases h1l : e.1 ∈ l.orVars
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inr ⟨Finset.mem_inter.mpr ⟨h1l, h1r⟩, by simp⟩⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inr ⟨Finset.mem_sdiff.mpr ⟨h1r, h1l⟩, by simp⟩⟩))
      · apply Finset.mem_union_left; apply Finset.mem_union_left
        have hnot1 : e.1 ∉ singleSet l := by rw [hSl]; simp [h1c]
        have hnot2 : e.2 ∉ singleSet l := by rw [hSl]; simp [h2c]
        have hmemM : e.1 ∈ M ∨ e.2 ∈ M := by
          have hl_or : e.1 ∈ l.orVars ∨ e.2 ∈ l.orVars := by
            by_contra h; push Not at h
            have hf := eval_pair_of_not_mem_both l e.1 e.2 h.1 h.2
            change l.eval (pairInput e.1 e.2) = false at hf; rw [hf] at hev; exact absurd hev.1 (by decide)
          have hr_or : e.1 ∈ r.orVars ∨ e.2 ∈ r.orVars := by
            by_contra h; push Not at h
            have hf := eval_pair_of_not_mem_both r e.1 e.2 h.1 h.2
            change r.eval (pairInput e.1 e.2) = false at hf; rw [hf] at hev; exact absurd hev.2 (by decide)
          have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
          rcases hl_or with h1l | h2l <;> rcases hr_or with h1r | h2r
          · exact Or.inl (Finset.mem_inter.mpr ⟨h1l, h1r⟩)
          · by_cases h2l' : e.2 ∈ l.orVars
            · exact Or.inr (Finset.mem_inter.mpr ⟨h2l', h2r⟩)
            · exfalso
              have h1 := eval_pair_of_not_mem l e.2 e.1 h2l'
              change l.eval (pairInput e.2 e.1) = l.eval (singleInput e.1) at h1; rw [← hsym] at h1
              exact hnot1 (by simp [singleSet, ← h1, hev.1])
          · by_cases h1l' : e.1 ∈ l.orVars
            · exact Or.inl (Finset.mem_inter.mpr ⟨h1l', h1r⟩)
            · exfalso
              have h1 := eval_pair_of_not_mem l e.1 e.2 h1l'
              change l.eval (pairInput e.1 e.2) = l.eval (singleInput e.2) at h1
              exact hnot2 (by simp [singleSet, ← h1, hev.1])
          · exact Or.inr (Finset.mem_inter.mpr ⟨h2l, h2r⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, hmemM, hev.1, hnot1, hnot2⟩, h1c, h2c⟩
  · intro e he
    simp only [E, Finset.mem_union] at he
    rcases he with (h1 | h2) | h3
    · rcases (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.1 with hm | hm
      · exact Or.inl (Finset.mem_insert_of_mem hm)
      · exact Or.inr (Finset.mem_insert_of_mem hm)
    · rcases (Finset.mem_filter.mp h2).2 with ⟨h, _⟩ | ⟨_, h⟩
      · simp at h; exact Or.inl (by rw [h]; simp)
      · simp at h; exact Or.inr (by rw [h]; simp)
    · rcases (Finset.mem_filter.mp h3).2 with ⟨h, _⟩ | ⟨_, h⟩
      · simp at h; exact Or.inl (by rw [h]; simp)
      · simp at h; exact Or.inr (by rw [h]; simp)
  · have hgolden : (singleSet l).card + (edgesM0NoC c M l).card +
        (((M ∩ l.orVars) \ singleSet l).filter fun u => petersenAdj c u = true).card ≤ l.leaves := by
      apply golden_read2_bound_with_c c M l hcM
      · intro v; have := hr2 v; simp [MonoFormula.varCount] at this; omega
      · intro m hm
        have hmr : m ∈ r.orVars := (Finset.mem_inter.mp hm).2
        rw [MonoFormula.mem_orVars_iff_varCount_pos] at hmr
        have := hr2 m; simp [MonoFormula.varCount] at this; omega
      · intro u v hm hadj
        have hr1 : r.eval (pairInput u v) = true := by
          rcases hm with hu | hv
          · exact r.eval_mono (singleInput u) (pairInput u v) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp (hMr hu)).2
          · exact r.eval_mono (singleInput v) (pairInput u v) (fun i hi => by
              simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp (hMr hv)).2
        cases hluv : l.eval (pairInput u v)
        · rfl
        · exfalso
          have hp := hle (pairInput u v) (by simp [MonoFormula.eval, hluv, hr1])
          rw [petersenFun_pair_iff] at hp; rw [hadj] at hp; exact absurd hp (by decide)
    have hM_eq : (M ∩ l.orVars) \ singleSet l = M := by
      ext u; simp only [Finset.mem_sdiff, Finset.mem_inter, M, hSl, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hl, hr⟩, _⟩, _⟩; exact ⟨hl, hr⟩
      · rintro ⟨hl, hr⟩; exact ⟨⟨⟨hl, hr⟩, hl⟩, fun h => hcM (h ▸ Finset.mem_inter.mpr ⟨hl, hr⟩)⟩
    rw [hM_eq, hSl, Finset.card_singleton] at hgolden
    have hbM : (bipEdges {c} M).card ≤ (M.filter fun u => petersenAdj c u = true).card := by
      have hs : bipEdges {c} M ⊆ (M.filter fun u => petersenAdj c u = true).image
          (fun u => if c < u then (c, u) else (u, c)) := by
        intro e he; simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
        have hlt := petersenEdges_lt e he.1; have hadj := petersenEdges_adj e he.1
        simp only [Finset.mem_image, Finset.mem_filter]
        rcases he.2 with ⟨rfl, h2⟩ | ⟨h1, rfl⟩
        · exact ⟨e.2, ⟨h2, hadj⟩, by simp [hlt]⟩
        · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
          exact ⟨e.1, ⟨h1, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
      exact le_trans (Finset.card_le_card hs) Finset.card_image_le
    have hbUr : (bipEdges {c} Ur).card ≤ Ur.card := bipEdges_le_right_of_card_le_one {c} Ur (by simp)
    have hr_le : M.card + Ur.card ≤ r.leaves := by
      have hd : Disjoint M Ur := by
        rw [Finset.disjoint_left]; intro u hm hu
        exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mp hm).1
      have hsub : M ∪ Ur ⊆ r.orVars := Finset.union_subset Finset.inter_subset_right Finset.sdiff_subset
      rw [← Finset.card_union_of_disjoint hd]
      exact le_trans (Finset.card_le_card hsub) r.orVars_card_le
    have hE_le : E.card ≤ (edgesM0NoC c M l).card + (bipEdges {c} Ur).card + (bipEdges {c} M).card := by
      change (edgesM0NoC c M l ∪ bipEdges {c} Ur ∪ bipEdges {c} M).card ≤ _
      have u1 := Finset.card_union_le (edgesM0NoC c M l ∪ bipEdges {c} Ur) (bipEdges {c} M)
      have u2 := Finset.card_union_le (edgesM0NoC c M l) (bipEdges {c} Ur)
      omega
    have hT_card : (insert c M).card = M.card + 1 := Finset.card_insert_of_notMem hcM
    simp only [MonoFormula.leaves]
    omega

def isCoveredOrTree : MonoFormula 10 → Prop
  | .var _ => True
  | .or l r => isCoveredOrTree l ∧ isCoveredOrTree r
  | .and l r =>
      (l.andDepth = 0 ∧ r.andDepth = 0) ∨
      ((singleSet l).card ≤ 1 ∧ l.orVars ∩ r.orVars ⊆ singleSet r) ∨
      ((singleSet r).card ≤ 1 ∧ l.orVars ∩ r.orVars ⊆ singleSet l) ∨
      (singleSet l = ∅ ∧ l.orVars ∩ r.orVars ∩ singleSet r = ∅) ∨
      (singleSet r = ∅ ∧ l.orVars ∩ r.orVars ∩ singleSet l = ∅)

lemma covered_or_tree_bound (F : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, F.varCount v ≤ 2)
    (hcov : isCoveredOrTree F)
    (hle : ∀ x : Fin 10 → Bool, F.eval x = true → petersenFun x = true) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, F.eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ F.leaves := by
  induction F with
  | var i =>
    exfalso; have h1 := hle (singleInput i) (by simp [MonoFormula.eval, singleInput])
    rw [petersenFun_single] at h1; exact absurd h1 (by decide)
  | or l r ihl ihr =>
    obtain ⟨hlc, hrc⟩ := hcov
    obtain ⟨T1, E1, hE1, hcov1, hbd1⟩ := ihl
      (fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega)
      hlc (fun x hx => hle x (by simp [MonoFormula.eval, hx]))
    obtain ⟨T2, E2, hE2, hcov2, hbd2⟩ := ihr
      (fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega)
      hrc (fun x hx => hle x (by simp [MonoFormula.eval, hx]))
    refine ⟨T1 ∪ T2, E1 ∪ E2, ?_, ?_, ?_⟩
    · intro e he hev; simp only [MonoFormula.eval, Bool.or_eq_true] at hev
      rw [Finset.mem_union]; rcases hev with hl | hr
      · exact Or.inl (hE1 e he hl)
      · exact Or.inr (hE2 e he hr)
    · intro e he; rw [Finset.mem_union] at he
      rcases he with h1 | h2
      · rcases hcov1 e h1 with hc | hc
        · exact Or.inl (Finset.mem_union_left _ hc)
        · exact Or.inr (Finset.mem_union_left _ hc)
      · rcases hcov2 e h2 with hc | hc
        · exact Or.inl (Finset.mem_union_right _ hc)
        · exact Or.inr (Finset.mem_union_right _ hc)
    · simp only [MonoFormula.leaves]
      have c1 := Finset.card_union_le E1 E2; have c2 := Finset.card_union_le T1 T2; omega
  | and l r _ _ =>
    rcases hcov with ⟨hdl, hdr⟩ | ⟨hSl1, hMr⟩ | ⟨hSr1, hMl⟩ | ⟨hSl0, hM0⟩ | ⟨hSr0, hM0⟩
    · exact sigma3_subformula_bound (l.and r) (by simp [MonoFormula.andDepth, hdl, hdr]) hle
    · by_cases hne : (singleSet l).Nonempty
      · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (le_antisymm hSl1 (Finset.card_pos.mpr hne))
        exact read2_and_sing1_bound c l r hr2 hle hc hMr
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        exact read2_and_clean_bound l r hr2 hle hne hMr
    · have hr2' : ∀ v, (r.and l).varCount v ≤ 2 := fun v => by
        have := hr2 v; simp [MonoFormula.varCount] at this ⊢; omega
      have hle' : ∀ x, (r.and l).eval x = true → petersenFun x = true := fun x hx =>
        hle x (by simpa [MonoFormula.eval, Bool.and_comm] using hx)
      have hMl' : r.orVars ∩ l.orVars ⊆ singleSet l := by rwa [Finset.inter_comm]
      by_cases hne : (singleSet r).Nonempty
      · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (le_antisymm hSr1 (Finset.card_pos.mpr hne))
        obtain ⟨T, E, hE, hcov, hbd⟩ := read2_and_sing1_bound c r l hr2' hle' hc hMl'
        exact ⟨T, E, fun e he hev => hE e he (by simpa [MonoFormula.eval, Bool.and_comm] using hev),
          hcov, by simpa [MonoFormula.leaves, Nat.add_comm] using hbd⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        obtain ⟨T, E, hE, hcov, hbd⟩ := read2_and_clean_bound r l hr2' hle' hne hMl'
        exact ⟨T, E, fun e he hev => hE e he (by simpa [MonoFormula.eval, Bool.and_comm] using hev),
          hcov, by simpa [MonoFormula.leaves, Nat.add_comm] using hbd⟩
    · exact read2_and_m0_empty_bound l r hr2 hSl0 hM0
    · have hr2' : ∀ v, (r.and l).varCount v ≤ 2 := fun v => by
        have := hr2 v; simp [MonoFormula.varCount] at this ⊢; omega
      have hM0' : r.orVars ∩ l.orVars ∩ singleSet l = ∅ := by rwa [Finset.inter_comm r.orVars l.orVars]
      obtain ⟨T, E, hE, hcov, hbd⟩ := read2_and_m0_empty_bound r l hr2' hSr0 hM0'
      exact ⟨T, E, fun e he hev => hE e he (by simpa [MonoFormula.eval, Bool.and_comm] using hev),
        hcov, by simpa [MonoFormula.leaves, Nat.add_comm] using hbd⟩

theorem petersen_covered_read2_leaves_ge_21 (F : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, F.varCount v ≤ 2)
    (hcov : isCoveredOrTree F)
    (hev : ∀ x : Fin 10 → Bool, F.eval x = petersenFun x) :
    21 ≤ F.leaves := by
  obtain ⟨T, E, hE, hcovT, hbd⟩ := covered_or_tree_bound F hr2 hcov (fun x hx => by rw [← hev x, hx])
  have hsub : petersenEdges ⊆ E := by
    intro e he; apply hE e he; rw [hev, petersenFun_pair_iff]; exact petersenEdges_adj e he
  have hE15 : 15 ≤ E.card := by rw [← petersenEdges_card]; exact Finset.card_le_card hsub
  have hT6 : 6 ≤ T.card := petersen_tau_ge_6 T (fun e he => hcovT e (hsub he))
  omega

theorem petersen_19_dichotomy_v5 (h : HasCircuitSize 10 petersenFun 19) :
    (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧
      wireFanOut 10 C 0 = 1) ∨
    (∃ l r : MonoFormula 10,
      (∀ x : Fin 10 → Bool, (l.or r).eval x = petersenFun x) ∧
      (l.or r).leaves = 20 ∧
      (∀ v : Fin 10, (l.or r).varCount v = 2) ∧
      2 ≤ (l.or r).andDepth ∧
      ¬ isCoveredOrTree (l.or r)) := by
  rcases petersen_19_dichotomy_v3 h with h1 | ⟨l, r, hev, hleaves, hcnt, hdepth⟩
  · exact Or.inl h1
  · right
    refine ⟨l, r, hev, hleaves, hcnt, hdepth, ?_⟩
    intro hcov
    have h21 := petersen_covered_read2_leaves_ge_21 (l.or r) (fun v => by rw [hcnt v]) hcov hev
    omega

/-!
### Closing World 2'' Completely: Unified Mixed `M0` / `M1` Bound

For any read-2 top-level `AND`-summand `l.and r ≤ petersenFun`, `petersen_biclique_star` forces
`(singleSet l).card ≤ 1 ∨ (singleSet r).card ≤ 1`. Swapping if needed, we always have
`singleSet l = ∅` or `singleSet l = {c}`. Partitioning `M = l.orVars ∩ r.orVars` into
`M0 = M ∩ singleSet r` and `M1 = (M \ singleSet r) \ singleSet l`, the unified induction
`golden_read2_bound_unified` bounds `E0` (edges touching `M0`), `E1` (edges inside `M1`),
a vertex cover `T1 ⊆ M1` of `E1`, and `N(c) ∩ (M0 ∪ M1)` simultaneously against
`l.leaves + (M1 ∩ l.orVars).card`. Combined with `r.leaves ≥ M0.card + M1.card + Ur.card`,
this gives `E.card + T.card ≤ (l.and r).leaves` for **every** read-2 `AND`-summand,
proving `petersen_read2_leaves_ge_21` and reducing `HasCircuitSize 10 petersenFun 19`
purely to World 1 (`petersen_19_world1_only`).
-/

def notCB (c? : Option (Fin 10)) (u : Fin 10) : Bool :=
  match c? with
  | none => true
  | some c => decide (u ≠ c)

def adjCB (c? : Option (Fin 10)) (u : Fin 10) : Bool :=
  match c? with
  | none => false
  | some c => petersenAdj c u

def edgesM0Opt (c? : Option (Fin 10)) (M0 : Finset (Fin 10)) (L : MonoFormula 10) : Finset (Fin 10 × Fin 10) :=
  (edgesM0 M0 L).filter fun e => notCB c? e.1 = true ∧ notCB c? e.2 = true

def edgesM1Opt (c? : Option (Fin 10)) (M1 : Finset (Fin 10)) (L : MonoFormula 10) : Finset (Fin 10 × Fin 10) :=
  petersenEdges.filter fun e =>
    e.1 ∈ M1 ∧ e.2 ∈ M1 ∧ L.eval (pairInput e.1 e.2) = true ∧
    e.1 ∉ singleSet L ∧ e.2 ∉ singleSet L ∧ notCB c? e.1 = true ∧ notCB c? e.2 = true

def bipEdgesOpt (c? : Option (Fin 10)) (A B : Finset (Fin 10)) : Finset (Fin 10 × Fin 10) :=
  (bipEdges A B).filter fun e => notCB c? e.1 = true ∧ notCB c? e.2 = true

lemma petersen_no_c4 : ∀ x1 x2 u v : Fin 10,
    petersenAdj x1 x2 = true → petersenAdj x2 u = true → petersenAdj x1 v = true →
    u ≠ v → u ≠ x1 → v ≠ x2 → petersenAdj u v = false := by
  decide

lemma petersen_incident_card : ∀ v : Fin 10,
    (petersenEdges.filter fun e => e.1 = v ∨ e.2 = v).card = 3 := by
  decide

lemma petersen_incident_inter_card : ∀ c z : Fin 10, c ≠ z →
    ((petersenEdges.filter fun e => e.1 = c ∨ e.2 = c) ∩
     (petersenEdges.filter fun e => e.1 = z ∨ e.2 = z)).card =
    if petersenAdj c z = true then 1 else 0 := by
  decide

lemma petersen_adj_card : ∀ c : Fin 10,
    (Finset.univ.filter fun u : Fin 10 => petersenAdj c u = true).card = 3 := by
  decide

lemma bipEdgesOpt_comm (c? : Option (Fin 10)) (A B : Finset (Fin 10)) :
    bipEdgesOpt c? A B = bipEdgesOpt c? B A := by
  simp only [bipEdgesOpt, bipEdges_comm]

lemma bipEdgesOpt_le_bipEdges (c? : Option (Fin 10)) (A B : Finset (Fin 10)) :
    (bipEdgesOpt c? A B).card ≤ (bipEdges A B).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma bipEdgesOpt_add_nc_le (c? : Option (Fin 10)) (A B : Finset (Fin 10))
    (hcA : ∀ u ∈ A, notCB c? u = true) (hdisj : Disjoint A B) :
    (bipEdgesOpt c? A B).card + (A.filter fun u => adjCB c? u = true).card ≤ A.card + 2 * B.card := by
  cases c? with
  | none =>
    have hnc : (A.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    rw [hnc, Finset.card_empty, add_zero]
    exact le_trans (bipEdgesOpt_le_bipEdges none A B) (bipEdges_le_add_two A B hdisj)
  | some c =>
    have hnot : c ∉ A := by intro hc; have := hcA c hc; simp [notCB] at this
    have heq : bipEdgesOpt (some c) A B = bipEdgesNoC c A B := by
      ext e; simp [bipEdgesOpt, bipEdgesNoC, notCB]
    rw [heq]
    exact bipEdgesNoC_add_nc_le c A B hnot hdisj

lemma bipEdgesOpt_of_ext (c? : Option (Fin 10)) (x1 x2 : Fin 10) (Y2 W2 : Finset (Fin 10))
    (hcY : ∀ u ∈ insert x2 Y2, notCB c? u = true)
    (hx1c : notCB c? x1 = true) (hx2N : adjCB c? x2 = false) (hx12 : petersenAdj x1 x2 = true)
    (hx2Y : x2 ∉ Y2) (hx1Y : x1 ∉ insert x2 Y2) (hx1W : x1 ∉ W2)
    (hdisj : Disjoint (insert x2 Y2) W2) :
    (bipEdgesOpt c? (insert x2 Y2) W2).card + ((insert x2 Y2).filter fun u => adjCB c? u = true).card ≤
      Y2.card + 2 * W2.card := by
  cases c? with
  | none =>
    have hnc : ((insert x2 Y2).filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    rw [hnc, Finset.card_empty, add_zero]
    exact le_trans (bipEdgesOpt_le_bipEdges none _ _)
      (bipEdges_le_add_two_of_ext x2 x1 Y2 W2 hx2Y hx1W (petersenAdj_symm x1 x2 hx12) hdisj)
  | some c =>
    have hcY' : c ∉ insert x2 Y2 := by intro h; have := hcY c h; simp [notCB] at this
    have hx1c' : x1 ≠ c := by simp [notCB] at hx1c; exact hx1c
    have heq : bipEdgesOpt (some c) (insert x2 Y2) W2 = bipEdgesNoC c (insert x2 Y2) W2 := by
      ext e; simp [bipEdgesOpt, bipEdgesNoC, notCB]
    rw [heq]
    exact bipEdgesNoC_of_ext c x1 x2 Y2 W2 hcY' hx1c' hx2N hx12 hx2Y hx1Y hx1W hdisj

lemma bipEdges_le_left_of_subset_nbr (x : Fin 10) (A B : Finset (Fin 10))
    (hxA : x ∉ A) (hBN : ∀ v ∈ B, petersenAdj x v = true) (hdisj : Disjoint A B) :
    (bipEdges A B).card ≤ A.card := by
  have hsub : bipEdges A B ⊆ A.biUnion fun u => bipEdges {u} B := by
    intro e he; simp only [bipEdges, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_singleton] at he ⊢
    rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨e.1, h1, he.1, Or.inl ⟨rfl, h2⟩⟩
    · exact ⟨e.2, h2, he.1, Or.inr ⟨h1, rfl⟩⟩
  calc (bipEdges A B).card
      ≤ (A.biUnion fun u => bipEdges {u} B).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ A, (bipEdges {u} B).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ A, 1 := Finset.sum_le_sum fun u hu => by
        have hux : u ≠ x := fun h => hxA (h ▸ hu)
        have hs : bipEdges {u} B ⊆ (Finset.univ.filter fun w => petersenAdj x w = true ∧ petersenAdj u w = true).image
            (fun w => if u < w then (u, w) else (w, u)) := by
          intro e he; simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
          have hlt := petersenEdges_lt e he.1; have hadj := petersenEdges_adj e he.1
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases he.2 with ⟨rfl, h2⟩ | ⟨h1, rfl⟩
          · exact ⟨e.2, ⟨hBN e.2 h2, hadj⟩, by simp [hlt]⟩
          · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
            exact ⟨e.1, ⟨hBN e.1 h1, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
        exact le_trans (Finset.card_le_card hs) (le_trans Finset.card_image_le (petersen_common_nbr_le_1 x u (Ne.symm hux)))
    _ = A.card := by simp

lemma bipEdgesOpt_x1_x1p_x2p_le (c? : Option (Fin 10)) (x1 : Fin 10) (X1' X2' : Finset (Fin 10))
    (hx1c : notCB c? x1 = true)
    (hx1_not1 : x1 ∉ X1') (hdisj : Disjoint X1' X2')
    (hX2N : ∀ v ∈ X2', petersenAdj x1 v = true) :
    (bipEdgesOpt c? {x1} X2').card + (bipEdgesOpt c? X1' X2').card + min X1'.card X2'.card +
      (X1'.filter fun u => adjCB c? u = true).card + (X2'.filter fun u => adjCB c? u = true).card ≤
      2 * X1'.card + 2 * X2'.card := by
  have he_x1 : (bipEdgesOpt c? {x1} X2').card ≤ X2'.card :=
    le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one {x1} X2' (by simp))
  have he_12 : (bipEdgesOpt c? X1' X2').card ≤ X1'.card :=
    le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_left_of_subset_nbr x1 X1' X2' hx1_not1 hX2N hdisj)
  have hnc1_le : (X1'.filter fun u => adjCB c? u = true).card ≤ X1'.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hnc2_le : (X2'.filter fun u => adjCB c? u = true).card ≤ X2'.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  cases c? with
  | none =>
    have h1 : (X1'.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    have h2 : (X2'.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    rw [h1, h2, Finset.card_empty]
    omega
  | some c =>
    have hnc1_le' : (X1'.filter fun u => petersenAdj c u = true).card ≤ X1'.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hnc2_le' : (X2'.filter fun u => petersenAdj c u = true).card ≤ X2'.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hx1c' : x1 ≠ c := by simp [notCB] at hx1c; exact hx1c
    have hnc2_le1 : (X2'.filter fun u => petersenAdj c u = true).card ≤ 1 := by
      have hs : X2'.filter (fun u => petersenAdj c u = true) ⊆
          Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj x1 u = true := by
        intro u hu; simp only [Finset.mem_filter] at hu; simp [hu.2, hX2N u hu.1]
      exact le_trans (Finset.card_le_card hs) (petersen_common_nbr_le_1 c x1 (Ne.symm hx1c'))
    have hnc_sum3 : (X1'.filter fun u => petersenAdj c u = true).card +
        (X2'.filter fun u => petersenAdj c u = true).card ≤ 3 := by
      have hd : Disjoint (X1'.filter fun u => petersenAdj c u = true)
          (X2'.filter fun u => petersenAdj c u = true) :=
        Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj
      rw [← Finset.card_union_of_disjoint hd]
      have hs : (X1'.filter fun u => petersenAdj c u = true) ∪
          (X2'.filter fun u => petersenAdj c u = true) ⊆
          Finset.univ.filter fun u => petersenAdj c u = true := by
        intro u hu; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        rcases hu with h | h <;> exact h.2
      exact le_trans (Finset.card_le_card hs) (by rw [petersen_adj_card c])
    change (bipEdgesOpt (some c) {x1} X2').card + (bipEdgesOpt (some c) X1' X2').card + min X1'.card X2'.card +
      (X1'.filter fun u => petersenAdj c u = true).card + (X2'.filter fun u => petersenAdj c u = true).card ≤
      2 * X1'.card + 2 * X2'.card
    by_cases hnc20 : (X2'.filter fun u => petersenAdj c u = true).card = 0
    · omega
    · by_cases hX1ge3 : 3 ≤ X1'.card
      · omega
      · by_cases hX10 : X1'.card = 0
        · omega
        · by_cases hX11 : X1'.card = 1
          · by_cases hX21 : X2'.card = 1
            · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hX11
              obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hX21
              have hcv : petersenAdj c v = true := by
                obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (X2'.filter fun u => petersenAdj c u = true).card)
                simp only [Finset.mem_filter, hv, Finset.mem_singleton] at hw
                rw [← hw.1]; exact hw.2
              by_cases hcu : petersenAdj c u = true
              · have he0 : bipEdgesOpt (some c) X1' X2' = ∅ := by
                  rw [hu, hv]; ext e
                  simp only [bipEdgesOpt, bipEdges, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
                  rintro ⟨⟨he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩, _⟩
                  · have hadj := petersenEdges_adj e he
                    rw [h1, h2] at hadj
                    have hf := petersen_no_triangle c u v hcu hadj
                    rw [hcv] at hf; exact absurd hf (by decide)
                  · have hadj := petersenEdges_adj e he
                    rw [h1, h2] at hadj
                    have hf := petersen_no_triangle c v u hcv hadj
                    rw [hcu] at hf; exact absurd hf (by decide)
                rw [he0, Finset.card_empty]; omega
              · have hnc10 : (X1'.filter fun u => petersenAdj c u = true).card = 0 := by
                  rw [hu]; simp [hcu]
                omega
            · omega
          · have hX12 : X1'.card = 2 := by omega
            by_cases hX2ge3 : 3 ≤ X2'.card
            · omega
            · by_cases hX21 : X2'.card = 1
              · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hX21
                have hcv : petersenAdj c v = true := by
                  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (X2'.filter fun u => petersenAdj c u = true).card)
                  simp only [Finset.mem_filter, hv, Finset.mem_singleton] at hw
                  rw [← hw.1]; exact hw.2
                have he_nc1 : (bipEdgesOpt (some c) X1' X2').card +
                    (X1'.filter fun u => petersenAdj c u = true).card ≤ X1'.card := by
                  let Nv := X1'.filter fun u => petersenAdj u v = true
                  let Nc1 := X1'.filter fun u => petersenAdj c u = true
                  have hd : Disjoint Nv Nc1 := by
                    rw [Finset.disjoint_left]; intro u h1 h2
                    simp only [Nv, Nc1, Finset.mem_filter] at h1 h2
                    have hf := petersen_no_triangle c u v h2.2 h1.2
                    rw [hcv] at hf; exact absurd hf (by decide)
                  have he_le : (bipEdgesOpt (some c) X1' X2').card ≤ Nv.card := by
                    have hs : bipEdgesOpt (some c) X1' X2' ⊆ Nv.image (fun u => if u < v then (u, v) else (v, u)) := by
                      intro e he; simp only [bipEdgesOpt, bipEdges, Finset.mem_filter, hv, Finset.mem_singleton] at he
                      have hlt := petersenEdges_lt e he.1.1; have hadj := petersenEdges_adj e he.1.1
                      simp only [Finset.mem_image, Nv, Finset.mem_filter]
                      rcases he.1.2 with ⟨h1, rfl⟩ | ⟨rfl, h2⟩
                      · exact ⟨e.1, ⟨h1, hadj⟩, by simp [hlt]⟩
                      · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
                        exact ⟨e.2, ⟨h2, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
                    exact le_trans (Finset.card_le_card hs) Finset.card_image_le
                  have hu : Nv ∪ Nc1 ⊆ X1' := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
                  have hsum := Finset.card_le_card hu
                  rw [Finset.card_union_of_disjoint hd] at hsum
                  change (bipEdgesOpt (some c) X1' X2').card + Nc1.card ≤ X1'.card
                  omega
                omega
              · have hX22 : X2'.card = 2 := by omega
                by_cases hnc12 : (X1'.filter fun u => petersenAdj c u = true).card ≤ 1
                · omega
                · have hnc1_eq2 : (X1'.filter fun u => petersenAdj c u = true).card = 2 := by omega
                  have hX1_sub_Nc : ∀ u ∈ X1', petersenAdj c u = true := by
                    have hfeq : X1'.filter (fun u => petersenAdj c u = true) = X1' :=
                      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
                    intro u hu; rw [← hfeq] at hu; exact (Finset.mem_filter.mp hu).2
                  obtain ⟨v1, hv1f⟩ := Finset.card_pos.mp (by omega : 0 < (X2'.filter fun u => petersenAdj c u = true).card)
                  have hv1X2 : v1 ∈ X2' := (Finset.mem_filter.mp hv1f).1
                  have hcv1 : petersenAdj c v1 = true := (Finset.mem_filter.mp hv1f).2
                  have hrem1 : (X2'.erase v1).card = 1 := by rw [Finset.card_erase_of_mem hv1X2, hX22]
                  obtain ⟨v2, hv2eq⟩ := Finset.card_eq_one.mp hrem1
                  have hv2X2 : v2 ∈ X2' := Finset.mem_of_mem_erase (by rw [hv2eq]; simp)
                  have hv2c : v2 ≠ c := by
                    intro h; subst h
                    have hadj := hX2N v2 hv2X2
                    have hf := petersen_no_triangle v2 v1 x1 hcv1 (petersenAdj_symm x1 v1 (hX2N v1 hv1X2))
                    rw [petersenAdj_symm x1 v2 hadj] at hf; exact absurd hf (by decide)
                  have he_le1 : (bipEdgesOpt (some c) X1' X2').card ≤ 1 := by
                    have hs : bipEdgesOpt (some c) X1' X2' ⊆
                        (Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj v2 u = true).image
                          (fun u => if u < v2 then (u, v2) else (v2, u)) := by
                      intro e he; simp only [bipEdgesOpt, bipEdges, Finset.mem_filter] at he
                      have hlt := petersenEdges_lt e he.1.1; have hadj := petersenEdges_adj e he.1.1
                      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                      rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                      · have h2ne : e.2 ≠ v1 := by
                          intro h; subst h
                          have hf := petersen_no_triangle c e.1 e.2 (hX1_sub_Nc e.1 h1) hadj
                          rw [hcv1] at hf; exact absurd hf (by decide)
                        have h2v2 : e.2 = v2 := by
                          have : e.2 ∈ X2'.erase v1 := Finset.mem_erase.mpr ⟨h2ne, h2⟩
                          rw [hv2eq, Finset.mem_singleton] at this; exact this
                        subst h2v2
                        exact ⟨e.1, ⟨hX1_sub_Nc e.1 h1, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hlt]⟩
                      · have h1ne : e.1 ≠ v1 := by
                          intro h; subst h
                          have hf := petersen_no_triangle c e.2 e.1 (hX1_sub_Nc e.2 h2) (petersenAdj_symm e.1 e.2 hadj)
                          rw [hcv1] at hf; exact absurd hf (by decide)
                        have h1v2 : e.1 = v2 := by
                          have : e.1 ∈ X2'.erase v1 := Finset.mem_erase.mpr ⟨h1ne, h1⟩
                          rw [hv2eq, Finset.mem_singleton] at this; exact this
                        subst h1v2
                        have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
                        exact ⟨e.2, ⟨hX1_sub_Nc e.2 h2, hadj⟩, by simp [hnot]⟩
                    exact le_trans (Finset.card_le_card hs)
                      (le_trans Finset.card_image_le (petersen_common_nbr_le_1 c v2 (Ne.symm hv2c)))
                  omega

lemma bipEdgesOpt_x1p_x2p_le_aux (c? : Option (Fin 10)) (X1' X2' : Finset (Fin 10))
    (hc1 : ∀ u ∈ X1', notCB c? u = true) (hc2 : ∀ u ∈ X2', notCB c? u = true)
    (hdisj : Disjoint X1' X2') (hle : X1'.card ≤ X2'.card) :
    (bipEdgesOpt c? X1' X2').card + (X1'.filter fun u => adjCB c? u = true).card +
      (X2'.filter fun u => adjCB c? u = true).card ≤ X1'.card + 2 * X2'.card := by
  cases c? with
  | none =>
    have h1 : (X1'.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    have h2 : (X2'.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    rw [h1, h2, Finset.card_empty, add_zero, add_zero]
    exact le_trans (bipEdgesOpt_le_bipEdges none _ _) (bipEdges_le_add_two X1' X2' hdisj)
  | some c =>
    have hc1' : c ∉ X1' := by intro h; have := hc1 c h; simp [notCB] at this
    have hc2' : c ∉ X2' := by intro h; have := hc2 c h; simp [notCB] at this
    change (bipEdgesOpt (some c) X1' X2').card + (X1'.filter fun u => petersenAdj c u = true).card +
      (X2'.filter fun u => petersenAdj c u = true).card ≤ X1'.card + 2 * X2'.card
    have hnc_sum3 : (X1'.filter fun u => petersenAdj c u = true).card +
        (X2'.filter fun u => petersenAdj c u = true).card ≤ 3 := by
      have hd : Disjoint (X1'.filter fun u => petersenAdj c u = true)
          (X2'.filter fun u => petersenAdj c u = true) :=
        Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj
      rw [← Finset.card_union_of_disjoint hd]
      have hs : (X1'.filter fun u => petersenAdj c u = true) ∪
          (X2'.filter fun u => petersenAdj c u = true) ⊆
          Finset.univ.filter fun u => petersenAdj c u = true := by
        intro u hu; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        rcases hu with h | h <;> exact h.2
      exact le_trans (Finset.card_le_card hs) (by rw [petersen_adj_card c])
    have htot9 : X1'.card + X2'.card ≤ 9 := by
      have hc_not : c ∉ X1' ∪ X2' := by simp [hc1', hc2']
      have hs : X1' ∪ X2' ⊆ Finset.univ.erase c := by
        intro z hz; exact Finset.mem_erase.mpr ⟨fun h => hc_not (h ▸ hz), Finset.mem_univ z⟩
      rw [← Finset.card_union_of_disjoint hdisj]
      exact le_trans (Finset.card_le_card hs) (by simp)
    by_cases h0 : X1'.card = 0
    · have he0 : bipEdgesOpt (some c) X1' X2' = ∅ := by
        rw [Finset.card_eq_zero.mp h0]; ext e; simp [bipEdgesOpt, bipEdges]
      have hnc10 : (X1'.filter fun u => petersenAdj c u = true).card = 0 := by
        rw [Finset.card_eq_zero.mp h0]; simp
      have hnc2 : (X2'.filter fun u => petersenAdj c u = true).card ≤ X2'.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rw [he0, Finset.card_empty]; omega
    · by_cases h1 : X1'.card = 1
      · have he : (bipEdgesOpt (some c) X1' X2').card ≤ X2'.card :=
          le_trans (bipEdgesOpt_le_bipEdges _ _ _) (bipEdges_le_right_of_card_le_one X1' X2' (by omega))
        by_cases hX21 : X2'.card = 1
        · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
          obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hX21
          have hnc1 : (X1'.filter fun w => petersenAdj c w = true).card ≤ 1 := by rw [hu]; exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
          have hnc2 : (X2'.filter fun w => petersenAdj c w = true).card ≤ 1 := by rw [hv]; exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
          omega
        · omega
      · by_cases h2 : X1'.card = 2
        · have he := le_trans (bipEdgesOpt_le_bipEdges (some c) _ _) (bipEdges_c4free_card2 X1' X2' hdisj h2)
          omega
        · by_cases h3 : X1'.card = 3
          · have he := le_trans (bipEdgesOpt_le_bipEdges (some c) _ _) (bipEdges_c4free_card3 X1' X2' hdisj h3)
            omega
          · have h4 : X1'.card = 4 := by omega
            by_cases hX24 : X2'.card = 4
            · let U := insert c (X1' ∪ X2')
              have hUcard : U.card = 9 := by
                have hc_not : c ∉ X1' ∪ X2' := by simp [hc1', hc2']
                rw [Finset.card_insert_of_notMem hc_not, Finset.card_union_of_disjoint hdisj]; omega
              have hrem : (Finset.univ \ U).Nonempty := by
                apply Finset.card_pos.mp
                rw [Finset.card_sdiff, Finset.inter_univ]; simp [hUcard]
              obtain ⟨z, hz⟩ := hrem
              have hzU : z ∉ U := (Finset.mem_sdiff.mp hz).2
              have hzc : z ≠ c := fun h => hzU (by rw [h]; exact Finset.mem_insert_self c _)
              have hz1 : z ∉ X1' := fun h => hzU (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
              have hz2 : z ∉ X2' := fun h => hzU (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
              let Ec := petersenEdges.filter fun e => e.1 = c ∨ e.2 = c
              let Ez := petersenEdges.filter fun e => e.1 = z ∨ e.2 = z
              have hd_e : Disjoint (bipEdgesOpt (some c) X1' X2') (Ec ∪ Ez) := by
                rw [Finset.disjoint_left]; intro e he heu
                simp only [bipEdgesOpt, bipEdges, Finset.mem_filter, notCB, decide_eq_true_eq] at he
                simp only [Ec, Ez, Finset.mem_union, Finset.mem_filter] at heu
                rcases heu with ⟨_, h | h⟩ | ⟨_, h | h⟩
                · exact he.2.1 h
                · exact he.2.2 h
                · rcases he.1.2 with ⟨h1, _⟩ | ⟨h1, _⟩
                  · exact hz1 (h ▸ h1)
                  · exact hz2 (h ▸ h1)
                · rcases he.1.2 with ⟨_, h2⟩ | ⟨_, h2⟩
                  · exact hz2 (h ▸ h2)
                  · exact hz1 (h ▸ h2)
              have hsub_p : bipEdgesOpt (some c) X1' X2' ∪ (Ec ∪ Ez) ⊆ petersenEdges :=
                Finset.union_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
                  (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
              have htot_e := Finset.card_le_card hsub_p
              rw [Finset.card_union_of_disjoint hd_e, petersenEdges_card] at htot_e
              have hEc3 : Ec.card = 3 := petersen_incident_card c
              have hEz3 : Ez.card = 3 := petersen_incident_card z
              have hEu := Finset.card_union_add_card_inter Ec Ez
              have hEi := petersen_incident_inter_card c z (Ne.symm hzc)
              change (Ec ∩ Ez).card = _ at hEi
              cases hcz : petersenAdj c z
              · have hEi0 : (Ec ∩ Ez).card = 0 := by rw [hEi, hcz]; simp
                omega
              · have hEi1 : (Ec ∩ Ez).card = 1 := by rw [hEi, hcz]; simp
                have hnc_le2 : (X1'.filter fun u => petersenAdj c u = true).card +
                    (X2'.filter fun u => petersenAdj c u = true).card ≤ 2 := by
                  have hd : Disjoint (X1'.filter fun u => petersenAdj c u = true)
                      (X2'.filter fun u => petersenAdj c u = true) :=
                    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj
                  rw [← Finset.card_union_of_disjoint hd]
                  have hs : (X1'.filter fun u => petersenAdj c u = true) ∪
                      (X2'.filter fun u => petersenAdj c u = true) ⊆
                      (Finset.univ.filter fun u => petersenAdj c u = true).erase z := by
                    intro u hu; simp only [Finset.mem_union, Finset.mem_filter] at hu
                    refine Finset.mem_erase.mpr ⟨?_, by rcases hu with h | h <;> simp [h.2]⟩
                    intro hzu; subst hzu; rcases hu with h | h
                    · exact hz1 h.1
                    · exact hz2 h.1
                  have hzin : z ∈ Finset.univ.filter fun u => petersenAdj c u = true := by simp [hcz]
                  calc ((X1'.filter fun u => petersenAdj c u = true) ∪ (X2'.filter fun u => petersenAdj c u = true)).card
                      ≤ ((Finset.univ.filter fun u => petersenAdj c u = true).erase z).card := Finset.card_le_card hs
                    _ = (Finset.univ.filter fun u => petersenAdj c u = true).card - 1 := Finset.card_erase_of_mem hzin
                    _ = 2 := by rw [petersen_adj_card c]
                omega
            · have hX25 : X2'.card = 5 := by omega
              by_cases hnc10 : (X1'.filter fun u => petersenAdj c u = true).card = 0
              · have hX1_noN : ∀ u ∈ X1', petersenAdj c u = false := by
                  intro u hu
                  cases hcu : petersenAdj c u
                  · rfl
                  · exfalso
                    have : u ∈ X1'.filter fun u => petersenAdj c u = true := Finset.mem_filter.mpr ⟨hu, hcu⟩
                    rw [Finset.card_eq_zero.mp hnc10] at this; exact Finset.notMem_empty u this
                have hex_edge : ∃ u ∈ X1', ∃ v ∈ X1', petersenAdj u v = true := by
                  let σ := petersenAut c
                  let A := X1'.image σ
                  have hAcard : A.card = 4 := by rw [Finset.card_image_of_injective X1' σ.injective, h4]
                  have hAsub : A ⊆ {2, 3, 6, 7, 8, 9} := by
                    intro y hy
                    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
                    have hu0 : σ u ≠ 0 := by intro h; exact hc1' (by have : u = c := σ.injective (by rw [h, petersenAut_apply]); exact this ▸ hu)
                    have h0u : petersenAdj 0 (σ u) = false := by
                      rw [← petersenAut_apply c, petersenAut_adj]; exact hX1_noN u hu
                    revert hu0 h0u; generalize σ u = w; revert w; decide
                  have hpart : A = (A ∩ {2, 3}) ∪ (A ∩ {6, 8}) ∪ (A ∩ {7, 9}) := by
                    ext y; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
                    constructor
                    · intro hy; have h6 := hAsub hy
                      simp only [Finset.mem_insert, Finset.mem_singleton] at h6
                      rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
                    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
                  have hd1 : Disjoint (A ∩ {2, 3}) (A ∩ {6, 8}) := by
                    rw [Finset.disjoint_left]; intro y h1 h2
                    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at h1 h2
                    rcases h1.2 with rfl | rfl <;> rcases h2.2 with h | h <;> exact absurd h (by decide)
                  have hd2 : Disjoint ((A ∩ {2, 3}) ∪ (A ∩ {6, 8})) (A ∩ {7, 9}) := by
                    rw [Finset.disjoint_left]; intro y h1 h2
                    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at h1 h2
                    rcases h1 with ⟨_, rfl | rfl⟩ | ⟨_, rfl | rfl⟩ <;> rcases h2.2 with h | h <;> exact absurd h (by decide)
                  have hsum : (A ∩ {2, 3}).card + (A ∩ {6, 8}).card + (A ∩ {7, 9}).card = 4 := by
                    rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2, ← hpart, hAcard]
                  have hex_pair : (2 ∈ A ∧ 3 ∈ A) ∨ (6 ∈ A ∧ 8 ∈ A) ∨ (7 ∈ A ∧ 9 ∈ A) := by
                    have hle2 : ∀ p q : Fin 10, p ≠ q → (A ∩ {p, q}).card ≤ 2 ∧ (2 ≤ (A ∩ {p, q}).card → p ∈ A ∧ q ∈ A) := by
                      intro p q hpq
                      refine ⟨le_trans (Finset.card_le_card Finset.inter_subset_right) (by rw [Finset.card_pair hpq]), fun h => ?_⟩
                      have heq : A ∩ {p, q} = {p, q} :=
                        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [Finset.card_pair hpq]; exact h)
                      exact ⟨(Finset.mem_inter.mp (heq ▸ Finset.mem_insert_self p {q})).1,
                        (Finset.mem_inter.mp (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q))).1⟩
                    have p1 := hle2 2 3 (by decide)
                    have p2 := hle2 6 8 (by decide)
                    have p3 := hle2 7 9 (by decide)
                    by_cases c1 : 2 ≤ (A ∩ {2, 3}).card
                    · exact Or.inl (p1.2 c1)
                    · by_cases c2 : 2 ≤ (A ∩ {6, 8}).card
                      · exact Or.inr (Or.inl (p2.2 c2))
                      · exact Or.inr (Or.inr (p3.2 (by omega)))
                  rcases hex_pair with ⟨h2, h3⟩ | ⟨h6, h8⟩ | ⟨h7, h9⟩
                  · obtain ⟨u, hu, hu2⟩ := Finset.mem_image.mp h2
                    obtain ⟨v, hv, hv3⟩ := Finset.mem_image.mp h3
                    exact ⟨u, hu, v, hv, by rw [← petersenAut_adj c, hu2, hv3]; decide⟩
                  · obtain ⟨u, hu, hu6⟩ := Finset.mem_image.mp h6
                    obtain ⟨v, hv, hv8⟩ := Finset.mem_image.mp h8
                    exact ⟨u, hu, v, hv, by rw [← petersenAut_adj c, hu6, hv8]; decide⟩
                  · obtain ⟨u, hu, hu7⟩ := Finset.mem_image.mp h7
                    obtain ⟨v, hv, hv9⟩ := Finset.mem_image.mp h9
                    exact ⟨u, hu, v, hv, by rw [← petersenAut_adj c, hu7, hv9]; decide⟩
                obtain ⟨u, hu1, v, hv1, huv⟩ := hex_edge
                have hv2 : v ∉ X2' := Finset.disjoint_left.mp hdisj hv1
                have he_u : (bipEdges {u} X2').card ≤ 2 := by
                  let N := Finset.univ.filter fun w : Fin 10 => petersenAdj u w = true
                  have hvN : v ∈ N := by simp [N, huv]
                  have hs : bipEdges {u} X2' ⊆ (N.erase v).image (fun w => if u < w then (u, w) else (w, u)) := by
                    intro e he; simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
                    have hlt := petersenEdges_lt e he.1; have hadj := petersenEdges_adj e he.1
                    simp only [Finset.mem_image, Finset.mem_erase, N, Finset.mem_filter, Finset.mem_univ, true_and]
                    rcases he.2 with ⟨rfl, hw⟩ | ⟨hw, rfl⟩
                    · exact ⟨e.2, ⟨fun h => hv2 (h ▸ hw), hadj⟩, by simp [hlt]⟩
                    · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
                      exact ⟨e.1, ⟨fun h => hv2 (h ▸ hw), petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
                  calc (bipEdges {u} X2').card
                      ≤ ((N.erase v).image _).card := Finset.card_le_card hs
                    _ ≤ (N.erase v).card := Finset.card_image_le
                    _ = N.card - 1 := Finset.card_erase_of_mem hvN
                    _ ≤ 2 := by have hN : N.card ≤ 3 := petersen_deg_le_3 u; omega
                have he_rest : (bipEdges (X1'.erase u) X2').card ≤ 9 := by
                  have h := bipEdges_le_three_left (X1'.erase u) X2' (Disjoint.mono_left (Finset.erase_subset _ _) hdisj)
                  rw [Finset.card_erase_of_mem hu1, h4] at h; exact h
                have hsub : bipEdges X1' X2' ⊆ bipEdges {u} X2' ∪ bipEdges (X1'.erase u) X2' := by
                  intro e he; simp only [bipEdges, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase] at he ⊢
                  rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · by_cases h : e.1 = u
                    · exact Or.inl ⟨he.1, Or.inl ⟨h, h2⟩⟩
                    · exact Or.inr ⟨he.1, Or.inl ⟨⟨h, h1⟩, h2⟩⟩
                  · by_cases h : e.2 = u
                    · exact Or.inl ⟨he.1, Or.inr ⟨h1, h⟩⟩
                    · exact Or.inr ⟨he.1, Or.inr ⟨h1, ⟨h, h2⟩⟩⟩
                have he_le11 := le_trans (bipEdgesOpt_le_bipEdges (some c) _ _)
                  (le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _))
                omega
              · obtain ⟨u, huf⟩ := Finset.card_pos.mp (by omega : 0 < (X1'.filter fun u => petersenAdj c u = true).card)
                have hu1 : u ∈ X1' := (Finset.mem_filter.mp huf).1
                have hcu : petersenAdj c u = true := (Finset.mem_filter.mp huf).2
                have he_u : (bipEdgesNoC c {u} X2').card ≤ 2 :=
                  bipEdgesNoC_nc_le_two_left c {u} X2' (fun y hy => by simp at hy; subst hy; exact hcu)
                    (Disjoint.mono_left (Finset.singleton_subset_iff.mpr hu1) hdisj)
                have he_rest : (bipEdges (X1'.erase u) X2').card ≤ 9 := by
                  have h := bipEdges_le_three_left (X1'.erase u) X2' (Disjoint.mono_left (Finset.erase_subset _ _) hdisj)
                  rw [Finset.card_erase_of_mem hu1, h4] at h; exact h
                have hsub : bipEdgesOpt (some c) X1' X2' ⊆ bipEdgesNoC c {u} X2' ∪ bipEdges (X1'.erase u) X2' := by
                  intro e he; simp only [bipEdgesOpt, bipEdgesNoC, bipEdges, Finset.mem_filter,
                    Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, notCB, decide_eq_true_eq] at he ⊢
                  rcases he.1.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · by_cases h : e.1 = u
                    · exact Or.inl ⟨⟨he.1.1, Or.inl ⟨h, h2⟩⟩, he.2⟩
                    · exact Or.inr ⟨he.1.1, Or.inl ⟨⟨h, h1⟩, h2⟩⟩
                  · by_cases h : e.2 = u
                    · exact Or.inl ⟨⟨he.1.1, Or.inr ⟨h1, h⟩⟩, he.2⟩
                    · exact Or.inr ⟨he.1.1, Or.inr ⟨h1, ⟨h, h2⟩⟩⟩
                have he_le11 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
                omega

lemma bipEdgesOpt_x1p_x2p_le (c? : Option (Fin 10)) (X1' X2' : Finset (Fin 10))
    (hc1 : ∀ u ∈ X1', notCB c? u = true) (hc2 : ∀ u ∈ X2', notCB c? u = true)
    (hdisj : Disjoint X1' X2') :
    (bipEdgesOpt c? X1' X2').card + min X1'.card X2'.card +
      (X1'.filter fun u => adjCB c? u = true).card + (X2'.filter fun u => adjCB c? u = true).card ≤
      2 * X1'.card + 2 * X2'.card := by
  by_cases hle : X1'.card ≤ X2'.card
  · have h := bipEdgesOpt_x1p_x2p_le_aux c? X1' X2' hc1 hc2 hdisj hle
    omega
  · have h := bipEdgesOpt_x1p_x2p_le_aux c? X2' X1' hc2 hc1 hdisj.symm (by omega)
    rw [bipEdgesOpt_comm] at h
    omega

lemma bipEdgesOpt_branch2_le (c? : Option (Fin 10)) (x : Fin 10) (X2 X2' : Finset (Fin 10))
    (hxc : notCB c? x = true) (hX2N : ∀ v ∈ X2, petersenAdj x v = true) :
    (bipEdgesOpt c? X2 {x}).card + (bipEdgesOpt c? {x} X2').card + min 1 X2'.card +
      (X2.filter fun u => adjCB c? u = true).card +
      (({x} : Finset (Fin 10)).filter fun u => adjCB c? u = true).card +
      (X2'.filter fun u => adjCB c? u = true).card ≤
      X2.card + 2 + 2 * X2'.card := by
  have he1 : (bipEdgesOpt c? X2 {x}).card ≤ X2.card := by
    rw [bipEdgesOpt_comm]
    exact le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one {x} X2 (by simp))
  have he2 : (bipEdgesOpt c? {x} X2').card ≤ X2'.card :=
    le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one {x} X2' (by simp))
  have hnc2' : (X2'.filter fun u => adjCB c? u = true).card ≤ X2'.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  cases c? with
  | none =>
    have h1 : (X2.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    have h2 : (({x} : Finset (Fin 10)).filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    have h3 : (X2'.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
    rw [h1, h2, h3, Finset.card_empty]
    omega
  | some c =>
    have hnc2'_c : (X2'.filter fun u => petersenAdj c u = true).card ≤ X2'.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hxc' : x ≠ c := by simp [notCB] at hxc; exact hxc
    have hnc_x_X2 : (X2.filter fun u => petersenAdj c u = true).card +
        (({x} : Finset (Fin 10)).filter fun u => petersenAdj c u = true).card ≤ 1 := by
      cases hcx : petersenAdj c x
      · have hx0 : (({x} : Finset (Fin 10)).filter fun u => petersenAdj c u = true).card = 0 := by simp [hcx]
        have hs : X2.filter (fun u => petersenAdj c u = true) ⊆
            Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj x u = true := by
          intro u hu; simp only [Finset.mem_filter] at hu; simp [hu.2, hX2N u hu.1]
        have h1 := le_trans (Finset.card_le_card hs) (petersen_common_nbr_le_1 c x (Ne.symm hxc'))
        omega
      · have hX20 : X2.filter (fun u => petersenAdj c u = true) = ∅ := by
          ext u; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
          rintro ⟨hu, hcu⟩
          have hf := petersen_no_triangle c x u hcx (hX2N u hu)
          rw [hcu] at hf; exact absurd hf (by decide)
        have hx1 : (({x} : Finset (Fin 10)).filter fun u => petersenAdj c u = true).card ≤ 1 :=
          le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
        rw [hX20, Finset.card_empty]; omega
    change (bipEdgesOpt (some c) X2 {x}).card + (bipEdgesOpt (some c) {x} X2').card + min 1 X2'.card +
      (X2.filter fun u => petersenAdj c u = true).card +
      (({x} : Finset (Fin 10)).filter fun u => petersenAdj c u = true).card +
      (X2'.filter fun u => petersenAdj c u = true).card ≤
      X2.card + 2 + 2 * X2'.card
    omega

set_option maxHeartbeats 1600000 in
theorem golden_read2_bound_unified (c? : Option (Fin 10)) (M0 M1 : Finset (Fin 10)) (L : MonoFormula 10)
    (hdisjM : Disjoint M0 M1)
    (hcM0 : ∀ u ∈ M0, notCB c? u = true)
    (hcM1 : ∀ u ∈ M1, notCB c? u = true)
    (hr2 : ∀ v : Fin 10, L.varCount v ≤ 2)
    (hM0 : ∀ m ∈ M0, L.varCount m ≤ 1)
    (hM1 : ∀ m ∈ M1, L.varCount m ≤ 1)
    (hno : ∀ u v : Fin 10, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → L.eval (pairInput u v) = false) :
    ∃ T1 : Finset (Fin 10),
      T1 ⊆ M1 ∧
      (∀ e ∈ edgesM1Opt c? M1 L, e.1 ∈ T1 ∨ e.2 ∈ T1) ∧
      (singleSet L).card + (edgesM0Opt c? M0 L).card + (edgesM1Opt c? M1 L).card + T1.card +
        ((((M0 ∪ M1) ∩ L.orVars) \ singleSet L).filter fun u => adjCB c? u = true).card ≤
        L.leaves + (M1 ∩ L.orVars).card := by
  induction L with
  | var i =>
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · intro e he
      simp only [edgesM1Opt, Finset.mem_filter, singleSet, Finset.mem_univ, true_and,
        MonoFormula.eval, pairInput, singleInput, decide_eq_true_eq] at he
      rcases he.2.2.2.1 with h | h
      · exact absurd h he.2.2.2.2.1
      · exact absurd h he.2.2.2.2.2.1
    · have hS : singleSet (MonoFormula.var i) = {i} := by
        ext v; simp [singleSet, MonoFormula.eval, singleInput, eq_comm]
      have hE0 : edgesM0Opt c? M0 (MonoFormula.var i) = ∅ := by
        ext e; simp only [edgesM0Opt, edgesM0, Finset.mem_filter, hS, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨⟨_, _, hev, h1, h2⟩, _⟩
        simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at hev
        rcases hev with h | h
        · exact h1 h.symm
        · exact h2 h.symm
      have hE1 : edgesM1Opt c? M1 (MonoFormula.var i) = ∅ := by
        ext e; simp only [edgesM1Opt, Finset.mem_filter, hS, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨_, _, _, hev, h1, h2, _⟩
        simp only [MonoFormula.eval, pairInput, decide_eq_true_eq] at hev
        rcases hev with h | h
        · exact h1 h.symm
        · exact h2 h.symm
      have hN : ((((M0 ∪ M1) ∩ (MonoFormula.var i).orVars) \ singleSet (MonoFormula.var i)).filter
          fun u => adjCB c? u = true) = ∅ := by
        ext u; simp [hS, MonoFormula.orVars]
      rw [hN, hS, hE0, hE1]; simp [MonoFormula.leaves]
  | or l r ihl ihr =>
    have hr2l : ∀ v, l.varCount v ≤ 2 := fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega
    have hr2r : ∀ v, r.varCount v ≤ 2 := fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega
    have hM0l : ∀ m ∈ M0, l.varCount m ≤ 1 := fun m hm => by have := hM0 m hm; simp [MonoFormula.varCount] at this; omega
    have hM0r : ∀ m ∈ M0, r.varCount m ≤ 1 := fun m hm => by have := hM0 m hm; simp [MonoFormula.varCount] at this; omega
    have hM1l : ∀ m ∈ M1, l.varCount m ≤ 1 := fun m hm => by have := hM1 m hm; simp [MonoFormula.varCount] at this; omega
    have hM1r : ∀ m ∈ M1, r.varCount m ≤ 1 := fun m hm => by have := hM1 m hm; simp [MonoFormula.varCount] at this; omega
    have hnol : ∀ u v, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → l.eval (pairInput u v) = false := by
      intro u v hm hadj; have h := hno u v hm hadj; simp [MonoFormula.eval] at h; exact h.1
    have hnor : ∀ u v, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → r.eval (pairInput u v) = false := by
      intro u v hm hadj; have h := hno u v hm hadj; simp [MonoFormula.eval] at h; exact h.2
    obtain ⟨T1l, hT1l_sub, hT1l_cov, hbdl⟩ := ihl hr2l hM0l hM1l hnol
    obtain ⟨T1r, hT1r_sub, hT1r_cov, hbdr⟩ := ihr hr2r hM0r hM1r hnor
    have hE1_sub : edgesM1Opt c? M1 (l.or r) ⊆ edgesM1Opt c? M1 l ∪ edgesM1Opt c? M1 r := by
      intro e he
      simp only [edgesM1Opt, Finset.mem_filter, Finset.mem_union, singleSet, Finset.mem_univ,
        true_and, MonoFormula.eval, Bool.or_eq_true, not_or] at he ⊢
      rcases he.2.2.2.1 with hl | hr
      · exact Or.inl ⟨he.1, he.2.1, he.2.2.1, hl, he.2.2.2.2.1.1, he.2.2.2.2.2.1.1, he.2.2.2.2.2.2⟩
      · exact Or.inr ⟨he.1, he.2.1, he.2.2.1, hr, he.2.2.2.2.1.2, he.2.2.2.2.2.1.2, he.2.2.2.2.2.2⟩
    refine ⟨T1l ∪ T1r, Finset.union_subset hT1l_sub hT1r_sub, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp (hE1_sub he) with hl | hr
      · rcases hT1l_cov e hl with h | h
        · exact Or.inl (Finset.mem_union_left _ h)
        · exact Or.inr (Finset.mem_union_left _ h)
      · rcases hT1r_cov e hr with h | h
        · exact Or.inl (Finset.mem_union_right _ h)
        · exact Or.inr (Finset.mem_union_right _ h)
    · have hS_sub : singleSet (l.or r) ⊆ singleSet l ∪ singleSet r := by
        intro v hv; simp only [singleSet, Finset.mem_filter, Finset.mem_univ, true_and,
          MonoFormula.eval, Bool.or_eq_true, Finset.mem_union] at hv ⊢; exact hv
      have hE0_sub : edgesM0Opt c? M0 (l.or r) ⊆ edgesM0Opt c? M0 l ∪ edgesM0Opt c? M0 r := by
        intro e he
        simp only [edgesM0Opt, edgesM0, Finset.mem_filter, Finset.mem_union, singleSet, Finset.mem_univ,
          true_and, MonoFormula.eval, Bool.or_eq_true, not_or] at he ⊢
        rcases he.1.2.2.1 with hl | hr
        · exact Or.inl ⟨⟨he.1.1, he.1.2.1, hl, he.1.2.2.2.1.1, he.1.2.2.2.2.1⟩, he.2⟩
        · exact Or.inr ⟨⟨he.1.1, he.1.2.1, hr, he.1.2.2.2.1.2, he.1.2.2.2.2.2⟩, he.2⟩
      have hN_sub : ((((M0 ∪ M1) ∩ (l.or r).orVars) \ singleSet (l.or r)).filter fun u => adjCB c? u = true) ⊆
          ((((M0 ∪ M1) ∩ l.orVars) \ singleSet l).filter fun u => adjCB c? u = true) ∪
          ((((M0 ∪ M1) ∩ r.orVars) \ singleSet r).filter fun u => adjCB c? u = true) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter, MonoFormula.orVars,
          Finset.mem_union, singleSet, Finset.mem_univ, true_and, MonoFormula.eval, Bool.or_eq_true, not_or] at hu ⊢
        rcases hu.1.1.2 with hl | hr
        · exact Or.inl ⟨⟨⟨hu.1.1.1, hl⟩, hu.1.2.1⟩, hu.2⟩
        · exact Or.inr ⟨⟨⟨hu.1.1.1, hr⟩, hu.1.2.2⟩, hu.2⟩
      have hM1_disj : Disjoint (M1 ∩ l.orVars) (M1 ∩ r.orVars) := by
        rw [Finset.disjoint_left]; intro m h1 h2
        have hm1 := (Finset.mem_inter.mp h1).1
        have hml := (Finset.mem_inter.mp h1).2
        have hmr := (Finset.mem_inter.mp h2).2
        rw [MonoFormula.mem_orVars_iff_varCount_pos] at hml hmr
        have h := hM1 m hm1; simp [MonoFormula.varCount] at h; omega
      have hM1_eq : (M1 ∩ l.orVars) ∪ (M1 ∩ r.orVars) = M1 ∩ (l.or r).orVars := by
        ext u; simp [MonoFormula.orVars, and_or_left]
      have hM1_card : (M1 ∩ (l.or r).orVars).card = (M1 ∩ l.orVars).card + (M1 ∩ r.orVars).card := by
        rw [← hM1_eq, Finset.card_union_of_disjoint hM1_disj]
      have c1 := le_trans (Finset.card_le_card hS_sub) (Finset.card_union_le _ _)
      have c2 := le_trans (Finset.card_le_card hE0_sub) (Finset.card_union_le _ _)
      have c3 := le_trans (Finset.card_le_card hE1_sub) (Finset.card_union_le _ _)
      have c4 := Finset.card_union_le T1l T1r
      have c5 := le_trans (Finset.card_le_card hN_sub) (Finset.card_union_le _ _)
      simp only [MonoFormula.leaves]
      omega
  | and l r _ _ =>
    let S1 := singleSet l
    let S2 := singleSet r
    let S := singleSet (l.and r)
    have hS_eq : S = S1 ∩ S2 := by ext v; simp [S, S1, S2, singleSet, MonoFormula.eval]
    let A0 := M0 ∩ l.orVars
    let B0 := M0 ∩ r.orVars
    let A1 := M1 ∩ l.orVars
    let B1 := M1 ∩ r.orVars
    have hAB0_disj : Disjoint A0 B0 := by
      rw [Finset.disjoint_left]; intro m h1 h2
      have hm := (Finset.mem_inter.mp h1).1
      have hml := (Finset.mem_inter.mp h1).2
      have hmr := (Finset.mem_inter.mp h2).2
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hml hmr
      have h := hM0 m hm; simp [MonoFormula.varCount] at h; omega
    have hAB1_disj : Disjoint A1 B1 := by
      rw [Finset.disjoint_left]; intro m h1 h2
      have hm := (Finset.mem_inter.mp h1).1
      have hml := (Finset.mem_inter.mp h1).2
      have hmr := (Finset.mem_inter.mp h2).2
      rw [MonoFormula.mem_orVars_iff_varCount_pos] at hml hmr
      have h := hM1 m hm; simp [MonoFormula.varCount] at h; omega
    have hA0_not_r : ∀ v ∈ A0, v ∉ r.orVars := fun v hv hr =>
      Finset.disjoint_left.mp hAB0_disj hv (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hr⟩)
    have hB0_not_l : ∀ v ∈ B0, v ∉ l.orVars := fun v hv hl =>
      Finset.disjoint_left.mp hAB0_disj (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hl⟩) hv
    have hA1_not_r : ∀ v ∈ A1, v ∉ r.orVars := fun v hv hr =>
      Finset.disjoint_left.mp hAB1_disj hv (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hr⟩)
    have hB1_not_l : ∀ v ∈ B1, v ∉ l.orVars := fun v hv hl =>
      Finset.disjoint_left.mp hAB1_disj (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hl⟩) hv
    have hA0A1_disj : Disjoint A0 A1 := Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisjM
    have hB0B1_disj : Disjoint B0 B1 := Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisjM
    let W1 := (l.orVars ∩ S2) \ S
    let W2 := (r.orVars ∩ S1) \ S
    let S1' := S1 \ r.orVars
    let S2' := S2 \ l.orVars
    let X1 := A0 ∩ S1'
    let Y1 := A0 \ S1'
    let X1' := A1 ∩ S1'
    let Y1' := A1 \ S1'
    let Z1 := S1' \ (A0 ∪ A1)
    let X2 := B0 ∩ S2'
    let Y2 := B0 \ S2'
    let X2' := B1 ∩ S2'
    let Y2' := B1 \ S2'
    let Z2 := S2' \ (B0 ∪ B1)
    have hS1_sub : S1 ⊆ l.orVars := singleSet_subset_orVars l
    have hS2_sub : S2 ⊆ r.orVars := singleSet_subset_orVars r
    have hM1_card : (M1 ∩ (l.and r).orVars).card = X1'.card + Y1'.card + X2'.card + Y2'.card := by
      have hu : A1 ∪ B1 = M1 ∩ (l.and r).orVars := by ext u; simp [A1, B1, MonoFormula.orVars, and_or_left]
      have hA1c : A1.card = X1'.card + Y1'.card := (Finset.card_inter_add_card_sdiff A1 S1').symm
      have hB1c : B1.card = X2'.card + Y2'.card := (Finset.card_inter_add_card_sdiff B1 S2').symm
      rw [← hu, Finset.card_union_of_disjoint hAB1_disj, hA1c, hB1c]; omega
    have hl_budget : S.card + W1.card + W2.card + X1.card + Y1.card + X1'.card + Y1'.card + Z1.card ≤ l.leaves := by
      have hnr_mem : ∀ x ∈ X1 ∪ Y1 ∪ X1' ∪ Y1' ∪ Z1, x ∉ r.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with (((h | h) | h) | h) | h
        · exact hA0_not_r x (Finset.mem_inter.mp h).1
        · exact hA0_not_r x (Finset.mem_sdiff.mp h).1
        · exact hA1_not_r x (Finset.mem_inter.mp h).1
        · exact hA1_not_r x (Finset.mem_sdiff.mp h).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2
      have hr_mem : ∀ x ∈ S ∪ W1 ∪ W2, x ∈ r.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with (h | h) | h
        · exact hS2_sub (Finset.mem_inter.mp (hS_eq ▸ h)).2
        · exact hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
      have d1 : Disjoint S W1 := by rw [Finset.disjoint_left]; intro x hx h2; exact (Finset.mem_sdiff.mp h2).2 hx
      have d2 : Disjoint (S ∪ W1) W2 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have h2' := Finset.mem_sdiff.mp h2; rw [Finset.mem_union] at hx
        rcases hx with hs | hw1
        · exact h2'.2 hs
        · exact h2'.2 (hS_eq ▸ Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h2'.1).2, (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2⟩)
      have d_sw_rest : Disjoint (S ∪ W1 ∪ W2) (X1 ∪ Y1 ∪ X1' ∪ Y1' ∪ Z1) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2; exact hnr_mem x hx2 (hr_mem x hx1)
      have dX1Y1 : Disjoint X1 Y1 := by rw [Finset.disjoint_left]; intro x h1 h2; exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
      have dX1'Y1' : Disjoint X1' Y1' := by rw [Finset.disjoint_left]; intro x h1 h2; exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
      have dA0A1' : Disjoint (X1 ∪ Y1) (X1' ∪ Y1') := by
        rw [Finset.disjoint_left]; intro x h1 h2
        have hxA0 : x ∈ A0 := by rcases Finset.mem_union.mp h1 with h | h; exact (Finset.mem_inter.mp h).1; exact (Finset.mem_sdiff.mp h).1
        have hxA1 : x ∈ A1 := by rcases Finset.mem_union.mp h2 with h | h; exact (Finset.mem_inter.mp h).1; exact (Finset.mem_sdiff.mp h).1
        exact Finset.disjoint_left.mp hA0A1_disj hxA0 hxA1
      have dZ1 : Disjoint (X1 ∪ Y1 ∪ (X1' ∪ Y1')) Z1 := by
        rw [Finset.disjoint_left]; intro x h1 h2
        have hnot := (Finset.mem_sdiff.mp h2).2
        simp only [Finset.mem_union] at h1 hnot
        rcases h1 with (h | h) | (h | h)
        · exact hnot (Or.inl (Finset.mem_inter.mp h).1)
        · exact hnot (Or.inl (Finset.mem_sdiff.mp h).1)
        · exact hnot (Or.inr (Finset.mem_inter.mp h).1)
        · exact hnot (Or.inr (Finset.mem_sdiff.mp h).1)
      have hsub : (S ∪ W1 ∪ W2) ∪ (X1 ∪ Y1 ∪ X1' ∪ Y1' ∪ Z1) ⊆ l.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with ((h | h) | h) | ((((h | h) | h) | h) | h)
        · exact hS1_sub (Finset.mem_inter.mp (hS_eq ▸ h)).1
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
        · exact hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact hS1_sub (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
      have hcard := le_trans (Finset.card_le_card hsub) l.orVars_card_le
      have hassoc : X1 ∪ Y1 ∪ X1' ∪ Y1' ∪ Z1 = (X1 ∪ Y1 ∪ (X1' ∪ Y1')) ∪ Z1 := by
        ext x; simp [or_assoc]
      rw [Finset.card_union_of_disjoint d_sw_rest, Finset.card_union_of_disjoint d2,
        Finset.card_union_of_disjoint d1, hassoc, Finset.card_union_of_disjoint dZ1,
        Finset.card_union_of_disjoint dA0A1', Finset.card_union_of_disjoint dX1Y1,
        Finset.card_union_of_disjoint dX1'Y1'] at hcard
      omega
    have hr_budget : S.card + W1.card + W2.card + X2.card + Y2.card + X2'.card + Y2'.card + Z2.card ≤ r.leaves := by
      have hnl_mem : ∀ x ∈ X2 ∪ Y2 ∪ X2' ∪ Y2' ∪ Z2, x ∉ l.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with (((h | h) | h) | h) | h
        · exact hB0_not_l x (Finset.mem_inter.mp h).1
        · exact hB0_not_l x (Finset.mem_sdiff.mp h).1
        · exact hB1_not_l x (Finset.mem_inter.mp h).1
        · exact hB1_not_l x (Finset.mem_sdiff.mp h).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2
      have hl_mem : ∀ x ∈ S ∪ W1 ∪ W2, x ∈ l.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with (h | h) | h
        · exact hS1_sub (Finset.mem_inter.mp (hS_eq ▸ h)).1
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
        · exact hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
      have d1 : Disjoint S W1 := by rw [Finset.disjoint_left]; intro x hx h2; exact (Finset.mem_sdiff.mp h2).2 hx
      have d2 : Disjoint (S ∪ W1) W2 := by
        rw [Finset.disjoint_left]; intro x hx h2
        have h2' := Finset.mem_sdiff.mp h2; rw [Finset.mem_union] at hx
        rcases hx with hs | hw1
        · exact h2'.2 hs
        · exact h2'.2 (hS_eq ▸ Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h2'.1).2, (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).2⟩)
      have d_sw_rest : Disjoint (S ∪ W1 ∪ W2) (X2 ∪ Y2 ∪ X2' ∪ Y2' ∪ Z2) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2; exact hnl_mem x hx2 (hl_mem x hx1)
      have dX2Y2 : Disjoint X2 Y2 := by rw [Finset.disjoint_left]; intro x h1 h2; exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
      have dX2'Y2' : Disjoint X2' Y2' := by rw [Finset.disjoint_left]; intro x h1 h2; exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
      have dB0B1' : Disjoint (X2 ∪ Y2) (X2' ∪ Y2') := by
        rw [Finset.disjoint_left]; intro x h1 h2
        have hxB0 : x ∈ B0 := by rcases Finset.mem_union.mp h1 with h | h; exact (Finset.mem_inter.mp h).1; exact (Finset.mem_sdiff.mp h).1
        have hxB1 : x ∈ B1 := by rcases Finset.mem_union.mp h2 with h | h; exact (Finset.mem_inter.mp h).1; exact (Finset.mem_sdiff.mp h).1
        exact Finset.disjoint_left.mp hB0B1_disj hxB0 hxB1
      have dZ2 : Disjoint (X2 ∪ Y2 ∪ (X2' ∪ Y2')) Z2 := by
        rw [Finset.disjoint_left]; intro x h1 h2
        have hnot := (Finset.mem_sdiff.mp h2).2
        simp only [Finset.mem_union] at h1 hnot
        rcases h1 with (h | h) | (h | h)
        · exact hnot (Or.inl (Finset.mem_inter.mp h).1)
        · exact hnot (Or.inl (Finset.mem_sdiff.mp h).1)
        · exact hnot (Or.inr (Finset.mem_inter.mp h).1)
        · exact hnot (Or.inr (Finset.mem_sdiff.mp h).1)
      have hsub : (S ∪ W1 ∪ W2) ∪ (X2 ∪ Y2 ∪ X2' ∪ Y2' ∪ Z2) ⊆ r.orVars := by
        intro x hx; simp only [Finset.mem_union] at hx
        rcases hx with ((h | h) | h) | ((((h | h) | h) | h) | h)
        · exact hS2_sub (Finset.mem_inter.mp (hS_eq ▸ h)).2
        · exact hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).2
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact hS2_sub (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
      have hcard := le_trans (Finset.card_le_card hsub) r.orVars_card_le
      have hassoc : X2 ∪ Y2 ∪ X2' ∪ Y2' ∪ Z2 = (X2 ∪ Y2 ∪ (X2' ∪ Y2')) ∪ Z2 := by
        ext x; simp [or_assoc]
      rw [Finset.card_union_of_disjoint d_sw_rest, Finset.card_union_of_disjoint d2,
        Finset.card_union_of_disjoint d1, hassoc, Finset.card_union_of_disjoint dZ2,
        Finset.card_union_of_disjoint dB0B1', Finset.card_union_of_disjoint dX2Y2,
        Finset.card_union_of_disjoint dX2'Y2'] at hcard
      omega
    have hE1_sub : edgesM1Opt c? M1 (l.and r) ⊆ bipEdgesOpt c? X1' X2' := by
      intro e he
      simp only [edgesM1Opt, Finset.mem_filter] at he
      obtain ⟨he_p, hm1, hm2, hev, hns1, hns2, hnc⟩ := he
      simp only [MonoFormula.eval, Bool.and_eq_true] at hev
      have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
      have hl_or : e.1 ∈ l.orVars ∨ e.2 ∈ l.orVars := by
        by_contra h; push Not at h
        have hf := eval_pair_of_not_mem_both l e.1 e.2 h.1 h.2
        change l.eval (pairInput e.1 e.2) = false at hf; rw [hf] at hev; exact absurd hev.1 (by decide)
      have hr_or : e.1 ∈ r.orVars ∨ e.2 ∈ r.orVars := by
        by_contra h; push Not at h
        have hf := eval_pair_of_not_mem_both r e.1 e.2 h.1 h.2
        change r.eval (pairInput e.1 e.2) = false at hf; rw [hf] at hev; exact absurd hev.2 (by decide)
      simp only [bipEdgesOpt, bipEdges, Finset.mem_filter]
      refine ⟨⟨he_p, ?_⟩, hnc⟩
      by_cases h1l : e.1 ∈ l.orVars
      · have h1A1 : e.1 ∈ A1 := Finset.mem_inter.mpr ⟨hm1, h1l⟩
        have h1nr : e.1 ∉ r.orVars := hA1_not_r e.1 h1A1
        have h2r : e.2 ∈ r.orVars := by rcases hr_or with h | h; exact absurd h h1nr; exact h
        have h2B1 : e.2 ∈ B1 := Finset.mem_inter.mpr ⟨hm2, h2r⟩
        have h2nl : e.2 ∉ l.orVars := hB1_not_l e.2 h2B1
        have hle1 : l.eval (singleInput e.1) = true := by
          have h0 := eval_pair_of_not_mem l e.2 e.1 h2nl
          change l.eval (pairInput e.2 e.1) = l.eval (singleInput e.1) at h0; rw [← h0, ← hsym]; exact hev.1
        have hre2 : r.eval (singleInput e.2) = true := by
          have h0 := eval_pair_of_not_mem r e.1 e.2 h1nr
          change r.eval (pairInput e.1 e.2) = r.eval (singleInput e.2) at h0; rw [← h0]; exact hev.2
        exact Or.inl ⟨Finset.mem_inter.mpr ⟨h1A1, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hle1], h1nr⟩⟩,
          Finset.mem_inter.mpr ⟨h2B1, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hre2], h2nl⟩⟩⟩
      · have h2l : e.2 ∈ l.orVars := by rcases hl_or with h | h; exact absurd h h1l; exact h
        have h2A1 : e.2 ∈ A1 := Finset.mem_inter.mpr ⟨hm2, h2l⟩
        have h2nr : e.2 ∉ r.orVars := hA1_not_r e.2 h2A1
        have h1r : e.1 ∈ r.orVars := by rcases hr_or with h | h; exact h; exact absurd h h2nr
        have h1B1 : e.1 ∈ B1 := Finset.mem_inter.mpr ⟨hm1, h1r⟩
        have hle2 : l.eval (singleInput e.2) = true := by
          have h0 := eval_pair_of_not_mem l e.1 e.2 h1l
          change l.eval (pairInput e.1 e.2) = l.eval (singleInput e.2) at h0; rw [← h0]; exact hev.1
        have hre1 : r.eval (singleInput e.1) = true := by
          have h0 := eval_pair_of_not_mem r e.2 e.1 h2nr
          change r.eval (pairInput e.2 e.1) = r.eval (singleInput e.1) at h0; rw [← h0, ← hsym]; exact hev.2
        exact Or.inr ⟨Finset.mem_inter.mpr ⟨h1B1, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hre1], h1l⟩⟩,
          Finset.mem_inter.mpr ⟨h2A1, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hle2], h2nr⟩⟩⟩
    have hE0_sub : edgesM0Opt c? M0 (l.and r) ⊆
        bipEdgesOpt c? A0 W1 ∪ bipEdgesOpt c? B0 W2 ∪ bipEdgesOpt c? X1 X2 ∪
        bipEdgesOpt c? X1 Z2 ∪ bipEdgesOpt c? X1 X2' ∪ bipEdgesOpt c? X2 Z1 ∪ bipEdgesOpt c? X2 X1' := by
      intro e he
      simp only [edgesM0Opt, Finset.mem_filter] at he
      obtain ⟨h1, hnc⟩ := he
      simp only [edgesM0, Finset.mem_filter] at h1
      have hdir : ∀ u v : Fin 10, (u, v) ∈ petersenEdges → u ∈ M0 →
          (l.and r).eval (pairInput u v) = true → u ∉ S → v ∉ S →
          (u, v) ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪
            bipEdges X1 Z2 ∪ bipEdges X1 X2' ∪ bipEdges X2 Z1 ∪ bipEdges X2 X1' := by
        intro u v he' hum huv hus hvs
        simp only [MonoFormula.eval, Bool.and_eq_true] at huv
        simp only [Finset.mem_union]
        by_cases hul : u ∈ l.orVars
        · have huA : u ∈ A0 := Finset.mem_inter.mpr ⟨hum, hul⟩
          have hunr : u ∉ r.orVars := hA0_not_r u huA
          have hrv : r.eval (singleInput v) = true := by
            have h0 := eval_pair_of_not_mem r u v hunr
            change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
          have hvS2 : v ∈ S2 := by simp [S2, singleSet, hrv]
          by_cases hvl : v ∈ l.orVars
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huA, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvl, hvS2⟩, hvs⟩⟩⟩))))))
          · have hvS2' : v ∈ S2' := Finset.mem_sdiff.mpr ⟨hvS2, hvl⟩
            have hlu : l.eval (singleInput u) = true := by
              have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
              have h0 := eval_pair_of_not_mem l v u hvl
              change l.eval (pairInput v u) = l.eval (singleInput u) at h0; rw [← h0, ← hsym]; exact huv.1
            have huX1 : u ∈ X1 := Finset.mem_inter.mpr ⟨huA, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hlu], hunr⟩⟩
            by_cases hvB0 : v ∈ B0
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX1, Finset.mem_inter.mpr ⟨hvB0, hvS2'⟩⟩⟩)))))
            · by_cases hvB1 : v ∈ B1
              · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX1, Finset.mem_inter.mpr ⟨hvB1, hvS2'⟩⟩⟩)))
              · exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX1, Finset.mem_sdiff.mpr ⟨hvS2', by simp [hvB0, hvB1]⟩⟩⟩))))
        · by_cases hur : u ∈ r.orVars
          · have huB : u ∈ B0 := Finset.mem_inter.mpr ⟨hum, hur⟩
            have hlv : l.eval (singleInput v) = true := by
              have h0 := eval_pair_of_not_mem l u v hul
              change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
            have hvS1 : v ∈ S1 := by simp [S1, singleSet, hlv]
            by_cases hvr : v ∈ r.orVars
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huB, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvr, hvS1⟩, hvs⟩⟩⟩))))))
            · have hvS1' : v ∈ S1' := Finset.mem_sdiff.mpr ⟨hvS1, hvr⟩
              have hru : r.eval (singleInput u) = true := by
                have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                have h0 := eval_pair_of_not_mem r v u hvr
                change r.eval (pairInput v u) = r.eval (singleInput u) at h0; rw [← h0, ← hsym]; exact huv.2
              have huX2 : u ∈ X2 := Finset.mem_inter.mpr ⟨huB, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hru], hul⟩⟩
              by_cases hvA0 : v ∈ A0
              · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨huX2, Finset.mem_inter.mpr ⟨hvA0, hvS1'⟩⟩⟩)))))
              · by_cases hvA1 : v ∈ A1
                · exact Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX2, Finset.mem_inter.mpr ⟨hvA1, hvS1'⟩⟩⟩)
                · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨huX2, Finset.mem_sdiff.mpr ⟨hvS1', by simp [hvA0, hvA1]⟩⟩⟩))
          · exfalso
            have hlv : l.eval (singleInput v) = true := by
              have h0 := eval_pair_of_not_mem l u v hul
              change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
            have hrv : r.eval (singleInput v) = true := by
              have h0 := eval_pair_of_not_mem r u v hur
              change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
            exact hvs (by simp [S, singleSet, MonoFormula.eval, hlv, hrv])
      have hrev : ∀ u v : Fin 10, (v, u) ∈ petersenEdges → u ∈ M0 →
          (l.and r).eval (pairInput u v) = true → u ∉ S → v ∉ S →
          (v, u) ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪
            bipEdges X1 Z2 ∪ bipEdges X1 X2' ∪ bipEdges X2 Z1 ∪ bipEdges X2 X1' := by
        intro u v he' hum huv hus hvs
        simp only [MonoFormula.eval, Bool.and_eq_true] at huv
        simp only [Finset.mem_union]
        by_cases hul : u ∈ l.orVars
        · have huA : u ∈ A0 := Finset.mem_inter.mpr ⟨hum, hul⟩
          have hunr : u ∉ r.orVars := hA0_not_r u huA
          have hrv : r.eval (singleInput v) = true := by
            have h0 := eval_pair_of_not_mem r u v hunr
            change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
          have hvS2 : v ∈ S2 := by simp [S2, singleSet, hrv]
          by_cases hvl : v ∈ l.orVars
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvl, hvS2⟩, hvs⟩, huA⟩⟩))))))
          · have hvS2' : v ∈ S2' := Finset.mem_sdiff.mpr ⟨hvS2, hvl⟩
            have hlu : l.eval (singleInput u) = true := by
              have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
              have h0 := eval_pair_of_not_mem l v u hvl
              change l.eval (pairInput v u) = l.eval (singleInput u) at h0; rw [← h0, ← hsym]; exact huv.1
            have huX1 : u ∈ X1 := Finset.mem_inter.mpr ⟨huA, Finset.mem_sdiff.mpr ⟨by simp [S1, singleSet, hlu], hunr⟩⟩
            by_cases hvB0 : v ∈ B0
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_inter.mpr ⟨hvB0, hvS2'⟩, huX1⟩⟩)))))
            · by_cases hvB1 : v ∈ B1
              · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_inter.mpr ⟨hvB1, hvS2'⟩, huX1⟩⟩)))
              · exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨hvS2', by simp [hvB0, hvB1]⟩, huX1⟩⟩))))
        · by_cases hur : u ∈ r.orVars
          · have huB : u ∈ B0 := Finset.mem_inter.mpr ⟨hum, hur⟩
            have hlv : l.eval (singleInput v) = true := by
              have h0 := eval_pair_of_not_mem l u v hul
              change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
            have hvS1 : v ∈ S1 := by simp [S1, singleSet, hlv]
            by_cases hvr : v ∈ r.orVars
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvr, hvS1⟩, hvs⟩, huB⟩⟩))))))
            · have hvS1' : v ∈ S1' := Finset.mem_sdiff.mpr ⟨hvS1, hvr⟩
              have hru : r.eval (singleInput u) = true := by
                have hsym : pairInput u v = pairInput v u := by funext i; simp [pairInput, or_comm]
                have h0 := eval_pair_of_not_mem r v u hvr
                change r.eval (pairInput v u) = r.eval (singleInput u) at h0; rw [← h0, ← hsym]; exact huv.2
              have huX2 : u ∈ X2 := Finset.mem_inter.mpr ⟨huB, Finset.mem_sdiff.mpr ⟨by simp [S2, singleSet, hru], hul⟩⟩
              by_cases hvA0 : v ∈ A0
              · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inl ⟨Finset.mem_inter.mpr ⟨hvA0, hvS1'⟩, huX2⟩⟩)))))
              · by_cases hvA1 : v ∈ A1
                · exact Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_inter.mpr ⟨hvA1, hvS1'⟩, huX2⟩⟩)
                · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he', Or.inr ⟨Finset.mem_sdiff.mpr ⟨hvS1', by simp [hvA0, hvA1]⟩, huX2⟩⟩))
          · exfalso
            have hlv : l.eval (singleInput v) = true := by
              have h0 := eval_pair_of_not_mem l u v hul
              change l.eval (pairInput u v) = l.eval (singleInput v) at h0; rw [← h0]; exact huv.1
            have hrv : r.eval (singleInput v) = true := by
              have h0 := eval_pair_of_not_mem r u v hur
              change r.eval (pairInput u v) = r.eval (singleInput v) at h0; rw [← h0]; exact huv.2
            exact hvs (by simp [S, singleSet, MonoFormula.eval, hlv, hrv])
      have hmem_raw : e ∈ bipEdges A0 W1 ∪ bipEdges B0 W2 ∪ bipEdges X1 X2 ∪
          bipEdges X1 Z2 ∪ bipEdges X1 X2' ∪ bipEdges X2 Z1 ∪ bipEdges X2 X1' := by
        rcases h1.2.1 with hm1 | hm2
        · exact hdir e.1 e.2 h1.1 hm1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2
        · have hsym : pairInput e.2 e.1 = pairInput e.1 e.2 := by funext i; simp [pairInput, or_comm]
          exact hrev e.2 e.1 h1.1 hm2 (by rw [hsym]; exact h1.2.2.1) h1.2.2.2.2 h1.2.2.2.1
      simp only [Finset.mem_union] at hmem_raw ⊢
      rcases hmem_raw with (((((h | h) | h) | h) | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨h, hnc⟩))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩))))
      · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩)))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩))
      · exact Or.inr (Finset.mem_filter.mpr ⟨h, hnc⟩)
    have hE0_union : (edgesM0Opt c? M0 (l.and r)).card ≤
        (bipEdgesOpt c? A0 W1).card + (bipEdgesOpt c? B0 W2).card + (bipEdgesOpt c? X1 X2).card +
        (bipEdgesOpt c? X1 Z2).card + (bipEdgesOpt c? X1 X2').card +
        (bipEdgesOpt c? X2 Z1).card + (bipEdgesOpt c? X2 X1').card := by
      have c0 := Finset.card_le_card hE0_sub
      have u1 := Finset.card_union_le (bipEdgesOpt c? A0 W1 ∪ bipEdgesOpt c? B0 W2 ∪ bipEdgesOpt c? X1 X2 ∪ bipEdgesOpt c? X1 Z2 ∪ bipEdgesOpt c? X1 X2' ∪ bipEdgesOpt c? X2 Z1) (bipEdgesOpt c? X2 X1')
      have u2 := Finset.card_union_le (bipEdgesOpt c? A0 W1 ∪ bipEdgesOpt c? B0 W2 ∪ bipEdgesOpt c? X1 X2 ∪ bipEdgesOpt c? X1 Z2 ∪ bipEdgesOpt c? X1 X2') (bipEdgesOpt c? X2 Z1)
      have u3 := Finset.card_union_le (bipEdgesOpt c? A0 W1 ∪ bipEdgesOpt c? B0 W2 ∪ bipEdgesOpt c? X1 X2 ∪ bipEdgesOpt c? X1 Z2) (bipEdgesOpt c? X1 X2')
      have u4 := Finset.card_union_le (bipEdgesOpt c? A0 W1 ∪ bipEdgesOpt c? B0 W2 ∪ bipEdgesOpt c? X1 X2) (bipEdgesOpt c? X1 Z2)
      have u5 := Finset.card_union_le (bipEdgesOpt c? A0 W1 ∪ bipEdgesOpt c? B0 W2) (bipEdgesOpt c? X1 X2)
      have u6 := Finset.card_union_le (bipEdgesOpt c? A0 W1) (bipEdgesOpt c? B0 W2)
      omega
    have hNc_le : ((((M0 ∪ M1) ∩ (l.and r).orVars) \ S).filter fun u => adjCB c? u = true).card ≤
        (A0.filter fun u => adjCB c? u = true).card + (B0.filter fun u => adjCB c? u = true).card +
        (X1'.filter fun u => adjCB c? u = true).card + (X2'.filter fun u => adjCB c? u = true).card +
        Y1'.card + Y2'.card := by
      have hs : ((((M0 ∪ M1) ∩ (l.and r).orVars) \ S).filter fun u => adjCB c? u = true) ⊆
          (A0.filter fun u => adjCB c? u = true) ∪ (B0.filter fun u => adjCB c? u = true) ∪
          (X1'.filter fun u => adjCB c? u = true) ∪ (X2'.filter fun u => adjCB c? u = true) ∪ Y1' ∪ Y2' := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union,
          MonoFormula.orVars, A0, B0, A1, B1, X1', Y1', X2', Y2'] at hu ⊢
        rcases hu.1.1.1 with hm0 | hm1
        · rcases hu.1.1.2 with hl | hr
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨hm0, hl⟩, hu.2⟩))))
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hm0, hr⟩, hu.2⟩))))
        · rcases hu.1.1.2 with hl | hr
          · by_cases h : u ∈ S1'
            · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨⟨hm1, hl⟩, h⟩, hu.2⟩)))
            · exact Or.inl (Or.inr ⟨⟨hm1, hl⟩, h⟩)
          · by_cases h : u ∈ S2'
            · exact Or.inl (Or.inl (Or.inr ⟨⟨⟨hm1, hr⟩, h⟩, hu.2⟩))
            · exact Or.inr ⟨⟨hm1, hr⟩, h⟩
      have c0 := Finset.card_le_card hs
      have u1 := Finset.card_union_le ((A0.filter fun u => adjCB c? u = true) ∪ (B0.filter fun u => adjCB c? u = true) ∪ (X1'.filter fun u => adjCB c? u = true) ∪ (X2'.filter fun u => adjCB c? u = true) ∪ Y1') Y2'
      have u2 := Finset.card_union_le ((A0.filter fun u => adjCB c? u = true) ∪ (B0.filter fun u => adjCB c? u = true) ∪ (X1'.filter fun u => adjCB c? u = true) ∪ (X2'.filter fun u => adjCB c? u = true)) Y1'
      have u3 := Finset.card_union_le ((A0.filter fun u => adjCB c? u = true) ∪ (B0.filter fun u => adjCB c? u = true) ∪ (X1'.filter fun u => adjCB c? u = true)) (X2'.filter fun u => adjCB c? u = true)
      have u4 := Finset.card_union_le ((A0.filter fun u => adjCB c? u = true) ∪ (B0.filter fun u => adjCB c? u = true)) (X1'.filter fun u => adjCB c? u = true)
      have u5 := Finset.card_union_le (A0.filter fun u => adjCB c? u = true) (B0.filter fun u => adjCB c? u = true)
      omega
    have hX1_adj : ∀ x ∈ X1, ∀ v ∈ W1 ∪ X2 ∪ X2' ∪ Z2, petersenAdj x v = true := by
      intro x hx v hv
      have hxM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      have hxS1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
      have hvS2 : v ∈ S2 := by
        simp only [Finset.mem_union] at hv
        rcases hv with ((h | h) | h) | h
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
      cases hadj : petersenAdj x v
      · exfalso
        have hf := hno x v (Or.inl hxM0) hadj
        have ht : (l.and r).eval (pairInput x v) = true := by
          simp only [MonoFormula.eval, Bool.and_eq_true]
          exact ⟨l.eval_mono (singleInput x) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hxS1).2,
            r.eval_mono (singleInput v) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp hvS2).2⟩
        rw [hf] at ht; exact absurd ht (by decide)
      · rfl
    have hX2_adj : ∀ x ∈ X2, ∀ v ∈ W2 ∪ X1 ∪ X1' ∪ Z1, petersenAdj x v = true := by
      intro x hx v hv
      have hxM0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      have hxS2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
      have hvS1 : v ∈ S1 := by
        simp only [Finset.mem_union] at hv
        rcases hv with ((h | h) | h) | h
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).1
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
      cases hadj : petersenAdj x v
      · exfalso
        have hf := hno x v (Or.inl hxM0) hadj
        have ht : (l.and r).eval (pairInput x v) = true := by
          simp only [MonoFormula.eval, Bool.and_eq_true]
          exact ⟨l.eval_mono (singleInput v) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp hvS1).2,
            r.eval_mono (singleInput x) (pairInput x v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp hxS2).2⟩
        rw [hf] at ht; exact absurd ht (by decide)
      · rfl
    have hbic1 : X1.card ≤ 1 ∨ (W1 ∪ X2 ∪ X2' ∪ Z2).card ≤ 1 := petersen_biclique_star X1 (W1 ∪ X2 ∪ X2' ∪ Z2) hX1_adj
    have hbic2 : X2.card ≤ 1 ∨ (W2 ∪ X1 ∪ X1' ∪ Z1).card ≤ 1 := petersen_biclique_star X2 (W2 ∪ X1 ∪ X1' ∪ Z1) hX2_adj
    have hdisj_A0W1 : Disjoint A0 W1 := by
      rw [Finset.disjoint_left]; intro x hxA hxW
      exact hA0_not_r x hxA (hS2_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).2)
    have hdisj_B0W2 : Disjoint B0 W2 := by
      rw [Finset.disjoint_left]; intro x hxB hxW
      exact hB0_not_l x hxB (hS1_sub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).2)
    have hdisj_X1'X2' : Disjoint X1' X2' := by
      rw [Finset.disjoint_left]; intro x h1 h2
      exact Finset.disjoint_left.mp hAB1_disj (Finset.mem_inter.mp h1).1 (Finset.mem_inter.mp h2).1
    have hA0_card : A0.card = X1.card + Y1.card := (Finset.card_inter_add_card_sdiff A0 S1').symm
    have hB0_card : B0.card = X2.card + Y2.card := (Finset.card_inter_add_card_sdiff B0 S2').symm
    have hcA0 : ∀ u ∈ A0, notCB c? u = true := fun u hu => hcM0 u (Finset.mem_inter.mp hu).1
    have hcB0 : ∀ u ∈ B0, notCB c? u = true := fun u hu => hcM0 u (Finset.mem_inter.mp hu).1
    have hcX1' : ∀ u ∈ X1', notCB c? u = true := fun u hu => hcM1 u (Finset.mem_inter.mp (Finset.mem_inter.mp hu).1).1
    have hcX2' : ∀ u ∈ X2', notCB c? u = true := fun u hu => hcM1 u (Finset.mem_inter.mp (Finset.mem_inter.mp hu).1).1
    have bAW := bipEdgesOpt_add_nc_le c? A0 W1 hcA0 hdisj_A0W1
    have bBW := bipEdgesOpt_add_nc_le c? B0 W2 hcB0 hdisj_B0W2
    let T1_def : Finset (Fin 10) := if X1'.card ≤ X2'.card then X1' else X2'
    have hT1_def_sub : T1_def ⊆ M1 := by
      dsimp only [T1_def]; split_ifs
      · exact Finset.inter_subset_left.trans Finset.inter_subset_left
      · exact Finset.inter_subset_left.trans Finset.inter_subset_left
    have hT1_def_cov : ∀ e ∈ edgesM1Opt c? M1 (l.and r), e.1 ∈ T1_def ∨ e.2 ∈ T1_def := by
      intro e he
      have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp (hE1_sub he)).1).2
      dsimp only [T1_def]; split_ifs
      · rcases hb with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2
      · rcases hb with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr h2
        · exact Or.inl h1
    have hT1_def_card : T1_def.card = min X1'.card X2'.card := by
      dsimp only [T1_def]; split_ifs with h <;> omega
    have hE1_le : (edgesM1Opt c? M1 (l.and r)).card ≤ (bipEdgesOpt c? X1' X2').card := Finset.card_le_card hE1_sub
    rcases hbic1 with hX1 | hR1
    · rcases hbic2 with hX2 | hL1
      · have bZ2 : (bipEdgesOpt c? X1 Z2).card ≤ Z2.card :=
          le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X1 Z2 hX1)
        have bZ1 : (bipEdgesOpt c? X2 Z1).card ≤ Z1.card :=
          le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X2 Z1 hX2)
        by_cases hX1ne : X1.Nonempty
        · obtain ⟨x1, hX1eq⟩ := Finset.card_eq_one.mp (le_antisymm hX1 (Finset.card_pos.mpr hX1ne))
          have hX1c : X1.card = 1 := by rw [hX1eq]; simp
          by_cases hX2ne : X2.Nonempty
          · obtain ⟨x2, hX2eq⟩ := Finset.card_eq_one.mp (le_antisymm hX2 (Finset.card_pos.mpr hX2ne))
            have hX2c : X2.card = 1 := by rw [hX2eq]; simp
            have hx1X1 : x1 ∈ X1 := by rw [hX1eq]; simp
            have hx2X2 : x2 ∈ X2 := by rw [hX2eq]; simp
            have hx12_adj : petersenAdj x1 x2 = true :=
              hX1_adj x1 hx1X1 x2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx2X2)))
            have hE1_empty : edgesM1Opt c? M1 (l.and r) = ∅ := by
              ext e; simp only [Finset.notMem_empty, iff_false]; intro he
              have hb := Finset.mem_filter.mp (Finset.mem_filter.mp (hE1_sub he)).1
              have hadj := petersenEdges_adj e hb.1
              rcases hb.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have h1a : petersenAdj x2 e.1 = true :=
                  hX2_adj x2 hx2X2 e.1 (Finset.mem_union_left _ (Finset.mem_union_right _ h1))
                have h2a : petersenAdj x1 e.2 = true :=
                  hX1_adj x1 hx1X1 e.2 (Finset.mem_union_left _ (Finset.mem_union_right _ h2))
                have hne : e.1 ≠ e.2 := ne_of_lt (petersenEdges_lt e hb.1)
                have h1x1 : e.1 ≠ x1 := fun h => Finset.disjoint_left.mp hA0A1_disj (Finset.mem_inter.mp hx1X1).1 (h ▸ (Finset.mem_inter.mp h1).1)
                have h2x2 : e.2 ≠ x2 := fun h => Finset.disjoint_left.mp hB0B1_disj (Finset.mem_inter.mp hx2X2).1 (h ▸ (Finset.mem_inter.mp h2).1)
                have hf := petersen_no_c4 x1 x2 e.1 e.2 hx12_adj h1a h2a hne h1x1 h2x2
                rw [hadj] at hf; exact absurd hf (by decide)
              · have h2a : petersenAdj x2 e.2 = true :=
                  hX2_adj x2 hx2X2 e.2 (Finset.mem_union_left _ (Finset.mem_union_right _ h2))
                have h1a : petersenAdj x1 e.1 = true :=
                  hX1_adj x1 hx1X1 e.1 (Finset.mem_union_left _ (Finset.mem_union_right _ h1))
                have hne : e.2 ≠ e.1 := Ne.symm (ne_of_lt (petersenEdges_lt e hb.1))
                have h2x1 : e.2 ≠ x1 := fun h => Finset.disjoint_left.mp hA0A1_disj (Finset.mem_inter.mp hx1X1).1 (h ▸ (Finset.mem_inter.mp h2).1)
                have h1x2 : e.1 ≠ x2 := fun h => Finset.disjoint_left.mp hB0B1_disj (Finset.mem_inter.mp hx2X2).1 (h ▸ (Finset.mem_inter.mp h1).1)
                have hf := petersen_no_c4 x1 x2 e.2 e.1 hx12_adj h2a h1a hne h2x1 h1x2
                rw [petersenAdj_symm e.1 e.2 hadj] at hf; exact absurd hf (by decide)
            have bX12 : (bipEdgesOpt c? X1 X2).card ≤ 1 := by
              have := le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X1 X2 hX1); omega
            have bX1X2' : (bipEdgesOpt c? X1 X2').card ≤ X2'.card :=
              le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X1 X2' hX1)
            have bX2X1' : (bipEdgesOpt c? X2 X1').card ≤ X1'.card :=
              le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X2 X1' hX2)
            have hncX1' : (X1'.filter fun u => adjCB c? u = true).card ≤ X1'.card := Finset.card_le_card (Finset.filter_subset _ _)
            have hncX2' : (X2'.filter fun u => adjCB c? u = true).card ≤ X2'.card := Finset.card_le_card (Finset.filter_subset _ _)
            have hA0_ins : A0 = insert x1 Y1 := by
              ext z; simp only [Finset.mem_insert, Y1, Finset.mem_sdiff]; constructor
              · intro hz; by_cases hzs : z ∈ S1'
                · left; have : z ∈ X1 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hX1eq, Finset.mem_singleton] at this; exact this
                · exact Or.inr ⟨hz, hzs⟩
              · rintro (hz | ⟨hz, _⟩); subst z; exact (Finset.mem_inter.mp hx1X1).1; exact hz
            have hB0_ins : B0 = insert x2 Y2 := by
              ext z; simp only [Finset.mem_insert, Y2, Finset.mem_sdiff]; constructor
              · intro hz; by_cases hzs : z ∈ S2'
                · left; have : z ∈ X2 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hX2eq, Finset.mem_singleton] at this; exact this
                · exact Or.inr ⟨hz, hzs⟩
              · rintro (hz | ⟨hz, _⟩); subst z; exact (Finset.mem_inter.mp hx2X2).1; exact hz
            have hx1Y1 : x1 ∉ Y1 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hx1X1).2
            have hx2Y2 : x2 ∉ Y2 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hx2X2).2
            have hx1A0 : x1 ∈ A0 := by rw [hA0_ins]; simp
            have hx2B0 : x2 ∈ B0 := by rw [hB0_ins]; simp
            have hx1_not_B0 : x1 ∉ B0 := Finset.disjoint_left.mp hAB0_disj hx1A0
            have hx2_not_A0 : x2 ∉ A0 := Finset.disjoint_right.mp hAB0_disj hx2B0
            have hx2W1 : x2 ∉ W1 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2X2).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
            have hx1W2 : x1 ∉ W2 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx1X1).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
            refine ⟨∅, Finset.empty_subset _, fun e he => by rw [hE1_empty] at he; exact absurd he (Finset.notMem_empty e), ?_⟩
            rw [hE1_empty, Finset.card_empty]
            change S.card + (edgesM0Opt c? M0 (l.and r)).card + 0 + 0 +
              ((((M0 ∪ M1) ∩ (l.and r).orVars) \ S).filter fun u => adjCB c? u = true).card ≤
              l.leaves + r.leaves + (M1 ∩ (l.and r).orVars).card
            cases hc1 : adjCB c? x1
            · have bAW' := bipEdgesOpt_of_ext c? x2 x1 Y1 W1 (hA0_ins ▸ hcA0) (hcB0 x2 hx2B0) hc1 (petersenAdj_symm x1 x2 hx12_adj) hx1Y1 (hA0_ins ▸ hx2_not_A0) hx2W1 (hA0_ins ▸ hdisj_A0W1)
              rw [← hA0_ins] at bAW'
              omega
            · have hc2 : adjCB c? x2 = false := by
                cases c? with
                | none => simp [adjCB] at hc1
                | some c => exact petersen_no_triangle c x1 x2 hc1 hx12_adj
              have bBW' := bipEdgesOpt_of_ext c? x1 x2 Y2 W2 (hB0_ins ▸ hcB0) (hcA0 x1 hx1A0) hc2 hx12_adj hx2Y2 (hB0_ins ▸ hx1_not_B0) hx1W2 (hB0_ins ▸ hdisj_B0W2)
              rw [← hB0_ins] at bBW'
              omega
          · rw [Finset.not_nonempty_iff_eq_empty] at hX2ne
            have eX12 : bipEdgesOpt c? X1 X2 = ∅ := by rw [hX2ne]; ext e; simp [bipEdgesOpt, bipEdges]
            have eX2Z1 : bipEdgesOpt c? X2 Z1 = ∅ := by rw [hX2ne]; ext e; simp [bipEdgesOpt, bipEdges]
            have eX2X1' : bipEdgesOpt c? X2 X1' = ∅ := by rw [hX2ne]; ext e; simp [bipEdgesOpt, bipEdges]
            rw [eX12, eX2Z1, eX2X1', Finset.card_empty] at hE0_union
            have hx1X1 : x1 ∈ X1 := by rw [hX1eq]; simp
            have hx1_not1 : x1 ∉ X1' := fun h => Finset.disjoint_left.mp hA0A1_disj (Finset.mem_inter.mp hx1X1).1 (Finset.mem_inter.mp h).1
            have bM1 := bipEdgesOpt_x1_x1p_x2p_le c? x1 X1' X2' (hcA0 x1 (Finset.mem_inter.mp hx1X1).1) hx1_not1 hdisj_X1'X2'
              (fun v hv => hX1_adj x1 hx1X1 v (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
            rw [← hX1eq] at bM1
            refine ⟨T1_def, hT1_def_sub, hT1_def_cov, ?_⟩
            change S.card + (edgesM0Opt c? M0 (l.and r)).card + (edgesM1Opt c? M1 (l.and r)).card + T1_def.card +
              ((((M0 ∪ M1) ∩ (l.and r).orVars) \ S).filter fun u => adjCB c? u = true).card ≤
              l.leaves + r.leaves + (M1 ∩ (l.and r).orVars).card
            omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hX1ne
          have eX12 : bipEdgesOpt c? X1 X2 = ∅ := by rw [hX1ne]; ext e; simp [bipEdgesOpt, bipEdges]
          have eX1Z2 : bipEdgesOpt c? X1 Z2 = ∅ := by rw [hX1ne]; ext e; simp [bipEdgesOpt, bipEdges]
          have eX1X2' : bipEdgesOpt c? X1 X2' = ∅ := by rw [hX1ne]; ext e; simp [bipEdgesOpt, bipEdges]
          rw [eX12, eX1Z2, eX1X2', Finset.card_empty] at hE0_union
          refine ⟨T1_def, hT1_def_sub, hT1_def_cov, ?_⟩
          change S.card + (edgesM0Opt c? M0 (l.and r)).card + (edgesM1Opt c? M1 (l.and r)).card + T1_def.card +
            ((((M0 ∪ M1) ∩ (l.and r).orVars) \ S).filter fun u => adjCB c? u = true).card ≤
            l.leaves + r.leaves + (M1 ∩ (l.and r).orVars).card
          by_cases hX2ne : X2.Nonempty
          · obtain ⟨x2, hX2eq⟩ := Finset.card_eq_one.mp (le_antisymm hX2 (Finset.card_pos.mpr hX2ne))
            have hx2X2 : x2 ∈ X2 := by rw [hX2eq]; simp
            have hx2_not2 : x2 ∉ X2' := fun h => Finset.disjoint_left.mp hB0B1_disj (Finset.mem_inter.mp hx2X2).1 (Finset.mem_inter.mp h).1
            have bM1 := bipEdgesOpt_x1_x1p_x2p_le c? x2 X2' X1' (hcB0 x2 (Finset.mem_inter.mp hx2X2).1) hx2_not2 hdisj_X1'X2'.symm
              (fun v hv => hX2_adj x2 hx2X2 v (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
            rw [← hX2eq, bipEdgesOpt_comm c? X2' X1'] at bM1
            omega
          · rw [Finset.not_nonempty_iff_eq_empty] at hX2ne
            have eX2Z1 : bipEdgesOpt c? X2 Z1 = ∅ := by rw [hX2ne]; ext e; simp [bipEdgesOpt, bipEdges]
            have eX2X1' : bipEdgesOpt c? X2 X1' = ∅ := by rw [hX2ne]; ext e; simp [bipEdgesOpt, bipEdges]
            rw [eX2Z1, eX2X1', Finset.card_empty] at hE0_union
            have bM1 := bipEdgesOpt_x1p_x2p_le c? X1' X2' hcX1' hcX2' hdisj_X1'X2'
            omega
      · -- hX1 : X1.card ≤ 1, hL1 : (W2 ∪ X1 ∪ X1' ∪ Z1).card ≤ 1
        have dW2X1 : Disjoint W2 X1 := by
          rw [Finset.disjoint_left]; intro x hxW hxX
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxX).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).1
        have dW2X1_X1' : Disjoint (W2 ∪ X1) X1' := by
          rw [Finset.disjoint_left]; intro x hx hx1'
          rw [Finset.mem_union] at hx
          rcases hx with hw2 | hx1
          · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx1').2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
          · exact Finset.disjoint_left.mp hA0A1_disj (Finset.mem_inter.mp hx1).1 (Finset.mem_inter.mp hx1').1
        have dAll_Z1 : Disjoint (W2 ∪ X1 ∪ X1') Z1 := by
          rw [Finset.disjoint_left]; intro x hx hxZ
          have hnr := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxZ).1).2
          have hnot := (Finset.mem_sdiff.mp hxZ).2
          simp only [Finset.mem_union] at hx hnot
          rcases hx with (hw2 | hx1) | hx1'
          · exact hnr (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw2).1).1
          · exact hnot (Or.inl (Finset.mem_inter.mp hx1).1)
          · exact hnot (Or.inr (Finset.mem_inter.mp hx1').1)
        have hsum1 : W2.card + X1.card + X1'.card + Z1.card ≤ 1 := by
          rw [← Finset.card_union_of_disjoint dW2X1, ← Finset.card_union_of_disjoint dW2X1_X1',
            ← Finset.card_union_of_disjoint dAll_Z1]; exact hL1
        refine ⟨T1_def, hT1_def_sub, hT1_def_cov, ?_⟩
        change S.card + (edgesM0Opt c? M0 (l.and r)).card + (edgesM1Opt c? M1 (l.and r)).card + T1_def.card +
          ((((M0 ∪ M1) ∩ (l.and r).orVars) \ S).filter fun u => adjCB c? u = true).card ≤
          l.leaves + r.leaves + (M1 ∩ (l.and r).orVars).card
        by_cases hX1'0 : X1'.card = 0
        · have eX2X1' : bipEdgesOpt c? X2 X1' = ∅ := by rw [Finset.card_eq_zero.mp hX1'0]; ext e; simp [bipEdgesOpt, bipEdges]
          have eX1'X2' : bipEdgesOpt c? X1' X2' = ∅ := by rw [Finset.card_eq_zero.mp hX1'0]; ext e; simp [bipEdgesOpt, bipEdges]
          have hncX1'0 : (X1'.filter fun u => adjCB c? u = true).card = 0 := by rw [Finset.card_eq_zero.mp hX1'0]; simp
          rw [eX2X1', Finset.card_empty] at hE0_union
          rw [eX1'X2', Finset.card_empty] at hE1_le
          have bZ2 : (bipEdgesOpt c? X1 Z2).card ≤ Z2.card :=
            le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X1 Z2 hX1)
          have bX1X2' : (bipEdgesOpt c? X1 X2').card ≤ X2'.card :=
            le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X1 X2' hX1)
          have bX12 : (bipEdgesOpt c? X1 X2).card ≤ X2.card :=
            le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X1 X2 hX1)
          have bZ1 : (bipEdgesOpt c? X2 Z1).card ≤ X2.card := by
            rw [bipEdgesOpt_comm]; exact le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one Z1 X2 (by omega))
          have hncX2' : (X2'.filter fun u => adjCB c? u = true).card ≤ X2'.card := Finset.card_le_card (Finset.filter_subset _ _)
          by_cases hX10 : X1.card = 0
          · have eX12 : bipEdgesOpt c? X1 X2 = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesOpt, bipEdges]
            have eZ2 : bipEdgesOpt c? X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesOpt, bipEdges]
            have eX1X2' : bipEdgesOpt c? X1 X2' = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesOpt, bipEdges]
            rw [eX12, eZ2, eX1X2', Finset.card_empty] at hE0_union
            by_cases hZ10 : Z1.card = 0
            · have eZ1 : bipEdgesOpt c? X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hZ10]; ext e; simp [bipEdgesOpt, bipEdges]
              rw [eZ1, Finset.card_empty] at hE0_union; omega
            · have hW20 : W2.card = 0 := by omega
              have eBW : bipEdgesOpt c? B0 W2 = ∅ := by rw [Finset.card_eq_zero.mp hW20]; ext e; simp [bipEdgesOpt, bipEdges]
              have hZ1eq : Z1.card = 1 := by omega
              obtain ⟨z1, hz1⟩ := Finset.card_eq_one.mp hZ1eq
              cases c? with
              | none =>
                have hB0nc : (B0.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
                rw [hB0nc, Finset.card_empty] at hNc_le; rw [eBW, Finset.card_empty] at hE0_union; omega
              | some c =>
                by_cases hzc : z1 = c
                · have eZ1 : bipEdgesOpt (some c) X2 Z1 = ∅ := by
                    rw [hz1, hzc]; ext e; simp only [bipEdgesOpt, bipEdges, notCB, decide_eq_true_eq, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
                    rintro ⟨⟨_, ⟨_, rfl⟩ | ⟨rfl, _⟩⟩, h1, h2⟩ <;> contradiction
                  rw [eZ1, eBW, Finset.card_empty] at hE0_union
                  have : (B0.filter fun u => adjCB (some c) u = true).card ≤ B0.card := Finset.card_le_card (Finset.filter_subset _ _)
                  omega
                · have hX2_nc : (X2.filter fun u => petersenAdj c u = true).card ≤ 1 := by
                    have hs : X2.filter (fun u => petersenAdj c u = true) ⊆
                        Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj z1 u = true := by
                      intro u hu; simp only [Finset.mem_filter] at hu
                      have hz := hX2_adj u hu.1 z1 (Finset.mem_union_right _ (by rw [hz1]; simp))
                      simp [hu.2, petersenAdj_symm u z1 hz]
                    exact le_trans (Finset.card_le_card hs) (petersen_common_nbr_le_1 c z1 (Ne.symm hzc))
                  have hB0_nc : (B0.filter fun u => adjCB (some c) u = true).card ≤
                      (X2.filter fun u => petersenAdj c u = true).card + Y2.card := by
                    have hs : B0.filter (fun u => adjCB (some c) u = true) ⊆
                        (X2.filter fun u => petersenAdj c u = true) ∪ Y2 := by
                      intro u hu
                      obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
                      simp only [adjCB] at hu2
                      simp only [Finset.mem_union, Finset.mem_filter, X2, Y2, Finset.mem_inter, Finset.mem_sdiff]
                      by_cases h : u ∈ S2'
                      · exact Or.inl ⟨⟨hu1, h⟩, hu2⟩
                      · exact Or.inr ⟨hu1, h⟩
                    exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
                  rw [eBW, Finset.card_empty] at hE0_union; omega
          · have hW20 : W2.card = 0 := by omega
            have hZ10 : Z1.card = 0 := by omega
            have eBW : bipEdgesOpt c? B0 W2 = ∅ := by rw [Finset.card_eq_zero.mp hW20]; ext e; simp [bipEdgesOpt, bipEdges]
            have eZ1 : bipEdgesOpt c? X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hZ10]; ext e; simp [bipEdgesOpt, bipEdges]
            rw [eBW, eZ1, Finset.card_empty] at hE0_union
            have hX1eq : X1.card = 1 := by omega
            obtain ⟨x1, hx1⟩ := Finset.card_eq_one.mp hX1eq
            have hx1X1 : x1 ∈ X1 := by rw [hx1]; simp
            cases c? with
            | none =>
              have hB0nc : (B0.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
              rw [hB0nc, Finset.card_empty] at hNc_le; omega
            | some c =>
              have hx1c : x1 ≠ c := by have := hcA0 x1 (Finset.mem_inter.mp hx1X1).1; simp [notCB] at this; exact this
              have hX2_nc : (X2.filter fun u => petersenAdj c u = true).card ≤ 1 := by
                have hs : X2.filter (fun u => petersenAdj c u = true) ⊆
                    Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj x1 u = true := by
                  intro u hu; simp only [Finset.mem_filter] at hu
                  have hz := hX1_adj x1 hx1X1 u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hu.1)))
                  simp [hu.2, hz]
                exact le_trans (Finset.card_le_card hs) (petersen_common_nbr_le_1 c x1 (Ne.symm hx1c))
              have hB0_nc : (B0.filter fun u => adjCB (some c) u = true).card ≤
                  (X2.filter fun u => petersenAdj c u = true).card + Y2.card := by
                have hs : B0.filter (fun u => adjCB (some c) u = true) ⊆
                    (X2.filter fun u => petersenAdj c u = true) ∪ Y2 := by
                  intro u hu
                  obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
                  simp only [adjCB] at hu2
                  simp only [Finset.mem_union, Finset.mem_filter, X2, Y2, Finset.mem_inter, Finset.mem_sdiff]
                  by_cases h : u ∈ S2'
                  · exact Or.inl ⟨⟨hu1, h⟩, hu2⟩
                  · exact Or.inr ⟨hu1, h⟩
                exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
              by_cases hX2_nc0 : (X2.filter fun u => petersenAdj c u = true).card = 0
              · omega
              · obtain ⟨x2, hx2f⟩ := Finset.card_pos.mp (by omega : 0 < (X2.filter fun u => petersenAdj c u = true).card)
                have hx2X2 : x2 ∈ X2 := (Finset.mem_filter.mp hx2f).1
                have hcx2 : petersenAdj c x2 = true := (Finset.mem_filter.mp hx2f).2
                have hx12_adj : petersenAdj x1 x2 = true :=
                  hX1_adj x1 hx1X1 x2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx2X2)))
                have hcx1 : adjCB (some c) x1 = false := petersen_no_triangle c x2 x1 hcx2 (petersenAdj_symm x1 x2 hx12_adj)
                have hA0_ins : A0 = insert x1 Y1 := by
                  ext z; simp only [Finset.mem_insert, Y1, Finset.mem_sdiff]; constructor
                  · intro hz; by_cases hzs : z ∈ S1'
                    · left; have : z ∈ X1 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hx1, Finset.mem_singleton] at this; exact this
                    · exact Or.inr ⟨hz, hzs⟩
                  · rintro (hz | ⟨hz, _⟩); subst z; exact (Finset.mem_inter.mp hx1X1).1; exact hz
                have hx1Y1 : x1 ∉ Y1 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hx1X1).2
                have hx2B0 : x2 ∈ B0 := (Finset.mem_inter.mp hx2X2).1
                have hx2_not_A0 : x2 ∉ A0 := Finset.disjoint_right.mp hAB0_disj hx2B0
                have hx2W1 : x2 ∉ W1 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2X2).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
                have bAW' := bipEdgesOpt_of_ext (some c) x2 x1 Y1 W1 (hA0_ins ▸ hcA0) (hcB0 x2 hx2B0) hcx1 (petersenAdj_symm x1 x2 hx12_adj) hx1Y1 (hA0_ins ▸ hx2_not_A0) hx2W1 (hA0_ins ▸ hdisj_A0W1)
                rw [← hA0_ins] at bAW'
                omega
        · -- X1'.card = 1, so W2 = X1 = Z1 = ∅
          have hX1'eq : X1'.card = 1 := by omega
          have hW20 : W2.card = 0 := by omega
          have hX10 : X1.card = 0 := by omega
          have hZ10 : Z1.card = 0 := by omega
          have eBW : bipEdgesOpt c? B0 W2 = ∅ := by rw [Finset.card_eq_zero.mp hW20]; ext e; simp [bipEdgesOpt, bipEdges]
          have eX12 : bipEdgesOpt c? X1 X2 = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesOpt, bipEdges]
          have eZ2 : bipEdgesOpt c? X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesOpt, bipEdges]
          have eX1X2' : bipEdgesOpt c? X1 X2' = ∅ := by rw [Finset.card_eq_zero.mp hX10]; ext e; simp [bipEdgesOpt, bipEdges]
          have eZ1 : bipEdgesOpt c? X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hZ10]; ext e; simp [bipEdgesOpt, bipEdges]
          rw [eBW, eX12, eZ2, eX1X2', eZ1, Finset.card_empty] at hE0_union
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hX1'eq
          have hX2N : ∀ v ∈ X2, petersenAdj x v = true := fun v hv =>
            petersenAdj_symm v x (hX2_adj v hv x (Finset.mem_union_left _ (Finset.mem_union_right _ (by rw [hx]; simp))))
          have b2 := bipEdgesOpt_branch2_le c? x X2 X2' (hcX1' x (by rw [hx]; simp)) hX2N
          rw [← hx] at b2
          have hB0_nc : (B0.filter fun u => adjCB c? u = true).card ≤
              (X2.filter fun u => adjCB c? u = true).card + Y2.card := by
            have hs : B0.filter (fun u => adjCB c? u = true) ⊆
                (X2.filter fun u => adjCB c? u = true) ∪ Y2 := by
              intro u hu; simp only [Finset.mem_filter, Finset.mem_union, X2, Y2, Finset.mem_inter, Finset.mem_sdiff] at hu ⊢
              by_cases h : u ∈ S2'
              · exact Or.inl ⟨⟨hu.1, h⟩, hu.2⟩
              · exact Or.inr ⟨hu.1, h⟩
            exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
          omega
    · -- Symmetric: hR1 : (W1 ∪ X2 ∪ X2' ∪ Z2).card ≤ 1
      have dW1X2 : Disjoint W1 X2 := by
        rw [Finset.disjoint_left]; intro x hxW hxX
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxX).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxW).1).1
      have dW1X2_X2' : Disjoint (W1 ∪ X2) X2' := by
        rw [Finset.disjoint_left]; intro x hx hx2'
        rw [Finset.mem_union] at hx
        rcases hx with hw1 | hx2
        · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2').2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
        · exact Finset.disjoint_left.mp hB0B1_disj (Finset.mem_inter.mp hx2).1 (Finset.mem_inter.mp hx2').1
      have dAll_Z2 : Disjoint (W1 ∪ X2 ∪ X2') Z2 := by
        rw [Finset.disjoint_left]; intro x hx hxZ
        have hnl := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxZ).1).2
        have hnot := (Finset.mem_sdiff.mp hxZ).2
        simp only [Finset.mem_union] at hx hnot
        rcases hx with (hw1 | hx2) | hx2'
        · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw1).1).1
        · exact hnot (Or.inl (Finset.mem_inter.mp hx2).1)
        · exact hnot (Or.inr (Finset.mem_inter.mp hx2').1)
      have hsum1 : W1.card + X2.card + X2'.card + Z2.card ≤ 1 := by
        rw [← Finset.card_union_of_disjoint dW1X2, ← Finset.card_union_of_disjoint dW1X2_X2',
          ← Finset.card_union_of_disjoint dAll_Z2]; exact hR1
      refine ⟨T1_def, hT1_def_sub, hT1_def_cov, ?_⟩
      change S.card + (edgesM0Opt c? M0 (l.and r)).card + (edgesM1Opt c? M1 (l.and r)).card + T1_def.card +
        ((((M0 ∪ M1) ∩ (l.and r).orVars) \ S).filter fun u => adjCB c? u = true).card ≤
        l.leaves + r.leaves + (M1 ∩ (l.and r).orVars).card
      by_cases hX2'0 : X2'.card = 0
      · have eX1X2' : bipEdgesOpt c? X1 X2' = ∅ := by rw [Finset.card_eq_zero.mp hX2'0]; ext e; simp [bipEdgesOpt, bipEdges]
        have eX1'X2' : bipEdgesOpt c? X1' X2' = ∅ := by rw [Finset.card_eq_zero.mp hX2'0]; ext e; simp [bipEdgesOpt, bipEdges]
        have hncX2'0 : (X2'.filter fun u => adjCB c? u = true).card = 0 := by rw [Finset.card_eq_zero.mp hX2'0]; simp
        rw [eX1X2', Finset.card_empty] at hE0_union
        rw [eX1'X2', Finset.card_empty] at hE1_le
        have hX2_le : X2.card ≤ 1 := by omega
        have bZ1 : (bipEdgesOpt c? X2 Z1).card ≤ Z1.card :=
          le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X2 Z1 hX2_le)
        have bX2X1' : (bipEdgesOpt c? X2 X1').card ≤ X1'.card :=
          le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X2 X1' hX2_le)
        have bX12 : (bipEdgesOpt c? X1 X2).card ≤ X1.card := by
          rw [bipEdgesOpt_comm]; exact le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one X2 X1 hX2_le)
        have bZ2 : (bipEdgesOpt c? X1 Z2).card ≤ X1.card := by
          rw [bipEdgesOpt_comm]; exact le_trans (bipEdgesOpt_le_bipEdges c? _ _) (bipEdges_le_right_of_card_le_one Z2 X1 (by omega))
        have hncX1' : (X1'.filter fun u => adjCB c? u = true).card ≤ X1'.card := Finset.card_le_card (Finset.filter_subset _ _)
        by_cases hX20 : X2.card = 0
        · have eX12 : bipEdgesOpt c? X1 X2 = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesOpt, bipEdges]
          have eZ1 : bipEdgesOpt c? X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesOpt, bipEdges]
          have eX2X1' : bipEdgesOpt c? X2 X1' = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesOpt, bipEdges]
          rw [eX12, eZ1, eX2X1', Finset.card_empty] at hE0_union
          by_cases hZ20 : Z2.card = 0
          · have eZ2 : bipEdgesOpt c? X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hZ20]; ext e; simp [bipEdgesOpt, bipEdges]
            rw [eZ2, Finset.card_empty] at hE0_union; omega
          · have hW10 : W1.card = 0 := by omega
            have eAW : bipEdgesOpt c? A0 W1 = ∅ := by rw [Finset.card_eq_zero.mp hW10]; ext e; simp [bipEdgesOpt, bipEdges]
            have hZ2eq : Z2.card = 1 := by omega
            obtain ⟨z2, hz2⟩ := Finset.card_eq_one.mp hZ2eq
            cases c? with
            | none =>
              have hA0nc : (A0.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
              rw [hA0nc, Finset.card_empty] at hNc_le; rw [eAW, Finset.card_empty] at hE0_union; omega
            | some c =>
              by_cases hzc : z2 = c
              · have eZ2 : bipEdgesOpt (some c) X1 Z2 = ∅ := by
                  rw [hz2, hzc]; ext e; simp only [bipEdgesOpt, bipEdges, notCB, decide_eq_true_eq, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
                  rintro ⟨⟨_, ⟨_, rfl⟩ | ⟨rfl, _⟩⟩, h1, h2⟩ <;> contradiction
                rw [eZ2, eAW, Finset.card_empty] at hE0_union
                have : (A0.filter fun u => adjCB (some c) u = true).card ≤ A0.card := Finset.card_le_card (Finset.filter_subset _ _)
                omega
              · have hX1_nc : (X1.filter fun u => petersenAdj c u = true).card ≤ 1 := by
                  have hs : X1.filter (fun u => petersenAdj c u = true) ⊆
                      Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj z2 u = true := by
                    intro u hu; simp only [Finset.mem_filter] at hu
                    have hz := hX1_adj u hu.1 z2 (Finset.mem_union_right _ (by rw [hz2]; simp))
                    simp [hu.2, petersenAdj_symm u z2 hz]
                  exact le_trans (Finset.card_le_card hs) (petersen_common_nbr_le_1 c z2 (Ne.symm hzc))
                have hA0_nc : (A0.filter fun u => adjCB (some c) u = true).card ≤
                    (X1.filter fun u => petersenAdj c u = true).card + Y1.card := by
                  have hs : A0.filter (fun u => adjCB (some c) u = true) ⊆
                      (X1.filter fun u => petersenAdj c u = true) ∪ Y1 := by
                    intro u hu
                    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
                    simp only [adjCB] at hu2
                    simp only [Finset.mem_union, Finset.mem_filter, X1, Y1, Finset.mem_inter, Finset.mem_sdiff]
                    by_cases h : u ∈ S1'
                    · exact Or.inl ⟨⟨hu1, h⟩, hu2⟩
                    · exact Or.inr ⟨hu1, h⟩
                  exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
                rw [eAW, Finset.card_empty] at hE0_union; omega
        · have hW10 : W1.card = 0 := by omega
          have hZ20 : Z2.card = 0 := by omega
          have eAW : bipEdgesOpt c? A0 W1 = ∅ := by rw [Finset.card_eq_zero.mp hW10]; ext e; simp [bipEdgesOpt, bipEdges]
          have eZ2 : bipEdgesOpt c? X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hZ20]; ext e; simp [bipEdgesOpt, bipEdges]
          rw [eAW, eZ2, Finset.card_empty] at hE0_union
          have hX2eq : X2.card = 1 := by omega
          obtain ⟨x2, hx2⟩ := Finset.card_eq_one.mp hX2eq
          have hx2X2 : x2 ∈ X2 := by rw [hx2]; simp
          cases c? with
          | none =>
            have hA0nc : (A0.filter fun u => adjCB none u = true) = ∅ := by ext u; simp [adjCB]
            rw [hA0nc, Finset.card_empty] at hNc_le; omega
          | some c =>
            have hx2c : x2 ≠ c := by have := hcB0 x2 (Finset.mem_inter.mp hx2X2).1; simp [notCB] at this; exact this
            have hX1_nc : (X1.filter fun u => petersenAdj c u = true).card ≤ 1 := by
              have hs : X1.filter (fun u => petersenAdj c u = true) ⊆
                  Finset.univ.filter fun u => petersenAdj c u = true ∧ petersenAdj x2 u = true := by
                intro u hu; simp only [Finset.mem_filter] at hu
                have hz := hX2_adj x2 hx2X2 u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hu.1)))
                simp [hu.2, hz]
              exact le_trans (Finset.card_le_card hs) (petersen_common_nbr_le_1 c x2 (Ne.symm hx2c))
            have hA0_nc : (A0.filter fun u => adjCB (some c) u = true).card ≤
                (X1.filter fun u => petersenAdj c u = true).card + Y1.card := by
              have hs : A0.filter (fun u => adjCB (some c) u = true) ⊆
                  (X1.filter fun u => petersenAdj c u = true) ∪ Y1 := by
                intro u hu
                obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
                simp only [adjCB] at hu2
                simp only [Finset.mem_union, Finset.mem_filter, X1, Y1, Finset.mem_inter, Finset.mem_sdiff]
                by_cases h : u ∈ S1'
                · exact Or.inl ⟨⟨hu1, h⟩, hu2⟩
                · exact Or.inr ⟨hu1, h⟩
              exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
            by_cases hX1_nc0 : (X1.filter fun u => petersenAdj c u = true).card = 0
            · omega
            · obtain ⟨x1, hx1f⟩ := Finset.card_pos.mp (by omega : 0 < (X1.filter fun u => petersenAdj c u = true).card)
              have hx1X1 : x1 ∈ X1 := (Finset.mem_filter.mp hx1f).1
              have hcx1 : petersenAdj c x1 = true := (Finset.mem_filter.mp hx1f).2
              have hx12_adj : petersenAdj x1 x2 = true :=
                petersenAdj_symm x2 x1 (hX2_adj x2 hx2X2 x1 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx1X1))))
              have hcx2 : adjCB (some c) x2 = false := petersen_no_triangle c x1 x2 hcx1 hx12_adj
              have hB0_ins : B0 = insert x2 Y2 := by
                ext z; simp only [Finset.mem_insert, Y2, Finset.mem_sdiff]; constructor
                · intro hz; by_cases hzs : z ∈ S2'
                  · left; have : z ∈ X2 := Finset.mem_inter.mpr ⟨hz, hzs⟩; rw [hx2, Finset.mem_singleton] at this; exact this
                  · exact Or.inr ⟨hz, hzs⟩
                · rintro (hz | ⟨hz, _⟩); subst z; exact (Finset.mem_inter.mp hx2X2).1; exact hz
              have hx2Y2 : x2 ∉ Y2 := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hx2X2).2
              have hx1A0 : x1 ∈ A0 := (Finset.mem_inter.mp hx1X1).1
              have hx1_not_B0 : x1 ∉ B0 := Finset.disjoint_left.mp hAB0_disj hx1A0
              have hx1W2 : x1 ∉ W2 := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx1X1).2).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
              have bBW' := bipEdgesOpt_of_ext (some c) x1 x2 Y2 W2 (hB0_ins ▸ hcB0) (hcA0 x1 hx1A0) hcx2 hx12_adj hx2Y2 (hB0_ins ▸ hx1_not_B0) hx1W2 (hB0_ins ▸ hdisj_B0W2)
              rw [← hB0_ins] at bBW'
              omega
      · -- X2'.card = 1, so W1 = X2 = Z2 = ∅
        have hX2'eq : X2'.card = 1 := by omega
        have hW10 : W1.card = 0 := by omega
        have hX20 : X2.card = 0 := by omega
        have hZ20 : Z2.card = 0 := by omega
        have eAW : bipEdgesOpt c? A0 W1 = ∅ := by rw [Finset.card_eq_zero.mp hW10]; ext e; simp [bipEdgesOpt, bipEdges]
        have eX12 : bipEdgesOpt c? X1 X2 = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesOpt, bipEdges]
        have eZ1 : bipEdgesOpt c? X2 Z1 = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesOpt, bipEdges]
        have eX2X1' : bipEdgesOpt c? X2 X1' = ∅ := by rw [Finset.card_eq_zero.mp hX20]; ext e; simp [bipEdgesOpt, bipEdges]
        have eZ2 : bipEdgesOpt c? X1 Z2 = ∅ := by rw [Finset.card_eq_zero.mp hZ20]; ext e; simp [bipEdgesOpt, bipEdges]
        rw [eAW, eX12, eZ1, eX2X1', eZ2, Finset.card_empty] at hE0_union
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hX2'eq
        have hX1N : ∀ v ∈ X1, petersenAdj x v = true := fun v hv =>
          petersenAdj_symm v x (hX1_adj v hv x (Finset.mem_union_left _ (Finset.mem_union_right _ (by rw [hx]; simp))))
        have b2 := bipEdgesOpt_branch2_le c? x X1 X1' (hcX2' x (by rw [hx]; simp)) hX1N
        rw [← hx, bipEdgesOpt_comm c? X2' X1'] at b2
        have hA0_nc : (A0.filter fun u => adjCB c? u = true).card ≤
            (X1.filter fun u => adjCB c? u = true).card + Y1.card := by
          have hs : A0.filter (fun u => adjCB c? u = true) ⊆
              (X1.filter fun u => adjCB c? u = true) ∪ Y1 := by
            intro u hu; simp only [Finset.mem_filter, Finset.mem_union, X1, Y1, Finset.mem_inter, Finset.mem_sdiff] at hu ⊢
            by_cases h : u ∈ S1'
            · exact Or.inl ⟨⟨hu.1, h⟩, hu.2⟩
            · exact Or.inr ⟨hu.1, h⟩
          exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
        omega

lemma read2_and_general_bound_left (l r : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, (l.and r).varCount v ≤ 2)
    (hle : ∀ x : Fin 10 → Bool, (l.and r).eval x = true → petersenFun x = true)
    (hSl1 : (singleSet l).card ≤ 1) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, (l.and r).eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ (l.and r).leaves := by
  let M := l.orVars ∩ r.orVars
  let M0 := M ∩ singleSet r
  let M1 := (M \ singleSet r) \ singleSet l
  let Ur := r.orVars \ l.orVars
  have hdisjM : Disjoint M0 M1 := by
    rw [Finset.disjoint_left]; intro u h0 h1
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h1).1).2 (Finset.mem_inter.mp h0).2
  have hM0_disj_Sl : Disjoint M0 (singleSet l) := by
    rw [Finset.disjoint_left]; intro u h0 hl
    have hlu : l.eval (singleInput u) = true := (Finset.mem_filter.mp hl).2
    have hru : r.eval (singleInput u) = true := (Finset.mem_filter.mp (Finset.mem_inter.mp h0).2).2
    have hp := hle (singleInput u) (by simp [MonoFormula.eval, hlu, hru])
    rw [petersenFun_single] at hp; exact absurd hp (by decide)
  have hr2l : ∀ v, l.varCount v ≤ 2 := fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega
  have hM0l : ∀ m ∈ M0, l.varCount m ≤ 1 := fun m hm => by
    have hmr : m ∈ r.orVars := (Finset.mem_inter.mp (Finset.mem_inter.mp hm).1).2
    rw [MonoFormula.mem_orVars_iff_varCount_pos] at hmr
    have := hr2 m; simp [MonoFormula.varCount] at this; omega
  have hM1l : ∀ m ∈ M1, l.varCount m ≤ 1 := fun m hm => by
    have hmr : m ∈ r.orVars := (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hm).1).1).2
    rw [MonoFormula.mem_orVars_iff_varCount_pos] at hmr
    have := hr2 m; simp [MonoFormula.varCount] at this; omega
  have hnol : ∀ u v, (u ∈ M0 ∨ v ∈ M0) → petersenAdj u v = false → l.eval (pairInput u v) = false := by
    intro u v hm hadj
    have hr1 : r.eval (pairInput u v) = true := by
      rcases hm with hu | hv
      · exact r.eval_mono (singleInput u) (pairInput u v) (fun i hi => by
          simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2
      · exact r.eval_mono (singleInput v) (pairInput u v) (fun i hi => by
          simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
    cases hluv : l.eval (pairInput u v)
    · rfl
    · exfalso
      have hp := hle (pairInput u v) (by simp [MonoFormula.eval, hluv, hr1])
      rw [petersenFun_pair_iff] at hp; rw [hadj] at hp; exact absurd hp (by decide)
  have hM1_eq : M1 ∩ l.orVars = M1 := by
    ext u; simp only [Finset.mem_inter, M1, M, Finset.mem_sdiff, and_iff_left_iff_imp]
    intro h; exact h.1.1.1
  have hr_budget : M0.card + M1.card + Ur.card ≤ r.leaves := by
    have d1 : Disjoint M0 M1 := hdisjM
    have d2 : Disjoint (M0 ∪ M1) Ur := by
      rw [Finset.disjoint_left]; intro u h1 h2
      have hnl := (Finset.mem_sdiff.mp h2).2
      rcases Finset.mem_union.mp h1 with h0 | h1'
      · exact hnl (Finset.mem_inter.mp (Finset.mem_inter.mp h0).1).1
      · exact hnl (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h1').1).1).1
    have hsub : M0 ∪ M1 ∪ Ur ⊆ r.orVars := by
      intro u hu; simp only [Finset.mem_union] at hu
      rcases hu with (h0 | h1) | hu'
      · exact (Finset.mem_inter.mp (Finset.mem_inter.mp h0).1).2
      · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h1).1).1).2
      · exact (Finset.mem_sdiff.mp hu').1
    rw [← Finset.card_union_of_disjoint d1, ← Finset.card_union_of_disjoint d2]
    exact le_trans (Finset.card_le_card hsub) r.orVars_card_le
  by_cases hne : (singleSet l).Nonempty
  · obtain ⟨c, hSl⟩ := Finset.card_eq_one.mp (le_antisymm hSl1 (Finset.card_pos.mpr hne))
    have hcM0 : ∀ u ∈ M0, notCB (some c) u = true := fun u hu => by
      simp only [notCB, decide_eq_true_eq]
      intro h; exact Finset.disjoint_left.mp hM0_disj_Sl hu (by rw [hSl, h]; simp)
    have hcM1 : ∀ u ∈ M1, notCB (some c) u = true := fun u hu => by
      simp only [notCB, decide_eq_true_eq]
      intro h; exact (Finset.mem_sdiff.mp hu).2 (by rw [hSl, h]; simp)
    obtain ⟨T1, hT1_sub, hT1_cov, hbd⟩ := golden_read2_bound_unified (some c) M0 M1 l hdisjM hcM0 hcM1 hr2l hM0l hM1l hnol
    let E := edgesM0Opt (some c) M0 l ∪ edgesM1Opt (some c) M1 l ∪ bipEdges {c} Ur ∪ bipEdges {c} (M0 ∪ M1)
    let T := insert c (M0 ∪ T1)
    refine ⟨T, E, ?_, ?_, ?_⟩
    · intro e he hev
      simp only [MonoFormula.eval, Bool.and_eq_true] at hev
      have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
      by_cases h1c : e.1 = c
      · have h2ne : e.2 ≠ c := h1c ▸ Ne.symm (ne_of_lt (petersenEdges_lt e he))
        have h2r : e.2 ∈ r.orVars := by
          by_contra hnr
          have h0 := eval_pair_of_not_mem r e.2 e.1 hnr
          change r.eval (pairInput e.2 e.1) = r.eval (singleInput e.1) at h0
          rw [← hsym, h1c] at h0
          have hrc : r.eval (singleInput c) = true := by rw [← h0, ← h1c]; exact hev.2
          have hlc : l.eval (singleInput c) = true := (Finset.mem_filter.mp (by rw [hSl]; simp : c ∈ singleSet l)).2
          have hp := hle (singleInput c) (by simp [MonoFormula.eval, hlc, hrc])
          rw [petersenFun_single] at hp; exact absurd hp (by decide)
        by_cases h2l : e.2 ∈ l.orVars
        · have h2M : e.2 ∈ M0 ∪ M1 := by
            by_cases h2sr : e.2 ∈ singleSet r
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h2l, h2r⟩, h2sr⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h2l, h2r⟩, h2sr⟩, by rw [hSl]; simp [h2ne]⟩)
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inl ⟨by simp [h1c], h2M⟩⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inl ⟨by simp [h1c], Finset.mem_sdiff.mpr ⟨h2r, h2l⟩⟩⟩))
      · by_cases h2c : e.2 = c
        · have h1r : e.1 ∈ r.orVars := by
            by_contra hnr
            have h0 := eval_pair_of_not_mem r e.1 e.2 hnr
            change r.eval (pairInput e.1 e.2) = r.eval (singleInput e.2) at h0
            rw [h2c] at h0
            have hrc : r.eval (singleInput c) = true := by rw [← h0, ← h2c]; exact hev.2
            have hlc : l.eval (singleInput c) = true := (Finset.mem_filter.mp (by rw [hSl]; simp : c ∈ singleSet l)).2
            have hp := hle (singleInput c) (by simp [MonoFormula.eval, hlc, hrc])
            rw [petersenFun_single] at hp; exact absurd hp (by decide)
          by_cases h1l : e.1 ∈ l.orVars
          · have h1M : e.1 ∈ M0 ∪ M1 := by
              by_cases h1sr : e.1 ∈ singleSet r
              · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h1l, h1r⟩, h1sr⟩)
              · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h1l, h1r⟩, h1sr⟩, by rw [hSl]; simp [h1c]⟩)
            exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inr ⟨h1M, by simp [h2c]⟩⟩)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, Or.inr ⟨Finset.mem_sdiff.mpr ⟨h1r, h1l⟩, by simp [h2c]⟩⟩))
        · have hnot1 : e.1 ∉ singleSet l := by rw [hSl]; simp [h1c]
          have hnot2 : e.2 ∉ singleSet l := by rw [hSl]; simp [h2c]
          have h1l : e.1 ∈ l.orVars := by
            by_contra hnl
            have h0 := eval_pair_of_not_mem l e.1 e.2 hnl
            change l.eval (pairInput e.1 e.2) = l.eval (singleInput e.2) at h0
            exact hnot2 (by simp [singleSet, ← h0, hev.1])
          have h2l : e.2 ∈ l.orVars := by
            by_contra hnl
            have h0 := eval_pair_of_not_mem l e.2 e.1 hnl
            change l.eval (pairInput e.2 e.1) = l.eval (singleInput e.1) at h0; rw [← hsym] at h0
            exact hnot1 (by simp [singleSet, ← h0, hev.1])
          by_cases hm0 : e.1 ∈ M0 ∨ e.2 ∈ M0
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, hm0, hev.1, hnot1, hnot2⟩, by simp [notCB, h1c, h2c]⟩)))
          · push Not at hm0
            have h1nsr : e.1 ∉ singleSet r := fun h => hm0.1 (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h1l, singleSet_subset_orVars r h⟩, h⟩)
            have h2nsr : e.2 ∉ singleSet r := fun h => hm0.2 (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h2l, singleSet_subset_orVars r h⟩, h⟩)
            have h1r : e.1 ∈ r.orVars := by
              by_contra hnr
              have h0 := eval_pair_of_not_mem r e.1 e.2 hnr
              change r.eval (pairInput e.1 e.2) = r.eval (singleInput e.2) at h0
              exact h2nsr (by simp [singleSet, ← h0, hev.2])
            have h2r : e.2 ∈ r.orVars := by
              by_contra hnr
              have h0 := eval_pair_of_not_mem r e.2 e.1 hnr
              change r.eval (pairInput e.2 e.1) = r.eval (singleInput e.1) at h0; rw [← hsym] at h0
              exact h1nsr (by simp [singleSet, ← h0, hev.2])
            have h1M1 : e.1 ∈ M1 := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h1l, h1r⟩, h1nsr⟩, hnot1⟩
            have h2M1 : e.2 ∈ M1 := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h2l, h2r⟩, h2nsr⟩, hnot2⟩
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨he, h1M1, h2M1, hev.1, hnot1, hnot2, by simp [notCB, h1c, h2c]⟩)))
    · intro e he
      simp only [E, T, Finset.mem_union, Finset.mem_insert] at he ⊢
      rcases he with ((h0 | h1) | h2) | h3
      · rcases (Finset.mem_filter.mp (Finset.mem_filter.mp h0).1).2.1 with h | h
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
      · rcases hT1_cov e h1 with h | h
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rcases (Finset.mem_filter.mp h2).2 with ⟨h, _⟩ | ⟨_, h⟩
        · simp at h; exact Or.inl (Or.inl h)
        · simp at h; exact Or.inr (Or.inl h)
      · rcases (Finset.mem_filter.mp h3).2 with ⟨h, _⟩ | ⟨_, h⟩
        · simp at h; exact Or.inl (Or.inl h)
        · simp at h; exact Or.inr (Or.inl h)
    · have hMM_eq : ((M0 ∪ M1) ∩ l.orVars) \ singleSet l = M0 ∪ M1 := by
        ext u; simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨⟨h, _⟩, _⟩; exact h
        · intro h
          refine ⟨⟨h, ?_⟩, ?_⟩
          · rcases h with h0 | h1
            · exact (Finset.mem_inter.mp (Finset.mem_inter.mp h0).1).1
            · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h1).1).1).1
          · rcases h with h0 | h1
            · exact Finset.disjoint_left.mp hM0_disj_Sl h0
            · exact (Finset.mem_sdiff.mp h1).2
      rw [hMM_eq, hM1_eq, hSl, Finset.card_singleton] at hbd
      have hbM : (bipEdges {c} (M0 ∪ M1)).card ≤ ((M0 ∪ M1).filter fun u => adjCB (some c) u = true).card := by
        have hs : bipEdges {c} (M0 ∪ M1) ⊆ ((M0 ∪ M1).filter fun u => petersenAdj c u = true).image
            (fun u => if c < u then (c, u) else (u, c)) := by
          intro e he; simp only [bipEdges, Finset.mem_filter, Finset.mem_singleton] at he
          have hlt := petersenEdges_lt e he.1; have hadj := petersenEdges_adj e he.1
          simp only [Finset.mem_image, Finset.mem_filter]
          rcases he.2 with ⟨rfl, h2⟩ | ⟨h1, rfl⟩
          · exact ⟨e.2, ⟨h2, hadj⟩, by simp [hlt]⟩
          · have hnot : ¬ (e.2 < e.1) := not_lt.mpr (le_of_lt hlt)
            exact ⟨e.1, ⟨h1, petersenAdj_symm e.1 e.2 hadj⟩, by simp [hnot]⟩
        exact le_trans (Finset.card_le_card hs) Finset.card_image_le
      have hbUr : (bipEdges {c} Ur).card ≤ Ur.card := bipEdges_le_right_of_card_le_one {c} Ur (by simp)
      have hE_le : E.card ≤ (edgesM0Opt (some c) M0 l).card + (edgesM1Opt (some c) M1 l).card +
          (bipEdges {c} Ur).card + (bipEdges {c} (M0 ∪ M1)).card := by
        change (edgesM0Opt (some c) M0 l ∪ edgesM1Opt (some c) M1 l ∪ bipEdges {c} Ur ∪ bipEdges {c} (M0 ∪ M1)).card ≤ _
        have u1 := Finset.card_union_le (edgesM0Opt (some c) M0 l ∪ edgesM1Opt (some c) M1 l ∪ bipEdges {c} Ur) (bipEdges {c} (M0 ∪ M1))
        have u2 := Finset.card_union_le (edgesM0Opt (some c) M0 l ∪ edgesM1Opt (some c) M1 l) (bipEdges {c} Ur)
        have u3 := Finset.card_union_le (edgesM0Opt (some c) M0 l) (edgesM1Opt (some c) M1 l)
        omega
      have hT_le : T.card ≤ 1 + M0.card + T1.card := by
        change (insert c (M0 ∪ T1)).card ≤ _
        have u1 := Finset.card_insert_le c (M0 ∪ T1)
        have u2 := Finset.card_union_le M0 T1
        omega
      simp only [MonoFormula.leaves]
      omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨T1, hT1_sub, hT1_cov, hbd⟩ := golden_read2_bound_unified none M0 M1 l hdisjM
      (fun _ _ => rfl) (fun _ _ => rfl) hr2l hM0l hM1l hnol
    let E := edgesM0Opt none M0 l ∪ edgesM1Opt none M1 l
    let T := M0 ∪ T1
    refine ⟨T, E, ?_, ?_, ?_⟩
    · intro e he hev
      simp only [MonoFormula.eval, Bool.and_eq_true] at hev
      have hsym : pairInput e.1 e.2 = pairInput e.2 e.1 := by funext i; simp [pairInput, or_comm]
      have hnot1 : e.1 ∉ singleSet l := by rw [hne]; exact Finset.notMem_empty _
      have hnot2 : e.2 ∉ singleSet l := by rw [hne]; exact Finset.notMem_empty _
      have h1l : e.1 ∈ l.orVars := by
        by_contra hnl
        have h0 := eval_pair_of_not_mem l e.1 e.2 hnl
        change l.eval (pairInput e.1 e.2) = l.eval (singleInput e.2) at h0
        exact hnot2 (by simp [singleSet, ← h0, hev.1])
      have h2l : e.2 ∈ l.orVars := by
        by_contra hnl
        have h0 := eval_pair_of_not_mem l e.2 e.1 hnl
        change l.eval (pairInput e.2 e.1) = l.eval (singleInput e.1) at h0; rw [← hsym] at h0
        exact hnot1 (by simp [singleSet, ← h0, hev.1])
      by_cases hm0 : e.1 ∈ M0 ∨ e.2 ∈ M0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, hm0, hev.1, hnot1, hnot2⟩, by simp [notCB]⟩)
      · push Not at hm0
        have h1nsr : e.1 ∉ singleSet r := fun h => hm0.1 (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h1l, singleSet_subset_orVars r h⟩, h⟩)
        have h2nsr : e.2 ∉ singleSet r := fun h => hm0.2 (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h2l, singleSet_subset_orVars r h⟩, h⟩)
        have h1r : e.1 ∈ r.orVars := by
          by_contra hnr
          have h0 := eval_pair_of_not_mem r e.1 e.2 hnr
          change r.eval (pairInput e.1 e.2) = r.eval (singleInput e.2) at h0
          exact h2nsr (by simp [singleSet, ← h0, hev.2])
        have h2r : e.2 ∈ r.orVars := by
          by_contra hnr
          have h0 := eval_pair_of_not_mem r e.2 e.1 hnr
          change r.eval (pairInput e.2 e.1) = r.eval (singleInput e.1) at h0; rw [← hsym] at h0
          exact h1nsr (by simp [singleSet, ← h0, hev.2])
        have h1M1 : e.1 ∈ M1 := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h1l, h1r⟩, h1nsr⟩, hnot1⟩
        have h2M1 : e.2 ∈ M1 := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h2l, h2r⟩, h2nsr⟩, hnot2⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, h1M1, h2M1, hev.1, hnot1, hnot2, by simp [notCB]⟩)
    · intro e he
      simp only [E, T, Finset.mem_union] at he ⊢
      rcases he with h0 | h1
      · rcases (Finset.mem_filter.mp (Finset.mem_filter.mp h0).1).2.1 with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rcases hT1_cov e h1 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
    · rw [hM1_eq] at hbd
      have hE_le : E.card ≤ (edgesM0Opt none M0 l).card + (edgesM1Opt none M1 l).card := Finset.card_union_le _ _
      have hT_le : T.card ≤ M0.card + T1.card := Finset.card_union_le _ _
      simp only [MonoFormula.leaves]
      omega

theorem read2_and_general_bound (l r : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, (l.and r).varCount v ≤ 2)
    (hle : ∀ x : Fin 10 → Bool, (l.and r).eval x = true → petersenFun x = true) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, (l.and r).eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ (l.and r).leaves := by
  have hbic : (singleSet l).card ≤ 1 ∨ (singleSet r).card ≤ 1 := by
    apply petersen_biclique_star
    intro u hu v hv
    have hlu : l.eval (singleInput u) = true := (Finset.mem_filter.mp hu).2
    have hrv : r.eval (singleInput v) = true := (Finset.mem_filter.mp hv).2
    have hev : (l.and r).eval (pairInput u v) = true := by
      simp only [MonoFormula.eval, Bool.and_eq_true]
      exact ⟨l.eval_mono (singleInput u) (pairInput u v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) hlu,
        r.eval_mono (singleInput v) (pairInput u v) (fun i hi => by simp only [singleInput, pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) hrv⟩
    have hp := hle (pairInput u v) hev
    rw [petersenFun_pair_iff] at hp; exact hp
  rcases hbic with hSl1 | hSr1
  · exact read2_and_general_bound_left l r hr2 hle hSl1
  · have hr2' : ∀ v, (r.and l).varCount v ≤ 2 := fun v => by
      have := hr2 v; simp [MonoFormula.varCount] at this ⊢; omega
    have hle' : ∀ x, (r.and l).eval x = true → petersenFun x = true := fun x hx =>
      hle x (by simpa [MonoFormula.eval, Bool.and_comm] using hx)
    obtain ⟨T, E, hE, hcov, hbd⟩ := read2_and_general_bound_left r l hr2' hle' hSr1
    exact ⟨T, E, fun e he hev => hE e he (by simpa [MonoFormula.eval, Bool.and_comm] using hev),
      hcov, by simpa [MonoFormula.leaves, Nat.add_comm] using hbd⟩

lemma read2_or_tree_bound (F : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, F.varCount v ≤ 2)
    (hle : ∀ x : Fin 10 → Bool, F.eval x = true → petersenFun x = true) :
    ∃ (T : Finset (Fin 10)) (E : Finset (Fin 10 × Fin 10)),
      (∀ e ∈ petersenEdges, F.eval (pairInput e.1 e.2) = true → e ∈ E) ∧
      (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧
      E.card + T.card ≤ F.leaves := by
  induction F with
  | var i =>
    exfalso; have h1 := hle (singleInput i) (by simp [MonoFormula.eval, singleInput])
    rw [petersenFun_single] at h1; exact absurd h1 (by decide)
  | or l r ihl ihr =>
    obtain ⟨T1, E1, hE1, hcov1, hbd1⟩ := ihl
      (fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega)
      (fun x hx => hle x (by simp [MonoFormula.eval, hx]))
    obtain ⟨T2, E2, hE2, hcov2, hbd2⟩ := ihr
      (fun v => by have := hr2 v; simp [MonoFormula.varCount] at this; omega)
      (fun x hx => hle x (by simp [MonoFormula.eval, hx]))
    refine ⟨T1 ∪ T2, E1 ∪ E2, ?_, ?_, ?_⟩
    · intro e he hev; simp only [MonoFormula.eval, Bool.or_eq_true] at hev
      rw [Finset.mem_union]; rcases hev with hl | hr
      · exact Or.inl (hE1 e he hl)
      · exact Or.inr (hE2 e he hr)
    · intro e he; rw [Finset.mem_union] at he
      rcases he with h1 | h2
      · rcases hcov1 e h1 with hc | hc
        · exact Or.inl (Finset.mem_union_left _ hc)
        · exact Or.inr (Finset.mem_union_left _ hc)
      · rcases hcov2 e h2 with hc | hc
        · exact Or.inl (Finset.mem_union_right _ hc)
        · exact Or.inr (Finset.mem_union_right _ hc)
    · simp only [MonoFormula.leaves]
      have c1 := Finset.card_union_le E1 E2; have c2 := Finset.card_union_le T1 T2; omega
  | and l r _ _ =>
    exact read2_and_general_bound l r hr2 hle

theorem petersen_read2_leaves_ge_21 (F : MonoFormula 10)
    (hr2 : ∀ v : Fin 10, F.varCount v ≤ 2)
    (hev : ∀ x : Fin 10 → Bool, F.eval x = petersenFun x) :
    21 ≤ F.leaves := by
  obtain ⟨T, E, hE, hcovT, hbd⟩ := read2_or_tree_bound F hr2 (fun x hx => by rw [← hev x, hx])
  have hsub : petersenEdges ⊆ E := by
    intro e he; apply hE e he; rw [hev, petersenFun_pair_iff]; exact petersenEdges_adj e he
  have hE15 : 15 ≤ E.card := by rw [← petersenEdges_card]; exact Finset.card_le_card hsub
  have hT6 : 6 ≤ T.card := petersen_tau_ge_6 T (fun e he => hcovT e (hsub he))
  omega

theorem petersen_19_world1_only (h : HasCircuitSize 10 petersenFun 19) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenFun x) ∧
      wireFanOut 10 C 0 = 1 := by
  rcases petersen_19_dichotomy_v3 h with h1 | ⟨l, r, hev, hleaves, hcnt, _⟩
  · exact h1
  · exfalso
    have h21 := petersen_read2_leaves_ge_21 (l.or r) (fun v => by rw [hcnt v]) hev
    omega

end PEqualNP.Outside.L_meta_651_step
