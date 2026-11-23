import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Triples273

open PEqualNP.CircuitLowerBounds

abbrev Mask := BitVec 6

def inputs : List Mask := [1,2,4,8,16,32]

def targets : Finset Mask := {7,28,49}

def fixed : List Mask := [0,1,2,4,8,16,32,7,28,49]

def makes (t x y : Mask) : Bool :=
  x != t && y != t && ((x ||| y) == t || (x &&& y) == t)

def single (t x : Mask) := fixed.any (makes t x)

def possible (t a b : Mask) := single t a || single t b || makes t a b

private lemma makes_swap (t x y : Mask) : makes t x y = makes t y x := by
  simp [makes, BitVec.or_comm x y, BitVec.and_comm x y, Bool.and_comm (x != t) (y != t)]

private lemma fixed_pair (t x y : Mask) (ht : t ∈ targets) (hx : x ∈ fixed) (hy : y ∈ fixed) :
    makes t x y = false := by
  have h : ([7,28,49] : List Mask).all (fun u => fixed.all (fun v => fixed.all (fun w => !(makes u v w)))) = true := by decide
  simpa using List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h t (by simpa [targets] using ht)) x hx) y hy

private lemma possible_of (t a b x y : Mask) (ht : t ∈ targets)
    (hx : x = a ∨ x = b ∨ x ∈ fixed) (hy : y = a ∨ y = b ∨ y ∈ fixed)
    (hm : makes t x y = true) : possible t a b = true := by
  have diag (z : Mask) : makes t z z = false := by
    by_cases h : z = t <;> simp [makes, h]
  have left (u v : Mask) (hu : u ∈ fixed) (hh : makes t v u = true) : single t v = true :=
    List.any_eq_true.mpr ⟨u, hu, hh⟩
  rcases hx with rfl | rfl | hx <;> rcases hy with rfl | rfl | hy
  · simp [diag] at hm
  · simp [possible, hm]
  · simp [possible, left _ _ hy hm]
  · rw [makes_swap] at hm
    simp [possible, hm]
  · simp [diag] at hm
  · simp [possible, left _ _ hy hm]
  · rw [makes_swap] at hm
    simp [possible, left _ _ hx hm]
  · rw [makes_swap] at hm
    simp [possible, left _ _ hx hm]
  · rw [fixed_pair _ _ _ ht hx hy] at hm
    contradiction

def pairsIn (t x : Mask) : Bool :=
  if t == 7 then x == 3 || x == 5 || x == 6
  else if t == 28 then x == 12 || x == 20 || x == 24
  else x == 17 || x == 33 || x == 48

private lemma single_table (t x : Mask) (ht : t ∈ targets) : single t x = pairsIn t x := by
  have allCases : ∀ n : Fin 64, (single 7 (BitVec.ofFin n) == pairsIn 7 (BitVec.ofFin n)) &&
      (single 28 (BitVec.ofFin n) == pairsIn 28 (BitVec.ofFin n)) &&
      (single 49 (BitVec.ofFin n) == pairsIn 49 (BitVec.ofFin n)) = true := by decide
  have h := allCases x.toFin
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp only [targets, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact h.1.1
  · exact h.1.2
  · simpa using h.2

def quick (t a b : Mask) := pairsIn t a || pairsIn t b || makes t a b

set_option maxRecDepth 10000 in
private lemma obstruction (a b : Mask) :
    ¬ (possible 7 a b = true ∧ possible 28 a b = true ∧ possible 49 a b = true) := by
  have allCases : ∀ i j : Fin 64, !(quick 7 (BitVec.ofFin i) (BitVec.ofFin j) &&
      quick 28 (BitVec.ofFin i) (BitVec.ofFin j) && quick 49 (BitVec.ofFin i) (BitVec.ofFin j)) = true := by decide
  have h := allCases a.toFin b.toFin
  intro ⟨h₁,h₂,h₃⟩
  simp only [possible, single_table _ _ (show (7 : Mask) ∈ targets by decide)] at h₁
  simp only [possible, single_table _ _ (show (28 : Mask) ∈ targets by decide)] at h₂
  simp only [possible, single_table _ _ (show (49 : Mask) ∈ targets by decide)] at h₃
  change !(quick 7 a b && quick 28 a b && quick 49 a b) = true at h
  change quick 7 a b = true at h₁
  change quick 28 a b = true at h₂
  change quick 49 a b = true at h₃
  rw [h₁,h₂,h₃] at h
  contradiction

def operand (w : List Mask) (g : Gate) (k : ℕ) := w.getD (g.inputs.getD k 0) 0

def andOp : GateOp → Bool
  | .and => true
  | _ => false

def value (w : List Mask) (g : Gate) : Mask :=
  if andOp g.op then operand w g 0 &&& operand w g 1
  else operand w g 0 ||| operand w g 1

def trace (w : List Mask) : List Gate → List Mask
  | [] => []
  | g :: gs => value w g :: trace (w ++ [value w g]) gs

private lemma trace_length (w : List Mask) (gs : List Gate) : (trace w gs).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [trace, ih]

private lemma get_in (w : List Mask) (i : Nat) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inl rfl
  | some x => exact Or.inr (List.mem_of_getElem? h)

private lemma map_get (w : List Mask) (i p : Nat) :
    ((w.map (fun z => z.getLsbD p)).getD i false) = (w.getD i 0).getLsbD p := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

def legal (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

private lemma sim_step (w : List Mask) (g : Gate) (hg : legal g) (p : Nat) :
    (value w g).getLsbD p =
      g.op.eval (g.inputs.map (fun i => (w.map (fun z => z.getLsbD p)).getD i false)) := by
  obtain ⟨hop, hl⟩ := hg
  obtain ⟨i,j,hij⟩ := List.length_eq_two.mp hl
  rcases hop with h | h
  · simp only [value,h,andOp,ite_true, BitVec.getLsbD_and, hij,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,map_get]
    simp [operand,hij]
  · simp only [value,h,andOp,Bool.false_eq_true,ite_false, BitVec.getLsbD_or, hij,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,map_get]
    simp [operand,hij]

private lemma sim_trace (w : List Mask) (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (p : Nat) :
    ((w ++ trace w gs).map (fun z => z.getLsbD p)) =
      gs.foldl (fun (v : List Bool) g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))])
        (w.map (fun z => z.getLsbD p)) := by
  induction gs generalizing w with
  | nil => simp [trace]
  | cons g gs ih =>
    have hh := ih (w ++ [value w g]) (fun u hu => hg u (by simp [hu]))
    simpa [trace, sim_step w g (hg g (by simp)) p] using hh

private lemma first_gate (w : List Mask) (gs : List Gate) (t : Mask)
    (hn : t ≠ 0) (hw : t ∉ w) (ht : t ∈ trace w gs) :
    ∃ x y, (x = 0 ∨ x ∈ w ++ trace w gs) ∧ (y = 0 ∨ y ∈ w ++ trace w gs) ∧ makes t x y = true := by
  induction gs generalizing w with
  | nil => simp [trace] at ht
  | cons g gs ih =>
    by_cases eq : value w g = t
    · let x := operand w g 0
      let y := operand w g 1
      have hx : x = 0 ∨ x ∈ w := get_in _ _
      have hy : y = 0 ∨ y ∈ w := get_in _ _
      have nx : x ≠ t := by rintro rfl; exact hx.elim hn hw
      have ny : y ≠ t := by rintro rfl; exact hy.elim hn hw
      refine ⟨x,y,hx.imp_right (fun h => List.mem_append_left _ h),
        hy.imp_right (fun h => List.mem_append_left _ h), ?_⟩
      change (if andOp g.op then x &&& y else x ||| y) = t at eq
      split at eq <;> simp [makes, nx, ny, eq]
    · have hnext : t ∉ w ++ [value w g] := by simp [hw, Ne.symm eq]
      have htail : t ∈ trace (w ++ [value w g]) gs := by simpa [trace, Ne.symm eq] using ht
      simpa [trace] using ih (w ++ [value w g]) hnext htail

private lemma cover_two (s : Finset Mask) (h : s.card ≤ 2) :
    ∃ a b : Mask, ∀ z ∈ s, z = a ∨ z = b := by
  interval_cases k : s.card
  · have e := Finset.card_eq_zero.mp k
    simp [e]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp k
    exact ⟨a,a,by simp⟩
  · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp k
    exact ⟨a,b,by simp⟩

def masks : Fin 3 → Mask := ![7,28,49]

private lemma input_bits (p : Fin 6) :
    inputs.map (fun z => z.getLsbD p.val) = List.ofFn (fun q : Fin 6 => decide (q = p)) := by
  fin_cases p <;> decide

private lemma mask_bits (i : Fin 3) (p : Fin 6) :
    (masks i).getLsbD p.val = true ↔
      p ∈ (![({0,1,2} : Finset (Fin 6)), {2,3,4}, {4,5,0}]) i := by
  fin_cases i <;> fin_cases p <;> decide

end PEqualNP.Outside.Triples273

open PEqualNP.Outside.Triples273 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_273 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C,o,hsize,hg,ho⟩
  let ws := trace inputs C.gates
  let allW := inputs ++ ws
  have hbit (p : Fin 6) : allW.map (fun z => z.getLsbD p.val) = C.wires (List.ofFn (fun q => decide (q = p))) := by
    simpa only [Circuit.wires,input_bits] using sim_trace inputs C.gates hg p.val
  have hout (i : Fin 3) : allW.getD (o i) 0 = masks i := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let p : Fin 6 := ⟨n,hn⟩
    have hb := congrArg (fun (v : List Bool) => v.getD (o i) false) (hbit p)
    rw [map_get] at hb
    apply Bool.eq_iff_iff.mpr
    exact (hb ▸ (ho i).1 p).trans (mask_bits i p).symm
  have subset : targets ⊆ ws.toFinset := by
    intro t ht
    have hex : ∃ i, t = masks i := by
      simp only [targets,Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    obtain ⟨i,rfl⟩ := hex
    have h := get_in allW (o i)
    rw [hout] at h
    have nonzero (j : Fin 3) : masks j ≠ 0 := by fin_cases j <;> decide
    have noninput (j : Fin 3) : masks j ∉ inputs := by fin_cases j <;> decide
    exact List.mem_toFinset.mpr ((List.mem_append.mp (h.resolve_left (nonzero i))).resolve_left (noninput i))
  have size : ws.toFinset.card ≤ 5 := by
    exact ws.toFinset_card_le.trans ((trace_length inputs C.gates) ▸ hsize)
  have extra : (ws.toFinset \ targets).card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset subset]
    have : targets.card = 3 := by decide
    omega
  obtain ⟨a,b,hab⟩ := cover_two _ extra
  have classify (z : Mask) (hz : z = 0 ∨ z ∈ allW) : z = a ∨ z = b ∨ z ∈ fixed := by
    rcases hz with rfl | hz
    · exact Or.inr (Or.inr (by decide))
    rcases List.mem_append.mp hz with hin | hg'
    · right; right
      simp [inputs] at hin
      simp [fixed]; tauto
    by_cases ht : z ∈ targets
    · right; right
      simp [targets] at ht
      simp [fixed]; tauto
    · exact (hab z (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hg',ht⟩)).imp_right Or.inl
  have reach (t : Mask) (ht : t ∈ targets) : possible t a b = true := by
    have hn : t ≠ 0 := by intro e; subst t; exact (by decide : (0 : Mask) ∉ targets) ht
    have hw : t ∉ inputs := by
      have hh : ∀ x ∈ inputs, x ∉ targets := by decide
      intro h; exact hh t h ht
    obtain ⟨x,y,hx,hy,hm⟩ := first_gate inputs C.gates t hn hw (List.mem_toFinset.mp (subset ht))
    exact possible_of _ _ _ _ _ ht (classify _ hx) (classify _ hy) hm
  exact obstruction a b ⟨reach 7 (by decide),reach 28 (by decide),reach 49 (by decide)⟩
