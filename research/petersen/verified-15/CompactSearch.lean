import Mathlib
import PEqualNP.Defs

namespace PetersenSigned
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Signal (α : Type) := α → Bool
def neg {α} (a : Signal α) : Signal α := fun x => !(a x)
def conj {α} (a b : Signal α) : Signal α := fun x => a x && b x

/-- Constants and both polarities of every stored signal are available. -/
inductive Available {α : Type} (s : List (Signal α)) : Signal α → Prop where
  | zero : Available s (fun _ => false)
  | one : Available s (fun _ => true)
  | pos {a} : a ∈ s → Available s a
  | negated {a} : a ∈ s → Available s (neg a)

private theorem flip {α} {s : List (Signal α)} {a} (h : Available s a) :
    Available s (neg a) := by
  cases h with
  | zero => exact .one
  | one => exact .zero
  | pos h => exact .negated h
  | negated h =>
    rename_i t
    have e : neg (neg t) = t := by funext x; simp [neg]
    rw [e]
    exact .pos h

private theorem extend {α} {s : List (Signal α)} {a} (h : Available s a) (g) :
    Available (g::s) a := by
  cases h with
  | zero => exact .zero
  | one => exact .one
  | pos h => exact .pos (List.mem_cons_of_mem _ h)
  | negated h => exact .negated (List.mem_cons_of_mem _ h)

/-- A binary AND adds a stored wire. Input and output polarity changes are free. -/
inductive Builds {α : Type} : Nat → List (Signal α) → Signal α → Prop where
  | stop {s f} : Available s f → Builds 0 s f
  | gate {k s f a b} : Available s a → Available s b →
      Builds k (conj a b :: s) f → Builds (k+1) s f

private def readWire {α} (w : List (Signal α)) (i : Nat) : Signal α := w.getD i (fun _ => false)
private def run {α} (w : List (Signal α)) : List Gate → List (Signal α)
  | [] => w
  | g :: gs => run (w ++ [fun x => g.op.eval (g.inputs.map fun i => readWire w i x)]) gs

private theorem read_ok {α} {w s : List (Signal α)} (hw : ∀ a ∈ w, Available s a) (i : Nat) :
    Available s (readWire w i) := by
  simp only [readWire,List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact .zero
  | some a => exact hw _ (List.mem_of_getElem? h)

private theorem factors {α} {s : List (Signal α)} (l : List (Signal α))
    (hl : l.length ≤ 2) (h : ∀ a ∈ l, Available s a) :
    ∃ a b, Available s a ∧ Available s b ∧
      (fun x => l.all (fun z => z x)) = conj a b := by
  cases l with
  | nil => exact ⟨_,_,.one,.one,rfl⟩
  | cons a as =>
    cases as with
    | nil =>
      exact ⟨a,_,h a (by simp),.one,by funext x; simp [conj]⟩
    | cons b bs =>
      cases bs with
      | nil => exact ⟨a,b,h a (by simp),h b (by simp),by funext x; simp [conj]⟩
      | cons c cs => simp at hl

def binaryOp : GateOp → Bool
  | .and | .or => true
  | _ => false

private theorem normalize {α : Type} (gs : List Gate) (out : Nat) (w s : List (Signal α))
    (hw : ∀ a ∈ w, Available s a) (ok : ∀ g ∈ gs,
     (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    Builds (gs.countP fun g => binaryOp g.op) s (readWire (run w gs) out) := by
  induction gs generalizing w s with
  | nil => exact .stop (read_ok hw out)
  | cons g gs ih =>
    let v : Signal α := fun x => g.op.eval (g.inputs.map fun i => readWire w i x)
    let reads := g.inputs.map (readWire w)
    have hr : ∀ z ∈ reads, Available s z := by
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact read_ok hw i
    obtain ⟨hops,hlen⟩ := ok g (by simp)
    have len : reads.length ≤ 2 := by simpa [reads] using hlen
    have tailok := fun k (hk : k ∈ gs) => ok k (by simp [hk])
    have next {s' : List (Signal α)} (hkeep : ∀ f ∈ w, Available s' f) (hv : Available s' v) :
        Builds (gs.countP fun g => binaryOp g.op) s' (readWire (run w (g::gs)) out) := by
      apply ih (w++[v]) s' _ tailok
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hkeep _ ha
      · simpa only [List.mem_singleton.mp ha] using hv
    rcases hops with ha | ho | hn
    · obtain ⟨a,b,aa,ab,e⟩ := factors reads len hr
      have he : v = conj a b := by
        rw [← e]
        funext x
        simp [v,reads,ha,GateOp.eval,List.all_map,Function.comp_def]
      simp only [List.countP_cons,ha,binaryOp]
      apply Builds.gate aa ab
      apply next (fun f hf => extend (hw f hf) _)
      rw [he]
      exact .pos (by simp)
    · obtain ⟨a,b,aa,ab,e⟩ := factors (reads.map neg) (by simpa using len) (by
        intro z hz; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz; exact flip (hr i hi))
      have he : v = neg (conj a b) := by
        rw [← e]
        funext x
        simp [v,reads,ho,GateOp.eval,List.any_map,List.all_map,Function.comp_def,neg]
        induction g.inputs with
        | nil => rfl
        | cons i is ih => simp [ih,Bool.not_and]
      simp only [List.countP_cons,ho,binaryOp]
      apply Builds.gate aa ab
      apply next (fun f hf => extend (hw f hf) _)
      rw [he]
      exact .negated (by simp)
    · simp only [List.countP_cons,hn,binaryOp]
      apply next hw
      cases ind : g.inputs with
      | nil => simpa only [v,hn,ind,List.map_nil,GateOp.eval,List.headD_nil,Bool.not_false] using (Available.one (s := s))
      | cons i is =>
        have e : v = neg (readWire w i) := by funext x; simp [v,hn,ind,GateOp.eval,neg]
        rw [e]; exact flip (read_ok hw i)

private lemma read_map {α} (w : List (Signal α)) (i : Nat) (x : α) :
    (w.map (fun f => f x)).getD i false = readWire w i x := by
  simp only [readWire,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private lemma run_eval {α} (w : List (Signal α)) (gs : List Gate) (x : α) :
    (run w gs).map (fun f => f x) =
      gs.foldl (fun (v : List Bool) g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))])
        (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, ih, List.foldl_cons,List.map_append,List.map_singleton,read_map]

def raw (n : Nat) : List (Signal (Fin n → Bool)) := List.ofFn (fun i : Fin n => fun x => x i)


/-- A project circuit yields a signed binary plan. Its length is exactly the number
of AND and OR gates, including any degenerate ones the project permits. -/
theorem circuit_to_signed (n : Nat) (C : Circuit) (hc : FanInTwo C) :
    Builds (C.gates.countP fun g => binaryOp g.op) (raw n) (fun x => C.eval (List.ofFn x)) := by
  have h := normalize C.gates C.output (raw n) (raw n) (fun _ h => .pos h) (by
    intro g hg
    obtain ⟨ha,hb⟩ := hc g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ha,hb⟩)
  suffices e : readWire (run (raw n) C.gates) C.output = (fun x => C.eval (List.ofFn x)) by
    rwa [← e]
  funext x
  rw [← read_map,run_eval]
  simp [raw,List.map_ofFn,Circuit.eval,Circuit.wires,Function.comp_def]

/-- Separate the two sufficiency obligations for a gate-count lower bound.
The first concerns circuits containing no NOT; the second counts only binary gates. -/
theorem lower_of_two_bounds {n s : Nat} (f : (Fin n → Bool) → Bool)
    (mono : ∀ C : Circuit, FanInTwo C → C.size ≤ s+1 →
      (∀ g ∈ C.gates, g.op ≠ .not) →
      ¬ ∀ x, C.eval (List.ofFn x) = f x)
    (signed : ∀ k ≤ s, ¬ Builds k (raw n) f) : ¬ HasCircuitSize n f (s+1) := by
  rintro ⟨C,hc,hs,he⟩
  by_cases hm : ∀ g ∈ C.gates, g.op ≠ .not
  · exact mono C hc hs hm he
  · push Not at hm
    obtain ⟨g,hg,hn⟩ := hm
    have lt : C.gates.countP (fun z => binaryOp z.op) < C.gates.length := by
      apply Nat.lt_of_le_of_ne (List.countP_le_length ..)
      intro eqn
      have b := List.countP_eq_length.mp eqn g hg
      simp [hn,binaryOp] at b
    change C.gates.length ≤ s+1 at hs
    have hb := circuit_to_signed n C hc
    rw [show (fun x => C.eval (List.ofFn x)) = f from funext he] at hb
    exact signed _ (by omega) hb

/-- An explicit signed straight-line plan keeps the operands of every binary step. -/
def Trace {α} (s : List (Signal α)) : List (Signal α × Signal α) → Signal α → Prop
  | [], f => Available s f
  | (a,b)::gs, f => Available s a ∧ Available s b ∧ Trace (conj a b :: s) gs f

theorem trace_of_builds {α} {k s} {f : Signal α} (h : Builds k s f) :
    ∃ gs, gs.length = k ∧ Trace s gs f := by
  induction h with
  | stop h => exact ⟨[],rfl,h⟩
  | @gate k s f a b ha hb h ih =>
    obtain ⟨gs,hl,ht⟩ := ih
    exact ⟨(a,b)::gs,by simp [hl],ha,hb,ht⟩

private theorem transport {α β} (σ : β → α) {s : List (Signal α)} {t : List (Signal β)}
    (rel : ∀ z ∈ s, Available t (z ∘ σ)) {a} (h : Available s a) : Available t (a ∘ σ) := by
  cases h with
  | zero => exact .zero
  | one => exact .one
  | pos hz => exact rel _ hz
  | negated hz => exact flip (rel _ hz)

/-- Count projected gates that are already available as a constant or an earlier literal.
Earlier projected gates remain available even when their own computation was eliminated. -/
noncomputable def saved {α β} (σ : β → α) (s : List (Signal α)) :
    List (Signal α × Signal α) → Nat
  | [] => 0
  | (a,b)::gs => by
    classical
    let v := conj a b
    exact (if Available (s.map (fun z => z ∘ σ)) (v ∘ σ) then 1 else 0) + saved σ (v::s) gs

theorem restrict_trace {α β} (σ : β → α) (s : List (Signal α)) (gs : List (Signal α × Signal α))
    (f : Signal α) (h : Trace s gs f) (t : List (Signal β))
    (rel : ∀ z ∈ s, Available t (z ∘ σ)) :
    ∃ k, k + saved σ s gs = gs.length ∧ Builds k t (f ∘ σ) := by
  classical
  induction gs generalizing s t with
  | nil => exact ⟨0,rfl,.stop (transport σ rel h)⟩
  | cons g gs ih =>
    obtain ⟨a,b⟩ := g
    obtain ⟨ha,hb,hh⟩ := h
    let v := conj a b
    by_cases already : Available (s.map (fun z => z ∘ σ)) (v ∘ σ)
    · have hv : Available t (v ∘ σ) := by
        have hmap : ∀ z ∈ s.map (fun z => z ∘ σ), Available t z := by
          intro z hz
          obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
          exact rel _ hw
        exact transport id (fun z hz => hmap z hz) already
      have rel' : ∀ z ∈ v::s, Available t (z ∘ σ) := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hv
        · exact rel _ hz
      obtain ⟨k,hk,hb⟩ := ih (s := v::s) hh t rel'
      refine ⟨k,?_,hb⟩
      change k + ((if Available (s.map (fun z => z ∘ σ)) (v ∘ σ) then 1 else 0) +
        saved σ (v::s) gs) = gs.length + 1
      simp only [already,ite_true]
      omega
    · let new := conj (a ∘ σ) (b ∘ σ)
      have rel' : ∀ z ∈ v::s, Available (new::t) (z ∘ σ) := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Available.pos (List.mem_cons_self)
        · exact extend (rel _ hz) new
      obtain ⟨k,hk,ht⟩ := ih (s := v::s) hh (new::t) rel'
      refine ⟨k+1,?_,.gate (transport σ rel ha) (transport σ rel hb) ht⟩
      change k + 1 + ((if Available (s.map (fun z => z ∘ σ)) (v ∘ σ) then 1 else 0) +
        saved σ (v::s) gs) = gs.length + 1
      simp only [already,ite_false,zero_add]
      omega

/-- Agreement on all these input signals determines the target. -/
def Determines {α} (S : Finset (Signal α)) (f : Signal α) : Prop :=
  ∀ x y, (∀ a ∈ S, a x = a y) → f x = f y

private theorem singleton_cover {α} {s : List (Signal α)} {a} (h : Available s a) :
    ∃ S : Finset (Signal α), (∀ w ∈ S, w ∈ s) ∧ S.card ≤ 1 ∧ Determines S a := by
  classical
  cases h with
  | zero | one => exact ⟨∅,by simp,by simp,by intro x y h; rfl⟩
  | pos hw =>
    exact ⟨{a},by simpa,by simp,by intro x y h; exact h a (by simp)⟩
  | @negated w hw =>
    exact ⟨{w},by simpa,by simp,by intro x y h; exact congrArg (! ·) (h w (by simp))⟩

/-- An output with k binary gates remaining needs at most k+1 presently
available signals. This bound also applies to shared subcircuits. -/
theorem small_cover {α} {k s} {f : Signal α} (h : Builds k s f) :
    ∃ S : Finset (Signal α), (∀ w ∈ S, w ∈ s) ∧ S.card ≤ k+1 ∧ Determines S f := by
  classical
  induction h with
  | stop h => exact singleton_cover h
  | @gate k s f a b ha hb hh ih =>
    obtain ⟨S,hS,hs,determined⟩ := ih
    let v := conj a b
    by_cases used : v ∈ S
    · obtain ⟨A,haS,ca,da⟩ := singleton_cover ha
      obtain ⟨B,hbS,cb,db⟩ := singleton_cover hb
      let T := (S.erase v ∪ A) ∪ B
      have mem {z} (hz : z ∈ S.erase v) : z ∈ s := by
        obtain ⟨hne,hin⟩ := Finset.mem_erase.mp hz
        exact (List.mem_cons.mp (hS z hin)).resolve_left hne
      refine ⟨T,?_,?_,?_⟩
      · intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · rcases Finset.mem_union.mp hz with hz | hz
          · exact mem hz
          · exact haS _ hz
        · exact hbS _ hz
      · have h1 := Finset.card_union_le (S.erase v) A
        have h2 := Finset.card_union_le (S.erase v ∪ A) B
        have h3 := Finset.card_erase_of_mem used
        change ((S.erase v ∪ A) ∪ B).card ≤ k+1+1
        omega
      · intro x y agree
        apply determined x y
        intro w hw
        by_cases eqv : w = v
        · subst w
          exact congrArg₂ (· && ·) (da x y (fun z hz => agree z (by simp [T,hz])))
            (db x y (fun z hz => agree z (by simp [T,hz])))
        · exact agree w (by simp [T,Finset.mem_erase,hw,eqv])
    · refine ⟨S,?_,by omega,determined⟩
      intro w hw
      exact (List.mem_cons.mp (hS w hw)).resolve_left (by rintro rfl; exact used hw)

def inputSignal {n : Nat} (i : Fin n) : Signal (Fin n → Bool) := fun x => x i

private theorem input_inj {n} : Function.Injective (@inputSignal n) := by
  intro i j eqn
  by_contra ne
  have h := congrFun eqn (fun k => decide (k = i))
  simp [inputSignal] at h
  exact ne h.symm

/-- Each witnessed coordinate must occur in every sufficient cover, even if the
additional wires are available without charge. -/
theorem indispensable {n k : Nat} {f : Signal (Fin n → Bool)} (extra : List (Signal (Fin n → Bool)))
    (I : Finset (Fin n)) (h : Builds k (extra ++ raw n) f)
    (essential : ∀ i ∈ I, ∃ x y, (∀ j ≠ i, x j = y j) ∧
      (∀ g ∈ extra, g x = g y) ∧ f x ≠ f y) : I.card ≤ k+1 := by
  classical
  obtain ⟨S,hS,hcard,hd⟩ := small_cover h
  have all : I.image inputSignal ⊆ S := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hg
    by_contra miss
    obtain ⟨x,y,away,agree,diff⟩ := essential i hi
    apply diff (hd x y ?_)
    intro w hw
    rcases List.mem_append.mp (hS w hw) with he | hr
    · exact agree w he
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      apply away j
      rintro rfl
      exact miss hw
  rw [← Finset.card_image_of_injective I input_inj]
  exact (Finset.card_le_card all).trans hcard

/-- Any available wire can substitute for another stored wire with the same meaning. -/
theorem simulate {α} {k s} {f : Signal α} (h : Builds k s f) (t : List (Signal α))
    (hr : ∀ z ∈ s, Available t z) : Builds k t f := by
  induction h generalizing t with
  | stop h => exact .stop (transport id (fun z hz => hr z hz) h)
  | @gate k s f a b ha hb hh ih =>
    apply Builds.gate (transport id (fun z hz => hr z hz) ha) (transport id (fun z hz => hr z hz) hb)
    apply ih
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact .pos List.mem_cons_self
    · exact extend (hr _ hz) _

/-- Pack a signal on an arbitrary list of examples, least significant bit first. -/
def table {α} (pts : List α) (f : Signal α) : BitVec pts.length :=
  (BitVec.ofBoolListLE (pts.map f)).cast (by simp)

private theorem bit_table {α} (pts : List α) (f : Signal α) (i : Nat) (h : i < pts.length) :
    (table pts f).getLsbD i = f pts[i] := by
  simp [table, List.getElem?_eq_getElem h]

private theorem table_zero {α} (p : List α) : table p (fun _ => false) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi; simp [bit_table p _ i hi]

private theorem table_neg {α} (p : List α) (a : Signal α) : table p (neg a) = ~~~(table p a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not,bit_table p _ i hi,bit_table p _ i hi]
  simp [hi,neg]

theorem table_conj {α} (p : List α) (a b : Signal α) :
    table p (conj a b) = table p a &&& table p b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi; simp [bit_table p _ i hi,conj]

def literals {m} (s : List (BitVec m)) : List (BitVec m) :=
  0 :: (~~~0) :: s.flatMap fun z => [z,~~~z]

private theorem mem_flip {m} {s : List (BitVec m)} {z} (hz : z ∈ literals s) :
    ~~~z ∈ literals s := by
  simp only [literals,List.mem_cons,List.mem_flatMap,List.not_mem_nil,or_false] at hz ⊢
  rcases hz with rfl | rfl | ⟨x,hx,rfl | rfl⟩
  · exact Or.inr (Or.inl rfl)
  · simp
  · exact Or.inr (Or.inr ⟨_,hx,Or.inr rfl⟩)
  · exact Or.inr (Or.inr ⟨_,hx,Or.inl (by simp)⟩)

private theorem lit_extend {m} {s : List (BitVec m)} {z} (hz : z ∈ literals s) (a) :
    z ∈ literals (a::s) := by
  simp only [literals,List.mem_cons,List.flatMap_cons,List.mem_append] at hz ⊢
  tauto

theorem available_table {α} {p : List α} {s : List (Signal α)} {t : List (BitVec p.length)}
    (hr : ∀ a ∈ s, table p a ∈ literals t) {a} (h : Available s a) :
    table p a ∈ literals t := by
  cases h with
  | zero => simp [table_zero,literals]
  | one =>
    change table p (neg (fun _ => false)) ∈ literals t
    rw [table_neg,table_zero]; simp [literals]
  | pos h => exact hr _ h
  | negated h => rw [table_neg]; exact mem_flip (hr _ h)

def canonical {m} (z : BitVec m) : BitVec m := if z.getLsbD 0 then ~~~z else z

theorem recover {m} (z : BitVec m) (t : List (BitVec m)) : z ∈ literals (canonical z :: t) := by
  by_cases h : z.getLsbD 0 <;> simp [canonical,h,literals]

def nextTables {m} (s : List (BitVec m)) : List (BitVec m) :=
  let l := literals s
  ((l.flatMap fun a => l.map fun b => canonical (a &&& b)).eraseDups).filter
    (fun z => !(l.contains z))

/-- Search all new signed AND results up to the remaining binary-gate budget. -/
def viable {m} : Nat → List (BitVec m) → BitVec m → Bool
  | 0, s, f => (literals s).contains f
  | k+1, s, f => (literals s).contains f || (nextTables s).any fun z => viable k (z::s) f

private theorem accepts_literal {m} {s : List (BitVec m)} {f} (hf : f ∈ literals s) (k) :
    viable k s f = true := by cases k <;> simp [viable,hf]

theorem search_complete {α} (pts : List α) {k s} {f : Signal α} (h : Builds k s f)
    (t : List (BitVec pts.length)) (hr : ∀ a ∈ s, table pts a ∈ literals t)
    (budget : Nat) (hk : k ≤ budget) : viable budget t (table pts f) = true := by
  induction h generalizing t budget with
  | stop h => exact accepts_literal (available_table hr h) _
  | @gate k s f a b ha hb hh ih =>
    let z := table pts a &&& table pts b
    let v := canonical z
    have zrep : table pts (conj a b) = z := table_conj pts a b
    by_cases hv : v ∈ literals t
    · have keep : z ∈ literals t := by
        by_cases hz : z.getLsbD 0
        · have hn : ~~~z ∈ literals t := by simpa [v,canonical,hz] using hv
          simpa using mem_flip hn
        · simpa [v,canonical,hz] using hv
      apply ih t _ budget (by omega)
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rwa [zrep]
      · exact hr _ hw
    · cases budget with
      | zero => omega
      | succ n =>
        simp only [viable,Bool.or_eq_true]
        right
        apply List.any_eq_true.mpr
        refine ⟨v,?_,ih (v::t) ?_ n (by omega)⟩
        · simp only [nextTables,List.mem_filter,List.mem_eraseDups,List.mem_flatMap,List.mem_map]
          refine ⟨⟨table pts a,available_table hr ha,table pts b,available_table hr hb,rfl⟩,?_⟩
          simpa using hv
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · rw [zrep]; exact recover z t
          · exact lit_extend (hr _ hw) _

theorem reject_sample {α} (pts : List α) {s : List (Signal α)} {f : Signal α} (budget : Nat)
    (no : viable budget (s.map (table pts)) (table pts f) = false) :
    ∀ k ≤ budget, ¬ Builds k s f := by
  intro k hk h
  have yes := search_complete pts h (s.map (table pts)) (by
    intro a ha
    have hm : table pts a ∈ s.map (table pts) := List.mem_map.mpr ⟨a,ha,rfl⟩
    simp only [literals,List.mem_cons,List.mem_flatMap]
    exact Or.inr (Or.inr ⟨_,hm,Or.inl rfl⟩)) budget hk
  rw [no] at yes
  contradiction

private def hits {m} (goal a b : BitVec m) : Bool :=
  let z := a &&& b
  z == goal || ~~~z == goal

private theorem one_step_test {m} {l : List (BitVec m)} {z f : BitVec m}
    (hz : z ∈ nextTables l) (hf : f ∈ literals (z::l)) (old : f ∉ literals l) :
    (literals l).any (fun a => (literals l).any (fun b => hits f a b)) = true := by
  have eqz : f = z ∨ f = ~~~z := by
    simp only [literals,List.flatMap_cons,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hf old
    tauto
  simp only [nextTables,List.mem_filter,List.mem_eraseDups,List.mem_flatMap,List.mem_map] at hz
  obtain ⟨⟨a,ha,b,hb,rfl⟩,_⟩ := hz
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
  rcases eqz with rfl | rfl <;> by_cases h : (a &&& b).getLsbD 0 <;> simp [hits,canonical,h]

/-- At the final gate, compare its result directly with the output. -/
def quick {m} : Nat → List (BitVec m) → BitVec m → Bool
  | 0, l, f => (literals l).contains f
  | 1, l, f => let t := literals l; t.contains f || t.any fun a => t.any fun b => hits f a b
  | n+2, l, f => (literals l).contains f || (nextTables l).any fun z => quick (n+1) (z::l) f

private theorem quick_of_viable {m} (k : Nat) (l : List (BitVec m)) (f : BitVec m)
    (yes : viable k l f = true) : quick k l f = true := by
  induction k generalizing l with
  | zero => exact yes
  | succ n ih =>
    cases n with
    | zero =>
      by_cases old : f ∈ literals l
      · simp [quick,old]
      · simp only [viable,Bool.or_eq_true,List.contains_iff_mem] at yes
        obtain ⟨z,hz,hf⟩ := List.any_eq_true.mp (yes.resolve_left old)
        simp only [quick,Bool.or_eq_true]
        exact Or.inr (one_step_test hz (List.contains_iff_mem.mp hf) old)
    | succ n =>
      simp only [viable,Bool.or_eq_true] at yes
      simp only [quick,Bool.or_eq_true]
      rcases yes with h | h
      · exact Or.inl h
      · obtain ⟨z,hz,h⟩ := List.any_eq_true.mp h
        exact Or.inr (List.any_eq_true.mpr ⟨z,hz,ih _ h⟩)

theorem reject_quick {α} (pts : List α) {s : List (Signal α)} {f : Signal α} (budget : Nat)
    (no : quick budget (s.map (table pts)) (table pts f) = false) :
    ∀ k ≤ budget, ¬ Builds k s f := by
  apply reject_sample pts budget
  cases hv : viable budget (s.map (table pts)) (table pts f) with
  | false => rfl
  | true => have h := quick_of_viable _ _ _ hv; rw [no] at h; contradiction

end PetersenSigned
#print axioms PetersenSigned.circuit_to_signed
#print axioms PetersenSigned.lower_of_two_bounds

#print axioms PetersenSigned.restrict_trace

#print axioms PetersenSigned.reject_sample
namespace PetersenSigned.Compact

inductive Plan {m : Nat} : Nat → List (BitVec m) → BitVec m → Prop where
  | stop {s f} : f ∈ literals s → Plan 0 s f
  | gate {k s f a b} : a ∈ literals s → b ∈ literals s →
      Plan k (canonical (a &&& b)::s) f → Plan (k+1) s f

private theorem present {m} {w : BitVec m} {s} (h : w ∈ s) : w ∈ literals s := by
  simp only [literals,List.mem_cons,List.mem_flatMap,List.not_mem_nil,or_false]
  exact Or.inr (Or.inr ⟨w,h,Or.inl rfl⟩)

private theorem complement {m} {w : BitVec m} {s} (h : w ∈ literals s) : ~~~w ∈ literals s := by
  simp only [literals,List.mem_cons,List.mem_flatMap,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl | rfl | ⟨a,ha,rfl | rfl⟩
  · exact Or.inr (Or.inl rfl)
  · simp
  · exact Or.inr (Or.inr ⟨_,ha,Or.inr rfl⟩)
  · exact Or.inr (Or.inr ⟨a,ha,Or.inl (by simp)⟩)

private theorem transport_lit {m} {s t : List (BitVec m)}
    (st : ∀ w ∈ s, w ∈ literals t) {a} (ha : a ∈ literals s) : a ∈ literals t := by
  simp only [literals,List.mem_cons,List.mem_flatMap,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | ⟨a,ha,rfl | rfl⟩
  · simp [literals]
  · simp [literals]
  · exact st _ ha
  · exact complement (st _ ha)

theorem rebase {m k s} {f : BitVec m} (h : Plan k s f) (t : List (BitVec m))
    (st : ∀ a ∈ s, a ∈ literals t) : Plan k t f := by
  induction h generalizing t with
  | stop hf => exact .stop (transport_lit st hf)
  | @gate k s f a b ha hb tail ih =>
    apply Plan.gate (transport_lit st ha) (transport_lit st hb)
    apply ih
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact present List.mem_cons_self
    · exact transport_lit (fun w hw => present (List.mem_cons_of_mem _ hw)) (st _ hz)

theorem of_builds {α} (pts : List α) {k s} {f : Signal α} (h : Builds k s f)
    (t : List (BitVec pts.length)) (hr : ∀ a ∈ s, table pts a ∈ literals t) :
    Plan k t (table pts f) := by
  induction h generalizing t with
  | stop ha => exact .stop (available_table hr ha)
  | @gate k s f a b ha hb tail ih =>
    apply Plan.gate (available_table hr ha) (available_table hr hb)
    apply ih
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [table_conj]; apply recover
    · exact transport_lit (fun u hu => present (List.mem_cons_of_mem _ hu)) (hr _ hw)

private theorem support_one {m s} {a : BitVec m} (h : a ∈ literals s) :
    ∃ S : Finset (BitVec m), (∀ w ∈ S, w ∈ s) ∧ S.card ≤ 1 ∧ a ∈ literals S.toList := by
  simp only [literals,List.mem_cons,List.mem_flatMap,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | ⟨w,hw,rfl | rfl⟩
  · exact ⟨∅,by simp,by simp,by simp [literals]⟩
  · exact ⟨∅,by simp,by simp,by simp [literals]⟩
  · exact ⟨{a},by simpa,by simp,present (by simp)⟩
  · exact ⟨{w},by simpa,by simp,complement (present (by simp))⟩

theorem compact_plan {m k s} {f : BitVec m} (h : Plan k s f) :
    ∃ S : Finset (BitVec m), (∀ w ∈ S, w ∈ s) ∧
      ∃ t ≤ k, S.card ≤ t+1 ∧ Plan t S.toList f := by
  classical
  induction h with
  | stop h =>
    obtain ⟨S,hm,hc,ha⟩ := support_one h
    exact ⟨S,hm,0,by omega,hc,.stop ha⟩
  | @gate k s f a b ha hb tail ih =>
    obtain ⟨S,hm,t,ht,hc,hs⟩ := ih
    let v := canonical (a &&& b)
    by_cases used : v ∈ S
    · obtain ⟨A,hA,ca,la⟩ := support_one ha
      obtain ⟨B,hB,cb,lb⟩ := support_one hb
      let T := (S.erase v ∪ A) ∪ B
      have ra : a ∈ literals T.toList := transport_lit (fun z hz => present (by
        have hz' : z ∈ A := by simpa using hz
        simp [T,hz'])) la
      have rb : b ∈ literals T.toList := transport_lit (fun z hz => present (by
        have hz' : z ∈ B := by simpa using hz
        simp [T,hz'])) lb
      refine ⟨T,?_,t+1,by omega,?_,.gate ra rb (rebase hs _ ?_)⟩
      · intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · rcases Finset.mem_union.mp hz with hz | hz
          · obtain ⟨hne,hin⟩ := Finset.mem_erase.mp hz
            exact (List.mem_cons.mp (hm z hin)).resolve_left hne
          · exact hA _ hz
        · exact hB _ hz
      · have h1 := Finset.card_union_le (S.erase v) A
        have h2 := Finset.card_union_le (S.erase v ∪ A) B
        have h3 := Finset.card_erase_of_mem used
        change ((S.erase v ∪ A) ∪ B).card ≤ t+1+1
        omega
      · intro z hz
        have hin : z ∈ S := by simpa using hz
        by_cases eqn : z = v
        · subst z; exact present List.mem_cons_self
        · apply present
          apply List.mem_cons_of_mem
          simp [T,Finset.mem_erase,hin,eqn]
    · refine ⟨S,?_,t,by omega,hc,hs⟩
      intro w hw
      exact (List.mem_cons.mp (hm w hw)).resolve_left (by rintro rfl; exact used hw)

end PetersenSigned.Compact
#print axioms PetersenSigned.Compact.compact_plan
namespace PetersenSigned.Compact

private theorem agree_lit {m} {s : List (BitVec m)} {p n : Nat} (hp : p < m) (hn : n < m)
    (same : ∀ w ∈ s, w.getLsbD p = w.getLsbD n) {z} (hz : z ∈ literals s) :
    z.getLsbD p = z.getLsbD n := by
  simp only [literals,List.mem_cons,List.mem_flatMap,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | ⟨w,hw,rfl | rfl⟩
  · simp
  · simp [hp,hn]
  · exact same _ hw
  · simp only [BitVec.getLsbD_not,decide_eq_true hp,decide_eq_true hn,same _ hw]

theorem agree_plan {m k s} {f : BitVec m} (h : Plan k s f)
    (p n : Nat) (hp : p < m) (hn : n < m)
    (same : ∀ w ∈ s, w.getLsbD p = w.getLsbD n) : f.getLsbD p = f.getLsbD n := by
  induction h with
  | stop hf => exact agree_lit hp hn same hf
  | @gate k s f a b ha hb tail ih =>
    apply ih
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · have aa := agree_lit hp hn same ha
      have bb := agree_lit hp hn same hb
      unfold canonical; split <;> simp only [BitVec.getLsbD_not,BitVec.getLsbD_and,decide_eq_true hp,decide_eq_true hn,aa,bb]
    · exact same _ hw

def diffBits {m} (r : Nat) (w : BitVec m) : BitVec r := (w ^^^ (w >>> r)).setWidth r

def coverage {m} (r : Nat) : List (BitVec m) → BitVec r
  | [] => 0
  | w::ws => diffBits r w ||| coverage r ws

private theorem missing_bit {m} (r : Nat) (s : List (BitVec m)) (i : Nat)
    (miss : (coverage r s).getLsbD i = false) : ∀ w ∈ s, (diffBits r w).getLsbD i = false := by
  induction s with
  | nil => simp
  | cons w ws ih =>
    simp only [coverage,BitVec.getLsbD_or,Bool.or_eq_false_iff] at miss
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact miss.1
    · exact ih miss.2 z hz

theorem covers {m k s} {f : BitVec m} (h : Plan k s f) (r : Nat) (hr : r+r ≤ m) :
    coverage r s ||| diffBits r f = coverage r s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases he : (coverage r s).getLsbD i with
  | true => simp [he]
  | false =>
    have same : ∀ w ∈ s, w.getLsbD i = w.getLsbD (r+i) := by
      intro w hw
      have hz := missing_bit r s i he w hw
      simpa [diffBits,hi] using hz
    have hf := agree_plan h i (r+i) (by omega) (by omega) same
    have hz : (diffBits r f).getLsbD i = false := by simp [diffBits,hi,hf]
    simp only [BitVec.getLsbD_or,he,hz,Bool.false_or]

/-- Choose enough live wires to cover any designated set of at most k wires. -/
def choices {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _+1, [] => [[]]
  | k+1, a::s => if s.length ≤ k then [a::s] else
      ((choices k s).map (a::·)) ++ choices (k+1) s

private theorem choices_cover {α : Type} [DecidableEq α] (s : List α) (k : Nat) (S : Finset α)
    (hm : ∀ w ∈ S, w ∈ s) (hc : S.card ≤ k) :
    ∃ u ∈ choices k s, ∀ w ∈ S, w ∈ u := by
  induction s generalizing S k with
  | nil =>
    cases k <;> exact ⟨[],by simp [choices],hm⟩
  | cons a s ih =>
    cases k with
    | zero =>
      have emp : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst S; exact ⟨[],by simp [choices],by simp⟩
    | succ k =>
      by_cases all : s.length ≤ k
      · exact ⟨_,by simp [choices,all],hm⟩
      · by_cases used : a ∈ S
        · have hh : ∀ w ∈ S.erase a, w ∈ s := by
            intro w hw
            obtain ⟨hne,hin⟩ := Finset.mem_erase.mp hw
            exact (List.mem_cons.mp (hm w hin)).resolve_left hne
          obtain ⟨u,hu,span⟩ := ih k (S.erase a) hh (by
            have := Finset.card_erase_of_mem used; omega)
          refine ⟨a::u,?_,?_⟩
          · simp only [choices,all,ite_false,List.mem_append,List.mem_map]
            exact Or.inl ⟨u,hu,rfl⟩
          · intro w hw
            by_cases e : w = a
            · exact List.mem_cons.mpr (Or.inl e)
            · exact List.mem_cons_of_mem _ (span w (Finset.mem_erase.mpr ⟨e,hw⟩))
        · obtain ⟨u,hu,span⟩ := ih (k+1) S (by
            intro w hw
            exact (List.mem_cons.mp (hm w hw)).resolve_left (by rintro rfl; exact used hw)) hc
          exact ⟨u,by simp [choices,all,hu],span⟩

def search {m} (r : Nat) : Nat → List (BitVec m) → BitVec m → Bool
  | 0, s, f => (literals s).contains f
  | k+1, s, f =>
    let c := coverage r s
    (literals s).contains f || ((c ||| diffBits r f == c) &&
      (nextTables s).any fun v => (choices k s).any fun u => search r k (v::u) f)

private theorem accepts_old {m} {s : List (BitVec m)} {f} (hf : f ∈ literals s) (r k) :
    search r k s f = true := by cases k <;> simp [search,hf]

theorem search_yes {m} (r : Nat) (hr : r+r ≤ m) (t : Nat) :
    ∀ budget, t ≤ budget → ∀ s (f : BitVec m), Plan t s f → search r budget s f = true := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro budget hbudget s f plan
    cases plan with
    | stop ha => exact accepts_old ha _ _
    | @gate k s f a b ha hb tail =>
      let v := canonical (a &&& b)
      by_cases old : v ∈ literals s
      · apply ih k (by omega) budget (by omega) s f
        exact rebase tail _ (fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ old) (fun hw => present hw))
      obtain ⟨S,hm,j,hj,card,small⟩ := compact_plan tail
      by_cases used : v ∈ S
      · cases budget with
        | zero => omega
        | succ n =>
          have cover := covers (Plan.gate ha hb tail) r hr
          have span : ∀ w ∈ S.erase v, w ∈ s := by
            intro w hw
            obtain ⟨hne,hin⟩ := Finset.mem_erase.mp hw
            exact (List.mem_cons.mp (hm w hin)).resolve_left hne
          obtain ⟨u,hu,hU⟩ := choices_cover s n (S.erase v) span (by
            have := Finset.card_erase_of_mem used; omega)
          simp only [search,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
          right
          refine ⟨cover,List.any_eq_true.mpr ⟨v,?_,List.any_eq_true.mpr ⟨u,hu,?_⟩⟩⟩
          · simp only [nextTables,List.mem_filter,List.mem_eraseDups,List.mem_flatMap,List.mem_map]
            exact ⟨⟨a,ha,b,hb,rfl⟩,by simpa using old⟩
          · apply ih j (by omega) n (by omega) _ f (rebase small _ ?_)
            intro w hw
            have hin : w ∈ S := by simpa using hw
            apply present
            by_cases e : w = v
            · exact List.mem_cons.mpr (Or.inl e)
            · exact List.mem_cons_of_mem _ (hU w (Finset.mem_erase.mpr ⟨e,hin⟩))
      · apply ih j (by omega) budget (by omega) s f (rebase small _ ?_)
        intro w hw
        have hin : w ∈ S := by simpa using hw
        exact present ((List.mem_cons.mp (hm w hin)).resolve_left (by rintro rfl; exact used hin))

theorem reject {α} (pts : List α) (r budget : Nat) (hr : r+r ≤ pts.length)
    {s : List (Signal α)} {f : Signal α}
    (no : search r budget (s.map (table pts)) (table pts f) = false) :
    ∀ k ≤ budget, ¬ Builds k s f := by
  intro k hk h
  have plan := of_builds pts h (s.map (table pts)) (fun w hw => present (List.mem_map.mpr ⟨w,hw,rfl⟩))
  have yes := search_yes r hr k budget hk _ _ plan
  rw [no] at yes; contradiction

end PetersenSigned.Compact
#print axioms PetersenSigned.Compact.reject
