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

/-- A signal either agrees on the two test inputs or becomes constant on the cofactor. -/
def Compatible {α β} (σ : β → α) (x y : α) (u : Signal α) : Prop :=
  u x = u y ∨ ∃ c : Bool, (u ∘ σ) = fun _ => c

private theorem compatible_available {α β} {σ : β → α} {x y : α} {s : List (Signal α)}
    (hs : ∀ u ∈ s, Compatible σ x y u) {u} (h : Available s u) : Compatible σ x y u := by
  cases h with
  | zero | one => exact Or.inl rfl
  | pos hw => exact hs _ hw
  | negated hw =>
    rcases hs _ hw with h | ⟨c,hc⟩
    · exact Or.inl (congrArg (! ·) h)
    · refine Or.inr ⟨!c,?_⟩
      funext z
      exact congrArg (! ·) (congrFun hc z)

private theorem projected_member {α β} (σ : β → α) {s : List (Signal α)} {a}
    (h : Available s a) : Available (s.map fun z => z ∘ σ) (a ∘ σ) :=
  transport σ (fun z hz => .pos (List.mem_map.mpr ⟨z,hz,rfl⟩)) h

private theorem and_compatible_or_saved {α β} {σ : β → α} {x y : α} {s : List (Signal α)}
    (hs : ∀ u ∈ s, Compatible σ x y u) {a b} (ha : Available s a) (hb : Available s b) :
    Compatible σ x y (conj a b) ∨ Available (s.map fun z => z ∘ σ) ((conj a b) ∘ σ) := by
  have left_const (c : Bool) (hc : (a ∘ σ) = fun _ => c) :
      Available (s.map fun z => z ∘ σ) ((conj a b) ∘ σ) := by
    have eqn : (conj a b) ∘ σ = (fun i => c && (b ∘ σ) i) := by
      funext i
      exact congrArg (fun bit => bit && b (σ i)) (congrFun hc i)
    rw [eqn]
    cases c with
    | false =>
      simpa only [Bool.false_and] using (Available.zero (s := s.map fun z => z ∘ σ))
    | true =>
      simpa only [Bool.true_and] using projected_member σ hb
  have right_const (c : Bool) (hc : (b ∘ σ) = fun _ => c) :
      Available (s.map fun z => z ∘ σ) ((conj a b) ∘ σ) := by
    have eqn : (conj a b) ∘ σ = (fun i => (a ∘ σ) i && c) := by
      funext i
      exact congrArg (fun bit => a (σ i) && bit) (congrFun hc i)
    rw [eqn]
    cases c with
    | false => simpa only [Bool.and_false] using (Available.zero (s := s.map fun z => z ∘ σ))
    | true => simpa only [Bool.and_true] using projected_member σ ha
  rcases compatible_available hs ha with ea | ⟨c,h⟩
  · rcases compatible_available hs hb with eb | ⟨d,h⟩
    · exact Or.inl (Or.inl (congrArg₂ (· && ·) ea eb))
    · exact Or.inr (right_const _ h)
  · exact Or.inr (left_const _ h)

/-- A computation distinguishing the test inputs while remaining nonconstant after
restriction must save at least one binary gate if all its starting signals are compatible. -/
theorem saves_one {α β} (σ : β → α) (x y : α) {s : List (Signal α)} {gs} {f}
    (plan : Trace s gs f) (ok : ∀ a ∈ s, Compatible σ x y a) (diff : ¬ Compatible σ x y f) :
    0 < saved σ s gs := by
  classical
  induction gs generalizing s with
  | nil => exact False.elim (diff (compatible_available ok plan))
  | cons g gs ih =>
    obtain ⟨a,b⟩ := g
    obtain ⟨ha,hb,ht⟩ := plan
    by_cases reusable : Available (s.map fun z => z ∘ σ) ((conj a b) ∘ σ)
    · simp [saved,reusable]
    · have safe := (and_compatible_or_saved ok ha hb).resolve_right reusable
      have more := ih ht (fun z hz => (List.mem_cons.mp hz).elim (fun he => he ▸ safe) (ok z))
      simpa only [saved,reusable,ite_false,zero_add] using more

/-- The first gate disappears on the cofactor and masks the varying input on the test pair.
The later distinguishing computation then has to lose a second gate. -/
theorem saves_two {α β} (σ : β → α) (x y : α) {s : List (Signal α)} {gs a b f}
    (h : Trace s ((a,b)::gs) f) (ok : ∀ z ∈ s, Compatible σ x y z)
    (agree : conj a b x = conj a b y)
    (erase : Available (s.map fun z => z ∘ σ) ((conj a b) ∘ σ))
    (diff : ¬ Compatible σ x y f) :
    ∃ k, k+2 ≤ gs.length+1 ∧ Builds k (s.map fun z => z ∘ σ) (f ∘ σ) := by
  classical
  have tail := saves_one σ x y h.2.2 (by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inl agree
    · exact ok z hz) diff
  obtain ⟨k,eqn,build⟩ := restrict_trace σ s ((a,b)::gs) f h
    (s.map fun z => z ∘ σ) (fun z hz => .pos (List.mem_map.mpr ⟨z,hz,rfl⟩))
  simp only [saved,erase,ite_true,List.length_cons] at eqn
  exact ⟨k,by omega,build⟩

noncomputable def raws {n} (I : Finset (Fin n)) : List (Signal (Fin n → Bool)) := I.toList.map inputSignal
def fixed {n} (i : Fin n) (x : Fin n → Bool) : Fin n → Bool := Function.update x i false
def lit {n} (i : Fin n) (p : Bool) : Signal (Fin n → Bool) :=
  fun x => if p then !(x i) else x i

private theorem raw_specs {n I a} (h : Available (raws (n := n) I) a) :
    (∃ c : Bool, a = fun _ => c) ∨ ∃ i ∈ I, ∃ p, a = lit i p := by
  cases h with
  | zero => exact Or.inl ⟨_,rfl⟩
  | one => exact Or.inl ⟨_,rfl⟩
  | pos hw =>
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact Or.inr ⟨i,by simpa using hi,false,rfl⟩
  | negated hw =>
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact Or.inr ⟨i,by simpa using hi,true,rfl⟩

private theorem const_left {α} {s : List (Signal α)} {b} (hb : Available s b) (c : Bool) :
    Available s (conj (fun _ => c) b) := by
  cases c with
  | false => exact .zero
  | true =>
    have eqn : conj (fun _ => true) b = b := by funext x; simp [conj]
    rwa [eqn]

private theorem const_right {α} {s : List (Signal α)} {a} (ha : Available s a) (c : Bool) :
    Available s (conj a (fun _ => c)) := by
  have e : conj a (fun _ => c) = conj (fun _ => c) a := by funext x; simp [conj,Bool.and_comm]
  rw [e]; exact const_left ha c

private theorem lit_ok {n} {I : Finset (Fin n)} {i} (hi : i ∈ I) (p : Bool) :
    Available (raws I) (lit i p) := by
  have h : inputSignal i ∈ raws I := List.mem_map.mpr ⟨i,by simpa using hi,rfl⟩
  cases p with
  | false => exact .pos h
  | true => exact .negated h

private theorem same_input {n} {I : Finset (Fin n)} {i} (hi : i ∈ I) (p q : Bool) :
    Available (raws I) (conj (lit i p) (lit i q)) := by
  by_cases e : p = q
  · subst q
    have e : conj (lit i p) (lit i p) = lit i p := by funext x; simp [conj]
    rw [e]; exact lit_ok hi p
  · have e' : conj (lit i p) (lit i q) = (fun _ => false) := by
      funext x; cases p <;> cases q <;> simp_all [lit,conj]
    rw [e']; exact .zero

private theorem project_raws {n} (I : Finset (Fin n)) (i : Fin n) :
    ∀ z ∈ (raws I).map (fun z => z ∘ fixed i), Available (raws (I.erase i)) z := by
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
  by_cases e : j = i
  · subst j
    have eqn : inputSignal i ∘ fixed i = fun _ => false := by funext x; simp [inputSignal,fixed]
    rw [eqn]; exact .zero
  · have eqn : inputSignal j ∘ fixed i = inputSignal j := by
      funext x; simp [inputSignal,fixed,Function.update_of_ne e]
    rw [eqn]
    exact .pos (List.mem_map.mpr ⟨j,by simpa [e] using hj,rfl⟩)

/-- A lower bound for every one-input cofactor lifts by two gates when the
target remains sensitive to each first operand with the other operand fixed. -/
theorem lift_two {n L} (I : Finset (Fin n)) (f : Signal (Fin n → Bool))
    (not_input : ¬ Available (raws I) f)
    (robust : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ p : Bool, ∃ x y,
      x j = p ∧ y j = p ∧ (∀ h ≠ i, x h = y h) ∧ f x ≠ f y)
    (nonconst : ∀ i ∈ I, ¬ ∃ c : Bool, f ∘ fixed i = fun _ => c)
    (child : ∀ i ∈ I, ∀ t < L, ¬ Builds t (raws (I.erase i)) (f ∘ fixed i)) :
    ∀ k < L+2, ¬ Builds k (raws I) f := by
  intro k
  induction k with
  | zero =>
    intro _ h
    cases h with | stop h => exact not_input h
  | succ k ih =>
    intro hk h
    cases h with
    | @gate _ _ _ a b ha hb tail =>
      have redundant (hv : Available (raws I) (conj a b)) : False := by
        apply ih (by omega)
        exact simulate tail _ (fun z hz => (List.mem_cons.mp hz).elim
          (fun eqn => eqn ▸ hv) (fun hz => .pos hz))
      rcases raw_specs ha with ⟨c,rfl⟩ | ⟨i,hi,p,rfl⟩
      · exact redundant (const_left hb c)
      rcases raw_specs hb with ⟨c,rfl⟩ | ⟨j,hj,q,rfl⟩
      · exact redundant (const_right ha c)
      by_cases ij : i = j
      · subst j; exact redundant (same_input hi p q)
      obtain ⟨x,y,xj,yj,away,changeF⟩ := robust i hi j hj ij q
      obtain ⟨gs,hkGs,ht⟩ := trace_of_builds tail
      have agree : conj (lit i p) (lit j q) x = conj (lit i p) (lit j q) y := by
        cases q <;> simp_all [conj,lit]
      have erase : Available ((raws I).map (fun z => z ∘ fixed i))
          (conj (lit i p) (lit j q) ∘ fixed i) := by
        have eqn : conj (lit i p) (lit j q) ∘ fixed i = conj (fun _ => p) (lit j q ∘ fixed i) := by
          funext z; cases p <;> simp [conj,lit,fixed]
        rw [eqn]
        exact const_left (projected_member (fixed i) hb) p
      have ok : ∀ z ∈ raws I, Compatible (fixed i) x y z := by
        intro z hz
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
        by_cases e : u = i
        · subst u
          exact Or.inr ⟨false,by funext z; simp [inputSignal,fixed]⟩
        · exact Or.inl (away u e)
      have bad : ¬ Compatible (fixed i) x y f := fun h => h.elim changeF (nonconst i hi)
      obtain ⟨t,hle,small⟩ := saves_two (fixed i) x y (s := raws I) (gs := gs)
        (a := lit i p) (b := lit j q) (f := f) ⟨ha,hb,ht⟩ ok agree erase bad
      exact child i hi t (by omega) (simulate small _ (project_raws I i))

/-- Fixing an essential input to zero saves a gate whenever the resulting
function is nonconstant. The varying pair need only agree off that input. -/
theorem lift_one {n L} (I : Finset (Fin n)) (i : Fin n) (f : Signal (Fin n → Bool))
    (essential : ∃ x y, (∀ j ≠ i, x j = y j) ∧ f x ≠ f y)
    (nonconst : ¬ ∃ c : Bool, f ∘ fixed i = fun _ => c)
    (child : ∀ k < L, ¬ Builds k (raws (I.erase i)) (f ∘ fixed i)) :
    ∀ k < L+1, ¬ Builds k (raws I) f := by
  intro k hk hb
  obtain ⟨x,y,away,diff⟩ := essential
  obtain ⟨gs,hlen,ht⟩ := trace_of_builds hb
  have saved_gate := saves_one (fixed i) x y ht (by
    intro z hz
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
    by_cases h : j = i
    · subst j; exact Or.inr ⟨false,by funext w; simp [inputSignal,fixed]⟩
    · exact Or.inl (away _ h)) (fun h => h.elim diff nonconst)
  obtain ⟨t,hts,hb'⟩ := restrict_trace (fixed i) _ gs f ht _ (by
    intro z hz
    exact .pos (List.mem_map.mpr ⟨z,hz,rfl⟩))
  exact child t (by omega) (simulate hb' _ (project_raws I i))
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

private theorem table_conj {α} (p : List α) (a b : Signal α) :
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

private theorem available_table {α} {p : List α} {s : List (Signal α)} {t : List (BitVec p.length)}
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

private theorem recover {m} (z : BitVec m) (t : List (BitVec m)) : z ∈ literals (canonical z :: t) := by
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




namespace PetersenSigned.Petersen
open PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def edge (x : Fin 10 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
private def singleMasks : Array Nat := #[
19816716759939451299108491264,19816717052781513469253910528,19816749816504831399507853312,19845730979610756548866871296,79237838645637695698173431808,19816716759795336111032635392,19816716757633608289894797312,19816712037717083617539133440,19807045353382534265710841856,9676131373366900722503680,19816716759939451299108491264,19816717052781513469253910528,19816717052638516484503502864,19816750109203896584896512016,19845731272309267580527312912,79237838938336768580149837856,19816717052637390584596660240,19816716757490611305150677008,19816712330272033614858289168,19807045941229504630458679312,
9676424072432086117515280,19816717052638516484503502864,19816749816504831399507853312,19816750109203896584896512016,19816749816361834414757381122,19845764036032585497770460162,79237871702060086768101753858,19817316500338652872276182018,19816749814055991405543687170,19816712037429971457595671554,19807078409804917381359731714,9709187795750016371393538,19816749816361834414757381122,19845730979610756548866871296,19845731272309267580527312912,19845764036032585497770460162,19845730979467205410256061442,79266852865165457505902396418,19884416605693747643939816450,19845730977161362401042367490,
19845726257100722540610847746,19807045353239537276665463810,38690350901121011870073858,19845730979467205410256061442,79237838645637695698173431808,79237838938336768580149837856,79237871702060086768101753858,79266852865165457505902396418,79237838645494706410004415490,79237838645493580510097572866,158466001157453200994334671874,79237833923128223540359201794,79228167238937789376606766082,9676131230368816460465154,79237838645494706410004415490,19816716759795336111032635392,19816717052637390584596660240,19817316500338652872276182018,19884416605693747643939816450,79237838645493580510097572866,
19816716759795328414451237890,19816716757489485405237543938,19816712037428845544806024194,19807045353238411381053588482,9676131229244016065250306,19816716759795328414451237890,19816716757633608289894797312,19816716757490611305150677008,19816749814055991405543687170,19845730977161362401042367490,158466001157453200994334671874,19816716757489485405237543938,19816716757490611305144386562,19816712035124128435499172866,19807045350933694271746737154,9676128924526906758398978,19816716757490611305144386562,19816712037717083617539133440,19816712330272033614858289168,19816712037429971457595671554,
19845726257100722540610847746,79237833923128223540359201794,19816712037428845544806024194,19816712035124128435499172866,19816712037429971444712866818,19807040630873054411315217410,9671408863887046326879234,19816712037429971444712866818,19807045353382534265710841856,19807045941229504630458679312,19807078409804917381359731714,19807045353239537276665463810,79228167238937789376606766082,19807045353238411381053588482,19807045350933694271746737154,19807040630873054411315217410,19807045353239537280960431106,4724673452882574443522,19807045353239537280960431106,9676131373366900722503680,
9676424072432086117515280,9709187795750016371393538,38690350901121011870073858,9676131230368816460465154,9676131229244016065250306,9676128924526906758398978,9671408863887046326879234,4724673452882574443522,9676131230369915972092930,9676131230369915972092930,19816716759939451299108491264,19816717052638516484503502864,19816749816361834414757381122,19845730979467205410256061442,79237838645494706410004415490,19816716759795328414451237890,19816716757490611305144386562,19816712037429971444712866818,19807045353239537280960431106,9676131230369915972092930,
19816716759796454314358080514]
private def pairMasks : Array Nat := #[
0,0,24763721496199015655094091776,638782202933183930158897205252,22285348005814882957193641984,636303902639412796122239895554,19811876331849064126229774336,638782198210763404098018512900,10035609749256765702144,633835878224412832051226517512,178418268870332677130438049792,950892995055255976773205098496,22285350367290860567078633472,633828020199661045860121217026,24763683717267117550071709696,633830442775826231883435376644,59430802773922165318750306304,643738491835107791233093763080,19884496902087392002557607936,321139511712058582286352,
19845773496927860892461170688,673459045323890430086190497808,0,0,178273046655958594947838387208,643738945191504511565224255496,19811876331849064106898232324,638782198210763404098018512900,9445891517842943116296,633826812453279003514126770177,178264585209397512775003014272,635064751311971637171707707392,337029789898528473525273232640,634135087946119386872280547584,24763683717267117513560298500,633830442775826231883435376644,59430802773922165308004508680,643738491835107791233093763080,19884496902087391983213544464,321139511712058582286352,
19809470288427363842226388992,636303902639415047930643513346,99036422695127544582413222976,635064752492564383787952209921,0,0,20116525638387429486455161872,950757595234349680185013485584,9445885887254635742216,633826812453279003514126770177,178264585209391882315544659072,635064751311971637171707707392,22285350366998124392276558850,633828020199661045860121217026,59459854772484238209161102368,633864892471600568104355136000,59430802773881624126010958856,643738491835107791233093763080,19884496902064856412234777616,321139511712058582286352,
19809458480227833856059768832,636303902639415047930643513346,24760009711531724826296189956,635064752492564383787952148481,22285338558776074208815481858,636303902639412796251088914434,0,0,5631150950188544,633826812453279003514127286273,178264574582920004953281922176,635064751311971637171707707392,22285338559068810383752168450,633828020199661045860121217026,24763636488990602835192189956,633830442775826231883435376644,59459807511966488946307826720,673478066997690745713953112128,19884411881043956275234276368,321139511712058582286352,
11808262584781177356288,636303902639415047947823382530,10626482012660447577092,635064752492564383787952148481,9447038808750660002818,636303902639412796122239895554,4785351633671172,638782198211033620075660742660,0,0,10626483138699941905536,635064751311971637171707707392,11808514786360545248258,633828020199661045860121217026,47228281053535390405636,633830442775826231883435376644,9481666995090194703368,643738491835107791233093763080,85076460299650515141696,453421113517406452547648,
19809470288449884039386497024,636303902639415047930643480576,24760020338009232787604767748,635064752492564383787952111616,22285348005814882957193651202,636303902639412796122239860736,19811876331849064126229779460,638782198210763404098018476032,9445891517853681583112,633826812453279003514126729216,0,0,22285350367290860567078896642,633828020199661045860121182208,24764250401245590188474766340,633830442775826231883435343872,99044884067983851059960357896,643738491835107791233093730304,19884496902087392002557674512,321139511712058582237184,
19809470288449884039386497024,636303902639415047844742070274,24760020338009232787604767748,635064752492564383719231623169,22285348005814882957193651202,636303902639412796044928387074,19811876331849064126229779460,638782198210763404024999874564,9445891517853681583112,633826812453279003444332503041,178264585209397512914590499968,635064751311971637101913440256,0,0,24763683717267117550071714820,633830442775826231810416738308,59430802773922165318750315528,643738491835107791164365897736,19961943712406454184062354448,321139511711989846032400,
19809470288449884039386497024,636303902639268678743730716674,24760020338009232787604767748,635064752492419141600457822209,22285348005814882957193651202,636303902639268678735140784130,19811876331849064126229779460,638782198210601270113386663940,9445891517853681583112,633826812453133761326632443905,336720910237926188239117354240,635064751311827520884120223744,22285350367290860567078896642,633828020199514676673208420354,0,0,59430802773922165318750315528,643738491834954660049670144008,19884496902087392002557674512,321139367579278320386064,
19809470288449884039386497024,636303598044471059829313536002,24760020338009232787604767748,635064449079364937908640321537,22285348005814882957193651202,636303598044468808020909918210,19811876331849064126229779460,638781895974696814422297448452,9445891517853681583112,633826509040079557634814943233,178264585209397512914590499968,635064449079363812009807183872,22285350367579090943499305986,633827717965900299193613846530,24763683717267117550071714820,633830135817393159338069098500,0,0,19884496902087392002557674512,144132848998203408,
19809470288449884039386497024,304595090357374144249858,24760020338009232787604767748,303413344688135526715393,22285348005814882957193651202,304595088105565740632066,19811876331849064126229779460,302236228723733371588612,9445891517853681583112,303413344688136600461313,178264585209397512914590499968,302232751941519282274304,22285350367290860567078896642,302233907115853420201986,24763683717267117550071714820,306958433072618384949252,59430802773922165318750315528,153131252151517192,0,0,
19809470288449884039386497024,636303902639415047930643513346,24760020338009232787604767748,635064752492564383787952148481,22285348005814882957193651202,636303902639412796122239895554,19811876331849064126229779460,638782198210763404098018512900,9445891517853681583112,633826812453279003514126770177,178264585209397512914590499968,635064751311971637171707707392,22285350367290860567078896642,633828020199661045860121217026,24763683717267117550071714820,633830442775826231883435376644,59430802773922165318750315528,643738491835107791233093763080,19884496902087392002557674512,321139511712058582286352]
def region (d e : Fin 11) : Finset (Fin 10) :=
  Finset.univ.filter (fun v => v.val ≠ d.val ∧ v.val ≠ e.val)
def graph (I : Finset (Fin 10)) (x : Fin 10 → Bool) :=
  edge (fun k => decide (k ∈ I) && x k)
private def single (d e : Fin 11) (i j : Fin 10) :=
  (singleMasks[d.val*11 + e.val]!).testBit (i.val*10+j.val)
private def pair (d : Fin 11) (i j : Fin 10) (p : Bool) (h : Fin 10) :=
  let idx := ((d.val*10+i.val)*10+j.val)*2 + (if p then 1 else 0)
  (pairMasks[idx/10]!).testBit (idx%10*10+h.val)

private theorem region_card : ∀ d e, 8 ≤ (region d e).card := by decide +kernel
theorem region_erase : ∀ (d : Fin 11) (i : Fin 10),
    (region d 10).erase i = region d i.castSucc := by decide +kernel
theorem region_swap : ∀ d e, region d e = region e d := by decide +kernel
theorem all_region : region 10 10 = Finset.univ := by decide +kernel

theorem graph_fixed (I : Finset (Fin 10)) (i : Fin 10) :
    graph I ∘ fixed i = graph (I.erase i) := by
  funext x
  simp only [Function.comp_apply,graph]
  apply congrArg edge
  funext j
  by_cases h : j = i
  · subst j; simp [fixed]
  · simp [fixed,Function.update_of_ne h,h]

private theorem single_valid : ∀ d e i, i ∈ region d e →
    graph (region d e) (single d e i) = false ∧
    graph (region d e) (Function.update (single d e i) i true) = true := by
  simp only [region,Finset.mem_filter,Finset.mem_univ,true_and]
  decide +kernel

private theorem pair_valid : ∀ d i j p, i ∈ region d 10 → j ∈ region d 10 → i ≠ j →
    pair d i j p j = p ∧ graph (region d 10) (pair d i j p) = false ∧
    graph (region d 10) (Function.update (pair d i j p) i true) = true := by
  simp only [region,Finset.mem_filter,Finset.mem_univ,true_and]
  decide +kernel

private theorem base (d e : Fin 11) (k : Nat) (hk : k < 7) :
    ¬ Builds k (raws (region d e)) (graph (region d e)) := by
  intro h
  have hr := simulate h (raw 10) (by
    intro z hz
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
    exact .pos (List.mem_ofFn.mpr ⟨j,rfl⟩))
  have hc := indispensable [] (region d e) (by simpa using hr) (by
    intro i hi
    obtain ⟨h0,h1⟩ := single_valid d e i hi
    refine ⟨single d e i,Function.update (single d e i) i true,?_,by simp,?_⟩
    · intro j hj; simp [Function.update_of_ne hj]
    · rw [h0,h1]; decide)
  have := region_card d e
  omega

theorem no_raw (d e : Fin 11) :
    ¬ Available (raws (region d e)) (graph (region d e)) := fun h => base d e 0 (by decide) (.stop h)
theorem varies (d e : Fin 11) :
    ¬ ∃ c : Bool, graph (region d e) = fun _ => c := by
  rintro ⟨c,he⟩
  apply no_raw d e
  rw [he]
  cases c
  · exact .zero
  · exact .one
theorem robust (d : Fin 11) : ∀ i ∈ region d 10, ∀ j ∈ region d 10,
    i ≠ j → ∀ p : Bool, ∃ x y : Fin 10 → Bool, x j = p ∧ y j = p ∧
    (∀ h ≠ i, x h = y h) ∧ graph (region d 10) x ≠ graph (region d 10) y := by
  intro i hi j hj ij p
  obtain ⟨hp,h0,h1⟩ := pair_valid d i j p hi hj ij
  refine ⟨pair d i j p,Function.update (pair d i j p) i true,hp,?_,?_,?_⟩
  · simpa [Function.update_of_ne ij.symm] using hp
  · intro h hn; simp [Function.update_of_ne hn]
  · rw [h0,h1]; decide

private theorem nine (d : Fin 11) : ∀ k < 9, ¬ Builds k (raws (region d 10)) (graph (region d 10)) := by
  apply lift_two (L := 7) _ _ (no_raw d 10) (robust d)
  · intro i _; rw [graph_fixed,region_erase]; exact varies d i.castSucc
  · intro i _; rw [graph_fixed,region_erase]; exact base d i.castSucc

theorem full_signed_lower : ∀ k < 11, ¬ Builds k (raw 10) edge := by
  have h := lift_two (L := 9) _ _ (no_raw 10 10) (robust 10) (by
    intro i _; rw [graph_fixed,region_erase]; exact varies 10 i.castSucc) (by
    intro i _; rw [graph_fixed,region_erase,region_swap 10 i.castSucc]; exact nine i.castSucc)
  have he : graph (region 10 10) = edge := by funext x; simp [graph,all_region]
  rw [he] at h
  intro k hk hb
  apply h _ hk
  apply simulate hb
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact .pos (List.mem_map.mpr ⟨i,by simp [all_region],rfl⟩)

theorem full_ordinary_lower : ¬ HasCircuitSize 10 edge 10 := by
  rintro ⟨C,hc,hs,he⟩
  have hb := circuit_to_signed 10 C hc
  rw [show (fun x => C.eval (List.ofFn x)) = edge from funext he] at hb
  apply full_signed_lower _ _ hb
  have h := List.countP_le_length (p := fun g => binaryOp g.op) (l := C.gates)
  change C.gates.length ≤ 10 at hs
  omega

end PetersenSigned.Petersen

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

namespace PetersenSigned.LowerSeeds

def path (x : Fin 4 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
def cycle (x : Fin 5 → Bool) :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0)
def feed {n m} (v : Fin n → Option (Fin m)) (x : Fin m → Bool) (i : Fin n) :=
  (v i).elim false x

theorem project_lower {n m L} (I : Finset (Fin n)) (v : Fin n → Option (Fin m))
    (f : Signal (Fin n → Bool)) (g : Signal (Fin m → Bool))
    (eqn : ∀ x, f (feed v x) = g x) (small : ∀ k < L, ¬ Builds k (raw m) g) :
    ∀ k < L, ¬ Builds k (raws I) f := by
  intro k hk hb
  obtain ⟨gs,hlen,ht⟩ := trace_of_builds hb
  obtain ⟨t,hs,plan⟩ := restrict_trace (feed v) _ _ _ ht (raw m) (by
    intro z hz
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
    cases he : v j with
    | none =>
      have e : inputSignal j ∘ feed v = fun _ => false := by funext x; simp [inputSignal,feed,he]
      rw [e]; exact .zero
    | some i =>
      have e : inputSignal j ∘ feed v = inputSignal i := by funext x; simp [inputSignal,feed,he]
      rw [e]; exact .pos (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have e : f ∘ feed v = g := funext eqn
  rw [e] at plan
  exact small t (by omega) plan


end PetersenSigned.LowerSeeds


namespace PetersenSigned.CycleSeven
def cycle (x : Fin 5 → Bool) :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0)
def samples : List (Fin 5 → Bool) := ([3,3,3,3,3,3,3,6,6,6,6,6,6,6,7,11,11,12,12,12,12,12,12,12,13,13,14,17,17,17,17,17,17,17,19,21,21,22,22,24,24,24,24,24,24,24,25,26,26,28,1,2,5,9,10,18,20,2,4,5,9,10,18,20,5,9,10,4,5,8,9,10,18,20,5,9,10,1,5,9,10,16,18,20,18,5,20,18,20,5,8,9,10,16,18,20,9,10,18,20] : List Nat).map (fun w i => w.testBit i.val)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : ∀ k < 7, ¬ Builds k (raw 5) cycle := by
  intro k hk
  apply Compact.reject samples 50 6 (by decide) ?_ k (by omega)
  decide +kernel
end PetersenSigned.CycleSeven


namespace PetersenSigned.Petersen
open LowerSeeds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 20000
-- Each row stores five cycle vertices, three vertices to delete, and one
-- surviving neighbor of each deleted vertex. Every row is checked below.
private def layouts : Array Nat := #[
2694912049953,3880609354802,10404375324995,7118996805409,6767112520481,6749931602721,3790394070066,7162214908705,8325059483425,2694912049953,2694912049953,
3880609354802,6062181024576,4778543645504,6079629326656,8270329108530,3867719210034,4757064614720,4963206267712,10185030859072,6062181024576,6062181024576,
10404375324995,4778543645504,5516687672848,6943205066256,6977563756048,7234993296912,4744178664256,6616736171536,9914750899728,5516687672848,5516687672848,
7118996805409,6079629326656,6943205066256,5568530313744,8047030530576,7222107346448,8042733466128,6603850221072,7767822004752,5568530313744,5568530313744,
6767112520481,8270329108530,6977563756048,8047030530576,5577119199760,6741337473825,8051322352144,7153589257744,7776410890768,5577119199760,5577119199760,
6749931602721,3867719210034,7234993296912,7222107346448,6741337473825,3442540294672,4615352627728,4611056611856,4542320357904,3442540294672,3442540294672,
3790394070066,4757064614720,4744178664256,8042733466128,8051322352144,4615352627728,3438244278800,4606760595984,4538024342032,3438244278800,3438244278800,
7162214908705,4963206267712,6616736171536,6603850221072,7153589257744,4611056611856,4606760595984,3369508024848,4469288088080,3369508024848,3369508024848,
8325059483425,10185030859072,9914750899728,7767822004752,7776410890768,4542320357904,4538024342032,4469288088080,2269727961616,2269727961616,2269727961616,
2694912049953,6062181024576,5516687672848,5568530313744,5577119199760,3442540294672,3438244278800,3369508024848,2269727961616,2269727961616,2269727961616,
2694912049953,6062181024576,5516687672848,5568530313744,5577119199760,3442540294672,3438244278800,3369508024848,2269727961616,2269727961616,2269727961616]

private def digit (d e : Fin 11) (h : Nat) : Fin 10 :=
  ⟨((layouts[d.val*11+e.val]! >>> (4*h))%16)%10, Nat.mod_lt _ (by decide)⟩
private def cycleMap (d e : Fin 11) (j : Fin 10) : Option (Fin 5) :=
  if j = digit d e 0 then some 0 else if j = digit d e 1 then some 1 else
  if j = digit d e 2 then some 2 else if j = digit d e 3 then some 3 else
  if j = digit d e 4 then some 4 else none
private def live (d e : Fin 11) : Nat → Finset (Fin 10)
  | 0 => region d e
  | h+1 => (live d e h).erase (digit d e (5+h))
private def witness (d e : Fin 11) (h : Nat) (i : Fin 10) :=
  decide (i = digit d e (8+h))

private theorem recognizes_cycle : ∀ d e x,
    graph (live d e 3) (feed (cycleMap d e) x) = cycle x := by decide +kernel
private theorem recognizes_neighbor : ∀ d e (h : Fin 3),
    graph (live d e h.val) (witness d e h.val) = false ∧
    graph (live d e h.val) (Function.update (witness d e h.val) (digit d e (5+h.val)) true) = true := by decide +kernel

private abbrev Lower (I : Finset (Fin 10)) (L : Nat) :=
  ∀ k < L, ¬ Builds k (raws I) (graph I)

private theorem raise_one (d e : Fin 11) (h : Fin 3) (L : Nat) (hp : 0 < L)
    (child : Lower (live d e (h.val+1)) L) : Lower (live d e h.val) (L+1) := by
  let I := live d e h.val
  let i := digit d e (5+h.val)
  apply lift_one I i
  · obtain ⟨h0,h1⟩ := recognizes_neighbor d e h
    refine ⟨witness d e h.val, Function.update (witness d e h.val) i true,?_,?_⟩
    · intro j hj; simp [Function.update_of_ne hj]
    · change graph (live d e h.val) _ ≠ graph (live d e h.val) (Function.update _ (digit d e (5+h.val)) true)
      rw [h0,h1]; decide
  · rw [graph_fixed]
    rintro ⟨c,eqn⟩
    apply child 0 hp
    change Builds 0 (raws (I.erase i)) (graph (I.erase i))
    rw [eqn]
    cases c
    · exact .stop .zero
    · exact .stop .one
  · rw [graph_fixed]; exact child

private theorem base_ten (d e : Fin 11) : Lower (region d e) 10 := by
  have h3 : Lower (live d e 3) 7 := project_lower _ (cycleMap d e) _ _ (recognizes_cycle d e) CycleSeven.lower
  have h2 := raise_one d e 2 7 (by decide) h3
  have h1 := raise_one d e 1 8 (by decide) h2
  exact raise_one d e 0 9 (by decide) h1

private theorem deleted_twelve (d : Fin 11) : Lower (region d 10) 12 := by
  apply lift_two (L := 10) _ _ (no_raw d 10) (robust d)
  · intro i _; rw [graph_fixed,region_erase]; exact varies d i.castSucc
  · intro i _; rw [graph_fixed,region_erase]; exact base_ten d i.castSucc

theorem full_signed_fourteen : ∀ k < 14, ¬ Builds k (raw 10) edge := by
  have h := lift_two (L := 12) _ _ (no_raw 10 10) (robust 10) (by
    intro i _; rw [graph_fixed,region_erase]; exact varies 10 i.castSucc) (by
    intro i _; rw [graph_fixed,region_erase,region_swap 10 i.castSucc]; exact deleted_twelve i.castSucc)
  have he : graph (region 10 10) = edge := by funext x; simp [graph,all_region]
  rw [he] at h
  intro k hk hb
  apply h _ hk
  apply simulate hb
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact .pos (List.mem_map.mpr ⟨i,by simp [all_region],rfl⟩)

theorem full_ordinary_fourteen : ¬ HasCircuitSize 10 edge 13 := by
  rintro ⟨C,hc,hs,he⟩
  have hb := circuit_to_signed 10 C hc
  rw [show (fun x => C.eval (List.ofFn x)) = edge from funext he] at hb
  apply full_signed_fourteen _ _ hb
  have h := List.countP_le_length (p := fun g => binaryOp g.op) (l := C.gates)
  change C.gates.length ≤ 13 at hs
  omega
end PetersenSigned.Petersen
namespace PetersenSigned.Compact

def missing {m} (r : Nat) (s : List (BitVec m)) (f : BitVec m) :=
  diffBits r f &&& ~~~(coverage r s)

private theorem cover_of_search {m} (r k : Nat) (hr : r+r ≤ m)
    {s : List (BitVec m)} {f} (h : search r k s f = true) :
    coverage r s ||| diffBits r f = coverage r s := by
  cases k with
  | zero =>
    exact covers (Plan.stop (List.contains_iff_mem.mp h)) r hr
  | succ k =>
    simp only [search,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at h
    exact h.elim (fun hf => covers (Plan.stop hf) r hr) And.left

private theorem necessary {m} (r : Nat) (s : List (BitVec m)) (f v : BitVec m)
    (yes : coverage r (v::s) ||| diffBits r f = coverage r (v::s)) :
    diffBits r v &&& missing r s f = missing r s f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := congrArg (fun z : BitVec r => z.getLsbD i) yes
  simp only [coverage,BitVec.getLsbD_or] at h
  simp only [missing,BitVec.getLsbD_and,BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and]
  revert h
  cases (diffBits r v).getLsbD i <;> cases (coverage r s).getLsbD i <;>
    cases (diffBits r f).getLsbD i <;> decide

/-- Precompute which distinguishing input pairs each retained set still needs.
Each new gate is compared with these masks before recursing. -/
def fast {m} (r : Nat) : Nat → List (BitVec m) → BitVec m → Bool
  | 0, s, f => (literals s).contains f
  | k+1, s, f =>
    let gates := (nextTables s).map (fun v => (v,diffBits r v))
    let sets := (choices k s).map (fun u => (u,missing r u f))
    (literals s).contains f || sets.any fun (u,need) =>
      gates.any fun (v,g) => (g &&& need == need) && fast r k (v::u) f

theorem fast_of_search {m} (r k : Nat) (hr : r+r ≤ m) (s : List (BitVec m)) (f)
    (h : search r k s f = true) : fast r k s f = true := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    simp only [search,Bool.or_eq_true,Bool.and_eq_true] at h
    simp only [fast,Bool.or_eq_true]
    rcases h with old | ⟨_,more⟩
    · exact Or.inl old
    · right
      obtain ⟨v,hv,h1⟩ := List.any_eq_true.mp more
      obtain ⟨u,hu,h2⟩ := List.any_eq_true.mp h1
      apply List.any_eq_true.mpr
      refine ⟨(u,missing r u f),List.mem_map.mpr ⟨u,hu,rfl⟩,List.any_eq_true.mpr
        ⟨(v,diffBits r v),List.mem_map.mpr ⟨v,hv,rfl⟩,?_⟩⟩
      have ne := necessary r u f v (cover_of_search r k hr h2)
      simp only [ne,beq_self_eq_true,Bool.true_and,ih _ h2]

theorem reject_fast {α} (pts : List α) (r budget : Nat) (hr : r+r ≤ pts.length)
    {s : List (Signal α)} {f : Signal α}
    (no : fast r budget (s.map (table pts)) (table pts f) = false) :
    ∀ k ≤ budget, ¬ Builds k s f := by
  apply reject pts r budget hr
  cases hc : search r budget (s.map (table pts)) (table pts f) with
  | false => rfl
  | true => have yes := fast_of_search r budget hr _ _ hc; rw [no] at yes; contradiction

end PetersenSigned.Compact
namespace PetersenSigned.Compact

def branch {m} (r n : Nat) (s : List (BitVec m)) (f v : BitVec m) : Bool :=
  let g := diffBits r v
  (choices n s).any fun u =>
    let need := missing r u f
    (g &&& need == need) && fast r n (v::u) f

theorem close_branches {m} (r n : Nat) (s : List (BitVec m)) (f : BitVec m)
    (groups : List (List (BitVec m)))
    (old : (literals s).contains f = false)
    (all : (nextTables s).all (fun v => groups.any (fun block => block.contains v)) = true)
    (no : ∀ block ∈ groups, block.all (fun v => !branch r n s f v) = true) :
    fast r (n+1) s f = false := by
  cases e : fast r (n+1) s f with
  | false => rfl
  | true =>
    simp only [fast,old,Bool.false_or,List.any_eq_true] at e
    obtain ⟨pair,hpair,gate,hgate,hy⟩ := e
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hpair
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hgate
    obtain ⟨bl,hbl,hm⟩ := List.any_eq_true.mp (List.all_eq_true.mp all v hv)
    have hn := List.all_eq_true.mp (no bl hbl) v (List.contains_iff_mem.mp hm)
    have yes : branch r n s f v = true := List.any_eq_true.mpr ⟨u,hu,hy⟩
    rw [yes] at hn
    contradiction
end PetersenSigned.Compact
namespace PetersenSigned.SixOpposite
private def pool0 : List (BitVec 156) := [2831170729190098197649741508028488183021568,11799928204385924285541859289069053153202258047,48003935036336746740697505720551124557958873087,20093350251259722296534018426673980364679970688,68691479095237412483749153503022177030613467136,15381939137966892415745956730628625435006599168,75959079290926652971162858767545182698019487744]
private def case0_0 : List (BitVec 156) := [17592236376064,19241453486080]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_0 : case0_0.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_1 : List (BitVec 156) := [576460752303521792,1008806316530991104]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_1 : case0_1.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_2 : List (BitVec 156) := [4719772413309517696,8070476920661082112]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_2 : case0_2.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_3 : List (BitVec 156) := [38960568283603750879232,226673591212923047378944]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_3 : case0_3.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_4 : List (BitVec 156) := [302222231531620438900736,2831170729190098197649740499222171652030464]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_4 : case0_4.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_5 : List (BitVec 156) := [2831170729190098197649740931567735879499776,2831170729190098197649741508009246729535488]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_5 : case0_5.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_6 : List (BitVec 156) := [2831170729190098197649741508010895946645504,2831171395122551749548178359120203763122176]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_6 : case0_6.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_7 : List (BitVec 156) := [724774262827397412859159242783960533464776704,1087161372641059899533163673733424067100278784]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_7 : case0_7.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_8 : List (BitVec 156) := [3584844837202922637743245174844921821272211456,3584844837868855131025622948721736481024917376]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_8 : case0_8.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_9 : List (BitVec 156) := [5798569763674949297567970196266047567164342272,5798572485933889780321225369778778996773650304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_9 : case0_9.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_10 : List (BitVec 156) := [7270431367084363039163253442882125871169142784,8653065151745649609499447038328064423325745024]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_10 : case0_10.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_11 : List (BitVec 156) := [10855276204287285716636938994184487032863080320,11440285099514072687034571388345915941354225664]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_11 : case0_11.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_12 : List (BitVec 156) := [11797094300763969778002711555783703613734387712,11799928204385924285541859288488088798721212416]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_12 : case0_12.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_13 : List (BitVec 156) := [14294777765325832516212793056895201367906320384,14294780487584772998966048230407932797515628416]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_13 : case0_13.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_14 : List (BitVec 156) := [14657164875139495002886797487844664901541822464,14659998778762747703560049927889834306103541760]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_14 : case0_14.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_15 : List (BitVec 156) := [15381939137966892415745654508397093814567698432,15381939137966892415745730057037412511959220224]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_15 : case0_15.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_16 : List (BitVec 156) := [15381939137966892415745956730628606193553113088,15384770308696082513943606472136634681736134656]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_16 : case0_16.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_17 : List (BitVec 156) := [20093350251259722296534018418603503444018888576,20093350251259722296534018421954207951370452992]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_17 : case0_17.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_18 : List (BitVec 156) := [20093350251259722296534018426673962772443594624,20096181421988912394731668168181991260626616192]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_18 : case0_18.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_19 : List (BitVec 156) := [20500339032245453456239879674503581471233540096,21180511623900782196067182100407404431780249472]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_19 : case0_19.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_20 : List (BitVec 156) := [22839578264599232190792916649712982699303370752,23246567045584963350498777902262356219166457856]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_20 : case0_20.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_21 : List (BitVec 156) := [28679918518081937943472746396326729864433369088,28682752421705190644145998836371899268995088384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_21 : case0_21.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_22 : List (BitVec 156) := [31539989092458761361490937035728475371815698432,43337086126115495548835146583284996434657411072]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_22 : case0_22.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_23 : List (BitVec 156) := [43339917296844685647032796324793024922840432640,43339917296844685647032796328936336583846428544]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_23 : case0_23.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_24 : List (BitVec 156) := [44064691559672083059891955567000524704001687552,45851900830638180292956236853309194331310096384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_24 : case0_24.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_25 : List (BitVec 156) := [47279160772844715027690112371218452833586118656,48003935036336746740697505719970160203477827456]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_25 : case0_25.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_26 : List (BitVec 156) := [68688647923842289931999605324663056826850344960,68688647924508222385551503761514148542430445568]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_26 : case0_26.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_27 : List (BitVec 156) := [68691479095237412483748926829430964107566088192,68691479095237412483749153494951700109952385024]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_27 : case0_27.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_28 : List (BitVec 156) := [70160509527251703673594888571279135130855145472,70890858977049858492688995717370571151967780864]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_28 : case0_28.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_29 : List (BitVec 156) := [75959079290926652971162556545313651077580587008,75959079290926652971162819806976899094268608512]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_29 : case0_29.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_30 : List (BitVec 156) := [75959079290926652971162858766536376381488496640,75959079291592585464445197580853713754021314432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_30 : case0_30.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_31 : List (BitVec 156) := [75961910461655843069360508508044404869671518208,75961910462321775522912406945904302901782609920]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_31 : case0_31.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_32 : List (BitVec 156) := [79543924128795508102188481716266919179044405120,79546755299524698200386092497206664063476547456]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_32 : case0_32.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_33 : List (BitVec 156) := [84073418233204304899494883560059589542572687360,88784829346497134780283171921625680474632355712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_33 : case0_33.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_34 : List (BitVec 156) := [89191818127482865939989033177525758501847007232,90253859778511425970128906997953115495535116160]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_34 : case0_34.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_35 : List (BitVec 156) := [90619078069689400674722908695435017004123029504,90984209228309580789223014144044551516647751552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_35 : case0_35.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_36 : List (BitVec 156) := [91341018428893545386908513275942276512587186176,91341018429559477880191154311482339189027913600]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_36 : case0_36.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
private def case0_37 : List (BitVec 156) := [91343852333181432387730302044186724374014738304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case0_37 : case0_37.all (fun v => !Compact.branch 78 6 pool0 302231454903657293676543 v) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem numeric0 : Compact.fast 78 7 pool0 302231454903657293676543 = false := by
  apply Compact.close_branches 78 6 pool0 302231454903657293676543 [case0_0,case0_1,case0_2,case0_3,case0_4,case0_5,case0_6,case0_7,case0_8,case0_9,case0_10,case0_11,case0_12,case0_13,case0_14,case0_15,case0_16,case0_17,case0_18,case0_19,case0_20,case0_21,case0_22,case0_23,case0_24,case0_25,case0_26,case0_27,case0_28,case0_29,case0_30,case0_31,case0_32,case0_33,case0_34,case0_35,case0_36,case0_37] (by decide +kernel) (by decide +kernel)
  intro bl hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked_case0_0
  · exact checked_case0_1
  · exact checked_case0_2
  · exact checked_case0_3
  · exact checked_case0_4
  · exact checked_case0_5
  · exact checked_case0_6
  · exact checked_case0_7
  · exact checked_case0_8
  · exact checked_case0_9
  · exact checked_case0_10
  · exact checked_case0_11
  · exact checked_case0_12
  · exact checked_case0_13
  · exact checked_case0_14
  · exact checked_case0_15
  · exact checked_case0_16
  · exact checked_case0_17
  · exact checked_case0_18
  · exact checked_case0_19
  · exact checked_case0_20
  · exact checked_case0_21
  · exact checked_case0_22
  · exact checked_case0_23
  · exact checked_case0_24
  · exact checked_case0_25
  · exact checked_case0_26
  · exact checked_case0_27
  · exact checked_case0_28
  · exact checked_case0_29
  · exact checked_case0_30
  · exact checked_case0_31
  · exact checked_case0_32
  · exact checked_case0_33
  · exact checked_case0_34
  · exact checked_case0_35
  · exact checked_case0_36
  · exact checked_case0_37
end PetersenSigned.SixOpposite
namespace PetersenSigned.SixOpposite
private def pool1 : List (BitVec 156) := [68688647924508222385551503761514148542430445568,11799928204385924285541859289069053153202258047,48003935036336746740697505720551124557958873087,20093350251259722296534018426673980364679970688,68691479095237412483749153503022177030613467136,15381939137966892415745956730628625435006599168,75959079290926652971162858767545182698019487744]
private def case1_0 : List (BitVec 156) := [4719772413309517696,8070459328424706048]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_0 : case1_0.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_1 : List (BitVec 156) := [8070476920661082112,38960568283603750879232]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_1 : case1_1.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_2 : List (BitVec 156) := [226673591193681593892864,226673591212923047378944]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_2 : case1_2.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_3 : List (BitVec 156) := [302222231531620438900736,665932453551898437859898032111091712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_3 : case1_3.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_4 : List (BitVec 156) := [2831170729190098197649741508028488183021568,2831171395122551749548178359120203763122176]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_4 : case1_4.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_5 : List (BitVec 156) := [724774262827397412859159242783960533464776704,1087161372641059899533163673733424067100278784]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_5 : case1_5.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_6 : List (BitVec 156) := [3584844837202922637743245174844921821272211456,3584844837868855131025622948721736481024917376]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_6 : case1_6.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_7 : List (BitVec 156) := [5798569763674949297567970196266047567164342272,5798572485933889780321225369778778996773650304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_7 : case1_7.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_8 : List (BitVec 156) := [7270431367084363039163253442882125871169142784,7270431367084363039163253443890932187700133888]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_8 : case1_8.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_9 : List (BitVec 156) := [8653065151745649609499447038328064423325745024,10855276204287285716636938994184487032863080320]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_9 : case1_9.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_10 : List (BitVec 156) := [11440285099514072687034571388345915941354225664,11797094300763969778002711555783703613734387712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_10 : case1_10.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_11 : List (BitVec 156) := [11799928204385924285541859288488088798721212416,14294777765325832516212793056895201367906320384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_11 : case1_11.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_12 : List (BitVec 156) := [14294780487584772998966048230407932797515628416,14657164875139495002886797487844664901541822464]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_12 : case1_12.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_13 : List (BitVec 156) := [14659998778762747703560049927889834306103541760,15381939137966892415745654508397093814567698432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_13 : case1_13.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_14 : List (BitVec 156) := [15381939137966892415745730057037412511959220224,15381939137966892415745730057037431753412706304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_14 : case1_14.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_15 : List (BitVec 156) := [20093350251259722296534018418603503444018888576,20093350251259722296534018418603521036255264640]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_15 : case1_15.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_16 : List (BitVec 156) := [20093350251259722296534018421954207951370452992,20500339032245453456239879674503581471233540096]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_16 : case1_16.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_17 : List (BitVec 156) := [20503170202974643554437529415435149207113039872,21180511623900782196067182100407404431780249472]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_17 : case1_17.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_18 : List (BitVec 156) := [22836747093870042092595266908781414963423870976,22839578264599232190792916649712982699303370752]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_18 : case1_18.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_19 : List (BitVec 156) := [23246567045584963350498777902262356219166457856,28679918518081937943472746396326729864433369088]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_19 : case1_19.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_20 : List (BitVec 156) := [28682752421705190644145998836371899268995088384,31539989092458761361490937035728475371815698432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_20 : case1_20.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_21 : List (BitVec 156) := [43339917296844685647032796328936336583846428544,44064691559672083059891955567000524704001687552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_21 : case1_21.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_22 : List (BitVec 156) := [45851900830638180292956236852732733579006574592,45851900830638180292956236853309194331310096384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_22 : case1_22.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_23 : List (BitVec 156) := [47279160772844715027690112371218452833586118656,48003935036336746740697505719970160203477827456]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_23 : case1_23.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_24 : List (BitVec 156) := [68688647923842289931999605323654250510319353856,68688647923842289931999605324663056826850344960]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_24 : case1_24.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_25 : List (BitVec 156) := [68688647924508222385551277087922954860836552704,68688647924508222385551503753443689214005739520]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_25 : case1_25.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_26 : List (BitVec 156) := [68691479095237412483748926829430964107566088192,68691479095237412483749153494951700109952385024]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_26 : case1_26.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_27 : List (BitVec 156) := [70160509527251703673594888571279135130855145472,70890858977049858492688995717370571151967780864]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_27 : case1_27.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_28 : List (BitVec 156) := [75959079290926652971162556545313651077580587008,75959079290926652971162819806976899094268608512]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_28 : case1_28.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_29 : List (BitVec 156) := [75959079291592585424714757205405080730130579456,75959079291592585464445197580853713754021314432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_29 : case1_29.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_30 : List (BitVec 156) := [75961910462321775522912406945904302901782609920,79543924128795508102188481716266919179044405120]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_30 : case1_30.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_31 : List (BitVec 156) := [79546755299524698200386092497206664063476547456,84070587062475114801297233818551580295843151872]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_31 : case1_31.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_32 : List (BitVec 156) := [84073418233204304899494883560059589542572687360,88781998175767944682085522180117669578685710208]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_32 : case1_32.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_33 : List (BitVec 156) := [88784829346497134780283171921625680474632355712,89191818127482865939989033176949297749543485440]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_33 : case1_33.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_34 : List (BitVec 156) := [89191818127482865939989033177525758501847007232,90253859778511425970128906997953115495535116160]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_34 : case1_34.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_35 : List (BitVec 156) := [90619078069689400674722908695435017004123029504,90984209228309580789223014144044551516647751552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_35 : case1_35.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_36 : List (BitVec 156) := [91341018428893545386908513275942276512587186176,91341018429559477880191154311482339189027913600]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_36 : case1_36.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_37 : List (BitVec 156) := [91343852333181432387730302044186724374014738304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_37 : case1_37.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem numeric1 : Compact.fast 78 7 pool1 302231454903657293676543 = false := by
  apply Compact.close_branches 78 6 pool1 302231454903657293676543 [case1_0,case1_1,case1_2,case1_3,case1_4,case1_5,case1_6,case1_7,case1_8,case1_9,case1_10,case1_11,case1_12,case1_13,case1_14,case1_15,case1_16,case1_17,case1_18,case1_19,case1_20,case1_21,case1_22,case1_23,case1_24,case1_25,case1_26,case1_27,case1_28,case1_29,case1_30,case1_31,case1_32,case1_33,case1_34,case1_35,case1_36,case1_37] (by decide +kernel) (by decide +kernel)
  intro bl hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked_case1_0
  · exact checked_case1_1
  · exact checked_case1_2
  · exact checked_case1_3
  · exact checked_case1_4
  · exact checked_case1_5
  · exact checked_case1_6
  · exact checked_case1_7
  · exact checked_case1_8
  · exact checked_case1_9
  · exact checked_case1_10
  · exact checked_case1_11
  · exact checked_case1_12
  · exact checked_case1_13
  · exact checked_case1_14
  · exact checked_case1_15
  · exact checked_case1_16
  · exact checked_case1_17
  · exact checked_case1_18
  · exact checked_case1_19
  · exact checked_case1_20
  · exact checked_case1_21
  · exact checked_case1_22
  · exact checked_case1_23
  · exact checked_case1_24
  · exact checked_case1_25
  · exact checked_case1_26
  · exact checked_case1_27
  · exact checked_case1_28
  · exact checked_case1_29
  · exact checked_case1_30
  · exact checked_case1_31
  · exact checked_case1_32
  · exact checked_case1_33
  · exact checked_case1_34
  · exact checked_case1_35
  · exact checked_case1_36
  · exact checked_case1_37
end PetersenSigned.SixOpposite
namespace PetersenSigned.SixOpposite
private def pool2 : List (BitVec 156) := [11797097033656734187344209547561024665019236479,11799928204385924285541859289069053153202258047,48003935036336746740697505720551124557958873087,20093350251259722296534018426673980364679970688,68691479095237412483749153503022177030613467136,15381939137966892415745956730628625435006599168,75959079290926652971162858767545182698019487744]
private def case2_0 : List (BitVec 156) := [4719772413309517696,8070476920661082112]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_0 : case2_0.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_1 : List (BitVec 156) := [38959559477287219888128,38960568283603750879232]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_1 : case2_1.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_2 : List (BitVec 156) := [226673591212923047378944,302222231531620438900736]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_2 : case2_2.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_3 : List (BitVec 156) := [2831170729190098197649741508028488183021568,2831171395122551749548178359120203763122176]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_3 : case2_3.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_4 : List (BitVec 156) := [724774262827397412859159242783960533464776704,1087161372641059899533163673733424067100278784]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_4 : case2_4.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_5 : List (BitVec 156) := [3584844837202922637743245174844921821272211456,3584844837202922637743245174844941062725697536]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_5 : case2_5.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_6 : List (BitVec 156) := [3584844837868855131025622948721736481024917376,3587676008598045229223272689220958652676947840]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_6 : case2_6.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_7 : List (BitVec 156) := [5798569763674949297567970196266047567164342272,5798572485933889780321225369778778996773650304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_7 : case2_7.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_8 : List (BitVec 156) := [7270431367084363039163253442882125871169142784,8653065151745649609499447038328064423325745024]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_8 : case2_8.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_9 : List (BitVec 156) := [8653065151745649609499447038328082015562121088,10855276204287285716636938994184487032863080320]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_9 : case2_9.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_10 : List (BitVec 156) := [11440285099514072687034571388345898349117849600,11440285099514072687034571388345915941354225664]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_10 : case2_10.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_11 : List (BitVec 156) := [11797094300763969778002711555783684372280901632,11797094300763969778002711555783703613734387712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_11 : case2_11.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_12 : List (BitVec 156) := [11797097033656734187344209547556521062841712640,11799928204385924285541859288488088798721212416]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_12 : case2_12.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_13 : List (BitVec 156) := [14294777765325832516212793056895201367906320384,14294780487584772998966048230407932797515628416]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_13 : case2_13.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_14 : List (BitVec 156) := [14657164875139495002886797487844664901541822464,14659998778762747703560049927889834306103541760]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_14 : case2_14.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_15 : List (BitVec 156) := [15381939137966892415745654508397093814567698432,15381939137966892415745730057037412511959220224]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_15 : case2_15.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_16 : List (BitVec 156) := [20093350251259722296534018418603503444018888576,20093350251259722296534018421954207951370452992]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_16 : case2_16.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_17 : List (BitVec 156) := [20500339032245453456239879674503581471233540096,21180511623900782196067182100407404431780249472]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_17 : case2_17.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_18 : List (BitVec 156) := [22839578264599232190792916649712982699303370752,23246567045584963350498777902262356219166457856]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_18 : case2_18.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_19 : List (BitVec 156) := [28679918518081937943472746396326729864433369088,28682752421705190644145998836371899268995088384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_19 : case2_19.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_20 : List (BitVec 156) := [31539989092458761361490937035728475371815698432,31542820263187951459688586776660043107695198208]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_20 : case2_20.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_21 : List (BitVec 156) := [43339917296844685647032796328936336583846428544,44064691559672083059891955567000524704001687552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_21 : case2_21.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_22 : List (BitVec 156) := [45851900830638180292956236853309194331310096384,47279160772844715027690112371218452833586118656]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_22 : case2_22.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_23 : List (BitVec 156) := [48003935036336746740697505719970160203477827456,48003935036336746740697505720546620955781349248]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_23 : case2_23.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_24 : List (BitVec 156) := [68688647923842289931999605324663056826850344960,68688647924508222385551503761514148542430445568]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_24 : case2_24.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_25 : List (BitVec 156) := [68691479095237412483748926829430964107566088192,68691479095237412483749153494951700109952385024]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_25 : case2_25.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_26 : List (BitVec 156) := [70160509527251703673594888571279135130855145472,70890858977049858492688995717370571151967780864]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_26 : case2_26.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_27 : List (BitVec 156) := [70893690147779048590886645458878582047914426368,75959079290926652971162556545313651077580587008]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_27 : case2_27.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_28 : List (BitVec 156) := [75959079290926652971162819806976899094268608512,75959079290926652971162819807985705410799599616]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_28 : case2_28.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_29 : List (BitVec 156) := [75959079291592585464445197580853713754021314432,75961910462321775522912406945904302901782609920]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_29 : case2_29.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_30 : List (BitVec 156) := [75961910462321775562642847322361723000750849920,79543924128795508102188481716266919179044405120]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_30 : case2_30.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_31 : List (BitVec 156) := [79546755299524698200386131456766141350696435584,84073418233204304899494883560059589542572687360]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_31 : case2_31.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_32 : List (BitVec 156) := [88784829346497134780283171921625680474632355712,89191818127482865939989033177525758501847007232]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_32 : case2_32.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_33 : List (BitVec 156) := [90253859778511425970128906997953115495535116160,90619078069689400674722908695435017004123029504]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_33 : case2_33.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_34 : List (BitVec 156) := [90984209228309580789223014144044551516647751552,90987040399038770887420663885552562412594397056]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_34 : case2_34.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_35 : List (BitVec 156) := [91341018428893545386908513275942276512587186176,91341018429559477880191154311482339189027913600]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_35 : case2_35.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_36 : List (BitVec 156) := [91343849600288667978388804052990348435757449088,91343852333181432387730302044186724374014738304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_36 : case2_36.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
private def case2_37 : List (BitVec 156) := [91343852333181432387730302044763185126318260096]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case2_37 : case2_37.all (fun v => !Compact.branch 78 6 pool2 302231454903657293676543 v) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem numeric2 : Compact.fast 78 7 pool2 302231454903657293676543 = false := by
  apply Compact.close_branches 78 6 pool2 302231454903657293676543 [case2_0,case2_1,case2_2,case2_3,case2_4,case2_5,case2_6,case2_7,case2_8,case2_9,case2_10,case2_11,case2_12,case2_13,case2_14,case2_15,case2_16,case2_17,case2_18,case2_19,case2_20,case2_21,case2_22,case2_23,case2_24,case2_25,case2_26,case2_27,case2_28,case2_29,case2_30,case2_31,case2_32,case2_33,case2_34,case2_35,case2_36,case2_37] (by decide +kernel) (by decide +kernel)
  intro bl hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked_case2_0
  · exact checked_case2_1
  · exact checked_case2_2
  · exact checked_case2_3
  · exact checked_case2_4
  · exact checked_case2_5
  · exact checked_case2_6
  · exact checked_case2_7
  · exact checked_case2_8
  · exact checked_case2_9
  · exact checked_case2_10
  · exact checked_case2_11
  · exact checked_case2_12
  · exact checked_case2_13
  · exact checked_case2_14
  · exact checked_case2_15
  · exact checked_case2_16
  · exact checked_case2_17
  · exact checked_case2_18
  · exact checked_case2_19
  · exact checked_case2_20
  · exact checked_case2_21
  · exact checked_case2_22
  · exact checked_case2_23
  · exact checked_case2_24
  · exact checked_case2_25
  · exact checked_case2_26
  · exact checked_case2_27
  · exact checked_case2_28
  · exact checked_case2_29
  · exact checked_case2_30
  · exact checked_case2_31
  · exact checked_case2_32
  · exact checked_case2_33
  · exact checked_case2_34
  · exact checked_case2_35
  · exact checked_case2_36
  · exact checked_case2_37
end PetersenSigned.SixOpposite
namespace PetersenSigned.SixOpposite
private def pool3 : List (BitVec 156) := [10855276204287285716636938994184487032863080320,11799928204385924285541859289069053153202258047,48003935036336746740697505720551124557958873087,20093350251259722296534018426673980364679970688,68691479095237412483749153503022177030613467136,15381939137966892415745956730628625435006599168,75959079290926652971162858767545182698019487744]
private def case3_0 : List (BitVec 156) := [4719772413309517696,8070476920661082112]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_0 : case3_0.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_1 : List (BitVec 156) := [38960568283603750879232,226673591212923047378944]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_1 : case3_1.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_2 : List (BitVec 156) := [302222231531620438900736,2831170729190098197649741508028488183021568]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_2 : case3_2.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_3 : List (BitVec 156) := [2831171395122551749548178359120203763122176,724774262827397412859159242783960533464776704]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_3 : case3_3.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_4 : List (BitVec 156) := [1087161372641059899533163673733424067100278784,2152034205698566447741268867237426624471252864]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_4 : case3_4.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_5 : List (BitVec 156) := [2202211052541636107137491963926881937962041344,3584844837202922637743018501253728139678318592]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_5 : case3_5.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_6 : List (BitVec 156) := [3584844837202922637743245174844921821272211456,3584844837202922677473724510861838448913825664]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_6 : case3_6.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_7 : List (BitVec 156) := [3584844837868855131025622948721736481024917376,5798569763674949297567970196266047567164342272]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_7 : case3_7.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_8 : List (BitVec 156) := [5798572485933889780321225369778778996773650304,7270431367084363039163214483322648583949254656]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_8 : case3_8.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_9 : List (BitVec 156) := [7270431367084363039163253442882125871169142784,7270431367084363078893920492930758893184761728]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_9 : case3_9.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_10 : List (BitVec 156) := [8653065151745649609499447030257605094901038976,8653065151745649609499447038328064423325745024]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_10 : case3_10.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_11 : List (BitVec 156) := [8703241998588719268895670126947060408391827456,11440285099514072687034571388345915941354225664]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_11 : case3_11.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_12 : List (BitVec 156) := [11440285099514072687034571396416375269778931712,11797094300763969778002711555783703613734387712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_12 : case3_12.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_13 : List (BitVec 156) := [11797094300763969778002938229374897295328280576,11799928204385924285541859288488088798721212416]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_13 : case3_13.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_14 : List (BitVec 156) := [14294777765325832516212793056895201367906320384,14294780487584772998966048230407932797515628416]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_14 : case3_14.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_15 : List (BitVec 156) := [14657164875139495002886797487844664901541822464,14659998778762747703560049927889834306103541760]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_15 : case3_15.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_16 : List (BitVec 156) := [15381939137966892415745654508397093814567698432,15381939137966892415745730057037412511959220224]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_16 : case3_16.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_17 : List (BitVec 156) := [20093350251259722296534018418603503444018888576,20093350251259722296534018421954207951370452992]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_17 : case3_17.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_18 : List (BitVec 156) := [20500339032245453456239879674503581471233540096,21180511623900782196067182100407404431780249472]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_18 : case3_18.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_19 : List (BitVec 156) := [22295561303801358403671510390600862302642012032,22652370505051255494639877223559384328191360896]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_19 : case3_19.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_20 : List (BitVec 156) := [22839578264599232190792916649712982699303370752,23246567045584963350498777902262356219166457856]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_20 : case3_20.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_21 : List (BitVec 156) := [28679918518081937943472746396326729864433369088,28682752421705190644145998836371899268995088384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_21 : case3_21.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_22 : List (BitVec 156) := [31539989092458761361490937035728475371815698432,34636675298255966378137126197269503762145083392]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_22 : case3_22.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_23 : List (BitVec 156) := [43339917296844685647032796328936336583846428544,44064691559672083059891955567000524704001687552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_23 : case3_23.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_24 : List (BitVec 156) := [45491951502543252094774065191453990795008163712,45851900830638180292956236853309194331310096384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_24 : case3_24.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_25 : List (BitVec 156) := [47279160772844715027690112371218452833586118656,48003935036336746740697505719970160203477827456]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_25 : case3_25.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_26 : List (BitVec 156) := [68688647923842289931999605324663056826850344960,68688647923842289931999644284222534114070233088]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_26 : case3_26.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_27 : List (BitVec 156) := [68688647924508222385551503761514148542430445568,68691479095237412483748926829430964107566088192]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_27 : case3_27.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_28 : List (BitVec 156) := [68691479095237412483749153494951700109952385024,70160509527251703673594888571279135130855145472]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_28 : case3_28.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_29 : List (BitVec 156) := [70890858977049858492688995717370571151967780864,75959079290926652971162556545313651077580587008]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_29 : case3_29.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_30 : List (BitVec 156) := [75959079290926652971162819806976899094268608512,75959079291592585464445197580853713754021314432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_30 : case3_30.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_31 : List (BitVec 156) := [75961910462321775522912406945904302901782609920,79543924128129575648636583278407021146933313408]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_31 : case3_31.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_32 : List (BitVec 156) := [79543924128795508102188481716266919179044405120,79546755299524698200386092497206664063476547456]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_32 : case3_32.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_33 : List (BitVec 156) := [84073418233204304899494883560059589542572687360,88784829346497134780283171921625680474632355712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_33 : case3_33.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_34 : List (BitVec 156) := [89191818127482865939989033177525758501847007232,90253859778511425970128906997953115495535116160]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_34 : case3_34.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_35 : List (BitVec 156) := [90619078069689400674722908695435017004123029504,90984209228309580789223014144044551516647751552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_35 : case3_35.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_36 : List (BitVec 156) := [91341018428893545386908513275942276512587186176,91341018429559477880191154311482339189027913600]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_36 : case3_36.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
private def case3_37 : List (BitVec 156) := [91343852333181432387730302044186724374014738304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case3_37 : case3_37.all (fun v => !Compact.branch 78 6 pool3 302231454903657293676543 v) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem numeric3 : Compact.fast 78 7 pool3 302231454903657293676543 = false := by
  apply Compact.close_branches 78 6 pool3 302231454903657293676543 [case3_0,case3_1,case3_2,case3_3,case3_4,case3_5,case3_6,case3_7,case3_8,case3_9,case3_10,case3_11,case3_12,case3_13,case3_14,case3_15,case3_16,case3_17,case3_18,case3_19,case3_20,case3_21,case3_22,case3_23,case3_24,case3_25,case3_26,case3_27,case3_28,case3_29,case3_30,case3_31,case3_32,case3_33,case3_34,case3_35,case3_36,case3_37] (by decide +kernel) (by decide +kernel)
  intro bl hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked_case3_0
  · exact checked_case3_1
  · exact checked_case3_2
  · exact checked_case3_3
  · exact checked_case3_4
  · exact checked_case3_5
  · exact checked_case3_6
  · exact checked_case3_7
  · exact checked_case3_8
  · exact checked_case3_9
  · exact checked_case3_10
  · exact checked_case3_11
  · exact checked_case3_12
  · exact checked_case3_13
  · exact checked_case3_14
  · exact checked_case3_15
  · exact checked_case3_16
  · exact checked_case3_17
  · exact checked_case3_18
  · exact checked_case3_19
  · exact checked_case3_20
  · exact checked_case3_21
  · exact checked_case3_22
  · exact checked_case3_23
  · exact checked_case3_24
  · exact checked_case3_25
  · exact checked_case3_26
  · exact checked_case3_27
  · exact checked_case3_28
  · exact checked_case3_29
  · exact checked_case3_30
  · exact checked_case3_31
  · exact checked_case3_32
  · exact checked_case3_33
  · exact checked_case3_34
  · exact checked_case3_35
  · exact checked_case3_36
  · exact checked_case3_37
end PetersenSigned.SixOpposite
namespace PetersenSigned.SixOpposite
def cycle (x : Fin 6 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def first (p q : Bool) (x : Fin 6 → Bool) := (if p then !(x 0) else x 0) && (if q then !(x 3) else x 3)
def samples : List (Fin 6 → Bool) := ([3,3,3,3,3,3,3,6,6,6,6,6,6,6,7,11,11,12,12,12,12,12,12,12,13,13,14,19,19,22,22,23,24,24,24,24,24,24,24,25,25,26,26,28,29,33,33,33,33,33,33,33,35,37,37,38,38,41,41,43,44,44,46,48,48,48,48,48,48,48,49,50,50,52,52,53,56,58,1,2,9,18,21,36,42,2,4,9,18,21,36,42,5,9,10,4,8,9,18,21,36,42,5,9,10,17,18,18,20,21,8,9,16,18,21,36,42,9,17,10,18,20,21,1,9,18,21,32,36,42,34,5,36,34,36,9,40,42,36,40,42,9,16,18,21,32,36,42,17,18,34,20,36,21,40,42] : List Nat).map (fun w i => w.testBit i.val)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem lower (p q : Bool) : ∀ k < 8, ¬ Builds k (first p q :: raw 6) cycle := by
  intro k hk
  apply Compact.reject_fast samples 78 7 (by decide) ?_ k (by omega)
  cases p <;> cases q
  · exact numeric0
  · exact numeric2
  · exact numeric1
  · exact numeric3
end PetersenSigned.SixOpposite
namespace PetersenSigned

/-- An essential cofactor saves one gate whenever the original pool's signals
agree on a distinguishing pair or become constant on that cofactor. -/
theorem project_save {α β} (σ : β → α) (s : List (Signal α)) (f : Signal α)
    (t : List (Signal β)) (L : Nat) (g : Signal β) (he : ∀ x, f (σ x) = g x)
    (witness : ∃ x y, f x ≠ f y ∧ ∀ u ∈ s, Compatible σ x y u)
    (varies : ¬ ∃ c : Bool, g = fun _ => c)
    (mapping : ∀ u ∈ s, Available t (u ∘ σ))
    (child : ∀ k < L, ¬ Builds k t g) : ∀ k < L+1, ¬ Builds k s f := by
  intro k hk hb
  obtain ⟨x,y,diff,ok⟩ := witness
  have eg : f ∘ σ = g := funext he
  obtain ⟨gs,hlen,ht⟩ := trace_of_builds hb
  have save := saves_one σ x y ht ok (fun h => h.elim diff (by rw [eg]; exact varies))
  obtain ⟨j,hs,plan⟩ := restrict_trace σ _ gs _ ht _ mapping
  rw [eg] at plan
  exact child j (by omega) plan

/-- It suffices to check the tail after each first gate on distinct raw inputs.
Constant gates and repeated input gates can be deleted. -/
theorem raw_first {n L} (I : Finset (Fin n)) (f : Signal (Fin n → Bool))
    (not_input : ¬ Available (raws I) f)
    (first : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ p q : Bool, ∀ k, k+1 < L →
      ¬ Builds k (conj (lit i p) (lit j q)::raws I) f) :
    ∀ k < L, ¬ Builds k (raws I) f := by
  intro k
  induction k with
  | zero => intro _ h; cases h with | stop ha => exact not_input ha
  | succ k ih =>
    intro hk h
    cases h with
    | @gate _ _ _ a b ha hb tail =>
      have redundant (hv : Available (raws I) (conj a b)) : False := by
        apply ih (by omega)
        exact simulate tail _ (fun z hz => (List.mem_cons.mp hz).elim
          (fun eqn => eqn ▸ hv) (fun hz => .pos hz))
      rcases raw_specs ha with ⟨c,rfl⟩ | ⟨i,hi,p,rfl⟩
      · exact redundant (const_left hb c)
      rcases raw_specs hb with ⟨c,rfl⟩ | ⟨j,hj,q,rfl⟩
      · exact redundant (const_right ha c)
      by_cases e : i = j
      · subst j; exact redundant (same_input hi p q)
      exact first i hi j hj e p q k hk tail

theorem getD_literal {α} (l : List (Signal α)) (j : Nat) (p : Bool) :
    Available l (if p then neg (l.getD j (fun _ => false)) else l.getD j (fun _ => false)) := by
  have main : Available l (l.getD j (fun _ => false)) := by
    simp only [List.getD_eq_getElem?_getD]
    cases e : l[j]? with
    | none => exact .zero
    | some a => exact .pos (List.mem_of_getElem? e)
  cases p
  · exact main
  · exact flip main

end PetersenSigned
namespace PetersenSigned.Theta

def pent (x : Fin 5 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0)
def hex (x : Fin 6 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def pend (x : Fin 6 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5)
def theta (x : Fin 7 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 2)
def opposite (p q : Bool) := conj (lit (0 : Fin 6) p) (lit 3 q)
private def appendZero (x : Fin 5 → Bool) (i : Fin 6) := if h : i.val < 5 then x ⟨i.val,h⟩ else false
private theorem pendant_lower (h5 : ∀ k < 7, ¬ Builds k (raw 5) pent) :
    ∀ k < 8, ¬ Builds k (raw 6) pend := by
  apply project_save appendZero _ _ (raw 5) 7 pent (by decide +kernel) _ _ _ h5
  · let x (i : Fin 6) := decide (i = 0)
    let y := Function.update x 5 true
    refine ⟨x,y,by decide +kernel,?_⟩
    intro w hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    by_cases e : j = 5
    · subst j; exact Or.inr ⟨false,rfl⟩
    · exact Or.inl (by simp [y,Function.update_of_ne e])
  · rintro ⟨c,h⟩
    have h0 : false = c := congrFun h (fun _ => false)
    have h1 : true = c := congrFun h (fun _ => true)
    simp_all
  · intro w hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    by_cases h : j.val < 5
    · have eqn : (fun x : Fin 6 → Bool => x j) ∘ appendZero = inputSignal ⟨j.val,h⟩ := by funext x; simp [inputSignal,appendZero,h]
      rw [eqn]; exact .pos (List.mem_ofFn.mpr ⟨_,rfl⟩)
    · have eqn : (fun x : Fin 6 → Bool => x j) ∘ appendZero = fun _ => false := by funext x; simp [appendZero,h]
      rw [eqn]; exact .zero

private def maps : Array Nat := #[
6,6,6,6,6,6,6,0,6,3,2,1,5,4,6,6,
6,6,6,6,6,0,1,2,6,5,4,3,2,1,0,5,
6,3,4,2,1,0,4,3,6,5,0,1,2,3,4,5,
6]
private def records : Array Nat := #[
0,0,0,0,900,4,897,1025,769,769,769,769,772,4,773,1029,
776,264,769,1281,832,320,769,1281,772,4,773,1029,900,897,4,1025,
0,0,0,0,897,900,385,1412,897,905,257,1289,897,916,129,1172,
897,932,641,1700,897,961,513,1601,769,769,769,769,897,385,900,1412,
0,0,0,0,784,272,772,1284,769,1,773,1029,769,1,773,1029,
800,288,772,1284,772,773,4,1029,772,786,132,1170,784,772,272,1284,
0,0,0,0,772,784,644,1680,772,804,516,1572,772,848,388,1488,
776,769,264,1281,769,778,129,1162,769,773,1,1029,769,776,641,1672,
0,0,0,0,769,808,385,1448,769,833,513,1601,832,769,320,1281,
769,834,129,1218,769,773,1,1029,769,777,513,1545,769,848,385,1488,
0,0,0,0,769,832,641,1728,772,773,4,1029,772,802,132,1186,
800,772,288,1284,772,808,388,1448,772,788,516,1556,772,800,644,1696,
0,0,0,0]

private def drop (i j : Fin 7) : Fin 7 := if i ≠ 0 ∧ i ≠ 2 then i else if j ≠ 0 ∧ j ≠ 2 then j else 1
private def record (i j : Fin 7) (p q : Bool) := records[((i.val*7+j.val)*2+(if p then 1 else 0))*2+(if q then 1 else 0)]!
private def mi (d j : Fin 7) := maps[d.val*7+j.val]!
private def proj (d : Fin 7) (x : Fin 6 → Bool) (j : Fin 7) := if h : mi d j < 6 then x ⟨mi d j,h⟩ else false
private def test (i j : Fin 7) (p q : Bool) (h : Fin 7) := (record i j p q).testBit h.val
private def polar (i j : Fin 7) (p q : Bool) := if i = 2 ∧ j = 0 then (q,p) else (p,q)
private def pool (i j : Fin 7) (p q : Bool) :=
  let pq := polar i j p q
  raw 6 ++ (if drop i j = 1 then [opposite pq.1 pq.2] else [])
private def childF (d : Fin 7) := if d = 1 then hex else pend
private theorem checks (i j : Fin 7) (p q : Bool) (ij : i ≠ j) :
    let d := drop i j
    let w := test i j p q
    let v := conj (lit i p) (lit j q)
    let u := Function.update w d true
    let data := record i j p q
    let t := pool i j p q
    theta w = false ∧ theta u = true ∧ v w = v u ∧ 6 ≤ mi d d ∧
    (∀ x, theta (proj d x) = childF d x) ∧
    (∀ x, v (proj d x) = (if data.testBit 10 then neg (t.getD ((data >>> 7)%8) (fun _ => false)) else t.getD ((data >>> 7)%8) (fun _ => false)) x) := by
  revert i j p q
  decide +kernel

theorem lower (h5 : ∀ k < 7, ¬ Builds k (raw 5) pent)
    (h6 : ∀ p q, ∀ k < 8, ¬ Builds k (opposite p q :: raw 6) hex) :
    ∀ k < 10, ¬ Builds k (raw 7) theta := by
  let I : Finset (Fin 7) := Finset.univ
  have tails (i j : Fin 7) (ij : i ≠ j) (p q : Bool) :
      ∀ k < 9, ¬ Builds k (conj (lit i p) (lit j q) :: raws I) theta := by
    let d := drop i j
    let t := pool i j p q
    let v := conj (lit i p) (lit j q)
    obtain ⟨h0,h1,agree,hout,he,hv⟩ := checks i j p q ij
    apply project_save (proj d) _ theta t 8 (childF d) he
    · refine ⟨test i j p q, Function.update (test i j p q) d true,?_,?_⟩
      · rw [h0,h1]; decide
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl agree
        · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
          by_cases e : u = d
          · subst u; exact Or.inr ⟨false,by funext x; simp [inputSignal,proj,Nat.not_lt.mpr (show 6 ≤ mi d d from hout)]⟩
          · exact Or.inl (by simp [inputSignal,Function.update_of_ne e])
    · rintro ⟨c,h⟩
      have a : ∀ d, childF d (fun _ => false) = false := by decide +kernel
      have b : ∀ d, childF d (fun _ => true) = true := by decide +kernel
      have fa := congrFun h (fun _ => false); have fb := congrFun h (fun _ => true)
      rw [a] at fa; rw [b] at fb; simp_all
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [show v ∘ proj d = _ from funext hv]
        exact getD_literal _ _ _
      · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
        by_cases h : mi d u < 6
        · have e : inputSignal u ∘ proj d = inputSignal ⟨mi d u,h⟩ := by funext x; simp [inputSignal,proj,h]
          rw [e]; exact .pos (List.mem_append_left _ (List.mem_ofFn.mpr ⟨_,rfl⟩))
        · have e : inputSignal u ∘ proj d = fun _ => false := by funext x; simp [inputSignal,proj,h]
          rw [e]; exact .zero
    · intro k hk hb
      by_cases one : d = 1
      · apply h6 (polar i j p q).1 (polar i j p q).2 k hk
        have eqt : t = raw 6 ++ [opposite (polar i j p q).1 (polar i j p q).2] := by simp [t,pool,show drop i j = 1 from one]
        rw [eqt,show childF d = hex by simp [childF,one]] at hb
        apply simulate hb
        intro z hz
        rcases List.mem_append.mp hz with hr | hw
        · exact .pos (List.mem_cons_of_mem _ hr)
        · exact .pos (List.mem_cons.mpr (Or.inl (by simpa using hw)))
      · apply pendant_lower h5 k hk
        simpa [t,pool,childF,d,show drop i j ≠ 1 from one] using hb
  have h := raw_first (L := 10) I theta (by
    intro ha
    apply tails 0 1 (by decide) false false 0 (by decide)
    exact simulate (.stop ha) _ (fun w hw => .pos (List.mem_cons_of_mem _ hw))) (by
    intro i _ j _ ij p q k hk; exact tails i j ij p q k (by omega))
  intro k hk hb
  apply h k hk (simulate hb _ ?_)
  intro w hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  exact .pos (List.mem_map.mpr ⟨i,by simp [I],rfl⟩)
end PetersenSigned.Theta
namespace PetersenSigned.Petersen.Fifteen
open LowerSeeds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 20000
-- Each row stores seven theta vertices, one vertex to delete, and a
-- surviving neighbor of the deleted vertex. Every row is checked below.
private def layouts : Array Nat := #[
14117209618,36126086947,26161138024,39820797846,31565514258,14117209618,9014105891,35857241731,31508875634,14060836914,14117209618,
36126086947,17335605027,36108334340,30710712693,21585082455,17299958083,17335605027,13531895860,40349411220,36090152323,17335605027,
26161138024,36108334340,18140726800,23509435920,35323385477,40671123092,406418692,18140726800,18107951424,23455873104,18140726800,
39820797846,30710712693,23509435920,4987389456,28326393089,28036843873,23777584976,4987389456,4954614080,1214412033,4987389456,
31565514258,21585082455,35323385477,28326393089,9535911169,4453533202,32618120562,28269754465,9552549665,9535911169,9535911169,
14117209618,17299958083,40671123092,28036843873,4453533202,10626413569,15190787122,15189816321,10626413569,10609509153,10626413569,
9014105891,17335605027,406418692,23777584976,32618120562,15190787122,15155343888,19735323456,19718746640,15155343888,15155343888,
35857241731,13531895860,18140726800,4987389456,28269754465,15189816321,19735323456,4987389456,1499608065,6045115200,4987389456,
31508875634,40349411220,18107951424,4954614080,9552549665,10626413569,19718746640,1499608065,6028538384,6028538384,6028538384,
14060836914,36090152323,23455873104,1214412033,9535911169,10609509153,15155343888,6045115200,6028538384,6028538384,6028538384,
14117209618,17335605027,18140726800,4987389456,9535911169,10626413569,15155343888,4987389456,6028538384,6028538384,6028538384]
private def digit (d e : Fin 11) (h : Nat) : Fin 10 :=
  ⟨((layouts[d.val*11+e.val]! >>> (4*h))%16)%10, Nat.mod_lt _ (by decide)⟩
private def thetaMap (d e : Fin 11) (j : Fin 10) : Option (Fin 7) :=
  if j = digit d e 0 then some 0 else if j = digit d e 1 then some 1 else
  if j = digit d e 2 then some 2 else if j = digit d e 3 then some 3 else
  if j = digit d e 4 then some 4 else if j = digit d e 5 then some 5 else
  if j = digit d e 6 then some 6 else none
private def live (d e : Fin 11) : Nat → Finset (Fin 10)
  | 0 => region d e
  | h+1 => (live d e h).erase (digit d e (7+h))
private def witness (d e : Fin 11) (h : Nat) (i : Fin 10) :=
  decide (i = digit d e (8+h))

def thetaModel (x : Fin 7 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 2)
private theorem recognizes_theta : ∀ d e x,
    graph (live d e 1) (feed (thetaMap d e) x) = thetaModel x := by decide +kernel
private theorem recognizes_neighbor : ∀ d e (h : Fin 1),
    graph (live d e h.val) (witness d e h.val) = false ∧
    graph (live d e h.val) (Function.update (witness d e h.val) (digit d e (7+h.val)) true) = true := by decide +kernel

private abbrev Lower (I : Finset (Fin 10)) (L : Nat) :=
  ∀ k < L, ¬ Builds k (raws I) (graph I)

private theorem raise_one (d e : Fin 11) (h : Fin 1) (L : Nat) (hp : 0 < L)
    (child : Lower (live d e (h.val+1)) L) : Lower (live d e h.val) (L+1) := by
  let I := live d e h.val
  let i := digit d e (7+h.val)
  apply lift_one I i
  · obtain ⟨h0,h1⟩ := recognizes_neighbor d e h
    refine ⟨witness d e h.val, Function.update (witness d e h.val) i true,?_,?_⟩
    · intro j hj; simp [Function.update_of_ne hj]
    · change graph (live d e h.val) _ ≠ graph (live d e h.val) (Function.update _ (digit d e (7+h.val)) true)
      rw [h0,h1]; decide
  · rw [graph_fixed]
    rintro ⟨c,eqn⟩
    apply child 0 hp
    change Builds 0 (raws (I.erase i)) (graph (I.erase i))
    rw [eqn]
    cases c
    · exact .stop .zero
    · exact .stop .one
  · rw [graph_fixed]; exact child

private theorem base_eleven (d e : Fin 11) (T : ∀ k < 10, ¬ Builds k (raw 7) thetaModel) : Lower (region d e) 11 := by
  have h1 : Lower (live d e 1) 10 := project_lower _ (thetaMap d e) _ _ (recognizes_theta d e) T
  exact raise_one d e 0 10 (by decide) h1

private theorem deleted_thirteen (T : ∀ k < 10, ¬ Builds k (raw 7) thetaModel) (d : Fin 11) : Lower (region d 10) 13 := by
  apply lift_two (L := 11) _ _ (no_raw d 10) (robust d)
  · intro i _; rw [graph_fixed,region_erase]; exact varies d i.castSucc
  · intro i _; rw [graph_fixed,region_erase]; exact base_eleven d i.castSucc T

theorem full_signed_fifteen (T : ∀ k < 10, ¬ Builds k (raw 7) thetaModel) : ∀ k < 15, ¬ Builds k (raw 10) edge := by
  have h := lift_two (L := 13) _ _ (no_raw 10 10) (robust 10) (by
    intro i _; rw [graph_fixed,region_erase]; exact varies 10 i.castSucc) (by
    intro i _; rw [graph_fixed,region_erase,region_swap 10 i.castSucc]; exact deleted_thirteen T i.castSucc)
  have he : graph (region 10 10) = edge := by funext x; simp [graph,all_region]
  rw [he] at h
  intro k hk hb
  apply h _ hk
  apply simulate hb
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact .pos (List.mem_map.mpr ⟨i,by simp [all_region],rfl⟩)

theorem full_ordinary_fifteen (T : ∀ k < 10, ¬ Builds k (raw 7) thetaModel) : ¬ HasCircuitSize 10 edge 14 := by
  rintro ⟨C,hc,hs,he⟩
  have hb := circuit_to_signed 10 C hc
  rw [show (fun x => C.eval (List.ofFn x)) = edge from funext he] at hb
  apply full_signed_fifteen T _ _ hb
  have h := List.countP_le_length (p := fun g => binaryOp g.op) (l := C.gates)
  change C.gates.length ≤ 14 at hs
  omega
end PetersenSigned.Petersen.Fifteen
namespace PetersenSigned.Petersen.Fifteen
theorem signed : ∀ k < 15, ¬ Builds k (raw 10) edge :=
  full_signed_fifteen (Theta.lower CycleSeven.lower SixOpposite.lower)
theorem ordinary : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 edge 14 :=
  full_ordinary_fifteen (Theta.lower CycleSeven.lower SixOpposite.lower)
end PetersenSigned.Petersen.Fifteen
#print axioms PetersenSigned.Petersen.Fifteen.signed
#print axioms PetersenSigned.Petersen.Fifteen.ordinary
