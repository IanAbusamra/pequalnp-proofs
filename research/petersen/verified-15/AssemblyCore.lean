import C5Seven
import SplitCompact
namespace PetersenSigned
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

private theorem transport {α β} (σ : β → α) {s : List (Signal α)} {t : List (Signal β)}
    (rel : ∀ z ∈ s, Available t (z ∘ σ)) {a} (h : Available s a) : Available t (a ∘ σ) := by
  cases h with
  | zero => exact .zero
  | one => exact .one
  | pos hz => exact rel _ hz
  | negated hz => exact flip (rel _ hz)

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
theorem given_opposite (h : ∀ p q, ∀ k < 8, ¬ Builds k (Theta.opposite p q :: raw 6) Theta.hex) :
    ∀ k < 15, ¬ Builds k (raw 10) edge :=
  full_signed_fifteen (Theta.lower CycleSeven.lower h)
end PetersenSigned.Petersen.Fifteen
#print axioms PetersenSigned.Petersen.Fifteen.given_opposite
