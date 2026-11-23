import CompactSearch
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
#print axioms PetersenSigned.Compact.reject_fast
