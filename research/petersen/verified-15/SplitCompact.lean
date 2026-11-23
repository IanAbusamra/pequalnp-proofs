import FastCompact
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
#print axioms PetersenSigned.Compact.close_branches
