import Mathlib

namespace PEqualNP.Outside.Subdivision303

private abbrev Edge {m : ℕ} (H : SimpleGraph (Fin m)) :=
  {uv : Fin m × Fin m // uv.1 < uv.2 ∧ H.Adj uv.1 uv.2}

private theorem edge_count {m : ℕ} (H : SimpleGraph (Fin m)) :
    Nat.card (Edge H) = H.edgeSet.ncard := by
  let f (e : Edge H) : H.edgeSet := ⟨s(e.1.1, e.1.2), e.2.2⟩
  have inj : Function.Injective f := by
    intro a b h
    have e := Sym2.eq_iff.mp (congrArg Subtype.val h)
    rcases e with ⟨e1,e2⟩ | ⟨e1,e2⟩
    · exact Subtype.ext (Prod.ext e1 e2)
    · have h1 := a.2.1
      have h2 := b.2.1
      rw [e1,e2] at h1
      exact (lt_asymm h1 h2).elim
  have sur : Function.Surjective f := by
    rintro ⟨edge, he⟩
    induction edge using Sym2.inductionOn with | _ u v
    change H.Adj u v at he
    rcases lt_or_gt_of_ne he.ne with h | h
    · exact ⟨⟨(u,v),h,he⟩,rfl⟩
    · exact ⟨⟨(v,u),h,he.symm⟩, Subtype.ext (Sym2.eq_swap)⟩
  simpa [Set.ncard_eq_toFinset_card', ← Nat.card_eq_fintype_card] using
    Nat.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)

private theorem digits {d a b i j : ℕ} (hi : i < d) (hj : j < d)
    (eq : d*a+i = d*b+j) : a=b ∧ i=j := by
  have hij := congrArg (· % d) eq
  simp [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hij
  have hd : 0 < d := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_left hd (by omega),hij⟩

private def threadVertex {k m : ℕ} (u v : Fin m) (i : Fin (2*k)) : Fin (m+2*k*(m*m)) :=
  ⟨m + 2*k*(u.val*m+v.val) + i.val, by
    have h1 : u.val*m + v.val < m*m := calc
      _ < u.val*m+m := Nat.add_lt_add_left v.isLt _
      _ = (u.val+1)*m := by ring
      _ ≤ m*m := Nat.mul_le_mul_right m u.isLt
    calc
      _ < m + (2*k)*((u.val*m+v.val)+1) := by
        rw [Nat.mul_succ]; have := i.isLt; omega
      _ ≤ m + (2*k)*(m*m) := Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _
      _ = _ := by ring⟩

private theorem inner_inj {k m : ℕ} {u v a b : Fin m} {i j : Fin (2*k)}
    (h : threadVertex u v i = threadVertex a b j) : u=a ∧ v=b ∧ i=j := by
  have h' := congrArg Fin.val h
  change m + 2*k*(u.val*m+v.val)+i.val = m + 2*k*(a.val*m+b.val)+j.val at h'
  obtain ⟨ht,hi⟩ := digits i.isLt j.isLt (by omega : 2*k*(u.val*m+v.val)+i.val = 2*k*(a.val*m+b.val)+j.val)
  obtain ⟨hu,hv⟩ := digits v.isLt b.isLt (by simpa [Nat.mul_comm] using ht : m*u.val+v.val=m*a.val+b.val)
  exact ⟨Fin.ext hu,Fin.ext hv,Fin.ext hi⟩

end PEqualNP.Outside.Subdivision303

open PEqualNP.Outside.Subdivision303

theorem PEqualNP.Outside.L_meta_303 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  classical
  intro m k H T F hF
  let V := Fin (m+2*k*(m*m))
  have old_mem {j : V} (u : Fin m) (hu : u ∈ T) (eq : j.val = u.val) : j ∈ F :=
    (hF j).2 (Or.inl ⟨u,hu,eq⟩)
  have new_mem {j : V} (u v : Fin m) (hu : u < v) (he : H.Adj u v) (i : Fin (2*k))
      (eq : j.val = (threadVertex u v i).val) (hp : i.val % 2 = 1 ↔ u ∈ T) : j ∈ F :=
    (hF j).2 (Or.inr ⟨u,v,i.val,i.isLt,hu,he,eq,hp⟩)
  let D := T ⊕ (Edge H × Fin k)
  let original (u : Fin m) : V := ⟨u.val, by have := u.isLt; omega⟩
  let slot (u : Fin m) (a : Fin k) : Fin (2*k) :=
    ⟨2*a.val + if u ∈ T then 1 else 0, by split <;> have := a.isLt <;> omega⟩
  have parity (u : Fin m) (a : Fin k) : (slot u a).val % 2 = 1 ↔ u ∈ T := by
    by_cases hu : u ∈ T <;> simp [slot,hu]
  let enc : D → V := Sum.elim (fun u => original u.val)
    (fun z => threadVertex z.1.val.1 z.1.val.2 (slot z.1.val.1 z.2))
  have member (d : D) : enc d ∈ F := by
    rcases d with u | ⟨e,a⟩
    · exact old_mem u.val u.property rfl
    · exact new_mem _ _ e.property.1 e.property.2 _ rfl (parity _ a)
  let f (d : D) : F := ⟨enc d,member d⟩
  have separate (u : T) (e : Edge H) (a : Fin k) :
      original u.val ≠ threadVertex e.val.1 e.val.2 (slot e.val.1 a) := by
    intro h
    have hh := congrArg Fin.val h
    change u.val.val = m+2*k*(_*m+_)+_ at hh
    have := u.val.isLt; omega
  have inj : Function.Injective f := by
    intro a b eq
    have h : enc a = enc b := congrArg Subtype.val eq
    rcases a with a | ⟨e,i⟩ <;> rcases b with b | ⟨e',j⟩
    · have hv : a.val.val = b.val.val := congrArg (fun z : V => z.val) h
      exact congrArg Sum.inl (Subtype.ext (Fin.ext hv))
    · exact (separate _ _ _ h).elim
    · exact (separate _ _ _ h.symm).elim
    · obtain ⟨hu,hv,hij⟩ := inner_inj h
      have he : e=e' := Subtype.ext (Prod.ext hu hv)
      subst e'
      have hval := congrArg Fin.val hij
      change 2*i.val + (if e.val.1 ∈ T then 1 else 0) = 2*j.val + (if e.val.1 ∈ T then 1 else 0) at hval
      have ij : i = j := Fin.ext (by omega)
      exact congrArg Sum.inr (Prod.ext rfl ij)
  have sur : Function.Surjective f := by
    rintro ⟨j,hj⟩
    rcases (hF j).1 hj with ⟨u,hu,eq⟩ | ⟨u,v,ii,hi,hu,he,eq,hp⟩
    · exact ⟨Sum.inl ⟨u,hu⟩, Subtype.ext (Fin.ext eq.symm)⟩
    · let i : Fin (2*k) := ⟨ii,hi⟩
      change i.val % 2 = 1 ↔ u ∈ T at hp
      let a : Fin k := ⟨i.val/2, by have := i.isLt; omega⟩
      have ha : slot u a = i := by
        apply Fin.ext
        change 2*(i.val/2)+(if u ∈ T then 1 else 0)=i.val
        by_cases h : u ∈ T <;> simp_all <;> omega
      refine ⟨Sum.inr (⟨(u,v),hu,he⟩,a), Subtype.ext (Fin.ext ?_)⟩
      change (threadVertex u v (slot u a)).val = j.val
      rw [ha]; exact eq.symm
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)
  have ec : Fintype.card (Edge H) = H.edgeSet.ncard := by simpa only [Nat.card_eq_fintype_card] using edge_count H
  simpa [ec, D, Nat.card_sum, Nat.card_prod, Nat.card_eq_finsetCard, edge_count H, Nat.mul_comm] using hc.symm
