import Mathlib

namespace PEqualNP.Outside.Subdivision289

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

private def threadVertex {k m : ℕ} (u v : Fin m) (i : Fin (2*k)) : Fin (m+2*k*m*m) :=
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

end PEqualNP.Outside.Subdivision289

open PEqualNP.Outside.Subdivision289

theorem PEqualNP.Outside.L_meta_289 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → ∀ R : Finset (Fin m), (∀ u : Fin m, u ∈ R ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val)) → (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro k m H hk S hS U cover R hR
  let V := Fin (m+2*k*m*m)
  let hub (u : Fin m) : V := ⟨u.val, by have := u.isLt; omega⟩
  have same (u : Fin m) (x : V) : x.val = u.val ↔ x = hub u := ⟨fun e => Fin.ext e,fun e => e ▸ rfl⟩
  have hub_ne (u a b : Fin m) (i : Fin (2*k)) : hub u ≠ threadVertex a b i := by
    intro h
    have := congrArg (fun z : V => z.val) h
    change u.val = m+2*k*(a.val*m+b.val)+i.val at this
    have := u.isLt; omega
  let absent (e : Edge H) := hub e.val.1 ∉ U ∧ hub e.val.2 ∉ U
  have memR (u : Fin m) : u ∈ R ↔ hub u ∈ U ∨ ∃ e : Edge H, e.val.1 = u ∧ absent e := by
    rw [hR]
    simp only [same, ne_eq]
    constructor
    · rintro (hu | ⟨v,huv,he,ha,hb⟩)
      · obtain ⟨x,hx,rfl⟩ := hu; exact Or.inl hx
      · exact Or.inr ⟨⟨(u,v),huv,he⟩, rfl, by simpa [absent] using And.intro ha hb⟩
    · rintro (hu | ⟨⟨⟨a,b⟩,hab,he⟩,rfl,ha,hb⟩)
      · exact Or.inl ⟨_,hu,rfl⟩
      · exact Or.inr ⟨b,hab,he,by simpa using ha,by simpa using hb⟩
  constructor
  · have ordered (u v : Fin m) (h : u < v) (he : H.Adj u v) : u ∈ R ∨ v ∈ R := by
      by_cases hu : hub u ∈ U
      · exact Or.inl ((memR _).2 (Or.inl hu))
      by_cases hv : hub v ∈ U
      · exact Or.inr ((memR _).2 (Or.inl hv))
      exact Or.inl ((memR _).2 (Or.inr ⟨⟨(u,v),h,he⟩,rfl,hu,hv⟩))
    intro u v he
    rcases lt_or_gt_of_ne he.ne with h | h
    · exact ordered u v h he
    · exact (ordered v u h he.symm).symm
  · let first : Fin (2*k) := ⟨0,by omega⟩
    have first_mem (e : Edge H) (ha : absent e) :
        threadVertex e.val.1 e.val.2 first ∈ U := by
      apply Or.resolve_right (cover _ _ ?_) ha.1
      rw [hS]
      exact ⟨(hub_ne _ _ _ _).symm, Or.inl ⟨_,_,e.property.1,e.property.2,first,rfl,Or.inl ⟨rfl,rfl⟩⟩⟩
    have last_mem (e : Edge H) (ha : absent e) (a : Fin (2*k)) (last : a.val+1=2*k) :
        threadVertex e.val.1 e.val.2 a ∈ U := by
      apply Or.resolve_right (cover _ _ ?_) ha.2
      rw [hS]
      exact ⟨(hub_ne _ _ _ _).symm, Or.inl ⟨_,_,e.property.1,e.property.2,a,rfl,Or.inr (Or.inr ⟨last,rfl⟩)⟩⟩
    have adjacent (e : Edge H) (a b : Fin (2*k)) (step : a.val+1=b.val) :
        threadVertex e.val.1 e.val.2 a ∈ U ∨ threadVertex e.val.1 e.val.2 b ∈ U := by
      apply cover
      rw [hS]
      refine ⟨fun eq => ?_, Or.inl ⟨_,_,e.property.1,e.property.2,a,rfl,Or.inr (Or.inl ⟨step ▸ b.isLt,?_⟩)⟩⟩
      · have hi := (inner_inj eq).2.2
        have := congrArg Fin.val hi; omega
      · change _ + b.val = _ + a.val + 1
        omega
    let low (e : Edge H) (a : Fin k) := 2*a.val + if absent e then 1 else 0
    have select_slot (e : Edge H) (a : Fin k) : ∃ i : Fin (2*k),
        threadVertex e.val.1 e.val.2 i ∈ U ∧ low e a ≤ i.val ∧ i.val ≤ low e a + 1 := by
      have ha := a.isLt
      have lo : low e a < 2*k := by dsimp [low]; split <;> omega
      let j : Fin (2*k) := ⟨_,lo⟩
      by_cases hh : low e a + 1 < 2*k
      · let l : Fin (2*k) := ⟨_,hh⟩
        rcases adjacent e j l rfl with h | h
        · exact ⟨j,h,le_rfl,Nat.le_succ _⟩
        · exact ⟨l,h,Nat.le_succ _,le_rfl⟩
      · have ab : absent e := by
          by_contra h
          simp [low,h] at hh
          omega
        exact ⟨j,last_mem e ab j (by change low e a + 1 = _; omega),le_rfl,Nat.le_succ _⟩
    choose slot slot_mem slot_lo slot_hi using select_slot
    have slot_inj (e : Edge H) {a b : Fin k} (eq : slot e a = slot e b) : a=b := by
      have h := congrArg Fin.val eq
      have h1 := slot_lo e a; have h2 := slot_hi e a
      have h3 := slot_lo e b; have h4 := slot_hi e b
      dsimp [low] at h1 h2 h3 h4
      apply Fin.ext; omega
    have slot_pos (e : Edge H) (ha : absent e) (i : Fin k) : 0 < (slot e i).val := by
      have h := slot_lo e i; simp [low,ha] at h; omega
    have pick (u : R) (hu : hub u.val ∉ U) : ∃ e : Edge H, e.val.1 = u.val ∧ absent e :=
      ((memR _).1 u.property).resolve_left hu
    let chosen (u : R) (hu : hub u.val ∉ U) := (pick u hu).choose
    have spec (u : R) (hu : hub u.val ∉ U) := (pick u hu).choose_spec
    let extra (u : R) : U := if h : hub u.val ∈ U then ⟨hub u.val,h⟩ else
      ⟨threadVertex (chosen u h).val.1 (chosen u h).val.2 first,first_mem _ (spec u h).2⟩
    let base (p : Edge H × Fin k) : U :=
      ⟨threadVertex p.1.val.1 p.1.val.2 (slot p.1 p.2),slot_mem p.1 p.2⟩
    have ei : Function.Injective extra := by
      intro u v eq
      have h := congrArg Subtype.val eq
      by_cases hu : hub u.val ∈ U <;> by_cases hv : hub v.val ∈ U <;> simp [extra,hu,hv] at h
      · exact Subtype.ext (Fin.ext (congrArg (fun x : V => x.val) h))
      · exact (hub_ne _ _ _ _ h).elim
      · exact (hub_ne _ _ _ _ h.symm).elim
      · have h1 := (inner_inj h).1
        exact Subtype.ext ((spec u hu).1.symm.trans (h1.trans (spec v hv).1))
    have bi : Function.Injective base := by
      rintro ⟨e,i⟩ ⟨g,j⟩ h
      obtain ⟨h1,h2,h3⟩ := inner_inj (congrArg Subtype.val h)
      have eq : e=g := Subtype.ext (Prod.ext h1 h2)
      subst g
      exact Prod.ext rfl (slot_inj e h3)
    have sep (u : R) (p : Edge H × Fin k) : extra u ≠ base p := by
      intro eq
      have h := congrArg Subtype.val eq
      by_cases hu : hub u.val ∈ U <;> simp [extra,base,hu] at h
      · exact hub_ne _ _ _ _ h
      · obtain ⟨h1,h2,hi⟩ := inner_inj h
        have he : chosen u hu = p.1 := Subtype.ext (Prod.ext h1 h2)
        have ab : absent p.1 := he ▸ (spec u hu).2
        have hp := slot_pos p.1 ab p.2
        have hz : 0 = (slot p.1 p.2).val := congrArg Fin.val hi
        omega
    let f := Sum.elim extra base
    have inj : Function.Injective f := by
      intro a b h
      rcases a with a | a <;> rcases b with b | b
      · exact congrArg Sum.inl (ei h)
      · exact (sep a b h).elim
      · exact (sep b a h.symm).elim
      · exact congrArg Sum.inr (bi h)
    have bound := Fintype.card_le_of_injective f inj
    have ec : Fintype.card (Edge H) = H.edgeSet.ncard := by simpa only [Nat.card_eq_fintype_card] using edge_count H
    simpa [ec,Nat.mul_comm] using bound
