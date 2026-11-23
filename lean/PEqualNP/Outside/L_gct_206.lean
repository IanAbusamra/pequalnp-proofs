import Mathlib

namespace PEqualNP.Outside.Border206
open Finset

-- The support is the union of the first row and the first column.
private def entry (x : Fin 7 → ℂ) (ij : Fin 4 × Fin 6) : ℂ :=
  match ij.1.val, ij.2.val with
  | 0, 0 => -(x 4 + x 5 + x 6)
  | 0, 1 => x 0
  | 0, 2 => x 1
  | 0, 3 => x 2
  | 0, 4 => x 3
  | 0, 5 => -(x 0 + x 1 + x 2 + x 3)
  | 1, 0 => x 4
  | 2, 0 => x 5
  | 3, 0 => x 6
  | _, _ => 0

private def border : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := entry
  map_add' x y := by funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> simp [entry] <;> ring
  map_smul' c x := by funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> simp [entry] <;> ring

private theorem injective : Function.Injective border := by
  intro x y h
  funext i
  fin_cases i
  · exact congrFun h (0,1)
  · exact congrFun h (0,2)
  · exact congrFun h (0,3)
  · exact congrFun h (0,4)
  · exact congrFun h (1,0)
  · exact congrFun h (2,0)
  · exact congrFun h (3,0)

private def minor (x : Fin 7 → ℂ) (k : ℕ) (R : Finset (Fin 4)) (C : Finset (Fin 6)) : ℂ :=
  if h : R.card=k ∧ C.card=k then
    Matrix.permanent (Matrix.of fun a b => entry x (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b))
  else 0

private theorem off_border (x : Fin 7 → ℂ) (i : Fin 4) (j : Fin 6) (hi : i ≠ 0) (hj : j ≠ 0) :
    entry x (i,j) = 0 := by
  fin_cases i <;> fin_cases j <;> first | contradiction | rfl

private theorem large (x : Fin 7 → ℂ) (k : ℕ) (hk : 3 ≤ k) (R : Finset (Fin 4)) (C : Finset (Fin 6)) :
    minor x k R C = 0 := by
  classical
  unfold minor
  split_ifs with h
  · unfold Matrix.permanent
    apply Finset.sum_eq_zero
    intro σ _
    let r (i : Fin k) := R.orderEmbOfFin h.1 (σ i)
    let c := C.orderEmbOfFin h.2
    have ir : Function.Injective r := (R.orderEmbOfFin h.1).injective.comp σ.injective
    let a : Fin k := ⟨0,by omega⟩
    let b : Fin k := ⟨1,by omega⟩
    let d : Fin k := ⟨2,by omega⟩
    have ab : a ≠ b := by intro eq; have := congrArg Fin.val eq; change 0=1 at this; omega
    have ad : a ≠ d := by intro eq; have := congrArg Fin.val eq; change 0=2 at this; omega
    have bd : b ≠ d := by intro eq; have := congrArg Fin.val eq; change 1=2 at this; omega
    have exists_off : ∃ i, r i ≠ 0 ∧ c i ≠ 0 := by
      by_contra! hn
      have choice (i : Fin k) : r i = 0 ∨ c i = 0 := or_iff_not_imp_left.mpr (hn i)
      rcases choice a with ha | ha <;> rcases choice b with hb | hb <;> rcases choice d with hd | hd <;>
        first | exact ab (ir (ha.trans hb.symm)) | exact ab (c.injective (ha.trans hb.symm)) |
                exact ad (ir (ha.trans hd.symm)) | exact ad (c.injective (ha.trans hd.symm)) |
                exact bd (ir (hb.trans hd.symm)) | exact bd (c.injective (hb.trans hd.symm))
    obtain ⟨i,hi,hj⟩ := exists_off
    exact Finset.prod_eq_zero (Finset.mem_univ i) (off_border x _ _ hi hj)
  · rfl

private theorem permTwo (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.permanent = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  unfold Matrix.permanent
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two,Fin.prod_univ_two,Equiv.swap_apply_def]

private theorem enumerate4_1 (f : Finset (Fin 4) → ℂ)
    (hf : ∀ S, S.card ≠ 1 → f S = 0) :
    (∑ S, f S) = f {0} + f {1} + f {2} + f {3} := by
  let xs : List (Finset (Fin 4)) := [{0}, {1}, {2}, {3}]
  have allSets : ∀ S : Finset (Fin 4), S.card = 1 → S ∈ xs := by decide
  have nodup : xs.Nodup := by decide
  have hsum := Finset.sum_subset (Finset.subset_univ xs.toFinset)
    (fun S _ h => hf S (fun eq => h (List.mem_toFinset.mpr (allSets S eq))))
  rw [← hsum, List.sum_toFinset _ nodup]
  simp [xs,add_assoc]

private theorem enumerate4_2 (f : Finset (Fin 4) → ℂ)
    (hf : ∀ S, S.card ≠ 2 → f S = 0) :
    (∑ S, f S) = f {0,1} + f {0,2} + f {0,3} + f {1,2} + f {1,3} + f {2,3} := by
  let xs : List (Finset (Fin 4)) := [{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}]
  have allSets : ∀ S : Finset (Fin 4), S.card = 2 → S ∈ xs := by decide
  have nodup : xs.Nodup := by decide
  have hsum := Finset.sum_subset (Finset.subset_univ xs.toFinset)
    (fun S _ h => hf S (fun eq => h (List.mem_toFinset.mpr (allSets S eq))))
  rw [← hsum, List.sum_toFinset _ nodup]
  simp [xs,add_assoc]

private theorem enumerate6_1 (f : Finset (Fin 6) → ℂ)
    (hf : ∀ S, S.card ≠ 1 → f S = 0) :
    (∑ S, f S) = f {0} + f {1} + f {2} + f {3} + f {4} + f {5} := by
  let xs : List (Finset (Fin 6)) := [{0}, {1}, {2}, {3}, {4}, {5}]
  have allSets : ∀ S : Finset (Fin 6), S.card = 1 → S ∈ xs := by decide
  have nodup : xs.Nodup := by decide
  have hsum := Finset.sum_subset (Finset.subset_univ xs.toFinset)
    (fun S _ h => hf S (fun eq => h (List.mem_toFinset.mpr (allSets S eq))))
  rw [← hsum, List.sum_toFinset _ nodup]
  simp [xs,add_assoc]

private theorem enumerate6_2 (f : Finset (Fin 6) → ℂ)
    (hf : ∀ S, S.card ≠ 2 → f S = 0) :
    (∑ S, f S) = f {0,1} + f {0,2} + f {0,3} + f {0,4} + f {0,5} + f {1,2} + f {1,3} + f {1,4} + f {1,5} + f {2,3} + f {2,4} + f {2,5} + f {3,4} + f {3,5} + f {4,5} := by
  let xs : List (Finset (Fin 6)) := [{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {1,2}, {1,3}, {1,4}, {1,5}, {2,3}, {2,4}, {2,5}, {3,4}, {3,5}, {4,5}]
  have allSets : ∀ S : Finset (Fin 6), S.card = 2 → S ∈ xs := by decide
  have nodup : xs.Nodup := by decide
  have hsum := Finset.sum_subset (Finset.subset_univ xs.toFinset)
    (fun S _ h => hf S (fun eq => h (List.mem_toFinset.mpr (allSets S eq))))
  rw [← hsum, List.sum_toFinset _ nodup]
  simp [xs,add_assoc]


private theorem order0 {n : ℕ} (i : Fin n) (h : ({i} : Finset (Fin n)).card=1) :
    ({i} : Finset (Fin n)).orderEmbOfFin h 0 = i := by
  simpa using ({i} : Finset (Fin n)).orderEmbOfFin_mem h 0

private theorem orderPair {n : ℕ} (a b : Fin n) (hab : a<b) (h : ({a,b} : Finset (Fin n)).card = 2) :
    ({a,b} : Finset (Fin n)).orderEmbOfFin h 0 = a ∧ ({a,b} : Finset (Fin n)).orderEmbOfFin h 1 = b := by
  let f := ({a,b} : Finset (Fin n)).orderEmbOfFin h
  have h0 : f 0=a ∨ f 0=b := by simpa only [f, Finset.mem_insert, Finset.mem_singleton] using ({a,b} : Finset (Fin n)).orderEmbOfFin_mem h 0
  have h1 : f 1=a ∨ f 1=b := by simpa only [f, Finset.mem_insert, Finset.mem_singleton] using ({a,b} : Finset (Fin n)).orderEmbOfFin_mem h 1
  have lt := f.strictMono (show (0 : Fin 2) < 1 by decide)
  change f 0 = a ∧ f 1 = b
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp_all <;> omega

private theorem singletonMinor (x : Fin 7 → ℂ) (i : Fin 4) (j : Fin 6) :
    minor x 1 {i} {j} = entry x (i,j) := by
  simp only [minor,card_singleton,dite_true,and_self]
  rw [Matrix.permanent_eq_elem_of_card_eq_one (by decide) (0 : Fin 1)]
  simp only [Matrix.of_apply,order0]

private theorem pairMinor (x : Fin 7 → ℂ) (a b : Fin 4) (i j : Fin 6) (hab : a<b) (hij : i<j) :
    minor x 2 {a,b} {i,j} = entry x (a,i)*entry x (b,j) + entry x (b,i)*entry x (a,j) := by
  have hr : ({a,b} : Finset (Fin 4)).card = 2 := by simp [hab.ne]
  have hc : ({i,j} : Finset (Fin 6)).card = 2 := by simp [hij.ne]
  simp only [minor,dite_eq_left (And.intro hr hc),permTwo,Matrix.of_apply,
    (orderPair a b hab hr).1,(orderPair a b hab hr).2,(orderPair i j hij hc).1,(orderPair i j hij hc).2]

private theorem degree1 (x : Fin 7 → ℂ) : (∑ R, ∑ C, minor x 1 R C) = 0 := by
  have cols (R : Finset (Fin 4)) := enumerate6_1 (minor x 1 R)
    (fun C h => by simp [minor,h])
  rw [enumerate4_1 (fun R => ∑ C, minor x 1 R C) (fun R h => by simp [minor,h])]
  simp only [cols]
  simp only [singletonMinor]
  simp [entry]; ring

private theorem degree2 (x : Fin 7 → ℂ) : (∑ R, ∑ C, minor x 2 R C) = 0 := by
  have cols (R : Finset (Fin 4)) := enumerate6_2 (minor x 2 R)
    (fun C h => by simp [minor,h])
  rw [enumerate4_2 (fun R => ∑ C, minor x 2 R C) (fun R h => by simp [minor,h])]
  simp only [cols]
  simp (disch := decide) only [pairMinor]
  simp [entry]; ring

end PEqualNP.Outside.Border206

open PEqualNP.Outside.Border206 in
theorem PEqualNP.Outside.L_gct_206 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), Module.finrank ℂ L = 7 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) := by
  classical
  refine ⟨LinearMap.range border, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj injective, Module.finrank_fin_fun]
  · rintro _ ⟨x,rfl⟩ k hk _
    change (∑ R, ∑ C, minor x k R C) = 0
    rcases k with _ | (_ | (_ | k))
    · omega
    · exact degree1 x
    · exact degree2 x
    · simp [large x _ (by omega : 3 ≤ k+3)]
