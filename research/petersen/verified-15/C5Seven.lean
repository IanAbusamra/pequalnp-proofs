import CompactSearch
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
#print axioms PetersenSigned.CycleSeven.lower
