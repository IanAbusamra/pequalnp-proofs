import SixNumeric0
import SixNumeric1
import SixNumeric2
import SixNumeric3
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
#print axioms PetersenSigned.SixOpposite.lower
