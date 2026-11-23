import Mathlib
import PEqualNP.Defs

namespace PetersenWitnesses
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (x : Fin 10 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

private def upperTwentyCircuit : Circuit where
  gates := [⟨.or,[1,4]⟩,
    ⟨.or,[10,5]⟩,
    ⟨.and,[0,11]⟩,
    ⟨.or,[2,6]⟩,
    ⟨.and,[1,13]⟩,
    ⟨.or,[2,4]⟩,
    ⟨.or,[15,8]⟩,
    ⟨.and,[3,16]⟩,
    ⟨.or,[2,5]⟩,
    ⟨.or,[18,9]⟩,
    ⟨.and,[7,19]⟩,
    ⟨.or,[6,5]⟩,
    ⟨.and,[8,21]⟩,
    ⟨.or,[4,6]⟩,
    ⟨.and,[9,23]⟩,
    ⟨.or,[12,14]⟩,
    ⟨.or,[25,17]⟩,
    ⟨.or,[26,20]⟩,
    ⟨.or,[27,22]⟩,
    ⟨.or,[28,24]⟩]
  output := 29

theorem upperTwenty : HasCircuitSize 10 (edge) 20 := by
  refine ⟨upperTwentyCircuit, ?_, by decide, ?_⟩
  · intro g hg
    simp [upperTwentyCircuit] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel

private def deletedUpperSixteenCircuit : Circuit where
  gates := [⟨.or,[1,3]⟩,
    ⟨.or,[1,8]⟩,
    ⟨.or,[2,9]⟩,
    ⟨.or,[3,9]⟩,
    ⟨.or,[3,5]⟩,
    ⟨.and,[8,14]⟩,
    ⟨.or,[9,11]⟩,
    ⟨.and,[2,10]⟩,
    ⟨.and,[4,13]⟩,
    ⟨.or,[5,12]⟩,
    ⟨.or,[6,15]⟩,
    ⟨.or,[7,17]⟩,
    ⟨.and,[20,16]⟩,
    ⟨.and,[19,21]⟩,
    ⟨.or,[18,23]⟩,
    ⟨.or,[24,22]⟩]
  output := 25

theorem deletedUpperSixteen : HasCircuitSize 10 (fun x => edge (Function.update x 0 false)) 16 := by
  refine ⟨deletedUpperSixteenCircuit, ?_, by decide, ?_⟩
  · intro g hg
    simp [deletedUpperSixteenCircuit] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel

end PetersenWitnesses
