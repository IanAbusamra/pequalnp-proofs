import AssemblyCore
import SixOpposite
namespace PetersenSigned.Petersen.Fifteen
theorem signed : ∀ k < 15, ¬ Builds k (raw 10) edge :=
  given_opposite SixOpposite.lower
theorem ordinary : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 edge 14 :=
  full_ordinary_fifteen (Theta.lower CycleSeven.lower SixOpposite.lower)
end PetersenSigned.Petersen.Fifteen
#print axioms PetersenSigned.Petersen.Fifteen.signed
#print axioms PetersenSigned.Petersen.Fifteen.ordinary
