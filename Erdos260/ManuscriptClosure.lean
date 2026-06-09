import Mathlib
import Erdos260.PerFailureAssembly

/-!
# Manuscript closure endpoint

This is the final no-`sorry`, no-`axiom` endpoint for the factory-based
closure refactor.  A `ManuscriptClosureData` value is precisely the remaining
analytic manuscript content, organized as a `GlobalClosureFactory`.  Once that
data is supplied, the canonical `Erdos260ClosureCertificate` and the final
conditional target theorem follow immediately.
-/

namespace Erdos260

noncomputable section

/-- The remaining manuscript content after the factory refactor. -/
structure ManuscriptClosureData where
  globalFactory : GlobalClosureFactory

/-- Build the canonical closure certificate from the manuscript closure data. -/
def ManuscriptClosureData.toClosureCertificate
    (data : ManuscriptClosureData) :
    Erdos260ClosureCertificate :=
  data.globalFactory.toCertificate

/-- Theorem A from the factory-organized manuscript closure data. -/
theorem theoremA_of_manuscriptClosureData
    (data : ManuscriptClosureData) :
    TheoremAStatement :=
  theoremA_of_closureCertificate data.toClosureCertificate

/-- Erdős 260 from the factory-organized manuscript closure data. -/
theorem erdos260Statement_of_manuscriptClosureData
    (data : ManuscriptClosureData) :
    Erdos260Statement :=
  erdos260Statement_of_closureCertificate data.toClosureCertificate

end

end Erdos260
