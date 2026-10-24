import BFGS.Arithmetic.IntervalArithmetic

/-! The rational input interval for the current scalar root certificate. -/
namespace BFGS.Counterexample.Trace

def rootInterval : BFGS.RationalInterval :=
  ⟨91781039164 / 100000000000, 91781039165 / 100000000000⟩

end BFGS.Counterexample.Trace
