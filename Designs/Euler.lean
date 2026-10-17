import Designs.Euler.Report
import Designs.Euler.P010
import Designs.Euler.P014
import Designs.Euler.P025
import Designs.Euler.P031
import Designs.Euler.P043
import Designs.Euler.P048
import Designs.Euler.P057
import Designs.Euler.P058
import Designs.Euler.P092
import Designs.Euler.P097

/-! The Project Euler solvers, by problem number. -/
namespace HDLean.Euler

def problems : List Problem := [P010.problem, P014.problem, P025.problem, P031.problem, P043.problem, P048.problem, P057.problem, P058.problem, P092.problem, P097.problem]

def find? (n : Nat) : Option Problem := problems.find? (·.number == n)

end HDLean.Euler
