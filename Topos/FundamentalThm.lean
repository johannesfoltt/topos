import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.Basic

namespace CategoryTheory

open Category Limits HasClassifier Power

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [IsTopos C]
variable (X : C)

--instance IsToposOver : IsTopos (Over X) := sorry
