import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.Power

namespace CategoryTheory

open Category Limits Over

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasClassifier C] [CartesianMonoidalCategory C]
