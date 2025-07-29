import Topos.NewDefinitions.NewPower
import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject

namespace CategoryTheory

universe u v

class Topos (C : Type u) [Category.{v} C] where
  [cartesianMonoidal : CartesianMonoidalCategory C]
  [hasPullbacks : HasPullbacks C]
  [classifier : Classifier C]
  [chosenPowerObjects : ChosenPowerObjects C]
  [cartesianClosed : CartesianClosed C]

attribute [instance] Topos.cartesianMonoidal
                     Topos.hasPullbacks

namespace Topos

variable (C : Type u) [Category.{v} C] [Topos C]

abbrev Ω : C := classifier.Ω

abbrev t : 𝟙_ C ⟶ Ω C := classifier.t

variable {C} {S X : C} (m : S ⟶ X) [Mono m]

def χ_ := classifier.char m
