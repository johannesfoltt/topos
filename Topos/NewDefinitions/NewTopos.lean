import Topos.NewDefinitions.NewExponentials
import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier PowerObject ChosenPowerObjects

namespace CategoryTheory

universe u v

class Topos (C : Type u) [Category.{v} C] where
  [cartesianMonoidal : CartesianMonoidalCategory C]
  [hasPullbacks : HasPullbacks C]
  [classifier : Classifier C]
  [cartesianClosed : CartesianClosed C]
  [chosenPowerObjects : ChosenPowerObjects C]

--idk what this is needed for
attribute [instance] Topos.cartesianMonoidal
                     Topos.hasPullbacks


variable {C : Type u} [Category.{v} C] [Topos C]

#check Ω
