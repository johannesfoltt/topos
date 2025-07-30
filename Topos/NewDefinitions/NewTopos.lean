import Topos.NewDefinitions.NewExponentials
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

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
                     Topos.classifier
                     Topos.cartesianClosed
                     Topos.chosenPowerObjects

namespace Topos

variable {C : Type u} [Category.{v} C] [Topos C]

instance hasEqualizers : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

instance hasFiniteLimits : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
