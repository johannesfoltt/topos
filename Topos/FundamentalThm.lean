import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.OverEqualizer
import Topos.Basic

namespace CategoryTheory

open Category Limits HasClassifier Power

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [IsTopos C]
variable (X : C)

instance CartesianMonoidalCategoryOver : CartesianMonoidalCategory (Over X) :=
  Over.cartesianMonoidalCategory X

instance HasEqualizersOver : HasEqualizers (Over X) := Over.HasEqualizers

instance HasFiniteLimitsOver : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasEqualizers_and_finite_products

instance IsToposOver : IsTopos (Over X) := sorry
