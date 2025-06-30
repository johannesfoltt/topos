import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.OverClassifier
import Topos.ClassifierMeet

namespace CategoryTheory

open Category Limits Over Power Topos HasClassifier

universe u v

noncomputable section


--Here we assume IsTopos C as a variable, because we need the equalizer, terminal objects, binary products, pullbacks, HasClassifier and HasPowerObjects (we need HasPowerObjects to define the inverse image)

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [IsTopos C] {X : C} (A : Over X)

--Why do I have to do this?
instance : CartesianMonoidalCategory (Over X) := cartesianMonoidalCategory X

namespace Over

abbrev powerOver.t : pow A.left ⨯ X ⟶ pow A.left := (𝟙 (pow A.left) ∧_P₂ (singleton X ≫ inverseImage A.hom))

abbrev powerOver.pow : Over X := mk (equalizer.ι prod.fst (powerOver.t A) ≫ prod.snd)

abbrev powerOver.in_ : (pow A) ⨯ A ⟶ Ω (Over X) := sorry
