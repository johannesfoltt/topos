import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Topos.PullbackProd
import Topos.Basic

namespace CategoryTheory.Topos

open Category Limits Topos HasClassifier Power

universe u v

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [IsTopos C]

lemma pullback_char {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : prod.map (𝟙 X) (g ≫ (singleton Z) ≫ (inverseImage f)) ≫ in_ X = χ_ (prod.lift (pullback.fst f g) (pullback.snd f g)) := by {
  apply HasClassifier.unique
  --have iv : prod.map (f) (𝟙 (pow Z)) ≫ (in_ Z) = prod.map (𝟙 X) (inverseImage)
  have lower_map : prod.map (𝟙 X) (g ≫ singleton Z ≫ inverseImage f) ≫ in_ X = (prod.map f g) ≫ (Predicate.eq Z) := by {
    rw [← comp_id (𝟙 X), ← prod.map_map_assoc, ← comp_id (𝟙 X), ← prod.map_map, assoc, inverseImage_comm]
    slice_lhs 2 3 => rw [prod.map_swap]
    slice_lhs 3 4 => unfold singleton; simp
    simp
  }
  rw [lower_map, terminal.hom_ext (terminal.from (pullback f g)) ((pullback.fst f g ≫ f) ≫ terminal.from Z)]
  have left := IsPullback.isPullback_Prod_Fst_of_isPullback (IsPullback.of_hasPullback f g)
  have right := HasClassifier.isPullback (diag Z)
  exact IsPullback.paste_vert left right
}
