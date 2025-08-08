import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.Over

universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

noncomputable section

instance : CartesianMonoidalCategory C := by exact ofFiniteProducts

#check pullback

def GammaFunc : (Over X) ⥤ C where
  obj := (fun (A : Over X) =>
    if ∃ (A' : C), A.left = X ⊗ A')
