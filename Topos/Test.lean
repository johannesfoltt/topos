import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

open CategoryTheory Category Limits

variable (C : Type u) [Category.{v} C]

lemma PullbackLimitTransfer_eq_bottom {W X Y Z : C} (k k' : Y ⟶ Z) (h : X ⟶ Z) (f : W ⟶ X) (g : W ⟶ Y) (eq : k = k') (comm : f ≫ h = g ≫ k)
  (lim : IsLimit (PullbackCone.mk f g comm)) : IsLimit (PullbackCone.mk f g (by
    show f ≫ h = g ≫ k'
    rw [←eq]
    assumption
  )) := by
    subst eq
    assumption
