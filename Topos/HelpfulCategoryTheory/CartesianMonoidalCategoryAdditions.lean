import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Topos.HelpfulCategoryTheory.ChosenTerminalObjects

universe u v

open CategoryTheory Category MonoidalCategory CartesianMonoidalCategory Limits.ChosenTerminalObject

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

namespace CategoryTheory.CartesianMonoidalCategory

abbrev diag (X : C) : X ⟶ X ⊗ X := lift (𝟙 X) (𝟙 X)

lemma comp_diag {X Y : C} (f : X ⟶ Y) : f ≫ diag Y = lift f f := by {
  rw [comp_lift, comp_id]
}

@[reassoc]
theorem diag_map {X Y : C} (f : X ⟶ Y) : diag X ≫ (f ⊗ f) = f ≫ diag Y := by simp

@[reassoc]
theorem diag_map_fst_snd {X Y : C} : diag (X ⊗ Y) ≫ ((fst X Y) ⊗ (snd X Y)) = 𝟙 (X ⊗ Y) := by simp

@[reassoc]
theorem diag_map_fst_snd_comp {X X' Y Y' : C} (g : X ⟶ Y) (g' : X' ⟶ Y') : diag (X ⊗ X') ≫ (((fst X X') ≫ g) ⊗ ((snd X X') ≫ g')) = g ⊗ g' := by simp

lemma rightUnitor_inv (X : C) : (ρ_ X).inv = lift (𝟙 X) (toUnit X) := by {
  refine hom_ext (ρ_ X).inv (lift (𝟙 X) (toUnit X)) ?_ ?_
  · rw [rightUnitor_inv_fst, lift_fst]
  · rw [rightUnitor_inv_snd, lift_snd]
}

instance tensor_map_mono {X₀ X₁ Y₀ Y₁ : C} (f₀ : X₀ ⟶ Y₀) [Mono f₀] (f₁ : X₁ ⟶ Y₁) [Mono f₁] : Mono (f₀ ⊗ f₁) where
  right_cancellation := by {
    intros Z g₀ g₁ h
    rw [CartesianMonoidalCategory.hom_ext_iff] at h
    have h₀ := h.left; simp at h₀
    have h₁ := h.right; simp at h₁
    rw [CartesianMonoidalCategory.hom_ext_iff]; apply And.intro
    · exact (cancel_mono_assoc_iff f₀).mp h₀
    · exact (cancel_mono_assoc_iff f₁).mp h₁
  }

end CartesianMonoidalCategory

namespace Limits.ChosenTerminalObject

instance of_CartesianMonoidalCategory [CartesianMonoidalCategory C] : Limits.ChosenTerminalObject C where
  top := (𝟙_ C)
  isTerminal := CartesianMonoidalCategory.isTerminalTensorUnit

@[simp]
lemma term_eq_Unit : ⊤_ = 𝟙_ C := rfl

@[simp]
lemma from_eq_toUnit (X : C) : from_ X = toUnit X := rfl
