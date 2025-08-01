import Topos.NewDefinitions.NewPower

open CategoryTheory Category Limits Functor IsPullback MonoidalCategory CartesianMonoidalCategory Classifier PowerObject

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [Classifier C]

namespace Classifier

def meet : (Ω : C) ⊗ (Ω : C) ⟶ (Ω : C) := χ_ (t_ ⊗ t_)

abbrev meet_hom₁ {X : C} (χ₀ χ₁ : X ⟶ Ω) : X ⟶ Ω := lift χ₀ χ₁ ≫ meet

notation χ₀ " ∧_C₁ " χ₁ => meet_hom₁ χ₀ χ₁

abbrev meet_hom₂ {X Y : C} (χ₀ : X ⟶ Ω) (χ₁ : Y ⟶ Ω) : X ⊗ Y ⟶ Ω := (χ₀ ⊗ χ₁) ≫ meet

notation χ₀ " ∧_C₂ " χ₁ => meet_hom₂ χ₀ χ₁

variable [HasPullbacks C]

lemma meet_pullback {X S₀ S₁: C} (s₀ : S₀ ⟶ X) (s₁ : S₁ ⟶ X) [Mono s₀] [Mono s₁] : ((χ_ s₀) ∧_C₁ (χ_ s₁)) = χ_ (pullback.fst s₀ s₁ ≫ s₀) := by {
  apply uniq
  have pbR := isPullback (t_ ⊗ t_ : (⊤_ ⊗ ⊤_ : C) ⟶ (Ω ⊗ Ω))
  change IsPullback _ _ meet _ at pbR
  have pbM := isPullbackOfTensor (isPullback s₀) (isPullback s₁)
  have pbL := (isPullback_Tensor_Fst_of_isPullback (of_hasPullback s₀ s₁)).flip
  have pb := paste_vert pbL (paste_vert pbM pbR)
  rw [toUnit_unique (_ ≫ _ ≫ _) (toUnit _), ← assoc, lift_map] at pb; simp at pb
  assumption
}
