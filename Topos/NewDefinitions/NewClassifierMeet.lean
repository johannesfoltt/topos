import Topos.NewDefinitions.NewPowerOperations

open CategoryTheory Category Limits Functor IsPullback MonoidalCategory CartesianMonoidalCategory Classifier PowerObject

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [Classifier C]

namespace Classifier

def meet : (Ω : C) ⊗ (Ω : C) ⟶ (Ω : C) := χ_ (t_ ⊗ t_)

variable (C)

abbrev meet_char_pullback : IsPullback ((t_ : (𝟙_ C) ⟶ Ω) ⊗ t_) (ChosenTerminalObject.from_ _) (meet) (t_) := isPullback ((t_ : (𝟙_ C) ⟶ Ω) ⊗ t_)

variable {C}

instance : SymmetricCategory C := toSymmetricCategory

lemma meet_braid :
  (β_ Ω Ω).hom ≫ meet = (meet : ((Ω : C) ⊗ (Ω : C)) ⟶ (Ω : C)) := by {
    apply Classifier.uniq
    have pbL := isPullback_braiding (t_ : (𝟙_ C) ⟶ Ω) t_
    have pbR := meet_char_pullback C
    have pb := paste_vert pbL pbR
    rw [ChosenTerminalObject.hom_ext (_ ≫ _) (ChosenTerminalObject.from_ ((⊤_ ⊗ ⊤_) : C))] at pb
    exact pb
  }

abbrev meet_hom₁ {X : C} (χ₀ χ₁ : X ⟶ Ω) : X ⟶ Ω := lift χ₀ χ₁ ≫ meet

notation χ₀ " ∧_C₁ " χ₁ => meet_hom₁ χ₀ χ₁

abbrev meet_hom₂ {X Y : C} (χ₀ : X ⟶ Ω) (χ₁ : Y ⟶ Ω) : X ⊗ Y ⟶ Ω := (χ₀ ⊗ χ₁) ≫ meet

notation χ₀ " ∧_C₂ " χ₁ => meet_hom₂ χ₀ χ₁

lemma meet_symm₁ {X : C} (χ₀ χ₁ : X ⟶ Ω) : (χ₀ ∧_C₁ χ₁) = (χ₁ ∧_C₁ χ₀) := by {
  nth_rw 1 [meet_hom₁, ← meet_braid]
  simp
}

abbrev meet_symm₂ {X Y : C} (χ₀ : X ⟶ Ω) (χ₁ : Y ⟶ Ω) : (β_ X Y).hom ≫ (χ₁ ∧_C₂ χ₀) = (χ₀ ∧_C₂ χ₁):= by {
  nth_rw 1 [meet_hom₂, ← meet_braid]
  slice_lhs 1 3 => {
    rw [BraidedCategory.braiding_naturality]
  }
  simp
}

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

lemma meet_comp {X S₀ S₁ : C} (s₀ : S₀ ⟶ S₁) (s₁ : S₁ ⟶ X) [Mono s₀] [Mono s₁] : ((χ_ (s₀ ≫ s₁)) ∧_C₁ (χ_ s₁)) = χ_ (s₀ ≫ s₁) := by {
  rw [meet_pullback]
  have pb₀ := isPullback_comp_mono s₀ s₁
  have pb₁ := isPullback (pullback.fst (s₀ ≫ s₁) s₁ ≫ s₀ ≫ s₁)
  apply uniq
  apply pb₁.of_iso (pb₀.isoPullback).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp; exact pullback.condition
  · simp
  · simp
  · simp
}

end Classifier

namespace PowerObject

def intersection (X : C) [PowerObject X] : (pow X) ⊗ (pow X) ⟶ pow X := PowOperation Classifier.meet X

abbrev intersection_hom₁ {X Y : C} [PowerObject X] (f₀ f₁ : Y ⟶ pow X) : Y ⟶ pow X := lift f₀ f₁ ≫ intersection X

notation f₀ " ∧_P₁ " f₁ => intersection_hom₁ f₀ f₁

abbrev intersection_hom₂ {X Y Z: C} [PowerObject X] (f₀ : Y ⟶ pow X) (f₁ : Z ⟶ pow X) : Y ⊗ Z ⟶ pow X := (f₀ ⊗ f₁) ≫ intersection X

notation f₀ " ∧_P₂ " f₁ => intersection_hom₂ f₀ f₁

lemma meet_transpose {X Y : C} [PowerObject X] (f₀ f₁ : X ⊗ Y ⟶ Ω) : (f₀ ∧_C₁ f₁)^ = (f₀^ ∧_P₁ f₁^) := PowOperation_transpose_ClassifierOperation Classifier.meet f₀ f₁

lemma meet_transposeInv {X Y : C} [PowerObject X] (f₀ f₁ : Y ⟶ pow X) : (f₀ ∧_P₁ f₁)^ = (f₀^ ∧_C₁ f₁^) := PowOperation_transposeInv_ClassifierOperation Classifier.meet f₀ f₁

lemma meet_name {X : C} [PowerObject X] (χ₀ χ₁ : X ⟶ Ω) : ⌜(χ₀ ∧_C₁ χ₁)⌝ = (⌜χ₀⌝ ∧_P₁ ⌜χ₁⌝) := by {
  unfold name
  rw [← meet_transpose ((fst _ _) ≫ χ₀) ((fst _ _) ≫ χ₁), comp_lift_assoc]
}

end PowerObject
