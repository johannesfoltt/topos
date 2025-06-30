import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Tactic.ApplyFun
import Mathlib.CategoryTheory.Subobject.Basic
import Topos.Classifier
import Topos.Images
import Topos.PullbackProd
import Topos.PowerOperations

universe u v u₀ v₀

open CategoryTheory Category Limits Functor IsPullback Power HasClassifier

variable {C : Type u} [Category.{v} C] [HasTerminal C]
variable (classifier : Classifier C)

namespace CategoryTheory

noncomputable section

def Classifier.meet [CartesianMonoidalCategory C] : classifier.Ω ⨯ classifier.Ω ⟶ classifier.Ω :=
  classifier.char (prod.map (classifier.t) (classifier.t))

--def Classifier.false [HasInitial C] : ⊤_ C ⟶ classifier.Ω :=
  --classifier.char (initial.to (⊤_ C))

variable [HasClassifier C] [CartesianMonoidalCategory C]

namespace HasClassifier

abbrev meet : (Ω C) ⨯ (Ω C) ⟶ (Ω C) := Classifier.meet (HasClassifier.exists_classifier.some)

abbrev meet_hom₁ {X : C} (χ₀ χ₁ : X ⟶ Ω C) : X ⟶ Ω C := prod.lift χ₀ χ₁ ≫ meet

notation χ₀ "∧_C₁" χ₁ => meet_hom₁ χ₀ χ₁

abbrev meet_hom₂ {X Y : C} (χ₀ : X ⟶ Ω C) (χ₁ : Y ⟶ Ω C) : X ⨯ Y ⟶ Ω C := prod.map χ₀ χ₁ ≫ meet

notation χ₀ "∧_C₂" χ₁ => meet_hom₂  (χ₀) (χ₁)

variable [HasPullbacks C]

lemma meet_pullback {X S₀ S₁: C} (s₀ : S₀ ⟶ X) (s₁ : S₁ ⟶ X) [Mono s₀] [Mono s₁] : ((χ_ s₀) ∧_C₁ (χ_ s₁)) = χ_ (pullback.fst s₀ s₁ ≫ s₀) := by {
  apply unique
  have pbR := isPullback (prod.map (t C) (t C))
  change IsPullback _ _ meet _ at pbR
  have pbM := isPullbackOfProd (isPullback s₀) (isPullback s₁)
  have pbL := (isPullback_Prod_Fst_of_isPullback (of_hasPullback s₀ s₁)).flip
  have pb := paste_vert pbL (paste_vert pbM pbR)
  rw [terminal.hom_ext (prod.lift (pullback.fst s₀ s₁) (pullback.snd s₀ s₁) ≫
    prod.map (terminal.from S₀) (terminal.from S₁) ≫ terminal.from ((⊤_ C) ⨯ ⊤_ C)) (terminal.from _), ← assoc, prod.lift_map] at pb; simp at pb
  assumption
}

end HasClassifier

namespace Power

abbrev PowerObject.meet {X : C} (po : PowerObject X) : po.pow ⨯ po.pow ⟶ po.pow :=  PowerOperation HasClassifier.meet po

variable [HasPowerObjects C]

--possible choice : HasPowerObjects.PowerOperation HasClassifier.meet

abbrev meet (X : C) : (pow X) ⨯ (pow X) ⟶ pow X := (HasPowerObjects.has_power_object X).some.meet

abbrev meet_hom₁ {X Y : C} (f₀ f₁ : Y ⟶ pow X) : Y ⟶ pow X := prod.lift f₀ f₁ ≫ meet X

notation f₀ "∧_P₁" f₁ => meet_hom₁ f₀ f₁

abbrev meet_hom₂ {X Y Z: C} (f₀ : Y ⟶ pow X) (f₁ : Z ⟶ pow X) : Y ⨯ Z ⟶ pow X := prod.map f₀ f₁ ≫ meet X

notation f₀ "∧_P₂" f₁ => meet_hom₂ f₀ f₁

lemma meet_transpose {X Y : C} (f₀ f₁ : X ⨯ Y ⟶ Ω C) : (f₀ ∧_C₁ f₁)^ = (f₀^ ∧_P₁ f₁^) := HasPowerObjects.PowerOperation_transpose_ClassifierOperation HasClassifier.meet f₀ f₁

variable [IsTopos C] --unneccessary, pls change

lemma meet_name {X : C} (χ₀ χ₁ : X ⟶ Ω C) : ⌈(χ₀ ∧_C₁ χ₁)⌉ = (⌈χ₀⌉ ∧_P₁ ⌈χ₁⌉) := by {
  unfold Topos.name
  rw [← meet_transpose ((prod.fst) ≫ χ₀) ((prod.fst) ≫ χ₁), prod.comp_lift_assoc]
}
