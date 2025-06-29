import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Tactic.ApplyFun
import Mathlib.CategoryTheory.Subobject.Basic
import Topos.Classifier
import Topos.Images
import Topos.PullbackProd
import Topos.PowerOperations

universe u v u₀ v₀

open CategoryTheory Category Limits Functor IsPullback Power

variable {C : Type u} [Category.{v} C] [HasTerminal C]
variable (classifier : Classifier C)

namespace CategoryTheory

noncomputable section

def Classifier.meet [CartesianMonoidalCategory C] : classifier.Ω ⨯ classifier.Ω ⟶ classifier.Ω :=
  classifier.char (prod.map (classifier.t) (classifier.t))

--def Classifier.false [HasInitial C] : ⊤_ C ⟶ classifier.Ω :=
  --classifier.char (initial.to (⊤_ C))

namespace HasClassifier

variable [HasClassifier C] [CartesianMonoidalCategory C]

abbrev meet : (Ω C) ⨯ (Ω C) ⟶ (Ω C) := Classifier.meet (HasClassifier.exists_classifier.some)

variable [HasPullbacks C]

lemma meet_pullback {X S₀ S₁: C} (s₀ : S₀ ⟶ X) (s₁ : S₁ ⟶ X) [Mono s₀] [Mono s₁] : prod.lift (χ_ s₀) (χ_ s₁) ≫ meet = χ_ (pullback.fst s₀ s₁ ≫ s₀) := by {
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
