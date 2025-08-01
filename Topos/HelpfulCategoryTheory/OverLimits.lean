import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Topos.HelpfulCategoryTheory.IsEqualizer

namespace CategoryTheory

open Category Limits Over

universe u v

noncomputable section

namespace Over

variable {C : Type u} [Category.{v} C] {X : C}

variable {A B : Over X} (f g : A ⟶ B) [HasEqualizer f.left g.left]

abbrev equalizerOver : Over X := Over.mk ((equalizer.ι f.left g.left) ≫ A.hom)

abbrev equalizerOver.ι : (equalizerOver f g) ⟶ A := Over.homMk (equalizer.ι f.left g.left)

lemma equalizerOver_IsEqualizer : IsEqualizer (equalizerOver.ι f g) f g where
  w := OverMorphism.ext (equalizer.condition f.left g.left)
  isLimit' := by {
    apply Nonempty.intro
    apply Fork.IsLimit.ofExistsUnique
    intro s
    have w' : s.ι.left ≫ f.left = s.ι.left ≫ g.left := by {
      rw [← comp_left, ← comp_left, ← OverMorphism.ext_iff]
      exact Fork.condition s
    }
    let l' := equalizer.lift s.ι.left w'
    simp at l'
    change s.pt.left ⟶ (equalizerOver f g).left at l'
    have w : l' ≫ (equalizerOver f g).hom = s.pt.hom := by {
      simp
      rw [← assoc, equalizer.lift_ι]
      simp
    }
    use homMk l'
    simp
    apply And.intro
    · refine OverMorphism.ext ?_
      rw [comp_left]
      exact equalizer.lift_ι s.ι.left w'
    · intros y hy
      refine OverMorphism.ext ?_
      rw [OverMorphism.ext_iff, comp_left] at hy; simp at hy
      apply equalizer.hom_ext
      rw [hy]; unfold l'; simp
  }


--Todo: Get HasEqualizer from IsEqualizer
instance hasEqualizer_of_HasEqualizer_left : HasEqualizer f g :=
  IsEqualizer.HasEqualizer_of_IsEqualizer (equalizerOver_IsEqualizer f g)

instance hasEqualizers_of_HasEqualizers [HasEqualizers C] : HasEqualizers (Over X) :=
  hasEqualizers_of_hasLimit_parallelPair (Over X)

lemma isPullback_of_isPullback_left {P Y₀ Y₁ Z : Over X} {fst : P ⟶ Y₀} {snd : P ⟶ Y₁} {f : Y₀ ⟶ Z} {g : Y₁ ⟶ Z} (hp: IsPullback fst.left snd.left f.left g.left) : IsPullback fst snd f g where
  w := by rw [OverMorphism.ext_iff, comp_left, comp_left, hp.w]
  isLimit' := by {
    sorry
  }
