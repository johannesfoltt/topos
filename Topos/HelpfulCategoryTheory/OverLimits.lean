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

variable {P Y₀ Y₁ Z : Over X} {fst : P ⟶ Y₀} {snd : P ⟶ Y₁} {f : Y₀ ⟶ Z} {g : Y₁ ⟶ Z}

lemma comm_iff_comm_left : fst.left ≫ f.left = snd.left ≫ g.left ↔ fst ≫ f = snd ≫ g := by rw [OverMorphism.ext_iff, comp_left, comp_left]

def PullbackCone_left_ofPullbackCone (s : PullbackCone f g) : PullbackCone f.left g.left := PullbackCone.mk s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition)

def isLimit_PullbackCone_of_isLimit_PullbackCone_left {w : fst.left ≫ f.left = snd.left ≫ g.left} (hL : IsLimit (PullbackCone.mk fst.left snd.left w)) : IsLimit (PullbackCone.mk fst snd (comm_iff_comm_left.1 w)) := by {
  have lift_w (s : PullbackCone f g) : s.pt.hom = PullbackCone.IsLimit.lift hL s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition) ≫ P.hom := by {
    have help := PullbackCone.IsLimit.lift_fst hL s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition)
    simp at help
    rw  [← Over.w fst, ← Over.w s.fst, ← assoc, help]
  }
  let lift := fun (s : PullbackCone f g) ↦ homMk (PullbackCone.IsLimit.lift hL s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition))
  apply PullbackCone.IsLimit.mk _ lift
  · intro s
    rw [OverMorphism.ext_iff, comp_left]
    unfold lift
    simp
    have help := PullbackCone.IsLimit.lift_fst hL s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition)
    simp at help
    rw [help]
  · intro s
    rw [OverMorphism.ext_iff, comp_left]
    unfold lift
    simp
    have help := PullbackCone.IsLimit.lift_snd hL s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition)
    simp at help
    rw [help]
  · intros s m h_fst h_snd
    rw [OverMorphism.ext_iff]
    rw [OverMorphism.ext_iff, comp_left] at h_fst
    rw [OverMorphism.ext_iff, comp_left] at h_snd
    unfold lift
    simp
    apply PullbackCone.IsLimit.hom_ext hL
    · simp
      have help := PullbackCone.IsLimit.lift_fst hL s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition)
      simp at help
      rw [h_fst, help]
    · simp
      have help := PullbackCone.IsLimit.lift_snd hL s.fst.left s.snd.left (comm_iff_comm_left.2 s.condition)
      simp at help
      rw [h_snd, help]

}

lemma isPullback_of_isPullback_left (hp: IsPullback fst.left snd.left f.left g.left) : IsPullback fst snd f g where
  w := comm_iff_comm_left.1 hp.w
  isLimit' := ⟨isLimit_PullbackCone_of_isLimit_PullbackCone_left hp.isLimit'.some⟩
