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

lemma lift_of_pullbackCone_left_w_snd (s : PullbackCone f.left g.left) : s.snd ≫ Y₁.hom = s.fst ≫ Y₀.hom := by {
  rw [← Over.w f, ← Over.w g, ← assoc, ← assoc, s.condition]
}

def isLimit_PullbackCone_left_of_isLimit_PullbackCone {w : fst ≫ f = snd ≫ g} (hL : IsLimit (PullbackCone.mk fst snd w)) : IsLimit (PullbackCone.mk fst.left snd.left (comm_iff_comm_left.2 w)) := by {
  let lift := fun (s : PullbackCone f.left g.left) ↦ (PullbackCone.IsLimit.lift hL (homMk s.fst : mk (s.fst ≫ Y₀.hom) ⟶ Y₀) (homMk s.snd (lift_of_pullbackCone_left_w_snd s): mk (s.fst ≫ Y₀.hom) ⟶ Y₁) (comm_iff_comm_left.1 s.condition)).left
  apply PullbackCone.IsLimit.mk _ lift
  · intro s
    unfold lift
    have help := PullbackCone.IsLimit.lift_fst hL (homMk s.fst : mk (s.fst ≫ Y₀.hom) ⟶ Y₀) (homMk s.snd (lift_of_pullbackCone_left_w_snd s): mk (s.fst ≫ Y₀.hom) ⟶ Y₁) (comm_iff_comm_left.1 s.condition)
    simp at help
    rw [← comp_left, help]
    simp
  · intro s
    unfold lift
    have help := PullbackCone.IsLimit.lift_snd hL (homMk s.fst : mk (s.fst ≫ Y₀.hom) ⟶ Y₀) (homMk s.snd (lift_of_pullbackCone_left_w_snd s): mk (s.fst ≫ Y₀.hom) ⟶ Y₁) (comm_iff_comm_left.1 s.condition)
    simp at help
    rw [← comp_left, help]
    simp
  · intros s l h_fst h_snd
    unfold lift
    have h_w : l ≫ P.hom = s.fst ≫ Y₀.hom := by rw [← Over.w fst, ← assoc, h_fst]
    let l' : mk (s.fst ≫ Y₀.hom) ⟶ P := homMk l
    change l'.left = _
    rw [← OverMorphism.ext_iff]
    apply PullbackCone.IsLimit.hom_ext hL
    · simp
      rw [OverMorphism.ext_iff, comp_left]
      change l ≫ _ = _
      have help := PullbackCone.IsLimit.lift_fst hL (homMk s.fst : mk (s.fst ≫ Y₀.hom) ⟶ Y₀) (homMk s.snd (lift_of_pullbackCone_left_w_snd s): mk (s.fst ≫ Y₀.hom) ⟶ Y₁) (comm_iff_comm_left.1 s.condition)
      simp at help
      rw [h_fst, help]
      simp
    · simp
      rw [OverMorphism.ext_iff, comp_left]
      change l ≫ _ = _
      have help := PullbackCone.IsLimit.lift_snd hL (homMk s.fst : mk (s.fst ≫ Y₀.hom) ⟶ Y₀) (homMk s.snd (lift_of_pullbackCone_left_w_snd s): mk (s.fst ≫ Y₀.hom) ⟶ Y₁) (comm_iff_comm_left.1 s.condition)
      simp at help
      rw [h_snd, help]
      simp
}

theorem isPullback_iff_isPullback_left : IsPullback fst snd f g ↔ IsPullback fst.left snd.left f.left g.left := Iff.intro
  (fun (h) ↦ ⟨⟨comm_iff_comm_left.2 h.w⟩, ⟨isLimit_PullbackCone_left_of_isLimit_PullbackCone h.isLimit'.some⟩⟩)
  (fun (h) ↦ ⟨⟨comm_iff_comm_left.1 h.w⟩, ⟨isLimit_PullbackCone_of_isLimit_PullbackCone_left h.isLimit'.some⟩⟩)
