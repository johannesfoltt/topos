import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.NewDefinitions.NewClassifier
import Topos.HelpfulCategoryTheory.OverLimits

namespace CategoryTheory

open Category Limits Over MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier

universe u v

namespace Over

noncomputable section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C] [Classifier C] {X : C}

instance : CartesianMonoidalCategory (Over X) := cartesianMonoidalCategory X


omit [HasPullbacks C] in
lemma classifierOver.isPullback_left {S A : Over X} (m : S ⟶ A) [Mono m] : IsPullback m.left S.hom (lift (χ_ m.left) A.hom) (lift (Predicate.true_ X) (𝟙 X)) where
  w := by {
    rw [comp_lift, comp_lift]
    apply CartesianMonoidalCategory.hom_ext
    · simp
      unfold Predicate.true_
      rw [← assoc, comp_from, Classifier.comm]
    · simp
  }
  isLimit' := by {
    apply Nonempty.intro
    have comm (s : PullbackCone (lift (χ_ m.left) A.hom) (lift (Predicate.true_ X) (𝟙 X))) : s.fst ≫ (char m.left) = (s.snd ≫ from_ X) ≫ t_ := by {
      rw [assoc, ← Predicate.true_]
      have help := (CartesianMonoidalCategory.hom_ext_iff.1 s.condition).1
      simp at help
      assumption
    }
    apply PullbackCone.IsLimit.mk _ (fun s ↦ ((isPullback m.left).lift _ _ (comm s)))
    · intro s
      simp
    · intro s
      nth_rewrite 2 [← comp_id s.snd]
      convert_to  _ = s.snd ≫ (lift (Predicate.true_ X) (𝟙 X) ≫ snd Ω X)
      · exact congrArg (CategoryStruct.comp s.snd) (id (Eq.symm (lift_snd (Predicate.true_ X) (𝟙 X))))
      rw [← assoc, ← s.condition]
      simp
      rw [← Over.w m, ← assoc, (isPullback m.left).lift_fst s.fst (toUnit s.pt) _]
    · intros s l h_fst h_snd
      apply (isPullback m.left).hom_ext
      · aesop_cat
      · aesop_cat
  }

omit [HasPullbacks C] in
lemma classifierOver.uniq_isPullback {S A : Over X} (m : S ⟶ A) [Mono m] (χ : A ⟶ mk (snd Ω X)) (hχ' : IsPullback m.left S.hom χ.left (lift (Predicate.true_ X) (𝟙 X))) : IsPullback m.left (from_ S.left) (χ.left ≫ fst Ω X) t_ where
  w := by rw [← assoc, hχ'.w, Predicate.true_]; simp
  isLimit' := by {
    apply Nonempty.intro
    have lift_w (s : PullbackCone (χ.left ≫ fst Ω X) t_) : s.fst ≫ χ.left = (s.fst ≫ A.hom) ≫ (lift (Predicate.true_ X) (𝟙 X)) := by {
      apply CartesianMonoidalCategory.hom_ext
      · simp
        rw [s.condition, Predicate.true_, ← assoc, ← assoc, ChosenTerminalObject.hom_ext s.snd _]
      · rw [← Over.w χ]
        simp
    }
    apply PullbackCone.IsLimit.mk _ (fun (s : PullbackCone (χ.left ≫ fst Ω X) t_) ↦ hχ'.lift _ _ (lift_w s))
    · intro s
      exact IsPullback.lift_fst hχ' s.fst (s.fst ≫ A.hom) (lift_w s)
    · intro s
      exact Eq.symm (ChosenTerminalObject.hom_ext s.snd (hχ'.lift s.fst (s.fst ≫ A.hom) (lift_w s) ≫ from_ S.left))
    · intros s l h_fst h_snd
      apply hχ'.hom_ext
      · simp
        assumption
      · simp
        rw [← h_fst, assoc, Over.w m]
  }

instance classifier : Classifier (Over X) where
  Ω := mk (snd Ω X)
  t_ := homMk (lift (Predicate.true_ X) (𝟙 X))
  char {S A : Over X} (m : S ⟶ A) [Mono m] := homMk (lift (χ_ m.left) (A.hom))
  isPullback {S A : Over X} (m : S ⟶ A) [Mono m] := by {
    apply isPullback_iff_isPullback_left.2
    simp
    exact classifierOver.isPullback_left m
  }
  uniq {S A : Over X} (m : S ⟶ A) [Mono m] (χ : A ⟶ mk (snd Ω X)) (hχ : IsPullback m (from_ S) χ (homMk (lift (Predicate.true_ X) (𝟙 X)))) := by {
    refine OverMorphism.ext ?_
    simp
    refine CartesianMonoidalCategory.hom_ext χ.left (lift (χ_ m.left) A.hom) ?_ ?_
    · simp
      apply uniq
      have hχ' := isPullback_iff_isPullback_left.1 hχ
      simp at hχ'
      exact classifierOver.uniq_isPullback m χ hχ'
    · simp
      exact Over.w χ
  }
