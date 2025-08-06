import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.NewDefinitions.NewClassifierMeet
import Topos.NewDefinitions.NewTopos
import Topos.HelpfulCategoryTheory.OverLimits
import Topos.HelpfulCategoryTheory.CartesianMonoidalCategoryAdditions
import Topos.HelpfulCategoryTheory.PullbackProd

namespace CategoryTheory

open Category Limits Over MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier PowerObject ChosenPowerObjects Topos

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
      apply Classifier.uniq
      have hχ' := isPullback_iff_isPullback_left.1 hχ
      simp at hχ'
      exact classifierOver.uniq_isPullback m χ hχ'
    · simp
      exact Over.w χ
  }


variable [ChosenPowerObjects C] [HasFiniteLimits C] (A : Over X)

abbrev powObj_t : (pow A.left) ⊗ X ⟶ pow A.left := (𝟙 (pow A.left) ∧_P₂ (singleton X ≫ inverseImage A.hom))

abbrev powObj_eq := equalizer.ι (fst _ _) (powObj_t A)

abbrev powObj : Over X := mk ((powObj_eq A) ≫ snd _ _)

abbrev powObj_in_hom : (A ⊗ powObj A).left ⟶ (Ω ⊗ X) := lift ((pullback_subObj A.hom ((powObj_eq A) ≫ (snd _ _))) ≫ ((𝟙 A.left) ⊗ (powObj_eq A) ≫ (fst _ _)) ≫ in_) (A ⊗ powObj A).hom

lemma powObj_in_w : (powObj_in_hom A) ≫ (Ω : Over X).hom = (A ⊗ powObj A).hom := by {
  change _ ≫ (snd Ω X) = _
  simp
}

abbrev powObj_in_ : (A ⊗ powObj A) ⟶ Ω := homMk (powObj_in_hom A) (powObj_in_w A)

variable {B : Over X} (f : A ⊗ B ⟶ Ω)

abbrev powObj_transpose_subObj : pullback (f.left ≫ fst _ _) t_ ⟶ A.left ⊗ B.left :=
  (pullback.fst (f.left ≫ fst _ _) (t_)) ≫ (pullback_subObj A.hom B.hom)


omit [HasFiniteLimits C] in
lemma powObj_transpose_subObj_meet_condition : ((χ_ (powObj_transpose_subObj A f)) ∧_C₁ (B.hom ≫ (singleton X) ≫ (inverseImage A.hom))^) = χ_ (powObj_transpose_subObj A f) := by {
  have help : singleton X = singleton ((Functor.fromPUnit X).obj A.right) := rfl
  change (χ_ (powObj_transpose_subObj A f) ∧_C₁ ((B.hom ≫ singleton X ≫ inverseImage A.hom)^ : (𝟭 C).obj A.left ⊗ (𝟭 C).obj B.left ⟶ Ω)) = χ_ (powObj_transpose_subObj A f)
  rw [help, pullback_char A.hom B.hom]
  exact meet_comp (pullback.fst (f.left ≫ fst _ _) t_) (lift (pullback.fst A.hom B.hom) (pullback.snd A.hom B.hom))
}

omit [HasFiniteLimits C] in
lemma powObj_transpose_equalizer_condition : (lift ((χ_ (powObj_transpose_subObj A f))^) B.hom) ≫ (fst _ _) = (lift ((χ_ (powObj_transpose_subObj A f))^) B.hom) ≫ powObj_t A := by {
  slice_lhs 1 3 => {
    rw [lift_fst, ← powObj_transpose_subObj_meet_condition, meet_transpose, transpose_right_inv]
    unfold intersection_hom₁
    rw [← comp_id ((χ_ ( powObj_transpose_subObj A f))^), ← lift_map]
  }
  simp
}

abbrev powObj_transpose : B ⟶ powObj A :=
  homMk (equalizer.lift (lift ((χ_ (powObj_transpose_subObj A f))^) B.hom) (powObj_transpose_equalizer_condition A f))


instance powerObject : PowerObject A where
  pow := powObj A
  in_ := powObj_in_ A
  transpose {B : Over X} (f : A ⊗ B ⟶ Ω) := powObj_transpose A f
  comm := by {
    intros B f
    rw [OverMorphism.ext_iff, comp_left, tensorHom_left, pullback.map]
    simp_rw [id_left, comp_id]
    rw [powObj_transpose]
    simp_rw [homMk_left]
    rw [powObj_in_hom, comp_lift]
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, pullback_subObj, ← assoc, comp_lift, ← assoc, lift_map]
      simp
      nth_rewrite 1 [← comp_id (pullback.fst A.hom B.hom)]
      rw [← lift_map, ← pullback_subObj, assoc]
      change _ ≫ (𝟙 A.left ⊗ _) ≫ in_ = _
      rw [← transposeInv, transpose_left_inv]
      simp_rw [← comp_lift]
      change _ ≫ χ_ (_ ≫ (pullback_subObj A.hom B.hom)) = _
      rw [comp_char, ← pred_eq_char_of_pullback]
    · change _ = f.left ≫ (Ω : Over X).hom
      rw [Over.w f]
      simp
  }
  uniq := by {
    intros Y f hat' h
    rw [OverMorphism.ext_iff, powObj_transpose, homMk_left _ _]
    apply equalizer.hom_ext
    rw [equalizer.lift_ι]
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, assoc, equalizer.condition]
      change _ = _ ≫ A.powObj_eq ≫ (𝟙 (pow A.left) ∧_P₂ (singleton X ≫ inverseImage A.hom))
      apply PowerObject.uniq
      unfold intersection_hom₂
      rw [← lift_comp_fst_snd A.powObj_eq]
      sorry
      /-
      rw [lift_fst, assoc, ← powObj_transpose_subObj_meet_condition A f]
      have help := pullback_char A.hom Y.hom
      simp at help
      rw [help, meet_pullback]
      unfold powObj_transpose_subObj
      -/
      /-
      rw [lift_fst, assoc, ← powObj_transpose_subObj_meet_condition A f, meet_transpose, transpose_right_inv]
      unfold intersection_hom₁
      rw [← comp_id (χ_ (A.powObj_transpose_subObj f)^), ← lift_map, assoc, ← intersection_hom₂]
      change (lift _ _) ≫ (powObj_t A) = _
    · rw [lift_snd, ← Over.w hat']
      simp
      -/
  }
