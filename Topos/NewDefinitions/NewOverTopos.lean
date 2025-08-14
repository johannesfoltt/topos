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

variable {A} {B : Over X} (f : A ⊗ B ⟶ Ω)

abbrev powObj_transpose_subObj : pullback (f.left ≫ fst _ _) t_ ⟶ A.left ⊗ B.left :=
  (pullback.fst (f.left ≫ fst _ _) (t_)) ≫ (pullback_subObj A.hom B.hom)


omit [HasFiniteLimits C] in
lemma powObj_transpose_subObj_meet_condition : ((χ_ (powObj_transpose_subObj f)) ∧_C₁ (B.hom ≫ (singleton X) ≫ (inverseImage A.hom))^) = χ_ (powObj_transpose_subObj f) := by {
  have help : singleton X = singleton ((Functor.fromPUnit X).obj A.right) := rfl
  change (χ_ (powObj_transpose_subObj f) ∧_C₁ ((B.hom ≫ singleton X ≫ inverseImage A.hom)^ : (𝟭 C).obj A.left ⊗ (𝟭 C).obj B.left ⟶ Ω)) = χ_ (powObj_transpose_subObj f)
  rw [help, pullback_char A.hom B.hom]
  exact meet_comp (pullback.fst (f.left ≫ fst _ _) t_) (lift (pullback.fst A.hom B.hom) (pullback.snd A.hom B.hom))
}

omit [HasFiniteLimits C] in
lemma powObj_transpose_equalizer_condition : (lift ((χ_ (powObj_transpose_subObj f))^) B.hom) ≫ (fst _ _) = (lift ((χ_ (powObj_transpose_subObj f))^) B.hom) ≫ powObj_t A := by {
  slice_lhs 1 3 => {
    rw [lift_fst, ← powObj_transpose_subObj_meet_condition, meet_transpose, transpose_right_inv]
    unfold intersection_hom₁
    rw [← comp_id ((χ_ ( powObj_transpose_subObj f))^), ← lift_map]
  }
  simp
}

abbrev powObj_transpose : B ⟶ powObj A :=
  homMk (equalizer.lift (lift ((χ_ (powObj_transpose_subObj f))^) B.hom) (powObj_transpose_equalizer_condition f))

abbrev powObj_transposeInv_left (f : B ⟶ powObj A) : (A ⊗ B).left ⟶ (Ω : Over X).left := (pullback_subObj A.hom B.hom) ≫ lift ((f.left ≫ powObj_eq A ≫ (fst (pow A.left) X))^) ((snd _ _) ≫ B.hom)

lemma powObj_transposeInv_w (f : B ⟶ powObj A) : (powObj_transposeInv_left f) ≫ (snd _ _) = (A ⊗ B).hom := by {
  rw [tensorObj_hom, assoc, lift_snd, pullback_subObj, ← assoc, lift_snd, pullback.condition]
}

abbrev powObj_transposeInv (f : B ⟶ powObj A) : (A ⊗ B) ⟶ (Ω : Over X) := homMk (powObj_transposeInv_left f) (powObj_transposeInv_w f)


abbrev powObj_in_ (A : Over X) : (A ⊗ powObj A) ⟶ Ω := powObj_transposeInv (𝟙 (powObj A))

lemma powObj_transpose_left_inv (f : A ⊗ B ⟶ Ω) : powObj_transposeInv (powObj_transpose f) = f := by {
  rw [powObj_transpose, powObj_transposeInv, OverMorphism.ext_iff]
  simp
  apply CartesianMonoidalCategory.hom_ext
  · simp
    simp_rw [← comp_lift]
    change _ ≫ χ_ (_ ≫ pullback_subObj A.hom B.hom) = _
    rw [comp_char, pred_eq_char_of_pullback]
  · simp
    rw [← pullback.condition, ← tensorObj_hom, ← Over.w f]
    rfl
}

lemma powObj_transpose_right_inv (f : B ⟶ powObj A) : powObj_transpose (powObj_transposeInv f) = f := by {
  rw [OverMorphism.ext_iff]
  simp
  apply equalizer.hom_ext
  rw [equalizer.lift_ι]
  apply CartesianMonoidalCategory.hom_ext
  · simp
    simp_rw [← comp_lift]
    change  (χ_ (pullback.fst (powObj_transposeInv_left f ≫ fst Ω X) t_ ≫ pullback_subObj A.hom B.hom))^ = _
    have h := Over.w f
    rw [mk_hom] at h
    slice_rhs 2 3 => {
      rw [equalizer.condition, ← powObj_eq]
      unfold powObj_t
      unfold intersection_hom₂
    }
    slice_rhs 1 3 => {
      rw [← assoc, ← lift_comp_fst_snd (f.left ≫ _)]
    }
    rw [lift_map, comp_id]
    slice_rhs 4 6 => {
      rw [h]
    }
    change _ = _ ∧_P₁ _
    slice_rhs 2 4 => {
      rw [← transpose_right_inv (_ ≫ _ ≫ _), pullback_char]
    }
    have eq : (powObj_transposeInv_left f ≫ fst Ω X) = (pullback_subObj A.hom B.hom) ≫ ((f.left ≫ powObj_eq A ≫ (fst (pow A.left) X))^) := by simp
    have help : pullback.fst (powObj_transposeInv_left f ≫ fst Ω X) t_ = (pullback.congrHom eq (rfl : t_ = t_)).hom ≫ (pullback.fst (pullback_subObj A.hom B.hom ≫ (f.left ≫ A.powObj_eq ≫ fst (pow A.left) X)^) t_) := by {
      rw [pullback.congrHom_hom, pullback.map]
      simp
    }
    simp_rw [help, assoc, char_iso_hom]
    apply PowerObject.uniq
    change transposeInv _ = _
    simp only [Functor.id_obj]
    rw [meet_transposeInv, transpose_left_inv]
    nth_rw 1 [← pred_eq_char_of_pullback ((f.left ≫ A.powObj_eq ≫ fst (pow A.left) X)^)]
    simp_rw [← pullbackRightPullbackFstIso_inv_fst ((f.left ≫ A.powObj_eq ≫ fst (pow A.left) X)^) t_ (pullback_subObj A.hom B.hom), assoc, char_iso_inv, ← meet_pullback]
    have w : (f.left ≫ A.powObj_eq) ≫ (mk (snd (pow A.left) X)).hom = B.hom := by {
      rw [← Over.w f]
      simp
    }
    rw [meet_symm₁]
  · simp
    rw [← Over.w f]
    simp
}

lemma powObj_transposeInv_naturality {B B' : Over X} (f : B ⟶ B') (g : B' ⟶ powObj A) : ((𝟙 A) ⊗ f) ≫ (powObj_transposeInv g) = powObj_transposeInv (f ≫ g) := by {
  rw [OverMorphism.ext_iff, comp_left, powObj_transposeInv, powObj_transposeInv, homMk_left _ _, homMk_left _ _, powObj_transposeInv_left, powObj_transposeInv_left, tensorHom_left, pullback.map]
  simp
  apply CartesianMonoidalCategory.hom_ext
  · simp
    rw [← assoc, comp_lift, pullback.lift_fst]
    slice_lhs 1 2 => {
      slice 1 2
      rw [pullback.lift_snd]
    }
    simp
  · simp
}

instance powerObject : PowerObject A where
  pow := powObj A
  in_ := powObj_in_ A
  transpose {B : Over X} (f : A ⊗ B ⟶ Ω) := powObj_transpose f
  comm {B : Over X} (f : A ⊗ B ⟶ Ω) := by {
    rw [powObj_transposeInv_naturality, comp_id, powObj_transpose_left_inv]
  }
  uniq {B : Over X} {f : A ⊗ B ⟶ Ω} {hat' : B ⟶ A.powObj} (h : (𝟙 A ⊗ hat') ≫ A.powObj_in_ = f) := by {
    rw [powObj_transposeInv_naturality, comp_id] at h
    rw [← h, powObj_transpose_right_inv]
  }
