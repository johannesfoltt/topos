import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.NewDefinitions.NewTopos
import Topos.HelpfulCategoryTheory.PullbackProd
import Topos.HelpfulCategoryTheory.IsEqualizer
import Topos.HelpfulCategoryTheory.PreservesColimitOfIsReflexivePairOfIsCoequalizer
import Topos.HelpfulCategoryTheory.Images

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier PowerObject ChosenPowerObjects Functor

namespace Topos

universe u v
variable {C}
variable [Category.{v, u} C] [Topos C]

noncomputable section

namespace DirectImage

variable {B B' : C} (k : B' ⟶ B) [Mono k]

@[simp]
abbrev e := χ_ ((pullback.fst (in_) (t_)) ≫ (k ⊗ (𝟙 _)))

def directImage : pow B' ⟶ pow B := (e k)^

lemma directImage_id {B : C} : directImage (𝟙 B) = 𝟙 (pow B) := by {
  unfold directImage
  simp
  have h : in_ = χ_ (pullback.fst (in_ : B ⊗ _ ⟶ _) (t_)) := by {
    apply Classifier.uniq
    rw [from_eq_toUnit, toUnit_unique (toUnit _) (pullback.snd in_ t_)]
    exact IsPullback.of_hasPullback (in_ : B ⊗ _ ⟶ _) (t_)
  }
  rw [← h]
  apply PowerObject.uniq
  simp
}

variable {S : C} (m : S ⟶ B') [Mono m]

lemma wDef_comm' : (m ⊗ (𝟙 _)) ≫ ((𝟙 _) ⊗ (name (χ_ m))) ≫ in_ = toUnit _ ≫ t_ := by
  rw [Predicate.NameDef, tensorHom_fst_assoc]
  have h : toUnit (S ⊗ 𝟙_ C) = fst _ _ ≫ toUnit S := CartesianMonoidalCategory.toUnit_unique_iff.mpr trivial
  rw [h, assoc, Classifier.comm]
  simp

lemma wDef_comm : (m ⊗ (name (χ_ m))) ≫ in_ = toUnit _ ≫ t_ := by
  -- for some reason there is an issue rewriting m = m ≫ 𝟙 _ ??
  -- TODO: should be able to wrestle this lemma's statement into the previous lemma's, merging the two
  have h := wDef_comm' m
  rw [tensor_id_comp_id_tensor_assoc] at h
  assumption

def w := pullback.lift (w := wDef_comm m)

lemma transposeOfMapDirectImage {X Y Z: C} (n : X ⟶ Y) [Mono n] (g : Z ⟶ pow X) : (g ≫ directImage n)^ = ((𝟙 Y) ⊗ g) ≫ (e n) := by
  calc ((𝟙 Y) ⊗ (g ≫ directImage n)) ≫ in_ = ((𝟙 Y) ⊗ g) ≫ ((𝟙 Y) ⊗ (directImage n)) ≫ in_ := by rw [id_tensor_comp_assoc]
  _= ((𝟙 Y) ⊗ g) ≫ ((e n)^)^ := rfl
  _= ((𝟙 Y) ⊗ g) ≫ (e n) := by rw [transpose_left_inv]

lemma directImage_NameChar_factors : name (χ_ m) ≫ directImage k = name (χ_ (m ≫ k)) := by
  symm
  apply PowerObject.uniq
  rw [prodCompClassEqClassOfComp]
  apply Classifier.uniq
  have pbU := isPullback (m ⊗ (𝟙 (𝟙_ C)))
  rw [← χ_, ← transpose_left_inv (χ_ (m ⊗ (𝟙 (𝟙_ C)))), ← prodCompClassEqClassOfComp, ← name] at pbU
  unfold transposeInv at pbU
  have pbUR := IsPullback.of_hasPullback (in_ : B' ⊗ _ ⟶ _) (t_)
  have pbUL := IsPullback.of_bot' pbU pbUR
  have pbR := isPullback ((pullback.fst in_ t_ ) ≫ (k ⊗ (𝟙 _)))
  have pbBL := IsPullback.isPullbackOfTensor (IsPullback.id_vert k) (IsPullback.id_horiz ⌜χ_ m⌝)
  have pbL := IsPullback.paste_horiz pbUL pbBL
  have pb := IsPullback.paste_vert pbL pbR
  rw [← ChosenTerminalObject.hom_ext (from_ (S ⊗ (𝟙_ C ))) (_ ≫ _), ← comp_tensor_id, ← χ_, ← e, ← transposeOfMapDirectImage] at pb
  exact pb

variable {S' : C}

lemma transposeOfDirectImageInverseImage (k : B' ⟶ B) [Mono k] (g : S ⟶ B) : (directImage k ≫ inverseImage g)^ = (g ⊗ (𝟙 _)) ≫ (e k) := by {
    calc ((𝟙 S) ⊗ (directImage k ≫ inverseImage g)) ≫ in_ = ((𝟙 S) ⊗ (directImage k)) ≫ ((𝟙 S) ⊗ (inverseImage g)) ≫ in_ := id_tensor_comp_assoc (directImage k) (inverseImage g) in_
    _ = ((𝟙 S) ⊗ (directImage k)) ≫ (g ⊗ (𝟙 _)) ≫ in_ := by rw [inverseImage_comm]
    _ = (g ⊗ (𝟙 _)) ≫ ((𝟙 _) ⊗ (directImage k)) ≫ in_ := by rw [id_tensor_comp_tensor_id_assoc, tensor_id_comp_id_tensor_assoc]
    _ = (g ⊗ (𝟙 _)) ≫ e k := by {rw [← transpose_left_inv (e k)]; congr}
}

variable {k}

theorem BeckChevalley_for_exists {g : S ⟶ B} {g' : S' ⟶ B'} {n : S' ⟶ S} (h_pullback : IsPullback g' n k g) : letI _: Mono n := PullbackCone.mono_snd_of_is_pullback_of_mono (IsPullback.isLimit h_pullback)
inverseImage g' ≫ directImage n = directImage k ≫ inverseImage g := by {
  let mono_n : Mono n := PullbackCone.mono_snd_of_is_pullback_of_mono (IsPullback.isLimit h_pullback)
  rw [← transpose_right_inv (inverseImage g' ≫ directImage n), ← transpose_right_inv (directImage k ≫ inverseImage g)]
  apply congrArg transpose
  have pbR₀ := isPullback ((pullback.fst in_ t_) ≫ (k ⊗ (𝟙 _)))
  have pbR₁ := isPullback ((pullback.fst in_ t_) ≫ (n ⊗ (𝟙 _)))
  have pbBL₀ := IsPullback.isPullbackOfTensor (IsPullback.flip h_pullback) (IsPullback.id_vert (𝟙 (pow B')))
  have pbBL₁ := IsPullback.isPullbackOfTensor (IsPullback.id_vert n) (IsPullback.id_horiz (inverseImage g'))
  have pbUR₀ := IsPullback.of_hasPullback (in_ : B' ⊗ _ ⟶ _) t_
  have pbUR₁ := IsPullback.of_hasPullback (in_ : S' ⊗ _ ⟶ _) t_
  have pbU₀ := IsPullback.of_hasPullback ((g' ⊗ (𝟙 (pow B'))) ≫ in_) t_
  have pbU₁ := pbU₀
  simp_rw [← inverseImage_comm g'] at pbU₁
  have pbUL₀ := IsPullback.of_bot' pbU₀ pbUR₀
  have pbUL₁ := IsPullback.of_bot' pbU₁ pbUR₁
  have pbL₀ := IsPullback.paste_horiz pbUL₀ pbBL₀
  have pbL₁ := IsPullback.paste_horiz pbUL₁ pbBL₁
  have pb₀ := IsPullback.paste_vert pbL₀ pbR₀
  have pb₁ := IsPullback.paste_vert pbL₁ pbR₁
  rw [toUnit_unique (_ ≫ _) (toUnit (pullback ((g' ⊗ (𝟙 (pow B'))) ≫ in_) t_)), ← χ_, ← e] at pb₀
  rw [toUnit_unique (_ ≫ _) (toUnit (pullback ((g' ⊗ (𝟙 (pow B'))) ≫ in_) t_)), ← χ_, ← e] at pb₁
  rw [transposeOfDirectImageInverseImage, transposeOfMapDirectImage, Classifier.uniq _ _ pb₀, Classifier.uniq _ _ pb₁]
}

variable (k)

theorem inverseImageOfDirectImageIsidentity : directImage k ≫ inverseImage k = 𝟙 _ := by
  rw [← BeckChevalley_for_exists (IsKernelPair.id_of_mono k), inverseImage_id, directImage_id, comp_id]

end DirectImage

instance PowRightAdj : IsRightAdjoint (powFunctor C) where
  exists_leftAdjoint := by
    apply Exists.intro (powFunctorOp C)
    exact ⟨powSelfAdj C⟩

instance PowFaithful : Functor.Faithful (powFunctor C) where
  map_injective := by
    intro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨g⟩ h
    change (inverseImage f = inverseImage g) at h
    congr
    have h' := congrArg (fun k ↦ transposeInv (singleton X ≫ k)) h
    dsimp only [transposeInv] at h'
    rw [id_tensor_comp, id_tensor_comp, assoc, assoc, inverseImage_comm, inverseImage_comm, ← assoc, ← tensor_comp, ← assoc, ← tensor_comp, id_comp, comp_id, id_comp, ←comp_id f, ←id_comp (singleton _), ←comp_id g, tensor_comp, tensor_comp, assoc, assoc, ChosenPowerObjects.singleton, PowerObject.comm] at h'
    have comm : (f ≫ toUnit _) ≫ t_ = (lift (𝟙 _) f) ≫ (f ⊗ (𝟙 _)) ≫ Predicate.eq _ := by {
      simp
      rw [Predicate.lift_eq]
      rfl
    }
    rw [comp_toUnit, h', ←assoc, lift_map, id_comp, comp_id] at comm
    exact (Predicate.eq_of_lift_eq comm.symm).symm


instance hasCoreflexiveEqualizers : HasCoreflexiveEqualizers C :=
  hasCoreflexiveEqualizers_of_hasEqualizers C

instance : HasCoequalizers Cᵒᵖ := hasCoequalizers_opposite

instance : HasReflexiveCoequalizers Cᵒᵖ := hasReflexiveCoequalizers_of_hasCoequalizers Cᵒᵖ

instance PowReflectsIsomorphisms : Functor.ReflectsIsomorphisms (powFunctor C) := reflectsIsomorphismsOp (F := powFunctor C)

instance PowPreservesIsCoequalizerOfReflexivePair : Monad.PreservesCoequalizerOfIsReflexivePair (powFunctor C) where
  out := by
    intro ⟨A⟩ ⟨B⟩ ⟨f⟩ ⟨g⟩ h₀
    change (B ⟶ A) at f; change (B ⟶ A) at g
    have h₁ := h₀.common_section'
    let s := h₁.choose
    have hs₁ := congrArg (fun k ↦ k.unop) h₁.choose_spec.1
    have hs₂ := congrArg (fun k ↦ k.unop) h₁.choose_spec.2
    change (f ≫ s.unop = 𝟙 _) at hs₁
    change (g ≫ s.unop = 𝟙 _) at hs₂
    refine PreservesIsCoequalizer.mk ?_
    intro ⟨P⟩ ⟨π⟩ h₂
    change (P ⟶ B) at π
    change IsCoequalizer (inverseImage f) (inverseImage g) (inverseImage π)
    have h₂' := IsPushout.unop (IsCoequalizer.IsPushoutOfReflexivePairAndIsCoequalizer h₀ h₂)
    simp at h₂'
    have : Mono g := SplitMono.mono (SplitMono.mk s.unop hs₂)
    have : Epi (π.op) := IsCoequalizer.epi_π h₂
    have hπ : Mono π := unop_mono_of_epi π.op
    exact IsSplitCoequalizer.IsCoequalizer {
      rightSection := DirectImage.directImage π
      leftSection := DirectImage.directImage g
      condition := by {
        change (powFunctor C).map f.op ≫ (powFunctor C).map π.op = (powFunctor C).map g.op ≫ (powFunctor C).map π.op
        simp_rw [← (powFunctor C).map_comp]
        refine (map_injective_iff (powFunctor C) (f.op ≫ π.op) (g.op ≫ π.op)).mpr ?_
        exact h₂.w
      }
      rightSection_π := DirectImage.inverseImageOfDirectImageIsidentity π
      leftSection_bottom := DirectImage.inverseImageOfDirectImageIsidentity g
      leftSection_top := Eq.symm (DirectImage.BeckChevalley_for_exists h₂')
    }

instance PowPreservesCoequalizersOfReflexivePair : Monad.PreservesColimitOfIsReflexivePair (powFunctor C) := Monad.PreservesColimitOfIsReflexivePairOfPreservesCoequalizer PowPreservesIsCoequalizerOfReflexivePair

instance powFunctorMonadic : MonadicRightAdjoint (powFunctor C) :=
  Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms (powSelfAdj C)

instance powFunctorComparison : (Monad.comparison (powSelfAdj C)).IsEquivalence := powFunctorMonadic.eqv

instance HasFiniteColimits : HasFiniteColimits C where
  out := by {
    intros J hJ F
    have hasLimitsOfShapeOpAlgebra : HasLimitsOfShape Jᵒᵖ (powSelfAdj C).toMonad.Algebra := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Adjunction.toMonad (powFunctorMonadic.adj)).forget
    have hasLimitsOfShapeOp : HasLimitsOfShape Jᵒᵖ Cᵒᵖ := (Adjunction.hasLimitsOfShape_of_equivalence (Monad.comparison (powSelfAdj C)))
    exact hasColimitsOfShape_of_hasLimitsOfShape_op
  }

#synth HasImages C
