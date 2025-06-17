/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.Basic
import Topos.PullbackProd
import Topos.IsEqualizer
import Topos.PreservesColimitOfIsReflexivePairOfIsCoequalizer

namespace CategoryTheory

open Category Limits HasClassifier Power Functor

namespace Topos

universe u v
variable {C}
variable [Category.{v, u} C] [CartesianMonoidalCategory C] [IsTopos C]

noncomputable section

-- TODO: prove that `powFunctor C` preserves colimits of reflexive pairs.

namespace BeckChevalley

/-
  In this section, we follow Mac Lane and Moerdijk in defining the direct image ∃ₖ : PB' ⟶ PB
  of a monomorphism k : B' ⟶ B, then show that ∃ₖ ≫ Pow_map k = 𝟙 PB'.
-/

variable {B B' : C} (k : B' ⟶ B) [Mono k]

#check transpose (χ_ ((pullback.fst (f := in_ B') (g := t C)) ≫ prod.map k (𝟙 _)))

@[simp]
abbrev e := χ_ ((pullback.fst (in_ B') (t C)) ≫ prod.map k (𝟙 _))

def directImage : pow B' ⟶ pow B :=
  transpose (e k)

lemma directImage_id {B : C} : directImage (𝟙 B) = 𝟙 (pow B) := by {
  unfold directImage
  simp
  have h : in_ B = χ_ (pullback.fst (in_ B) (t C)) := by {
    apply Classifier.uniq
    rw [terminal.hom_ext (terminal.from (pullback (in_ B) (t C))) (pullback.snd (in_ B) (t C))]
    exact IsPullback.of_hasPullback (in_ B) (t C)
  }
  rw [← h]
  apply @Power.unique
  simp
}

variable {S : C} (m : S ⟶ B') [Mono m]

lemma wDef_comm' : (prod.map m (𝟙 _)) ≫ (prod.map (𝟙 _) (name (χ_ m))) ≫ in_ B' = terminal.from _ ≫ t C := by
  rw [Predicate.NameDef, prod.map_fst_assoc]
  have h : terminal.from (S ⨯ ⊤_ C) = prod.fst ≫ terminal.from S := by apply terminal.hom_ext
  rw [h, assoc, HasClassifier.comm]

lemma wDef_comm : (prod.map m (name (χ_ m))) ≫ in_ B' = terminal.from _ ≫ t C := by
  -- for some reason there is an issue rewriting m = m ≫ 𝟙 _ ??
  -- TODO: should be able to wrestle this lemma's statement into the previous lemma's, merging the two
  have h := wDef_comm' m
  rw [prod.map_map_assoc, comp_id, id_comp] at h
  assumption

def w : S ⨯ ⊤_ C ⟶ pullback (in_ B') (t C) := pullback.lift (w := wDef_comm m)

lemma transposeOfMapDirectImage {X Y Z: C} (n : X ⟶ Y) [Mono n] (g : Z ⟶ pow X) : (g ≫ directImage n)^ = (prod.map (𝟙 Y) g) ≫ (e n) := by
  calc prod.map (𝟙 Y) (g ≫ directImage n) ≫ in_ Y = (prod.map (𝟙 Y) g) ≫ (prod.map (𝟙 Y) (directImage n)) ≫ in_ Y := by rw [prod.map_id_comp_assoc g (directImage n) (in_ Y)]
  _= (prod.map (𝟙 Y) g) ≫ ((e n)^)^ := rfl
  _= (prod.map (𝟙 Y) g) ≫ (e n) := by rw [transpose_left_inv]

lemma directImage_NameChar_factors : name (χ_ m) ≫ directImage k = name (χ_ (m ≫ k)) := by
  apply transposeInvInj
  nth_rewrite 2 [name]
  rw [transposeOfMapDirectImage _, transpose_left_inv, HasClassifier.prodCompClassEqClassOfComp]
  apply HasClassifier.unique
  have pbU := isPullback (prod.map m (𝟙 (⊤_ C)))
  rw [← transpose_left_inv (χ_ (prod.map m (𝟙 (⊤_ C)))), ← prodCompClassEqClassOfComp, ← name] at pbU
  unfold transposeInv at pbU
  have pbUR := IsPullback.of_hasPullback (in_ B') (t C)
  have pbUL := IsPullback.of_bot' pbU pbUR
  have pbR := isPullback ((pullback.fst (in_ B') (t C)) ≫ prod.map k (𝟙 _))
  have pbBL := IsPullback.isPullbackOfProd (IsPullback.id_vert k) (IsPullback.id_horiz ⌈χ_ m⌉)
  have pbL := IsPullback.paste_horiz pbUL pbBL
  have pb := IsPullback.paste_vert pbL pbR
  rw [terminal.hom_ext (_ ≫ _) (terminal.from (S ⨯ (⊤_ C))), prod.map_map, comp_id, ← e] at pb
  exact pb


variable {S' : C}

lemma transposeOfDirectImageInverseImage (k : B' ⟶ B) [Mono k] (g : S ⟶ B) : (directImage k ≫ inverseImage g)^ = (prod.map g (𝟙 _)) ≫ (e k) := by {
    calc prod.map (𝟙 S) (directImage k ≫ inverseImage g) ≫ in_ S = (prod.map (𝟙 S) (directImage k)) ≫ (prod.map (𝟙 S) (inverseImage g)) ≫ in_ S := prod.map_id_comp_assoc (directImage k) (inverseImage g) (in_ S)
    _ = (prod.map (𝟙 S) (directImage k)) ≫ (prod.map g (𝟙 _)) ≫ in_ _ := by rw [inverseImage_comm]
    _ = (prod.map g (𝟙 _)) ≫ (prod.map (𝟙 _) (directImage k)) ≫ in_ _ := by rw [← assoc, @prod.map_swap, assoc]
    _ = (prod.map g (𝟙 _)) ≫ e k := by {rw [← transpose_left_inv (e k)]; congr}
}

variable {k}
variable {g : S ⟶ B} {g' : S' ⟶ B'} {n : S' ⟶ S}
variable (h_pullback : IsPullback g' n k g)

theorem BeckChevalley_for_exists : letI _: Mono n := PullbackCone.mono_snd_of_is_pullback_of_mono (IsPullback.isLimit h_pullback)
inverseImage g' ≫ directImage n = directImage k ≫ inverseImage g := by {
  let mono_n : Mono n := PullbackCone.mono_snd_of_is_pullback_of_mono (IsPullback.isLimit h_pullback)
  apply transposeInvInj
  rw [transposeOfDirectImageInverseImage k g, transposeOfMapDirectImage n (inverseImage g')]
  have pbR₀ := isPullback ((pullback.fst (in_ B') (t C)) ≫ prod.map k (𝟙 _))
  have pbR₁ := isPullback ((pullback.fst (in_ S') (t C)) ≫ prod.map n (𝟙 _))
  have pbBL₀ := IsPullback.isPullbackOfProd (IsPullback.flip h_pullback) (IsPullback.id_vert (𝟙 (pow B')))
  have pbBL₁ := IsPullback.isPullbackOfProd (IsPullback.id_vert n) (IsPullback.id_horiz (inverseImage g'))
  have pbUR₀ := IsPullback.of_hasPullback (in_ B') (t C)
  have pbUR₁ := IsPullback.of_hasPullback (in_ S') (t C)
  have pbU₀ := IsPullback.of_hasPullback (prod.map g' (𝟙 (pow B')) ≫ in_ B') (t C)
  have pbU₁ := pbU₀
  simp_rw [← inverseImage_comm g'] at pbU₁
  have pbUL₀ := IsPullback.of_bot' pbU₀ pbUR₀
  have pbUL₁ := IsPullback.of_bot' pbU₁ pbUR₁
  have pbL₀ := IsPullback.paste_horiz pbUL₀ pbBL₀
  have pbL₁ := IsPullback.paste_horiz pbUL₁ pbBL₁
  have pb₀ := IsPullback.paste_vert pbL₀ pbR₀
  have pb₁ := IsPullback.paste_vert pbL₁ pbR₁
  rw [terminal.hom_ext (_ ≫ _) (terminal.from (pullback (prod.map g' (𝟙 (pow B')) ≫ in_ B') (t C)))] at pb₀
  rw[terminal.hom_ext (_ ≫ _) (terminal.from (pullback (prod.map g' (𝟙 (pow B')) ≫ in_ B') (t C)))] at pb₁
  rw [HasClassifier.unique (pullback.fst (prod.map g' (𝟙 (pow B')) ≫ in_ B') (t C) ≫ prod.map n (𝟙 (pow B'))) (prod.map g (𝟙 (pow B')) ≫ χ_ (pullback.fst (in_ B') (t C) ≫ prod.map k (𝟙 (pow B')))) pb₀]
  rw [HasClassifier.unique (pullback.fst (prod.map g' (𝟙 (pow B')) ≫ in_ B') (t C) ≫ prod.map n (𝟙 (pow B'))) (prod.map (𝟙 S) (inverseImage g') ≫ χ_ (pullback.fst (in_ S') (t C) ≫ prod.map n (𝟙 (pow S')))) pb₁]
}

variable (k)

theorem inverseImageOfDirectImageIsidentity : directImage k ≫ inverseImage k = 𝟙 _ := by
  rw [← BeckChevalley_for_exists (IsKernelPair.id_of_mono k), inverseImage_id, directImage_id, comp_id]

variable {k}

end BeckChevalley

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
    rw [prod.map_id_comp, prod.map_id_comp, Category.assoc, Category.assoc, inverseImage_comm, inverseImage_comm,
      ←Category.assoc, prod.map_map, ←Category.assoc, prod.map_map, id_comp, comp_id, id_comp, ←comp_id f,
      ←id_comp (singleton _), ←comp_id g, ←prod.map_map, ←prod.map_map, assoc, assoc, singleton, Power.comm] at h'
    have comm : (f ≫ terminal.from _) ≫ t C = prod.lift (𝟙 _) f ≫ prod.map f (𝟙 _) ≫ Predicate.eq _ := by
      rw [terminal.comp_from, ←assoc, prod.lift_map, comp_id, id_comp, Predicate.lift_eq, Predicate.true_]
    rw [terminal.comp_from, h', ←assoc, prod.lift_map, id_comp, comp_id] at comm
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
      rightSection := BeckChevalley.directImage π
      leftSection := BeckChevalley.directImage g
      condition := by {
        change (powFunctor C).map f.op ≫ (powFunctor C).map π.op = (powFunctor C).map g.op ≫ (powFunctor C).map π.op
        simp_rw [← (powFunctor C).map_comp]
        refine (map_injective_iff (powFunctor C) (f.op ≫ π.op) (g.op ≫ π.op)).mpr ?_
        exact h₂.w
      }
      rightSection_π := BeckChevalley.inverseImageOfDirectImageIsidentity π
      leftSection_bottom := BeckChevalley.inverseImageOfDirectImageIsidentity g
      leftSection_top := Eq.symm (BeckChevalley.BeckChevalley_for_exists h₂')
    }

instance PowPreservesCoequalizersOfReflexivePair : Monad.PreservesColimitOfIsReflexivePair (powFunctor C) := Monad.PreservesColimitOfIsReflexivePairOfPreservesCoequalizer PowPreservesIsCoequalizerOfReflexivePair

instance powFunctorMonadic : MonadicRightAdjoint (powFunctor C) :=
  Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms (powSelfAdj C)

instance : (Monad.comparison (powSelfAdj C)).IsEquivalence := MonadicRightAdjoint.eqv

variable {J}
variable [SmallCategory J] [FinCategory J]

instance : HasLimitsOfShape J (powSelfAdj C).toMonad.Algebra :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Adjunction.toMonad (powFunctorMonadic.adj)).forget


--Question: How to deal with
instance HasFiniteColimits : HasFiniteColimits C where
  out := by
    intros J 𝒥 ℱ
    have h : HasLimitsOfShape Jᵒᵖ Cᵒᵖ :=
      (Adjunction.hasLimitsOfShape_of_equivalence (Monad.comparison (powSelfAdj C)))
    exact hasColimitsOfShape_of_hasLimitsOfShape_op


end
end Topos
end CategoryTheory
