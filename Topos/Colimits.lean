/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.Basic

namespace CategoryTheory

open Category Limits MonoClassifier Power Functor

namespace Topos

universe u v
variable {C}
variable [Category.{v, u} C] [IsTopos C]

noncomputable section

-- TODO: prove that `powFunctor C` preserves colimits of reflexive pairs.

namespace BeckChevalley

/-
  In this section, we follow Mac Lane and Moerdijk in defining the direct image ∃ₖ : PB' ⟶ PB
  of a monomorphism k : B' ⟶ B, then show that ∃ₖ ≫ Pow_map k = 𝟙 PB'.
-/

variable {B B' : C} (k : B' ⟶ B) [Mono k]

#check transpose (χ_ ((pullback.fst (f := in_ B') (g := t C)) ≫ prod.map k (𝟙 _)))

def directImage : pow B' ⟶ pow B :=
  transpose (χ_ ((pullback.fst (f := in_ B') (g := t C)) ≫ prod.map k (𝟙 _)))

variable {S : C} (m : S ⟶ B') [Mono m]

lemma wDef_comm' : (prod.map m (𝟙 _)) ≫ (prod.map (𝟙 _) (name (χ_ m))) ≫ in_ B' = terminal.from _ ≫ t C := by
  rw [Predicate.NameDef, prod.map_fst_assoc]
  have h : terminal.from (S ⨯ ⊤_ C) = prod.fst ≫ terminal.from S := by apply terminal.hom_ext
  rw [h, assoc, MonoClassifier.comm]

lemma wDef_comm : (prod.map m (name (χ_ m))) ≫ in_ B' = terminal.from _ ≫ t C := by
  -- for some reason there is an issue rewriting m = m ≫ 𝟙 _ ??
  -- TODO: should be able to wrestle this lemma's statement into the previous lemma's, merging the two
  have h := wDef_comm' m
  rw [prod.map_map_assoc, comp_id, id_comp] at h
  assumption

def w : S ⨯ ⊤_ C ⟶ pullback (in_ B') (t C) := pullback.lift (w := wDef_comm m)

lemma directImage_NameChar_factors : name (χ_ m) ≫ directImage k = name (χ_ (m ≫ k)) := by
  have transpose : transposeInv (name (χ_ m) ≫ directImage k) = transposeInv (name (χ_ (m ≫ k))) := by
    dsimp only [name]
    rw [transpose_left_inv]
    dsimp only [transposeInv, directImage]
    rw [prod.map_id_comp, assoc, Power.comm]
    sorry

  sorry

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

instance PowPreservesCoproductOfReflexivePair : Monad.PreservesColimitOfIsReflexivePair (powFunctor C) where
  out := by
    intro ⟨A⟩ ⟨B⟩ ⟨f⟩ ⟨g⟩ h₀
    change (B ⟶ A) at f; change (B ⟶ A) at g
    have h₁ := h₀.common_section'
    let s := h₁.choose
    have hs₁ := congrArg (fun k ↦ k.unop) h₁.choose_spec.1
    have hs₂ := congrArg (fun k ↦ k.unop) h₁.choose_spec.2
    change (f ≫ s.unop = 𝟙 _) at hs₁
    change (g ≫ s.unop = 𝟙 _) at hs₂
    refine PreservesColimit.mk ?_
    intro ⟨pt, ι⟩ hc


    sorry

instance powFunctorMonadic : MonadicRightAdjoint (powFunctor C) := sorry

-- TODO: Use `powFunctorMonadic` to show that a topos has finite colimits.

instance HasFiniteColimits : HasFiniteColimits C := sorry


end
end Topos
end CategoryTheory
