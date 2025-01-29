/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.Basic

namespace CategoryTheory

open Category Limits Classifier Power Functor

namespace Topos

universe u v
variable {C}
variable [Category.{v, u} C] [Topos C]

noncomputable section

-- TODO: prove that `PowFunctor C` preserves colimits of reflexive pairs.

namespace BeckChevalley

/-
  In this section, we follow Mac Lane and Moerdijk in defining the direct image ∃ₖ : PB' ⟶ PB
  of a monomorphism k : B' ⟶ B, then show that ∃ₖ ≫ Pow_map k = 𝟙 PB'.
-/

variable {B B' : C} (k : B' ⟶ B) [Mono k]

#check P_transpose (ClassifierOfMono ((pullback.fst (f := in_ B') (g := t C)) ≫ prod.map k (𝟙 _))).val

def directImage : Pow B' ⟶ Pow B :=
  P_transpose (ClassifierOfMono ((pullback.fst (f := in_ B') (g := t C)) ≫ prod.map k (𝟙 _))).val

variable {S : C} (m : S ⟶ B') [Mono m]

#check Name

lemma wDef_comm' : (prod.map m (𝟙 _)) ≫ (prod.map (𝟙 _) (Name (ClassifierOfMono m))) ≫ in_ B' = terminal.from _ ≫ t C := by
  rw [Predicate.NameDef, prod.map_fst_assoc]
  have h : terminal.from (S ⨯ ⊤_ C) = prod.fst ≫ terminal.from S := by apply terminal.hom_ext
  rw [h, assoc, ClassifierMonoComm]

lemma wDef_comm : (prod.map m (Name (ClassifierOfMono m))) ≫ in_ B' = terminal.from _ ≫ t C := by
  -- for some reason there is an issue rewriting m = m ≫ 𝟙 _ ??
  -- TODO: should be able to wrestle this lemma's statement into the previous lemma's, merging the two
  have h := wDef_comm' m
  rw [prod.map_map_assoc, comp_id, id_comp] at h
  assumption

def w : S ⨯ ⊤_ C ⟶ pullback (in_ B') (t C) := pullback.lift (w := wDef_comm m)

lemma directImage_NameChar_factors : Name (ClassifierOfMono m) ≫ directImage k = Name (ClassifierOfMono (m ≫ k)) := by
  have transpose : P_transpose_inv (Name (ClassifierOfMono m) ≫ directImage k) = P_transpose_inv (Name (ClassifierOfMono (m ≫ k))) := by
    dsimp only [Name]
    rw [P_transpose_left_inv]
    dsimp only [P_transpose_inv, directImage]
    rw [prod.map_id_comp, assoc, Pow_powerizes]
    sorry

  sorry

end BeckChevalley

instance PowRightAdj : IsRightAdjoint (PowFunctor C) where
  exists_leftAdjoint := by
    apply Exists.intro (PowFunctorOp C)
    exact ⟨PowSelfAdj C⟩

instance PowFaithful : Functor.Faithful (PowFunctor C) where
  map_injective := by
    intro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨g⟩ h
    change (Pow_map f = Pow_map g) at h
    congr
    have h' := congrArg (fun k ↦ P_transpose_inv (singleton X ≫ k)) h
    dsimp only [P_transpose_inv] at h'
    rw [prod.map_id_comp, prod.map_id_comp, Category.assoc, Category.assoc, Pow_map_Powerizes, Pow_map_Powerizes,
      ←Category.assoc, prod.map_map, ←Category.assoc, prod.map_map, id_comp, comp_id, id_comp, ←comp_id f,
      ←id_comp (singleton _), ←comp_id g, ←prod.map_map, ←prod.map_map, assoc, assoc, singleton, Pow_powerizes] at h'
    have comm : (f ≫ terminal.from _) ≫ t C = prod.lift (𝟙 _) f ≫ prod.map f (𝟙 _) ≫ Predicate.eq _ := by
      rw [terminal.comp_from, ←assoc, prod.lift_map, comp_id, id_comp, Predicate.lift_eq, Predicate.true_]
    rw [terminal.comp_from, h', ←assoc, prod.lift_map, id_comp, comp_id] at comm
    exact (Predicate.eq_of_lift_eq comm.symm).symm


instance hasCoreflexiveEqualizers : HasCoreflexiveEqualizers C :=
  hasCoreflexiveEqualizers_of_hasEqualizers C

instance : HasCoequalizers Cᵒᵖ := hasCoequalizers_opposite

instance : HasReflexiveCoequalizers Cᵒᵖ := hasReflexiveCoequalizers_of_hasCoequalizers Cᵒᵖ

instance PowReflectsIsomorphisms : Functor.ReflectsIsomorphisms (PowFunctor C) := reflectsIsomorphismsOp (F := PowFunctor C)

instance PowPreservesCoproductOfReflexivePair : Monad.PreservesColimitOfIsReflexivePair (PowFunctor C) where
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

instance PowFunctorMonadic : MonadicRightAdjoint (PowFunctor C) := sorry

-- TODO: Use `PowFunctorMonadic` to show that a topos has finite colimits.

instance HasFiniteColimits : HasFiniteColimits C := sorry


end
end Topos
end CategoryTheory
