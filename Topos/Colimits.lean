import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.Basic

namespace CategoryTheory

open Category Limits Classifier Power

namespace Topos

variable [Category.{v, u} C] [Topos C]

noncomputable section

-- TODO: prove that `PowFunctor C` preserves colimits of reflexive pairs.

instance PowRightAdj : IsRightAdjoint (PowFunctor C) where
  left := PowFunctorOp C
  adj := PowSelfAdj C

instance PowFaithful : Faithful (PowFunctor C) where
  map_injective := by
    intro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨g⟩ h
    change (Y ⟶ X) at f; change (Y ⟶ X) at g
    change (Pow_map f = Pow_map g) at h
    congr
    have h' : (singleton X) ≫ Pow_map f = (singleton X) ≫ Pow_map g := by rw [h]
    have h'' := congrArg (fun k ↦ toPredicate k) h'
    dsimp only [toPredicate] at h''
    rw [prod.map_id_comp, prod.map_id_comp, Category.assoc, Category.assoc, ←Pow_map_Powerizes, ←Pow_map_Powerizes,
      ←Category.assoc, prod.map_map, ←Category.assoc, prod.map_map, id_comp, id_comp, comp_id, ←comp_id f,
      ←id_comp (singleton _), ←comp_id g, ←prod.map_map, ←prod.map_map, assoc, assoc, singleton, ←Pow_powerizes] at h''
    have comm₁ : (f ≫ terminal.from _) ≫ t C = prod.lift (𝟙 _) f ≫ prod.map f (𝟙 _) ≫ Predicate.eq _ := by
      rw [terminal.comp_from, ←assoc, prod.lift_map, comp_id, id_comp, Predicate.lift_eq, Predicate.true_]
    rw [terminal.comp_from, h'', ←assoc, prod.lift_map, id_comp, comp_id] at comm₁
    exact (Predicate.eq_of_lift_eq comm₁.symm).symm


instance hasCoreflexiveEqualizers : HasCoreflexiveEqualizers C :=
  hasCoreflexiveEqualizers_of_hasEqualizers C

instance : HasCoequalizers Cᵒᵖ := hasCoequalizers_opposite

instance : HasReflexiveCoequalizers Cᵒᵖ := hasReflexiveCoequalizers_of_hasCoequalizers Cᵒᵖ

instance PowReflectsIsomorphisms : ReflectsIsomorphisms (PowFunctor C) := reflectsIsomorphismsOp (F := PowFunctor C)

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

instance PowFunctorMonadic : MonadicRightAdjoint (PowFunctor C) :=
  Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms

-- TODO: Use `PowFunctorMonadic` to show that a topos has finite colimits.

end
end Topos
end CategoryTheory
