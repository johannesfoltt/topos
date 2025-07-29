import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.HelpfulCategoryTheory.IsEqualizer

namespace CategoryTheory

open CategoryTheory Limits IsCoequalizer

variable {C D : Type*} [Category C] [Category D]

class Limits.PreservesIsCoequalizer {X Y : C} (f g : X ⟶ Y) (F : C ⥤ D): Prop where
  preserves {P : C} {π : Y ⟶ P} (h : IsCoequalizer f g π) : IsCoequalizer (F.map f) (F.map g) (F.map π)


noncomputable def Limits.parallelPairFunctorObjectEq {X Y : C} (f g : X ⟶ Y) (F : C ⥤ D) (j : WalkingParallelPair) : (parallelPair (F.map f) (F.map g)).obj j ≅ (parallelPair f g ⋙ F).obj j := by {
  induction j
  · rfl
  · rfl
}

lemma Limits.parallelPairFunctorNaturality {X Y : C} (f g : X ⟶ Y) (F : C ⥤ D) {j k : WalkingParallelPair} (m : j ⟶ k) : (parallelPair (F.map f) (F.map g)).map m ≫ ((fun j ↦ parallelPairFunctorObjectEq f g F j) k).hom = ((fun j ↦ parallelPairFunctorObjectEq f g F j) j).hom ≫ (parallelPair f g ⋙ F).map m := by {
  induction m
  · unfold parallelPairFunctorObjectEq
    simp
  · unfold parallelPairFunctorObjectEq
    simp
  · simp
}

noncomputable def Limits.parallelPairFunctorIso {X Y : C} (f g : X ⟶ Y) (F : C ⥤ D) : parallelPair (F.map f) (F.map g) ≅ parallelPair f g ⋙ F := NatIso.ofComponents (fun j ↦ parallelPairFunctorObjectEq f g F j) (fun m ↦ parallelPairFunctorNaturality f g F m)

namespace Monad

class PreservesCoequalizerOfIsReflexivePair (F : C ⥤ D) where
  out : ∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesIsCoequalizer f g F

theorem PreservesColimitOfPreservesIsCoequalizer {X Y : C} {f g : X ⟶ Y} {F : C ⥤ D} (h : PreservesIsCoequalizer f g F) : PreservesColimit (parallelPair f g) F where
  preserves := by {
    intros c hc
    apply Nonempty.intro
    let help : ((Cocones.precompose (parallelPairFunctorIso f g F).inv).obj (Cofork.ofπ (F.map (c.ι.app WalkingParallelPair.one)) (h.preserves (of_isColimit_cocone hc)).w)).pt ≅ (F.mapCocone c).pt := by rfl
    have help' : ∀ (j : WalkingParallelPair), ((Cocones.precompose (parallelPairFunctorIso f g F).inv).obj (Cofork.ofπ (F.map (c.ι.app WalkingParallelPair.one)) (h.preserves (of_isColimit_cocone hc)).w)).ι.app j ≫ help.hom = (F.mapCocone c).ι.app j := by {
      intro j
      induction j
      · unfold help
        unfold parallelPairFunctorIso
        unfold parallelPairFunctorObjectEq
        simp
      · unfold help
        unfold parallelPairFunctorIso
        unfold parallelPairFunctorObjectEq
        simp
    }
    exact IsColimit.equivOfNatIsoOfIso _ _ _ (CategoryTheory.Limits.Cocones.ext help help') ((h.preserves (of_isColimit_cocone hc)).isColimit'.some)
  }

theorem PreservesColimitOfIsReflexivePairOfPreservesCoequalizer {F : C ⥤ D} (h : PreservesCoequalizerOfIsReflexivePair F) : PreservesColimitOfIsReflexivePair F where
  out := fun {A B} (f g) ↦ PreservesColimitOfPreservesIsCoequalizer (h.out f g)
