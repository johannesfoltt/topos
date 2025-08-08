import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

namespace CategoryTheory.Over

open Category Limits Over MonoidalCategory CartesianMonoidalCategory CartesianClosed Adjunction

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

noncomputable section

local instance cartesianMonoidalCategory_base : CartesianMonoidalCategory C := ofHasFiniteProducts

variable {X : C} [Exponentiable X]

--local instance cartesianMonoidalCategory_Over : CartesianMonoidalCategory (Over X) := cartesianMonoidalCategory X

lemma HomEq_toFun_w {A : C} {B : Over X} (f : (star X).obj A ⟶ B) : CartesianClosed.curry (f.left) ≫
((exp X).map B.hom) = (toUnit A) ≫ (internalizeHom (𝟙 X)) := by {
  rw [← curry_natural_right]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, internalizeHom, uncurry_curry]
  simp; rfl
}

variable [HasPullbacks C]

def Γ (X : C) [Exponentiable X] : (Over X) ⥤ C where
  obj := fun A => Limits.pullback ((exp X).map A.hom) (internalizeHom (𝟙 X))
  map := fun {A B} f => pullback.map _ _ _ _ ((exp X).map f.left) (𝟙 _) (𝟙 _) (by rw [comp_id, ← Functor.map_comp, Over.w]) (by simp)

lemma HomEq_invFun_w {A : C} {B : Over X} (f : A ⟶ (Γ X).obj B) : CartesianClosed.uncurry (f ≫ (pullback.fst ((exp X).map B.hom) (internalizeHom (𝟙 X)))) ≫ B.hom = ((star X).obj A).hom := by {
  rw [← uncurry_natural_right, assoc, pullback.condition, ← assoc, toUnit_unique (f ≫ _) (toUnit A), uncurry_natural_left, internalizeHom, uncurry_curry]
  simp; rfl
}

def HomEq (A : C) (B : Over X) : ((star X).obj A ⟶ B) ≃ (A ⟶ (Γ X).obj B) where
  toFun := fun f => pullback.lift _ _ (HomEq_toFun_w f)
  invFun := fun f => homMk (CartesianClosed.uncurry (f ≫ (pullback.fst ((exp X).map B.hom) (internalizeHom (𝟙 X))))) (HomEq_invFun_w f)
  left_inv := by aesop_cat
  right_inv := by {
    intro f
    simp
    apply pullback.hom_ext
    · simp
    · simp
      exact toUnit_unique _ _
  }

def coreHomEq : Adjunction.CoreHomEquiv (star X) (Γ X) where
  homEquiv (A B) := HomEq A B
  homEquiv_naturality_left_symm {A A' B} (f g):= by {
    rw [OverMorphism.ext_iff, comp_left, HomEq, HomEq]
    simp
    rw [uncurry_natural_left]
    refine ?_ =≫ CartesianClosed.uncurry (g ≫ pullback.fst ((exp X).map B.hom) (internalizeHom (𝟙 X)))
    --These steps are a bit goofy
    change ((𝟙 X) ⊗ f) = _
    refine hom_ext (𝟙 X ⊗ f) (prod.map (𝟙 X) f) ?_ ?_
    · change _ = _ ≫ prod.fst
      rw [tensorHom_fst, prod.map_fst, comp_id, comp_id]
      rfl
    · change _ = _ ≫ prod.snd
      rw [tensorHom_snd, prod.map_snd]
      rfl
  }
  homEquiv_naturality_right {A B B'} (f g) := by {
    unfold HomEq
    unfold Γ
    simp
    apply pullback.hom_ext
    · simp
      exact curry_natural_right f.left g.left
    · simp
  }

def starΓadj : (star X) ⊣ (Γ X) := Adjunction.mkOfHomEquiv coreHomEq
