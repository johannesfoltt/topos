import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

namespace CategoryTheory.Over

open Category Functor Limits Over MonoidalCategory CartesianMonoidalCategory CartesianClosed Adjunction

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

noncomputable section

local instance cartesianMonoidalCategory_base : CartesianMonoidalCategory C := ofHasFiniteProducts

variable {X : C} [Exponentiable X]

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

def starAdjΓ : (star X) ⊣ (Γ X) := Adjunction.mkOfHomEquiv coreHomEq

variable {X' : C} (f : X' ⟶ X)

def eqvOverOver_functor : Over (mk f) ⥤ Over X' where
  obj := fun A => mk A.hom.left
  map := fun g => homMk g.left.left (by rw [← (Over.w g)]; simp)

def eqvOverOver_inverse : Over X' ⥤ Over (mk f) where
  obj := fun A => mk (homMk A.hom : mk (A.hom ≫ f) ⟶ mk f)
  map := fun g => homMk (homMk g.left)

def equvOverOver_unitIso_eq_components (A : Over (mk f)) : (𝟭 (Over (mk f))).obj A = (eqvOverOver_functor f ⋙ eqvOverOver_inverse f).obj A := by {
  unfold eqvOverOver_functor
  unfold eqvOverOver_inverse
  simp
  sorry
}

def equvOverOver_counitIso_eq_components (A : Over X') : (eqvOverOver_inverse f ⋙ eqvOverOver_functor f).obj A = (𝟭 (Over X')).obj A := by {
  unfold eqvOverOver_functor
  unfold eqvOverOver_inverse
  simp
  sorry
}

def eqvOverOver : Over (mk f) ≌ Over X' where
  functor := eqvOverOver_functor f
  inverse := eqvOverOver_inverse f
  unitIso := NatIso.ofComponents (fun A => (eqToIso (equvOverOver_unitIso_eq_components f A)))
  counitIso := NatIso.ofComponents (fun A => (eqToIso (equvOverOver_counitIso_eq_components f A)))
  functor_unitIso_comp := by {
    intros X
    unfold eqvOverOver_functor
    unfold eqvOverOver_inverse
    simp
    rw [OverMorphism.ext_iff, homMk_left _ _]
    simp
  }

/-

instance eqvOverOver_Faithful : (eqvOverOver f).Faithful where
  map_injective := by {
    intros A B g g' h
    apply OverMorphism.ext ∘ OverMorphism.ext
    unfold eqvOverOver at h; simp at h
    rw [OverMorphism.ext_iff, homMk_left _ _, homMk_left _ _] at h
    exact h
  }

instance eqvOverOver_Full : (eqvOverOver f).Full where
  map_surjective := by {
    intros A B g
    unfold eqvOverOver at g; simp at g
    unfold eqvOverOver; simp
    refine Exists.intro ?_ ?_
    · refine homMk ?_ ?_
      · refine homMk ?_ ?_
        · exact g.left
        · have Ov_g := Over.w g; rw [mk_hom, mk_hom] at Ov_g
          have Ov_A := Over.w A.hom; simp at Ov_A
          have Ov_B := Over.w B.hom; simp at Ov_B
          rw [← Ov_B, ← assoc, Ov_g, Ov_A]
      · rw [OverMorphism.ext_iff, comp_left, homMk_left _ _]
        have Ov_g := Over.w g; rw [mk_hom, mk_hom] at Ov_g
        exact Ov_g
    · aesop_cat
  }

instance eqvOverOver_EssSurj : (eqvOverOver f).EssSurj where
  mem_essImage := by {
    intro Y
    use mk (homMk Y.hom : mk (Y.hom ≫ f) ⟶ mk f)
    apply Nonempty.intro
    apply Iso.refl
  }

instance eqvOverOver_IsEquivalence : (eqvOverOver f).IsEquivalence := {faithful := eqvOverOver_Faithful f, full := eqvOverOver_Full f, essSurj := eqvOverOver_EssSurj f}

-/
