import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Topos.HelpfulCategoryTheory.CartesianMonoidalCategoryAdditions

namespace CategoryTheory.IsPullback

open Category Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ P₁ P₂ : C}
variable {f₁ : X₁ ⟶ Z₁} {f₂ : X₂ ⟶ Z₂} {g₁ : Y₁ ⟶ Z₁} {g₂ : Y₂ ⟶ Z₂} {fst₁ : P₁ ⟶ X₁} {fst₂ : P₂ ⟶ X₂} {snd₁ : P₁ ⟶ Y₁} {snd₂ : P₂ ⟶ Y₂}

theorem isPullbackOfProd (hp₁ : IsPullback fst₁ snd₁ f₁ g₁) (hp₂ : IsPullback fst₂ snd₂ f₂ g₂) : IsPullback (prod.map fst₁ fst₂) (prod.map snd₁ snd₂) (prod.map f₁ f₂) (prod.map g₁ g₂) := {
  w := by rw [prod.map_map, prod.map_map, hp₁.w, hp₂.w]
  isLimit' := by {
    apply Nonempty.intro
    have eq : prod.map fst₁ fst₂ ≫ prod.map f₁ f₂ = prod.map snd₁ snd₂ ≫ prod.map g₁ g₂ := by rw [prod.map_map, prod.map_map, hp₁.w, hp₂.w]
    have w₁ (s : PullbackCone (prod.map f₁ f₂) (prod.map g₁ g₂)) : (s.fst ≫ prod.fst) ≫ f₁ = (s.snd ≫ prod.fst) ≫ g₁ := by rw [assoc, assoc, ← prod.map_fst f₁ f₂, ← prod.map_fst g₁ g₂, PullbackCone.condition_assoc]
    have w₂ (s : PullbackCone (prod.map f₁ f₂) (prod.map g₁ g₂)) : (s.fst ≫ prod.snd) ≫ f₂ = (s.snd ≫ prod.snd) ≫ g₂ := by rw [assoc, assoc, ← prod.map_snd f₁ f₂, ← prod.map_snd g₁ g₂, PullbackCone.condition_assoc]
    let lift := fun (s : PullbackCone (prod.map f₁ f₂) (prod.map g₁ g₂)) ↦ prod.lift (hp₁.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (w₁ s)) (hp₂.lift (s.fst ≫ prod.snd) (s.snd ≫ prod.snd) (w₂ s))
    apply PullbackCone.IsLimit.mk eq lift
    · intro s
      rw [prod.lift_map, hp₁.lift_fst (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (w₁ s), hp₂.lift_fst (s.fst ≫ prod.snd) (s.snd ≫ prod.snd) (w₂ s), ← @prod.comp_lift, @prod.lift_fst_snd, @comp_id]
    · intro s
      rw [prod.lift_map, hp₁.lift_snd (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (w₁ s), hp₂.lift_snd (s.fst ≫ prod.snd) (s.snd ≫ prod.snd) (w₂ s), ← @prod.comp_lift, @prod.lift_fst_snd, @comp_id]
    · intro s m h_fst h_snd
      unfold lift
      have h₁ : m ≫ prod.fst = (hp₁.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (w₁ s)) := by {
        apply IsPullback.hom_ext hp₁
        · rw [hp₁.lift_fst (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (w₁ s), assoc, ← prod.map_fst fst₁ fst₂, ← assoc, h_fst]
        · rw [hp₁.lift_snd (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (w₁ s), assoc, ← prod.map_fst snd₁ snd₂, ← assoc, h_snd]
      }
      have h₂ : m ≫ prod.snd = (hp₂.lift (s.fst ≫ prod.snd) (s.snd ≫ prod.snd) (w₂ s)) := by {
        apply IsPullback.hom_ext hp₂
        · rw [hp₂.lift_fst (s.fst ≫ prod.snd) (s.snd ≫ prod.snd) (w₂ s), assoc, ← prod.map_snd fst₁ fst₂, ← assoc, h_fst]
        · rw [hp₂.lift_snd (s.fst ≫ prod.snd) (s.snd ≫ prod.snd) (w₂ s), assoc, ← prod.map_snd snd₁ snd₂, ← assoc, h_snd]
      }
      rw [← h₁, ← h₂, ← @prod.comp_lift, @prod.lift_fst_snd, @comp_id]
  }
}

theorem isPullbackOfTensor (hp₁ : IsPullback fst₁ snd₁ f₁ g₁) (hp₂ : IsPullback fst₂ snd₂ f₂ g₂) : IsPullback (fst₁ ⊗ fst₂) (snd₁ ⊗ snd₂) (f₁ ⊗ f₂) (g₁ ⊗ g₂) := {
  w := by rw [← tensor_comp, ← tensor_comp, hp₁.w, hp₂.w]
  isLimit' := by {
    apply Nonempty.intro
    have eq : (fst₁ ⊗ fst₂) ≫ (f₁ ⊗ f₂) = (snd₁ ⊗ snd₂) ≫ (g₁ ⊗ g₂) := by rw [← tensor_comp, ← tensor_comp, hp₁.w, hp₂.w]
    have w₁ (s : PullbackCone (f₁ ⊗ f₂) (g₁ ⊗ g₂)) : (s.fst ≫ fst _ _) ≫ f₁ = (s.snd ≫ fst _ _) ≫ g₁ := by rw [assoc, assoc, ← tensorHom_fst f₁ f₂, ← tensorHom_fst g₁ g₂, PullbackCone.condition_assoc]
    have w₂ (s : PullbackCone (f₁ ⊗ f₂) (g₁ ⊗ g₂)) : (s.fst ≫ snd _ _) ≫ f₂ = (s.snd ≫ snd _ _) ≫ g₂ := by rw [assoc, assoc, ← tensorHom_snd f₁ f₂, ← tensorHom_snd g₁ g₂, PullbackCone.condition_assoc]
    let lift := fun (s : PullbackCone (f₁ ⊗ f₂) (g₁ ⊗ g₂)) ↦ CartesianMonoidalCategory.lift (hp₁.lift (s.fst ≫ fst _ _) (s.snd ≫ fst _ _) (w₁ s)) (hp₂.lift (s.fst ≫ snd _ _) (s.snd ≫ snd _ _) (w₂ s))
    apply PullbackCone.IsLimit.mk eq lift
    · intro s
      rw [lift_map, hp₁.lift_fst (s.fst ≫ fst _ _) (s.snd ≫ fst _ _) (w₁ s), hp₂.lift_fst (s.fst ≫ snd _ _) (s.snd ≫ snd _ _) (w₂ s), ← comp_lift, lift_fst_snd, comp_id]
    · intro s
      rw [lift_map, hp₁.lift_snd (s.fst ≫ fst _ _) (s.snd ≫ fst _ _) (w₁ s), hp₂.lift_snd (s.fst ≫ snd _ _) (s.snd ≫ snd _ _) (w₂ s), ← comp_lift, lift_fst_snd, comp_id]
    · intro s m h_fst h_snd
      unfold lift
      have h₁ : m ≫ fst _ _ = (hp₁.lift (s.fst ≫ fst _ _) (s.snd ≫ fst _ _) (w₁ s)) := by {
        apply IsPullback.hom_ext hp₁
        · rw [hp₁.lift_fst (s.fst ≫ fst _ _) (s.snd ≫ fst _ _) (w₁ s), assoc, ← tensorHom_fst fst₁ fst₂, ← assoc, h_fst]
        · rw [hp₁.lift_snd (s.fst ≫ fst _ _) (s.snd ≫ fst _ _) (w₁ s), assoc, ← tensorHom_fst snd₁ snd₂, ← assoc, h_snd]
      }
      have h₂ : m ≫ snd _ _ = (hp₂.lift (s.fst ≫ snd _ _) (s.snd ≫ snd _ _) (w₂ s)) := by {
        apply IsPullback.hom_ext hp₂
        · rw [hp₂.lift_fst (s.fst ≫ snd _ _) (s.snd ≫ snd _ _) (w₂ s), assoc, ← tensorHom_snd fst₁ fst₂, ← assoc, h_fst]
        · rw [hp₂.lift_snd (s.fst ≫ snd _ _) (s.snd ≫ snd _ _) (w₂ s), assoc, ← tensorHom_snd snd₁ snd₂, ← assoc, h_snd]
      }
      rw [← h₁, ← h₂, ← comp_lift, lift_fst_snd, comp_id]
  }
}

lemma isPullback_Prod_Fst_of_isPullback {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst snd f g) : IsPullback (prod.lift fst snd) (fst ≫ f) (prod.map f g) (diag Z) where
  w := by rw [prod.comp_diag, prod.lift_map, h.w]
  isLimit' := by {
    apply Nonempty.intro
    have eq (s : PullbackCone (prod.map f g) (diag Z)) : (s.fst ≫ prod.fst) ≫ f = (s.fst ≫ prod.snd) ≫ g := by {
      rw [assoc, assoc, ← prod.map_fst f g, ← prod.map_snd f g, ← assoc, ← assoc, s.condition, assoc, assoc]
      simp
    }
    let lift := fun (s : PullbackCone (prod.map f g) (diag Z)) ↦ h.lift (s.fst ≫ prod.fst) (s.fst ≫ prod.snd) (eq s)
    apply PullbackCone.IsLimit.mk _ lift
    · intro s
      refine Limits.prod.hom_ext ?_ ?_
      · simp
        exact lift_fst h (s.fst ≫ prod.fst) (s.fst ≫ prod.snd) (eq s)
      · simp
        exact lift_snd h (s.fst ≫ prod.fst) (s.fst ≫ prod.snd) (eq s)
    · intro s
      unfold lift; simp
      rw [← prod.map_fst f g, ← assoc, s.condition]
      simp
    · intro s m h₁ h₂
      unfold lift
      apply h.hom_ext
      · simp_rw [← h₁]
        simp
      · simp_rw [← h₁]
        simp
  }

lemma isPullback_Tensor_Fst_of_isPullback {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst snd f g) : IsPullback (CartesianMonoidalCategory.lift fst snd) (fst ≫ f) (f ⊗ g) (CartesianMonoidalCategory.diag Z) where
  w := by rw [comp_diag, lift_map, h.w]
  isLimit' := by {
    apply Nonempty.intro
    have eq (s : PullbackCone (f ⊗ g) (diag Z)) : (s.fst ≫ CartesianMonoidalCategory.fst _ _) ≫ f = (s.fst ≫ CartesianMonoidalCategory.snd _ _) ≫ g := by {
      rw [assoc, assoc, ← tensorHom_fst f g, ← tensorHom_snd f g, ← assoc, ← assoc, s.condition, assoc, assoc]
      simp
    }
    let lift := fun (s : PullbackCone (f ⊗ g) (diag Z)) ↦ h.lift (s.fst ≫ CartesianMonoidalCategory.fst _ _) (s.fst ≫ CartesianMonoidalCategory.snd _ _) (eq s)
    apply PullbackCone.IsLimit.mk _ lift
    · intro s
      refine CartesianMonoidalCategory.hom_ext (lift s ≫ CartesianMonoidalCategory.lift fst snd) s.fst ?_ ?_
      · simp
        exact lift_fst h (s.fst ≫ CartesianMonoidalCategory.fst _ _) (s.fst ≫ CartesianMonoidalCategory.snd _ _) (eq s)
      · simp
        exact lift_snd h (s.fst ≫ CartesianMonoidalCategory.fst _ _) (s.fst ≫ CartesianMonoidalCategory.snd _ _) (eq s)
    · intro s
      unfold lift; simp
      rw [← tensorHom_fst f g, ← assoc, s.condition]
      simp
    · intro s m h₁ h₂
      unfold lift
      apply h.hom_ext
      · simp_rw [← h₁]
        simp
      · simp_rw [← h₁]
        simp
  }

omit [CartesianMonoidalCategory C] in
lemma isPullback_comp_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g]: IsPullback (𝟙 X) f (f ≫ g) g where
  w := by aesop_cat
  isLimit' := by {
    apply Nonempty.intro
    apply PullbackCone.IsLimit.mk _ (fun s ↦ s.fst)
    · simp
    · intro s
      have h := s.condition; rw [← assoc] at h
      rw [← cancel_mono g]
      assumption
    · intro s m h₁ h₂
      aesop_cat
  }

lemma isPullbackProdFst {X Y : C} (f : X ⟶ Y) : IsPullback (prod.map f (terminal.from (⊤_ C))) (prod.fst) (prod.fst) f where
  w := prod.map_fst f (terminal.from (⊤_ C))
  isLimit' := by {
    apply Nonempty.intro
    apply PullbackCone.IsLimit.mk (prod.map_fst f (terminal.from (⊤_ C))) (fun (s : PullbackCone prod.fst f) ↦ prod.lift (s.snd) (terminal.from _)) ?_ (fun s ↦ prod.lift_fst s.snd (terminal.from s.pt)) ?_
    · intro s
      rw [prod.lift_map, terminal.hom_ext (terminal.from (⊤_ C)) (𝟙 (⊤_ C)), comp_id, ← s.condition, ← terminal.hom_ext (s.fst ≫ prod.snd) (terminal.from s.pt), ← prod.comp_lift, prod.lift_fst_snd, comp_id]
    · intro s m h_fst h_snd
      simp
      rw [← h_snd, terminal.hom_ext (terminal.from s.pt) (m ≫ prod.snd), ← prod.comp_lift, prod.lift_fst_snd, comp_id]
  }


lemma isPullbackTensorFst {X Y : C} (f : X ⟶ Y) : IsPullback (f ⊗ (toUnit (𝟙_ C))) (fst _ _) (fst _ _) f where
  w := tensorHom_fst f (toUnit (𝟙_ C))
  isLimit' := by {
    apply Nonempty.intro
    apply PullbackCone.IsLimit.mk (tensorHom_fst f (toUnit (𝟙_ C))) (fun (s : PullbackCone _ f) ↦ (CartesianMonoidalCategory.lift (s.snd) (toUnit _))) ?_ (fun s ↦ CartesianMonoidalCategory.lift_fst s.snd (toUnit s.pt)) ?_
    · intro s
      simp
      refine CartesianMonoidalCategory.hom_ext (CartesianMonoidalCategory.lift (s.snd ≫ f) (toUnit s.pt)) s.fst ?_ ?_
      · simp
        exact Eq.symm (PullbackCone.condition s)
      · simp
        exact CartesianMonoidalCategory.toUnit_unique_iff.mpr trivial
    · intro s m h_fst h_snd
      simp
      rw [← h_snd]
      refine CartesianMonoidalCategory.hom_ext m (CartesianMonoidalCategory.lift (m ≫ fst X (𝟙_ C)) (toUnit s.pt)) ?_ ?_
      · simp
      · simp
        exact CartesianMonoidalCategory.toUnit_unique_iff.mpr trivial
  }

instance mono_pullback_to_tensor {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct X Y] :
    Mono (CartesianMonoidalCategory.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => f ≫ fst _ _) h
    · simpa using congrArg (fun f => f ≫ snd _ _) h⟩


lemma comp_IsPullback {C : Type*} [Category C] {U S X : C} (u : U ⟶ S) (s : S ⟶ X) [Mono s] : IsPullback u (𝟙 U) s (u ≫ s) where
  w := by simp
  isLimit' := by {
    apply Nonempty.intro
    apply PullbackCone.IsLimit.mk _ (fun (c : PullbackCone s (u ≫ s)) ↦ c.snd)
    · intro c
      expose_names
      apply inst_1.right_cancellation (c.snd ≫ u) c.fst
      rw [assoc, c.condition]
    · intro c
      simp
    · intros c l h_fst h_snd
      simp at h_snd
      assumption
  }
