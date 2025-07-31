import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Images


namespace CategoryTheory

open Category Limits Functor

noncomputable section

universe u v
variable {C}
variable [Category.{v, u} C] [IsRegularMonoCategory C] [HasPushouts C] [HasEqualizers C]

variable {A B : C}

def EqualizerPushoutFactorisation (f : A ⟶ B) : MonoFactorisation f where
  I := equalizer (pushout.inl f f) (pushout.inr f f)
  m := equalizer.ι (pushout.inl f f) (pushout.inr f f)
  e := equalizer.lift f pushout.condition

lemma EqualizerPushoutFactorisation_comm (f : A ⟶ B) (F' : MonoFactorisation f) : (EqualizerPushoutFactorisation f).m ≫ (regularMonoOfMono F'.m).left = (EqualizerPushoutFactorisation f).m ≫ (regularMonoOfMono F'.m).right := by {
  have help₁ : f ≫ (regularMonoOfMono F'.m).left = f ≫ (regularMonoOfMono F'.m).right := by simp_rw [← F'.fac, assoc, (regularMonoOfMono F'.m).w]
  unfold EqualizerPushoutFactorisation; simp
  rw [← pushout.inl_desc (regularMonoOfMono F'.m).left (regularMonoOfMono F'.m).right help₁, ← assoc, equalizer.condition (pushout.inl f f) (pushout.inr f f), assoc, pushout.inr_desc]
}

def EqualizerPushoutFactorisation_IsImage (f : A ⟶ B) : IsImage (EqualizerPushoutFactorisation f) where
  lift := fun F' ↦ let regMonoF' := regularMonoOfMono F'.m; ↑(RegularMono.lift' F'.m (EqualizerPushoutFactorisation f).m (EqualizerPushoutFactorisation_comm f F'))
  lift_fac := by {
    intro F'
    let regMonoF' := regularMonoOfMono F'.m
    exact (RegularMono.lift' F'.m (EqualizerPushoutFactorisation f).m (EqualizerPushoutFactorisation_comm f F')).2
  }

def EqualizerPushout_ImageFactorisation (f : A ⟶ B) : ImageFactorisation f where
  F := EqualizerPushoutFactorisation f
  isImage := EqualizerPushoutFactorisation_IsImage f

instance EqualizerPushout_HasImage (f : A ⟶ B) : HasImage f where
  exists_image := ⟨EqualizerPushout_ImageFactorisation f⟩

instance EqualizerPushout_HasImages : HasImages C where
  has_image := fun f ↦ EqualizerPushout_HasImage f

omit [IsRegularMonoCategory C] [HasPushouts C]
