import Topos.Colimits
import Topos.CokernelPair

namespace CategoryTheory

open Category Limits HasClassifier Power Functor

universe u v
variable {C}
variable [Category.{v, u} C] [RegularMonoCategory C] [HasPushouts C] [HasEqualizers C]

variable {A B : C}

noncomputable def MonoEpiFactorisation (f : A ⟶ B) : MonoFactorisation f where
  I := equalizer (pushout.inl f f) (pushout.inr f f)
  m := equalizer.ι (pushout.inl f f) (pushout.inr f f)
  e := equalizer.lift f pushout.condition

lemma MonoEpiFactorisationEqualisationHelp (f : A ⟶ B) (F' : MonoFactorisation f) : (MonoEpiFactorisation f).m ≫ (regularMonoOfMono F'.m).left = (MonoEpiFactorisation f).m ≫ (regularMonoOfMono F'.m).right := by {
  have help₁ : f ≫ (regularMonoOfMono F'.m).left = f ≫ (regularMonoOfMono F'.m).right := by simp_rw [← F'.fac, assoc, (regularMonoOfMono F'.m).w]
  unfold MonoEpiFactorisation; simp
  rw [← pushout.inl_desc (regularMonoOfMono F'.m).left (regularMonoOfMono F'.m).right help₁, ← assoc,equalizer.condition (pushout.inl f f) (pushout.inr f f), assoc, pushout.inr_desc]
}

noncomputable def MonoEpiFactorisationIsImage (f : A ⟶ B) : IsImage (MonoEpiFactorisation f) where
  lift := fun F' ↦ let regMonoF' := regularMonoOfMono F'.m; ↑(RegularMono.lift' F'.m (MonoEpiFactorisation f).m (MonoEpiFactorisationEqualisationHelp f F'))
  lift_fac := by {
    intro F'
    let regMonoF' := regularMonoOfMono F'.m
    exact (RegularMono.lift' F'.m (MonoEpiFactorisation f).m (MonoEpiFactorisationEqualisationHelp f F')).2
  }

noncomputable def MonoEpiImageFactorisation (f : A ⟶ B) : ImageFactorisation f where
  F := MonoEpiFactorisation f
  isImage := MonoEpiFactorisationIsImage f

instance MonoEpiHasImage (f : A ⟶ B) : HasImage f where
  exists_image := ⟨MonoEpiImageFactorisation f⟩

instance hasImages : HasImages C where
  has_image := fun f ↦ MonoEpiHasImage f

omit [RegularMonoCategory C] [HasPushouts C]

noncomputable def SplitEpiEqualizerιOfImage (f : A ⟶ B) [HasImage f] (Z : C) (a b : image f ⟶ Z) (h : factorThruImage f ≫ a = factorThruImage f ≫ b) : SplitEpi (equalizer.ι a b) where
  section_ := by {
    let F : MonoFactorisation f := {
      I := equalizer a b
      m := equalizer.ι a b ≫ image.ι f
      e := equalizer.lift _ h
    }
    exact image.lift F
  }

instance FactorThruImageEpi (f : A ⟶ B) [HasImage f] : Epi (factorThruImage f) where
  left_cancellation := by {
    intro Z a b h
    let epi := SplitEpi.epi (SplitEpiEqualizerιOfImage f Z a b h)
    exact eq_of_epi_equalizer
  }
