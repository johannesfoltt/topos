import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.OverClassifier
import Topos.ClassifierMeet

namespace CategoryTheory

open Category Limits Over Power Topos HasClassifier

universe u v

noncomputable section


--Here we assume IsTopos C as a variable, because we need the equalizer, terminal objects, binary products, pullbacks, HasClassifier and HasPowerObjects (we need HasPowerObjects to define the inverse image)

namespace Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X : C}

--Why do I have to do this?
instance : CartesianMonoidalCategory (Over X) := cartesianMonoidalCategory X

--Do this somewhere else
abbrev pullback_prod_hom (A B : Over X) : (Limits.pullback (A.hom) (B.hom)) ⟶ X := (pullback.fst A.hom B.hom) ≫ A.hom

abbrev pullback_prod (A B : Over X) : Over X := mk (pullback_prod_hom A B)

notation A " ⨯_P " B => pullback_prod A B

lemma pullback_prod_snd (A B : Over X) : (A ⨯_P B) = mk ((pullback.snd A.hom B.hom) ≫ B.hom) := by rw [← pullback.condition]

def productIso (A B : Over X) : A ⨯ B ≅ A ⨯_P B := sorry

variable (A : Over X) [CartesianMonoidalCategory C] [IsTopos C]

abbrev powerOver.pow_t : pow A.left ⨯ X ⟶ pow A.left := (𝟙 (pow A.left) ∧_P₂ (singleton X ≫ inverseImage A.hom))

abbrev powerOver.pow : Over X := mk (equalizer.ι prod.fst (powerOver.pow_t A) ≫ prod.snd)

abbrev powerOver.in_hom : (Limits.pullback A.hom (equalizer.ι prod.fst (powerOver.pow_t A) ≫ prod.snd)) ⟶ (HasClassifier.exists_classifier.some.Ω ⨯ X) :=
  prod.lift ((prod.lift (pullback.fst A.hom (equalizer.ι prod.fst (pow_t A) ≫ prod.snd)) (pullback.snd A.hom (equalizer.ι prod.fst (pow_t A) ≫ prod.snd) ≫ (equalizer.ι prod.fst (pow_t A)) ≫ prod.fst)) ≫ (in_ A.left)) (pullback_prod_hom A (pow A))

abbrev powerOver.in_' : (A ⨯_P (pow A)) ⟶ (classifierOver.Ω HasClassifier.exists_classifier.some) := homMk (in_hom A)

abbrev powerOver.transpose_subobject {B : Over X} (f : (A ⨯_P B) ⟶ classifierOver.Ω HasClassifier.exists_classifier.some) : Limits.pullback (f.left ≫ prod.fst) (t C) ⟶ A.left ⨯ B.left :=
  (pullback.fst (f.left ≫ prod.fst) (t C)) ≫ (prod.lift (pullback.fst A.hom B.hom) (pullback.snd A.hom B.hom))

abbrev powerOver.transpose_hom {B : Over X} (f : (A ⨯_P B) ⟶ classifierOver.Ω HasClassifier.exists_classifier.some) : B.left ⟶ (equalizer prod.fst (powerOver.pow_t A)) := by {
  #check (f.left ≫ prod.fst : (A ⨯_P B).left ⟶  Ω C)
  #check (pullback.fst (f.left ≫ prod.fst) (t C))
  #check (prod.lift (pullback.fst A.hom B.hom) (pullback.snd A.hom B.hom) : Limits.pullback A.hom B.hom ⟶ A.left ⨯ B.left)
  #check (pullback.fst (f.left ≫ prod.fst) (t C)) ≫ (prod.lift (pullback.fst A.hom B.hom) (pullback.snd A.hom B.hom) : Limits.pullback A.hom B.hom ⟶ A.left ⨯ B.left)
  #check χ_ (transpose_subobject A f)
  sorry
}
