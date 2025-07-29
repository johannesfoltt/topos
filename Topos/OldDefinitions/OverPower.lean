import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.OldDefinitions.OverClassifier
import Topos.OldDefinitions.ClassifierMeet
import Topos.OldDefinitions.PullbackClassifier

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

--abbrev pullback_prod_map {A}

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

lemma powerOver.transpose_subobject_meet_condition {B : Over X} (f : (A ⨯_P B) ⟶ classifierOver.Ω HasClassifier.exists_classifier.some) : ((χ_ (transpose_subobject A f)) ∧_C₁ (B.hom ≫ (singleton X) ≫ (inverseImage A.hom))^) = χ_ (transpose_subobject A f) := by {
  have help : singleton X = singleton ((Functor.fromPUnit X).obj A.right) := rfl
  change (χ_ (transpose_subobject A f) ∧_C₁ ((B.hom ≫ Topos.singleton X ≫ inverseImage A.hom)^ : (𝟭 C).obj A.left ⨯ (𝟭 C).obj B.left ⟶ Ω C)) = χ_ (transpose_subobject A f)
  rw [help, pullback_char A.hom B.hom]
  exact meet_comp (pullback.fst (f.left ≫ prod.fst) (t C)) (prod.lift (pullback.fst A.hom B.hom) (pullback.snd A.hom B.hom))
}

lemma powerOver.transpose_equalizer_condition {B : Over X} (f : (A ⨯_P B) ⟶ classifierOver.Ω HasClassifier.exists_classifier.some) : (prod.lift ((χ_ (transpose_subobject A f))^) B.hom) ≫ prod.fst = (prod.lift ((χ_ (transpose_subobject A f))^) B.hom) ≫ pow_t A := by {
  slice_lhs 1 3 => {
    rw [prod.lift_fst, ← transpose_subobject_meet_condition, meet_transpose, transpose_right_inv]
    unfold Power.meet_hom₁
    rw [← comp_id ((χ_ (transpose_subobject A f))^), ← prod.lift_map]
  }
  simp
}

def powerOver.transpose' {B : Over X} (f : (A ⨯_P B) ⟶ classifierOver.Ω HasClassifier.exists_classifier.some) : B ⟶ pow A :=
  homMk (equalizer.lift (prod.lift ((χ_ (transpose_subobject A f))^) B.hom) (transpose_equalizer_condition A f))

lemma powerOver.comm' {B : Over X} (f : (A ⨯_P B) ⟶ classifierOver.Ω HasClassifier.exists_classifier.some) : prod.map (𝟙 B) (transpose' A f) ≫ in_' A = f := sorry
