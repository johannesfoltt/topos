import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.NewDefinitions.NewTopos
import Topos.HelpfulCategoryTheory.PullbackProd
import Topos.HelpfulCategoryTheory.IsEqualizer
import Topos.HelpfulCategoryTheory.PreservesColimitOfIsReflexivePairOfIsCoequalizer

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier PowerObject ChosenPowerObjects Functor

namespace Topos

universe u v
variable {C}
variable [Category.{v, u} C] [Topos C]

noncomputable section

namespace DirectImage

variable {B B' : C} (k : B' ⟶ B) [Mono k]

@[simp]
abbrev e := χ_ ((pullback.fst (in_) (t_)) ≫ (k ⊗ (𝟙 _)))

def directImage : pow B' ⟶ pow B := (e k)^

lemma directImage_id {B : C} : directImage (𝟙 B) = 𝟙 (pow B) := by {
  unfold directImage
  simp
  have h : in_ = χ_ (pullback.fst (in_ : B ⊗ _ ⟶ _) (t_)) := by {
    apply Classifier.uniq
    rw [from_eq_toUnit, toUnit_unique (toUnit _) (pullback.snd in_ t_)]
    exact IsPullback.of_hasPullback (in_ : B ⊗ _ ⟶ _) (t_)
  }
  rw [← h]
  apply PowerObject.uniq
  simp
}

variable {S : C} (m : S ⟶ B') [Mono m]

lemma wDef_comm' : (m ⊗ (𝟙 _)) ≫ ((𝟙 _) ⊗ (name (χ_ m))) ≫ in_ = toUnit _ ≫ t_ := by
  rw [Predicate.NameDef, tensorHom_fst_assoc]
  have h : toUnit (S ⊗ 𝟙_ C) = fst _ _ ≫ toUnit S := CartesianMonoidalCategory.toUnit_unique_iff.mpr trivial
  rw [h, assoc, Classifier.comm]
  simp

lemma wDef_comm : (m ⊗ (name (χ_ m))) ≫ in_ = toUnit _ ≫ t_ := by
  -- for some reason there is an issue rewriting m = m ≫ 𝟙 _ ??
  -- TODO: should be able to wrestle this lemma's statement into the previous lemma's, merging the two
  have h := wDef_comm' m
  rw [tensor_id_comp_id_tensor_assoc] at h
  assumption

def w := pullback.lift (w := wDef_comm m)

lemma transposeOfMapDirectImage {X Y Z: C} (n : X ⟶ Y) [Mono n] (g : Z ⟶ pow X) : (g ≫ directImage n)^ = ((𝟙 Y) ⊗ g) ≫ (e n) := by
  calc ((𝟙 Y) ⊗ (g ≫ directImage n)) ≫ in_ = ((𝟙 Y) ⊗ g) ≫ ((𝟙 Y) ⊗ (directImage n)) ≫ in_ := by rw [id_tensor_comp_assoc]
  _= ((𝟙 Y) ⊗ g) ≫ ((e n)^)^ := rfl
  _= ((𝟙 Y) ⊗ g) ≫ (e n) := by rw [transpose_left_inv]

lemma directImage_NameChar_factors : name (χ_ m) ≫ directImage k = name (χ_ (m ≫ k)) := by
  symm
  apply PowerObject.uniq
  rw [prodCompClassEqClassOfComp]
  apply Classifier.uniq
  have pbU := isPullback (m ⊗ (𝟙 (𝟙_ C)))
  rw [← χ_, ← transpose_left_inv (χ_ (m ⊗ (𝟙 (𝟙_ C)))), ← prodCompClassEqClassOfComp, ← name] at pbU
  unfold transposeInv at pbU
  have pbUR := IsPullback.of_hasPullback (in_ : B' ⊗ _ ⟶ _) (t_)
  have pbUL := IsPullback.of_bot' pbU pbUR
  have pbR := isPullback ((pullback.fst in_ t_ ) ≫ (k ⊗ (𝟙 _)))
  have pbBL := IsPullback.isPullbackOfTensor (IsPullback.id_vert k) (IsPullback.id_horiz ⌜χ_ m⌝)
  have pbL := IsPullback.paste_horiz pbUL pbBL
  have pb := IsPullback.paste_vert pbL pbR
  rw [← ChosenTerminalObject.hom_ext (from_ (S ⊗ (𝟙_ C ))) (_ ≫ _), ← comp_tensor_id, ← χ_, ← e, ← transposeOfMapDirectImage] at pb
  exact pb
