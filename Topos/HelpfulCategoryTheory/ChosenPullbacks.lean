import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory Category Limits

namespace CategoryTheory.Limits

universe u v

structure ChosenPullback {C : Type u} [Category.{v} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) where
  /-- A choice of a cone for the pair 'f : X ⟶ Z', 'g : Y ⟶ Z' of morphisms with the same target.-/
  pullbackCone : PullbackCone f g
  /-- The chosen cone is a limit-/
  isLimit : IsLimit pullbackCone

abbrev ChosenPullbacks (C : Type u) [Category.{v} C] :=
  ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), ChosenPullback f g

class ChosenPushout {C : Type u} [Category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) where
  /-- A choice of a cone for the pair 'f : X ⟶ Z', 'g : Y ⟶ Z' of morphisms with the same target.-/
  pushoutCocone : PushoutCocone f g
  /-- The chosen cone is a limit-/
  isColimit : IsColimit pushoutCocone

abbrev ChosenPushouts (C : Type u) [Category.{v} C] :=
  ∀ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), ChosenPushout f g

variable {C : Type u} [Category.{v} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (pb : ChosenPullback f g)

abbrev ChosenPullback.pt : C := pb.pullbackCone.pt

abbrev ChosenPullback.cone := pb.pullbackCone

/-- The first projection of the chosen pullback of `f` and `g`. -/
abbrev ChosenPullback.fst : pb.pt ⟶ X := pb.cone.fst

/-- The second projection of the chosen pullback of `f` and `g`. -/
abbrev ChosenPullback.snd : pb.pt ⟶ Y := pb.cone.snd

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `chosenpullback.lift : W ⟶ chosenpullback f g`. -/
abbrev ChosenPullback.lift {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : W ⟶ pb.pt :=
  pb.isLimit.lift (PullbackCone.mk h k w)

abbrev ChosenPullback.isPullback : IsPullback pb.fst pb.snd f g := IsPullback.of_isLimit pb.isLimit

@[reassoc]
theorem ChosenPullback.lift_fst {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pb.lift h k w ≫ pb.fst = h :=
  pb.isLimit.fac (PullbackCone.mk h k w) _

@[reassoc]
theorem ChosenPullback.lift_snd {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pb.lift h k w ≫ pb.snd = k :=
  pb.isLimit.fac (PullbackCone.mk h k w) _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ chosenpullback f g` such that `l ≫ chosenpullback.fst = h` and `l ≫ chosenpullback.snd = k`. -/
def chosenpullback.lift' {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : { l : W ⟶ chosenpullback f g // l ≫ chosenpullback.fst f g = h ∧ l ≫ chosenpullback.snd f g = k } :=
  ⟨lift h k w, lift_fst _ _ _, lift_snd _ _ _⟩

@[reassoc]
theorem chosenpullback.condition : fst f g ≫ f = snd f g ≫ g :=
  PullbackCone.condition _

/-- Two morphisms into a chosen pullback are equal if their compositions with the chosen pullback morphisms are equal -/
@[ext 1100]
theorem chosenpullback.hom_ext {X : C} {W : C} {k l : W ⟶ chosenpullback f g} (h₀ : k ≫ fst f g = l ≫ fst f g) (h₁ : k ≫ snd f g = l ≫ snd f g) : k = l :=
  IsLimit.hom_ext (isLimit f g) fun j ↦ PullbackCone.equalizer_ext (ChosenPullbacks.pullbackCone f g) h₀ h₁ j

variable (f g)

/-- The chosen pullback cone built from the pullback projections is a pullback. -/
def chosenpullbackIsPullback : IsLimit (PullbackCone.mk (chosenpullback.fst f g) (chosenpullback.snd f g) chosenpullback.condition) :=
  PullbackCone.mkSelfIsLimit <| chosenpullback.isLimit f g

variable {C : Type u} [Category.{v} C] [ChosenPushouts C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

abbrev chosenpushout : C := (ChosenPushouts.pushoutCocone f g).pt

abbrev chosenpushout.cocone := ChosenPushouts.pushoutCocone f g

/-- The first projection of the chosen pullback of `f` and `g`. -/
abbrev chosenpushout.inl : Y ⟶ chosenpushout f g := (cocone f g).inl

/-- The second projection of the chosen pullback of `f` and `g`. -/
abbrev chosenpushout.inr : Z ⟶ chosenpushout f g := (cocone f g).inr

variable {f g}

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `chosenpushout.desc : chosenpushout f g ⟶ W`. -/
abbrev chosenpushout.desc {W : C} (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : chosenpushout f g ⟶ W :=
  (ChosenPushouts.isColimit f g).desc (PushoutCocone.mk h k w)

variable (f g)

/-- The cone associated to a pullback is a limit cone. -/
abbrev chosenpushout.isColimit : IsColimit (cocone f g) :=
  ChosenPullbacks.isLimit f g

variable {f g}

@[reassoc]
theorem chosenpullback.lift_fst {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : lift h k w ≫ fst f g = h :=
  (isLimit f g).fac (PullbackCone.mk h k w) _

@[reassoc]
theorem chosenpullback.lift_snd {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : lift h k w ≫ snd f g = k :=
  (isLimit f g).fac (PullbackCone.mk h k w) _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ chosenpullback f g` such that `l ≫ chosenpullback.fst = h` and `l ≫ chosenpullback.snd = k`. -/
def chosenpullback.lift' {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : { l : W ⟶ chosenpullback f g // l ≫ chosenpullback.fst f g = h ∧ l ≫ chosenpullback.snd f g = k } :=
  ⟨lift h k w, lift_fst _ _ _, lift_snd _ _ _⟩

@[reassoc]
theorem chosenpullback.condition : fst f g ≫ f = snd f g ≫ g :=
  PullbackCone.condition _

/-- Two morphisms into a chosen pullback are equal if their compositions with the chosen pullback morphisms are equal -/
@[ext 1100]
theorem chosenpullback.hom_ext {X : C} {W : C} {k l : W ⟶ chosenpullback f g} (h₀ : k ≫ fst f g = l ≫ fst f g) (h₁ : k ≫ snd f g = l ≫ snd f g) : k = l :=
  IsLimit.hom_ext (isLimit f g) fun j ↦ PullbackCone.equalizer_ext (ChosenPullbacks.pullbackCone f g) h₀ h₁ j

variable (f g)

/-- The chosen pullback cone built from the pullback projections is a pullback. -/
def chosenpullbackIsPullback : IsLimit (PullbackCone.mk (chosenpullback.fst f g) (chosenpullback.snd f g) chosenpullback.condition) :=
  PullbackCone.mkSelfIsLimit <| chosenpullback.isLimit f g
