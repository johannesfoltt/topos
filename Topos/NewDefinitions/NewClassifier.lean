/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Topos.HelpfulCategoryTheory.ChosenTerminalObjects
import Topos.HelpfulCategoryTheory.CartesianMonoidalCategoryAdditions
import Topos.HelpfulCategoryTheory.PullbackProd
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import Mathlib.CategoryTheory.Subobject.Basic

/-!

# Subobject Classifier

We define what it means for a morphism in a category to be a subobject
classifier as `CategoryTheory.HasClassifier`. The reason for this
naming convention is to distinguish this internal categorical notion of
a subobject classifier from a classifier of terms of type `Subobject B`
for `B : C`.

c.f. the following Lean 3 code, where similar work was done:
https://github.com/b-mehta/topos/blob/master/src/subobject_classifier.lean

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Classifier C` is the data of a subobject classifier
  in `C`.

* `CategoryTheory.HasClassifier C` says that there is at least one
  subobject classifier.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and
  therefore regular) monomorphism.

* `MonoClassifier.balanced` shows that any category with a subobject classifier
  is balanced. This follows from the fact that every monomorphism is the
  pullback of a regular monomorphism (the truth morphism).

## Notation

* if `m` is a monomorphism, `χ_ m` denotes characteristic map of `m`,
  which is the corresponding map to the subobject classifier.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

-/

universe u v u₀ v₀

open CategoryTheory Category Limits Functor ChosenTerminalObject MonoidalCategory CartesianMonoidalCategory

variable (C : Type u) [Category.{v} C] [ChosenTerminalObject C]

namespace CategoryTheory

/-- A morphism `t : ⊤_ C ⟶ Ω` from the terminal object of a category `C`
is a subobject classifier if, for every monomorphism `m : U ⟶ X` in `C`,
there is a unique map `χ : X ⟶ Ω` such that the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
terminal.from U               χ
      |                       |
      v                       v
    ⊤_ C --------t----------> Ω
```
-/
class Classifier where
  /-- The target of the truth morphism -/
  {Ω : C}
  /-- the truth morphism for a subobject classifier -/
  t_ : ⊤_ ⟶ Ω
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  char {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `char m` forms the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (from_ U) (char m) t_
  /-- `char m` is the only map `X ⟶ Ω` which forms the appropriate pullback square. -/
  uniq {U X : C} {m : U ⟶ X} [Mono m] {χ : X ⟶ Ω} (hχ : IsPullback m (from_ U) χ t_) :
    χ = char m

/-
/-- A category `C` has a subobject classifier if there is at least one subobject classifier. -/
class HasClassifier : Prop where
  /-- There is some classifier. -/
  exists_classifier : Nonempty (Classifier C)
-/

namespace Classifier

variable {C} [Classifier C]

abbrev χ_ {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω := char m

@[reassoc]
lemma comm {U X : C} (m : U ⟶ X) [Mono m] : m ≫ (char m) = from_ _ ≫ t_ := (isPullback m).w

lemma char_true : 𝟙 (Ω : C) = χ_ t_ := by {
  apply uniq
  rw [from_self]
  exact IsPullback.of_id_snd
}

lemma char_iso_hom {U U' X : C} (m : U ⟶ X) [Mono m] (i : U' ≅ U) : χ_ (i.hom ≫ m) = χ_ (m) := by {
  apply uniq
  apply IsPullback.of_iso (isPullback (i.hom ≫ m)) i (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp
}

lemma char_iso_inv {U U' X : C} (m : U ⟶ X) [Mono m] (i : U ≅ U') : χ_ (i.inv ≫ m) = χ_ (m) := char_iso_hom m i.symm

lemma prodCompClassEqClassOfComp [CartesianMonoidalCategory C] {U X : C} (m : U ⟶ X) [Mono m] : fst _ _ ≫ χ_ m = χ_ ((m) ⊗ (𝟙 (𝟙_ C))) := by {
  apply uniq
  have TOP := IsPullback.isPullbackTensorFst m
  have BOT := isPullback m
  have PB := IsPullback.paste_vert TOP BOT
  simp at PB
  rw [toUnit_unique (toUnit (𝟙_ C)) (𝟙 (𝟙_ C))] at PB
  assumption
}

lemma pred_eq_char_of_pullback {X : C} (f : X ⟶ Ω) [HasPullback f t_] : χ_ (pullback.fst f t_) = f := by {
  symm
  apply uniq
  rw [ChosenTerminalObject.hom_ext (from_ (pullback f t_)) (pullback.snd f t_)]
  exact IsPullback.of_hasPullback f t_
}

/-- `c.t` is a regular monomorphism (because it is split). -/
noncomputable instance truthIsRegularMono : RegularMono (t_ : ⊤_ ⟶ (Ω : C)) :=
  RegularMono.ofIsSplitMono (t_)

/-- The following diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
-/
noncomputable instance monoIsRegularMono {A B : C} (m : A ⟶ B) [Mono m] : RegularMono m :=
  regularOfIsPullbackFstOfRegular (isPullback m).w (isPullback m).isLimit

instance regularMono : IsRegularMonoCategory C where
  regularMonoOfMono := fun f ↦ ⟨monoIsRegularMono f⟩

/-- `C` is a balanced category.  -/
instance balanced : Balanced C where
  isIso_of_mono_of_epi := fun f => isIso_of_epi_of_strongMono f

instance : Balanced Cᵒᵖ := balanced_opposite

/-- If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
instance reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

/-- If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
instance reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D]
(F : Cᵒᵖ ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F


/-- The predicate on `X` which corresponds to the subobject `𝟙 X: X ⟶ X`. -/
abbrev Predicate.true_ (B : C) : B ⟶ Ω := from_ B ≫ t_

variable [CartesianMonoidalCategory C]

/--
  The equality predicate on `X ⊗ X`.
-/
abbrev Predicate.eq (X : C) : X ⊗ X ⟶ Ω := char (diag X)

/-- The lift `X ⟶ B ⨯ B` of a morphism with itself, when composed
with `predicate.eq B`, is true.
-/
lemma Predicate.lift_eq {X B : C} (b : X ⟶ B) : lift b b ≫ Predicate.eq B  = Predicate.true_ X := by {
  rw [← @comp_diag, assoc, comm, ← assoc, comp_from]
}

/-- Two maps in a topos are equal if their lift composed with
the equality predicate on `B ⨯ B` is true.
In other words, this combined with `Predicate.lift_eq` states that
`Predicate.eq` is able to distinguish whether two morphisms are equal.
-/
lemma Predicate.eq_of_lift_eq {X B : C} {b b' : X ⟶ B} (comm' : lift b b' ≫ Predicate.eq B = Predicate.true_ X) : b = b' := by {
  dsimp only [Predicate.true_] at comm'
  have t : (isPullback _).lift _ _ comm' ≫ (CartesianMonoidalCategory.diag _) = lift b b' := IsPullback.lift_fst (isPullback (CartesianMonoidalCategory.diag B)) (lift b b') (from_ X) comm'
  rw [comp_diag] at t
  have t₁ := congrArg (fun k ↦ k ≫ fst _ _) t; simp at t₁
  have t₂ := congrArg (fun k ↦ k ≫ snd _ _) t; simp at t₂
  aesop_cat
}

omit [CartesianMonoidalCategory C] in
theorem comp_char {U S X : C} (u : U ⟶ S) [Mono u] (s : S ⟶ X) [Mono s] : s ≫ χ_ (u ≫ s) = χ_ u := by {
  apply uniq
  have pbL := IsPullback.comp_IsPullback u s
  have pbR := isPullback (u ≫ s)
  have pb := IsPullback.paste_vert pbL pbR
  simp at pb
  exact pb
}

omit [Classifier C] [CartesianMonoidalCategory C] in
lemma Iso_inv (c : Classifier C) (d : Classifier C) : c.χ_ (d.t_) ≫ d.χ_ (c.t_) = 𝟙 d.Ω := by {
  rw [char_true]
  apply uniq
  rw [ChosenTerminalObject.hom_ext (from_ ⊤_) ((from_ ⊤_) ≫ (from_ ⊤_))]
  exact IsPullback.paste_vert (c.isPullback d.t_) (d.isPullback c.t_)
}

def Iso [c : Classifier C] [d : Classifier C] : c.Ω ≅ d.Ω where
  hom := d.χ_ c.t_
  inv := c.χ_ d.t_
  hom_inv_id := Iso_inv d c
  inv_hom_id := Iso_inv c d

/-
Do as needed
variable [HasPullbacks C]
variable (classifier : Classifier C)

variable (B : C) (φ : B ⟶ classifier.Ω)
variable (s : Cone (cospan φ classifier.t))

example : (Subobject.mk (pullback.fst φ classifier.t)).arrow =
(Subobject.underlyingIso (pullback.fst φ classifier.t)).hom ≫ pullback.fst φ classifier.t := by
  exact Eq.symm (Subobject.underlyingIso_hom_comp_eq_mk (pullback.fst φ classifier.t))

example : pullback.fst φ classifier.t ≫ φ = pullback.snd φ classifier.t ≫ classifier.t := by
  exact pullback.condition

-- TODO: refactor so this `omit` is unnecessary.
omit [HasClassifier C] in
lemma subobject_pullback {B : C} (φ : B ⟶ classifier.Ω) :
IsPullback (Subobject.mk (pullback.fst φ classifier.t)).arrow
(terminal.from (Subobject.underlying.obj (Subobject.mk (pullback.fst φ classifier.t))))
φ classifier.t := by
  apply IsPullback.of_iso_pullback ?_ (Subobject.underlyingIso (pullback.fst φ classifier.t))
  · exact Subobject.underlyingIso_hom_comp_eq_mk (pullback.fst φ classifier.t)
  · exact terminal.hom_ext
      ((Subobject.underlyingIso (pullback.fst φ classifier.t)).hom ≫ pullback.snd φ classifier.t)
      (terminal.from (Subobject.underlying.obj (Subobject.mk (pullback.fst φ classifier.t))))
  · apply CommSq.mk
    rw [(Subobject.underlyingIso_hom_comp_eq_mk (pullback.fst φ classifier.t)).symm,
    assoc, pullback.condition, ←assoc]
    have h : ((Subobject.underlyingIso (pullback.fst φ classifier.t)).hom
    ≫ pullback.snd φ classifier.t) = terminal.from _ := by apply terminal.hom_ext
    rw [h]

variable (S : Subobject B)

def subobjectIso1 : Subobject.underlying.obj
(Subobject.mk (pullback.fst (classifier.char S.arrow) classifier.t))
≅ pullback (classifier.char S.arrow) classifier.t :=
  Subobject.underlyingIso (pullback.fst (classifier.char S.arrow) classifier.t)

def subobjectIso2 :
pullback (classifier.char S.arrow) classifier.t ≅ Subobject.underlying.obj S where
  hom :=
    (classifier.isPullback S.arrow).lift
    (pullback.fst (classifier.char S.arrow) classifier.t)
    (pullback.snd (classifier.char S.arrow) classifier.t)
    pullback.condition
  inv := pullback.lift S.arrow (terminal.from _) (classifier.isPullback S.arrow).w

def subobjectIso3 :
Subobject.underlying.obj (Subobject.mk (pullback.fst (classifier.char S.arrow) classifier.t)) ≅
Subobject.underlying.obj S where
  hom := (subobjectIso1 classifier B S).hom ≫ (subobjectIso2 classifier B S).hom
  inv := (subobjectIso2 classifier B S).inv ≫ (subobjectIso1 classifier B S).inv

variable [HasPullbacks C]

def subobjectEquiv (B : C) : (B ⟶ Ω) ≃ Subobject B where
  toFun := fun φ => Subobject.mk (pullback.fst φ t_)
  invFun := fun S => χ_ S.arrow
  left_inv := by
    intro φ
    simp
    symm
    apply uniq
    exact subobject_pullback classifier φ
  right_inv := by
    intro S
    ext
    · exact subobjectIso3 classifier B S
    · simp [subobjectIso3, subobjectIso1, subobjectIso2]


lemma subobjectClassifierExt {B X Y} {f : X ⟶ B} {g : Y ⟶ B} [Mono f] [Mono g] (h : classifier.char f = classifier.char g) : Subobject.mk f = Subobject.mk g := by {
  sorry
}

def subobjectRepresentableByClassifier : RepresentableBy (Subobject.functor C) classifier.Ω where
  homEquiv := fun {X} ↦ subobjectEquiv classifier X
  homEquiv_comp := by {
    intro X Y f g
    unfold subobjectEquiv; simp
    rw [@Subobject.pullback_obj]
    apply subobjectClassifierExt classifier
    sorry
  }

def classifierHomEquiv (B : C) : (B ⟶ classifier.Ω) ≃ (B ⟶ Ω C) where
  toFun := fun φ ↦
  (subobjectEquiv HasClassifier.exists_classifier.some _).invFun (
    (subobjectEquiv classifier _).toFun φ)
  invFun := fun φ' ↦
  (subobjectEquiv classifier _).invFun (
    (subobjectEquiv HasClassifier.exists_classifier.some _).toFun φ')
  left_inv := by intro φ; simp
  right_inv := by intro φ'; simp

variable {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ classifier.Ω)

instance : Mono (classifier.t) := IsSplitMono.mono classifier.t

def classifierIso (classifier : Classifier C) : classifier.Ω ≅ Ω C := by
  apply Yoneda.ext (
    p := fun φ ↦ (classifierHomEquiv classifier _).toFun φ) (
    q := fun φ' ↦ (classifierHomEquiv classifier _).invFun φ')
  · simp
  · simp
  · intro Z Z' f g
    dsimp
    /-
    show (subobjectEquiv HasClassifier.exists_classifier.some _).invFun (
    (subobjectEquiv classifier _).toFun (f ≫ g))
    = f ≫ (subobjectEquiv HasClassifier.exists_classifier.some _).invFun (
    (subobjectEquiv classifier _).toFun g)
    -/
    show χ_ (Subobject.mk (pullback.fst (f ≫ g) classifier.t)).arrow
    = f ≫ χ_ (Subobject.mk (pullback.fst g (classifier.t))).arrow
    symm
    apply HasClassifier.unique
    apply IsPullback.of_iso_pullback
    · apply CommSq.mk
      /-

      -/
      let l' : Subobject.underlying.obj (Subobject.mk (pullback.fst (f ≫ g) classifier.t))
      ≅ pullback (f ≫ g) classifier.t :=
        Subobject.underlyingIso (pullback.fst (f ≫ g) classifier.t)

      have h : (Subobject.mk (pullback.fst (f ≫ g) classifier.t)).arrow
      = (Subobject.underlyingIso (pullback.fst (f ≫ g) classifier.t)).hom
      ≫ (pullback.fst (f ≫ g) classifier.t) :=
        Eq.symm (Subobject.underlyingIso_hom_comp_eq_mk (pullback.fst (f ≫ g) classifier.t))
      rw [(Subobject.underlyingIso_hom_comp_eq_mk (pullback.fst (f ≫ g) classifier.t)).symm]
      rw [assoc]
      let lift : pullback (f ≫ g) classifier.t ⟶ pullback g classifier.t := by
        refine pullback.lift (pullback.fst (f ≫ g) classifier.t ≫ f) (terminal.from _) ?_
        have h' : terminal.from (pullback (f ≫ g) classifier.t) = pullback.snd _ _ := by
          apply terminal.hom_ext
        rw [assoc, pullback.condition, h']
      have h' : (pullback.fst _ _) ≫ f = lift ≫ (pullback.fst _ _) := by
        symm; apply pullback.lift_fst
      rw [←(assoc _ f), h', assoc]
      -- let lift₁ :
      sorry
    · sorry
    · sorry
    · sorry
-/


end Classifier
