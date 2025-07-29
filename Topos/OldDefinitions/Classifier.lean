/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.Tactic.ApplyFun
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Topos.HelpfulCategoryTheory.PullbackProd

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

open CategoryTheory Category Limits Functor

variable (C : Type u) [Category.{v} C] [HasTerminal C]

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
structure Classifier where
  /-- The target of the truth morphism -/
  {Ω : C}
  /-- the truth morphism for a subobject classifier -/
  t : ⊤_ C ⟶ Ω
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  char {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `char m` forms the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (terminal.from U) (char m) t
  /-- `char m` is the only map `X ⟶ Ω` which forms the appropriate pullback square. -/
  uniq {U X : C} (m : U ⟶ X) [Mono m] (χ : X ⟶ Ω) (hχ : IsPullback m (terminal.from U) χ t) :
    χ = char m


/-- A category `C` has a subobject classifier if there is at least one subobject classifier. -/
class HasClassifier : Prop where
  /-- There is some classifier. -/
  exists_classifier : Nonempty (Classifier C)

namespace HasClassifier

variable [HasClassifier C]

noncomputable section

/-- Notation for the object in an arbitrary choice of a subobject classifier -/
abbrev Ω : C := HasClassifier.exists_classifier.some.Ω

/-- Notation for the "truth arrow" in an arbitrary choice of a subobject classifier -/
abbrev t : ⊤_ C ⟶ Ω C := HasClassifier.exists_classifier.some.t

variable {C}
variable {U X : C} (m : U ⟶ X) [Mono m]

/-- returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]` -/
def characteristicMap : X ⟶ Ω C :=
  HasClassifier.exists_classifier.some.char m

/-- shorthand for the characteristic morphism, `ClassifierOf m` -/
abbrev χ_ := characteristicMap m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
is a pullback square.
-/
lemma isPullback : IsPullback m (terminal.from U) (χ_ m) (t C) :=
  HasClassifier.exists_classifier.some.isPullback m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
commutes.
-/
@[reassoc]
lemma comm : m ≫ (χ_ m) = terminal.from _ ≫ t C := (isPullback m).w

/-- `characteristicMap m` is the only map for which the associated square
is a pullback square.
-/
lemma unique (χ : X ⟶ Ω C) (hχ : IsPullback m (terminal.from _) χ (t C)) : χ = χ_ m :=
  HasClassifier.exists_classifier.some.uniq m χ hχ

lemma prodCompClassEqClassOfComp [CartesianMonoidalCategory C] : prod.fst ≫ χ_ m = χ_ (prod.map (m) (𝟙 (⊤_ C))) := by {
  apply unique
  have TOP := IsPullback.isPullbackProdFst m
  have BOT := isPullback m
  have PB := IsPullback.paste_vert TOP BOT
  rw [terminal.hom_ext (terminal.from (⊤_ C)) (𝟙 (⊤_ C)), terminal.comp_from prod.fst] at PB
  exact PB
}

/-- `t C` is a regular monomorphism (because it is split). -/
noncomputable instance truthIsRegularMono : RegularMono (t C) :=
  RegularMono.ofIsSplitMono (t C)

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

def subobjectEquiv (B : C) : (B ⟶ classifier.Ω) ≃ Subobject B where
  toFun := fun φ => Subobject.mk (pullback.fst φ classifier.t)
  invFun := fun S => classifier.char S.arrow
  left_inv := by
    intro φ
    simp
    symm
    apply classifier.uniq
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


end
end CategoryTheory.HasClassifier
