/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts


namespace CategoryTheory

universe u v u₀ v₀

open CategoryTheory Category Limits Functor

variable {C : Type u} [Category.{v} C] [HasTerminal C]

structure classifying {U X Ω : C} (t : ⊤_ C ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) where
  comm : f ≫ χ = (terminal.from U) ≫ t
  pb : IsLimit (PullbackCone.mk f (terminal.from U) comm)

structure IsSubobjectClassifier {Ω : C} (t : ⊤_ C ⟶ Ω) where
  classifier_of : ∀ {U X : C} (f : U ⟶ X) [Mono f], X ⟶ Ω
  classifies : ∀ {U X : C} (f : U ⟶ X) [Mono f], classifying t f (classifier_of f)
  unique' : ∀ {U X : C} (f : U ⟶ X) [Mono f] (χ : X ⟶ Ω), classifying t f χ → χ = classifier_of f

variable (C)

class HasSubobjectClassifier where
  Ω : C
  t : ⊤_ C ⟶ Ω
  is_subobject_classifier : IsSubobjectClassifier t

variable [HasSubobjectClassifier C]

namespace Classifier

abbrev Ω : C := HasSubobjectClassifier.Ω

def t : ⊤_ C ⟶ Ω C := HasSubobjectClassifier.t

def SubobjectClassifier_IsSubobjectClassifier : IsSubobjectClassifier (t C) :=
  HasSubobjectClassifier.is_subobject_classifier

variable {C}
variable {U X : C} (χ : X ⟶ Ω C) (f : U ⟶ X) [Mono f]

def ClassifierOf : X ⟶ Ω C :=
  (SubobjectClassifier_IsSubobjectClassifier C).classifier_of f

def Classifies : classifying (t C) f (ClassifierOf f) :=
  (SubobjectClassifier_IsSubobjectClassifier C).classifies f

def ClassifierComm : f ≫ ClassifierOf f = terminal.from _ ≫ t C :=
  ((SubobjectClassifier_IsSubobjectClassifier C).classifies f).comm

def ClassifierPb : IsLimit (PullbackCone.mk f (terminal.from _) (ClassifierComm _)) :=
  ((SubobjectClassifier_IsSubobjectClassifier C).classifies f).pb

def unique (χ : X ⟶ Ω C) (hχ : classifying (t C) f χ) : χ = ClassifierOf f :=
  (SubobjectClassifier_IsSubobjectClassifier C).unique' f χ hχ

noncomputable def ClassifierCone : PullbackCone (ClassifierOf f) (t C) :=
  PullbackCone.mk f (terminal.from U) (ClassifierComm f)

theorem ClassifierPullback : IsPullback f (terminal.from U) (ClassifierOf f) (t C) :=
  IsPullback.of_isLimit (ClassifierPb f)

noncomputable def ClassifierCone_into {Z : C} (g : Z ⟶ X) (comm' : g ≫ (ClassifierOf f) = (terminal.from Z ≫ t C)) :
  Z ⟶ U := PullbackCone.IsLimit.lift (Classifies f).pb _ _ comm'

def ClassifierCone_into_comm {Z : C} (g : Z ⟶ X) (comm' : g ≫ (ClassifierOf f) = (terminal.from Z ≫ t C)) :
  ClassifierCone_into (comm' := comm') ≫ f = g :=
    PullbackCone.IsLimit.lift_fst (ht := ClassifierPb f) (h := g) (k := terminal.from _) (w := comm')

end Classifier

open Classifier

variable {C}

namespace Topos

noncomputable instance truth_is_RegularMono : RegularMono (t C) :=
  RegularMono.ofIsSplitMono (t C)

noncomputable instance Mono_is_RegularMono {A B : C} (m : A ⟶ B) [Mono m] : RegularMono m :=
  regularOfIsPullbackFstOfRegular (Classifies m).comm (Classifies m).pb

/-- A category with a subobject classifier is balanced. -/
def balanced {A B : C} (f : A ⟶ B) [ef : Epi f] [Mono f] : IsIso f :=
  @isIso_limit_cone_parallelPair_of_epi _ _ _ _ _ _ _ (Mono_is_RegularMono f).isLimit ef
  -- isIso_limit_cone_parallelPair_of_epi (h := (Mono_is_RegularMono f).isLimit) (_ := ef)

instance : Balanced C where
  isIso_of_mono_of_epi := λ f => balanced f

instance : Balanced Cᵒᵖ := balanced_opposite

/--
  If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
def reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] : Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

/--
  If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
def reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D) [Functor.Faithful F] : Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

end Topos
end CategoryTheory
