/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Functor.EpiMono
import Topos.Category


namespace CategoryTheory

universe u v u₁ v₁

open CategoryTheory Category Limits Functor

variable {C : Type u} [Category.{v} C]

abbrev classifying {Ω Ω₀ U X : C} (t : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) :=
  HasPullbackTop f χ t

structure IsSubobjectClassifier {Ω Ω₀ : C} (t : Ω₀ ⟶ Ω) where
  classifier_of : ∀ {U X : C} (f : U ⟶ X) [Mono f], X ⟶ Ω
  classifies : ∀ {U X : C} (f : U ⟶ X) [Mono f], classifying t f (classifier_of f)
  unique' : ∀ {U X : C} (f : U ⟶ X) [Mono f] (χ : X ⟶ Ω), classifying t f χ → χ = classifier_of f

variable (C)

class HasSubobjectClassifier where
  Ω : C
  Ω₀ : C
  t : Ω₀ ⟶ Ω
  t_mono : Mono t
  is_subobject_classifier : IsSubobjectClassifier t

variable [HasSubobjectClassifier C]

namespace Classifier

abbrev Ω : C := HasSubobjectClassifier.Ω

def Ω₀ : C := HasSubobjectClassifier.Ω₀

def t : Ω₀ C ⟶ Ω C := HasSubobjectClassifier.t

instance t_mono : Mono (t C) := HasSubobjectClassifier.t_mono

def SubobjectClassifier_IsSubobjectClassifier : IsSubobjectClassifier (t C) := HasSubobjectClassifier.is_subobject_classifier

variable {C}

def ClassifierOf {U X : C} (f : U ⟶ X) [Mono f] : X ⟶ Ω C :=
  (SubobjectClassifier_IsSubobjectClassifier C).classifier_of f

def Classifies {U X : C} (f : U ⟶ X) [Mono f] : classifying (t C) f (ClassifierOf f) :=
  (SubobjectClassifier_IsSubobjectClassifier C).classifies f

def unique {U X : C} (f : U ⟶ X) [Mono f] (χ : X ⟶ Ω C) (hχ : classifying (t C) f χ) : χ = ClassifierOf f :=
  (SubobjectClassifier_IsSubobjectClassifier C).unique' f χ hχ

end Classifier



open Classifier

variable {C}

instance uniqueTo_Ω₀ (P : C) : Unique (P ⟶ Ω₀ C) := {
  default := (Classifies (𝟙 _)).top,
  uniq := λ a => by
    rw [← cancel_mono (t C), default, (Classifies (𝟙 _)).comm, id_comp, unique (𝟙 P) (a ≫ t C)]
    exact left_iso_has_pullback_top a (𝟙 P) (t C) _ (id_comp _).symm
}

def terminal_Ω₀ : IsTerminal (Ω₀ C) := IsTerminal.ofUnique (Ω₀ C)

instance has_Terminal : HasTerminal C := hasTerminal_of_unique (Ω₀ C)


instance truth_is_SplitMono : SplitMono (t C) where
  retraction := default

instance truth_IsSplitMono : IsSplitMono (t C) where
  exists_splitMono := ⟨truth_is_SplitMono⟩

noncomputable instance truth_is_RegularMono : RegularMono (t C) :=
  RegularMono.ofIsSplitMono (t C)

theorem Mono_is_RegularMono {A B : C} (m : A ⟶ B) [Mono m] : RegularMono m :=
  regularOfIsPullbackSndOfRegular (Classifies m).comm (Classifies m).pb

/-- A category with a subobject classifier is balanced. -/
def balanced {A B : C} (f : A ⟶ B) [ef : Epi f] [Mono f] : IsIso f :=
  @isIso_limit_cone_parallelPair_of_epi _ _ _ _ _ _ _ (Mono_is_RegularMono f).isLimit ef

instance : Balanced C where
  isIso_of_mono_of_epi := λ f => balanced f

/--
  If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
def reflectsIsomorphisms (D : Type u₂) [Category.{v₂} D] (F : C ⥤ D) [Faithful F] : ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

end CategoryTheory
