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

namespace Classifier

structure IsClassifier {Ω : C} (t : ⊤_ C ⟶ Ω) where
  char {X : C} (S : Subobject X) : Unique { χ : X ⟶ Ω // IsPullback S.arrow (terminal.from (S : C)) χ t }

variable (C)

class HasClassifier where
  Ω : C
  t : ⊤_ C ⟶ Ω
  is_subobject_classifier : IsClassifier t

variable [HasClassifier C]

abbrev Ω : C := HasClassifier.Ω

def t : ⊤_ C ⟶ Ω C := HasClassifier.t

def Classifier_IsClassifier : IsClassifier (t C) :=
  HasClassifier.is_subobject_classifier

variable {C}
variable {X : C} (χ : X ⟶ Ω C) (S : Subobject X)

def ClassifierOf : { χ : X ⟶ Ω C // IsPullback S.arrow (terminal.from (S : C)) χ (t C) } :=
  ((Classifier_IsClassifier C).char S).default

def ClassifierMap : X ⟶ Ω C := (ClassifierOf S).val

instance : Inhabited { χ : X ⟶ Ω C // IsPullback S.arrow (terminal.from (S : C)) χ (t C) } :=
  Inhabited.mk (ClassifierOf S)

def ClassifierPb : IsPullback S.arrow (terminal.from (S : C)) (ClassifierOf S) (t C) := 
  (ClassifierOf S).prop

def ClassifierComm : S.arrow ≫ ClassifierOf S = terminal.from _ ≫ t C := (ClassifierPb S).w

def unique (χ : X ⟶ Ω C) (hχ : IsPullback S.arrow (terminal.from _) χ (t C)) : χ = ClassifierOf S := by
  have h := ((Classifier_IsClassifier C).char S).uniq (Subtype.mk χ hχ)
  apply_fun (λ x => x.val) at h
  assumption

noncomputable def ClassifierCone : PullbackCone (ClassifierOf S).val (t C) :=
  PullbackCone.mk S.arrow (terminal.from _) (ClassifierComm S)

noncomputable def ClassifierPullback : IsLimit (PullbackCone.mk S.arrow (terminal.from _) (ClassifierComm S)) := 
  (ClassifierPb S).isLimit'.some

noncomputable def ClassifierCone_into {Z : C} (g : Z ⟶ X) (comm' : g ≫ (ClassifierOf S).val = (terminal.from Z ≫ t C)) :
  Z ⟶ (S : C) := IsPullback.lift (ClassifierPb S) _ _ comm'

def ClassifierCone_into_comm {Z : C} (g : Z ⟶ X) (comm' : g ≫ ClassifierMap S = (terminal.from Z ≫ t C)) :
    ClassifierCone_into (comm' := comm') ≫ S.arrow = g :=
  IsPullback.lift_fst (ClassifierPb S) _ _ comm'

variable {U : C} (f : U ⟶ X) [Mono f]

def ClassifierOfMono := ClassifierOf (Subobject.mk f)

def ClassifierMonoPb : IsPullback f (terminal.from _) (ClassifierOfMono f) (t C) := by
  have h : IsPullback f ((Subobject.underlyingIso f).inv) (𝟙 _) (Subobject.mk f).arrow := by
    apply IsPullback.of_vert_isIso; simp
  have h' := IsPullback.paste_vert h (ClassifierPb (Subobject.mk f))
  simp at h'
  assumption

def ClassifierMonoComm : f ≫ (ClassifierOfMono f) = (terminal.from _) ≫ (t C) :=
  (ClassifierMonoPb f).w

noncomputable def ClassifierMonoCone_into {Z : C} (g : Z ⟶ X) (comm' : g ≫ (ClassifierOfMono f) = terminal.from Z ≫ t C) :
    Z ⟶ U :=
  IsPullback.lift (ClassifierMonoPb f) g _ comm'

def ClassifierMonoCone_into_comm {Z : C} (g : Z ⟶ X) (comm' : g ≫ (ClassifierOfMono f) = terminal.from Z ≫ t C) :
    ClassifierMonoCone_into (comm' := comm') ≫ f = g :=
  IsPullback.lift_fst (ClassifierMonoPb f) _ _ comm'

end Classifier

open Classifier

namespace Topos

variable [HasClassifier C]

noncomputable instance truth_is_RegularMono : RegularMono (t C) :=
  RegularMono.ofIsSplitMono (t C)

noncomputable instance Mono_is_RegularMono {A B : C} (m : A ⟶ B) [Mono m] : RegularMono m :=
  regularOfIsPullbackFstOfRegular (ClassifierMonoPb m).w (ClassifierMonoPb m).isLimit

/-- A category with a subobject classifier is balanced. -/
def balanced {A B : C} (f : A ⟶ B) [ef : Epi f] [Mono f] : IsIso f :=
  @isIso_limit_cone_parallelPair_of_epi _ _ _ _ _ _ _ (Mono_is_RegularMono f).isLimit ef

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
