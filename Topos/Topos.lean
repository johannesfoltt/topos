/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Topos.Power
import Topos.SubobjectClassifier

namespace CategoryTheory

open Category Limits Classifier Power

universe u v

variable (C : Type u) [Category.{v} C]

class Topos where
  [finite_limits : HasPullbacks C]
  [subobject_classifier : HasSubobjectClassifier C]
  [cartesian_closed : HasPowerObjects C]

attribute [instance] Topos.finite_limits Topos.subobject_classifier Topos.cartesian_closed

variable [Topos C] {C}

namespace Topos

def Predicate.true_ (B : C) : B ⟶ Ω C := (uniqueTo_Ω₀ B).default ≫ (t C)

noncomputable section

/--
  The equality predicate on B ⨯ B.
-/
def Predicate.eq (B : C) : B ⨯ B ⟶ Ω C := ClassifierOf (diag B)

/--
  The "singleton" map {•}_B : B ⟶ Pow B.
  In Set, this map sends b ∈ B to the singleton set {b}.
-/
def singleton (B : C) : B ⟶ Pow B := P_transpose (Predicate.eq B)


instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := sorry -- TODO: fill in proof

def Predicate.isSingleton (B : C) : Pow B ⟶ Ω C := ClassifierOf (singleton B)



end
end Topos
end CategoryTheory
