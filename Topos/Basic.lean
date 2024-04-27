
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
  [has_terminal : HasTerminal C]
  [finite_limits : HasPullbacks C]
  [subobject_classifier : HasSubobjectClassifier C]
  [cartesian_closed : HasPowerObjects C]

attribute [instance] Topos.has_terminal Topos.finite_limits Topos.subobject_classifier Topos.cartesian_closed

variable [Topos C] {C}

namespace Topos

noncomputable section

def Predicate.true_ (B : C) : B ⟶ Ω C := terminal.from B ≫ (t C)

/--
  The equality predicate on `B ⨯ B`.
-/
def Predicate.eq (B : C) : B ⨯ B ⟶ Ω C := ClassifierOf (diag B)

/--
  The "singleton" map {•}_B : B ⟶ Pow B.
  In Set, this map sends b ∈ B to the singleton set {b}.
-/
def singleton (B : C) : B ⟶ Pow B := P_transpose (Predicate.eq B)

/-- The singleton map {•}_B : B ⟶ Pow B is a monomorphism. -/
instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := by
    intro X b b' h
    rw [singleton] at h
    have h₁ : prod.map (𝟙 _) (b ≫ P_transpose (Predicate.eq B)) ≫ in_ B = prod.map (𝟙 _) (b' ≫ P_transpose (Predicate.eq B)) ≫ in_ B :=
      congrFun (congrArg CategoryStruct.comp (congrArg (prod.map (𝟙 B)) h)) (in_ B)

    sorry

def Predicate.isSingleton (B : C) : Pow B ⟶ Ω C := ClassifierOf (singleton B)

/-- The name ⌈φ⌉ : ⊤_ C ⟶ Pow B of a predicate `φ : B ⟶ Ω C`. -/
def Name {B} (φ : B ⟶ Ω C) : ⊤_ C ⟶ Pow B := P_transpose ((prod.rightUnitor B).hom ≫ φ)

def Predicate.fromName {B} (φ' : ⊤_ C ⟶ Pow B) := (prod.map (𝟙 _) φ') ≫ in_ B

-- TODO: prove equivalence of the types (B ⟶ Ω C), (T_ C ⟶ Pow B), and (Subobject B).



end
end Topos
end CategoryTheory
