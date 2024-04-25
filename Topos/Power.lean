-- import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Topos.Category
import Topos.SubobjectClassifier

namespace CategoryTheory

open CategoryTheory Limits Classifier

/-!
# Power Objects

Defines power objects for a category C with a subobject classifier and pullbacks.
-/

universe u v

variable {C : Type u} [Category.{v} C] [HasSubobjectClassifier C] [HasPullbacks C]


/--
  Having a subobject classifier implies having terminal objects.
  Combined with having pullbacks, this shows that C has binary products.
-/
instance hasBinaryProducts : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C

instance hasFiniteProducts : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal

/--
  We say that `f_hat : A ⟶ PB` "powerizes" `f : B ⨯ A ⟶ Ω C` if ∈_B ∘ (1 × f') = f.
-/
abbrev Powerizes {B PB : C} (in_B : B ⨯ PB ⟶ Ω C) (f : B ⨯ A ⟶ Ω C) (f_hat : A ⟶ PB) :=
  f = (prod.map (𝟙 B) f_hat) ≫ in_B

structure IsPowerObject {B PB : C} (in_B : B ⨯ PB ⟶ Ω C) where
  hat : ∀ {A} (_ : B ⨯ A ⟶ Ω C), A ⟶ PB
  powerizes : ∀ {A} (f : B ⨯ A ⟶ Ω C), Powerizes in_B f (hat f)
  unique' : ∀ {A} {f : B ⨯ A ⟶ Ω C} {hat' : A ⟶ PB}, Powerizes in_B f hat' → hat f = hat'

/-- What it means for an object B to have a power object. -/
class HasPowerObject (B : C) where
  PB : C
  in_B : B ⨯ PB ⟶ Ω C
  is_power : IsPowerObject in_B

variable (C)

class HasPowerObjects where
  has_power_object : ∀ (B : C), HasPowerObject B

variable {C}

attribute [instance] HasPowerObjects.has_power_object

variable [HasPowerObjects C]



namespace Power

/-- Notation for the power object of an object. -/
abbrev Pow (B : C) : C := (HasPowerObjects.has_power_object B).PB

/-- Notation for the predicate "b ∈ S" as a map `B ⨯ P(B) ⟶ Ω`. -/
abbrev in_ (B : C) : B ⨯ (Pow B) ⟶ Ω C := (HasPowerObjects.has_power_object B).in_B

instance Pow_is_power (B : C) : IsPowerObject (in_ B) := (HasPowerObjects.has_power_object B).is_power

/-- The map Hom(B⨯A,Ω) → Hom(A,P(B)). -/
def P_transpose {B A} (f : B ⨯ A ⟶ Ω C) : A ⟶ Pow B := (Pow_is_power B).hat f

def Pow_powerizes (B : C) : ∀ {A} (f : B ⨯ A ⟶ Ω C), Powerizes (in_ B) f (P_transpose f) :=
  (Pow_is_power B).powerizes

def Pow_unique (B : C) : ∀ {A} {f : B ⨯ A ⟶ Ω C} {hat' : A ⟶ Pow B},
  Powerizes (in_ B) f hat' → P_transpose f = hat' :=
    (Pow_is_power B).unique'

noncomputable section
-- the stuff involving products is noncomputable because ???

-- want a computable version of this
/-- The map Hom(B⨯A,Ω) → Hom(B,P(A)). -/
def P_transpose_swap {B A} (f : B ⨯ A ⟶ Ω C) : B ⟶ Pow A := P_transpose ((prod.braiding A B).1 ≫ f)

-- not sure why this isn't computable either? It's just the composition of two maps.
def toPredicate {B A} (f : A ⟶ Pow B) : B ⨯ A ⟶ Ω C := (prod.map (𝟙 _) f) ≫ in_ B

def PowFunctor {B A : C} (h : A ⟶ B) : Pow B ⟶ Pow A :=
  P_transpose ((prod.map h (𝟙 (Pow B))) ≫ (in_ B))

end

end Power

end CategoryTheory
