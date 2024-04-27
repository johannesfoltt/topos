import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Topos.Category
import Topos.SubobjectClassifier

namespace CategoryTheory

open CategoryTheory Category Limits Classifier

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

/--
  The power object functor's action on arrows.
  Sends `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ Pow B ⟶ B ⨯ Pow B ⟶ Ω`.
-/
def Pow_map {B A : C} (h : A ⟶ B) : Pow B ⟶ Pow A :=
  P_transpose ((prod.map h (𝟙 (Pow B))) ≫ (in_ B))

-- /-- A functor preserves identity morphisms. -/
--   map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by aesop_cat
--   /-- A functor preserves composition. -/
--   map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by aesop_cat

lemma Pow_map_Powerizes {B : C} (h : A ⟶ B) : Powerizes (in_ A) ((prod.map h (𝟙 (Pow B))) ≫ (in_ B)) (Pow_map h) := by
  dsimp [Pow_map]
  apply Pow_powerizes

theorem Pow_map_square {B A : C} (h : A ⟶ B) : (prod.map h (𝟙 (Pow B))) ≫ (in_ B) = (prod.map (𝟙 A) (Pow_map h)) ≫ (in_ A) :=
  Pow_map_Powerizes h

/-- `Pow_map` sends the identity on an object `X` to the identity on `Pow X`. -/
lemma Pow_map_id {B : C} : Pow_map (𝟙 B) = 𝟙 (Pow B) := by
  apply Pow_unique; rfl


/--
  The Power object functor.
  Sends objects `B` to their power objects `Pow B`.
  Sends arrows `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ Pow B ⟶ B ⨯ Pow B ⟶ Ω`.
-/
def PowFunctor : Cᵒᵖ ⥤ C where
  obj := fun B ↦ Pow B.unop
  map := fun {A B} (h : A ⟶ B) ↦ Pow_map h.unop
  map_id := by
    intro X
    apply Pow_unique
    trivial
  map_comp := by
    intro X Y Z f g
    apply Pow_unique
    calc
      prod.map (f ≫ g).unop (𝟙 (Pow X.unop)) ≫ in_ X.unop
      = (prod.map g.unop (𝟙 (Pow X.unop))) ≫ (prod.map f.unop (𝟙 (Pow X.unop))) ≫ in_ X.unop := by simp
      _ = (prod.map g.unop (𝟙 (Pow X.unop))) ≫ (prod.map (𝟙 Y.unop) (Pow_map f.unop)) ≫ in_ Y.unop := by rw [Pow_map_Powerizes]
      _ = (prod.map (𝟙 Z.unop) (Pow_map f.unop)) ≫ (prod.map g.unop (𝟙 (Pow Y.unop))) ≫ in_ Y.unop := by simp
      _ = (prod.map (𝟙 Z.unop) (Pow_map f.unop)) ≫ (prod.map (𝟙 Z.unop) (Pow_map g.unop)) ≫ in_ Z.unop := by rw [Pow_map_Powerizes]
      _ = prod.map (𝟙 Z.unop) (Pow_map f.unop ≫ Pow_map g.unop) ≫ in_ Z.unop := by simp

end

end Power

open Power

namespace Classifier

noncomputable section

theorem Iso_Ω₀_terminal : Ω₀ C ≅ ⊤_ C :=
  (terminalIsoIsTerminal (terminal_Ω₀)).symm

theorem prod_terminal_right (B : C) : B ⨯ ⊤_ C ≅ B:=
  prod.rightUnitor B

theorem prod_terminal_Ω₀_Iso (B : C) : B ⨯ Ω₀ C ≅ B ⨯ ⊤_ C :=
  prod.mapIso (Iso.refl B) Iso_Ω₀_terminal

abbrev from_prod_Ω₀_right (B : C) : B ⨯ Ω₀ C ⟶ B := (prod_terminal_Ω₀_Iso B).hom ≫ (prod_terminal_right B).hom

/-- The name ⌈φ⌉ : • ⟶ Pow B of a predicate `φ : B ⟶ Ω C`. -/
def Name {B} (φ : B ⟶ Ω C) : Ω₀ C ⟶ Pow B := P_transpose (from_prod_Ω₀_right B ≫ φ)

def Name' {B} (φ : B ⟶ Ω C) : ⊤_ C ⟶ Pow B := P_transpose ((prod_terminal_right B).hom  ≫ φ)

-- TODO: prove equivalence of the types (B ⟶ Ω C), (Ω₀ ⟶ Pow B), (T_ C ⟶ Pow B), and (Subobject B).

end

end Classifier

end CategoryTheory
