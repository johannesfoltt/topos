import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monad.Monadicity
import Topos.Category
import Topos.SubobjectClassifier

namespace CategoryTheory

open CategoryTheory Category Limits Classifier

/-!
# Power Objects

Defines power objects for a category C with a subobject classifier and pullbacks.
-/

universe u v

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasSubobjectClassifier C] [HasPullbacks C]


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

/-- Equivalence between Hom(B⨯A,Ω) and Hom(A,P(B)). -/
def transposeEquiv (A B : C) : (B ⨯ A ⟶ Ω C) ≃ (A ⟶ Pow B) where
  toFun := P_transpose
  invFun := fun g => (prod.map (𝟙 _) g) ≫ in_ B
  left_inv := by
    intro
    exact (Pow_powerizes _ _).symm
  right_inv := by
    intro g
    apply Pow_unique
    dsimp only [Powerizes]


/-- The map Hom(B⨯A,Ω) → Hom(B,P(A)). -/
def P_transpose_symm {B A} (f : B ⨯ A ⟶ Ω C) : B ⟶ Pow A := P_transpose ((prod.braiding A B).hom ≫ f)

/-- Equivalence between Hom(B⨯A,Ω) and Hom(B,P(A)). -/
def transposeEquivSymm (A B : C) : (B ⨯ A ⟶ Ω C) ≃ (B ⟶ Pow A) where
  toFun := P_transpose_symm
  invFun := fun g => (prod.braiding A B).inv ≫ (prod.map (𝟙 _) g) ≫ in_ A
  left_inv := by
    intro f
    dsimp only [P_transpose_symm]
    rw [←Pow_powerizes, ←assoc, Iso.inv_hom_id, id_comp]
  right_inv := by
    intro g
    apply Pow_unique
    rw [←assoc, Iso.hom_inv_id, id_comp]

/--
  Equivalence between Hom(A,P(B)) and Hom(B, P(A)).
  This is just the composition of `transposeEquiv` and `transposeEquivSymm`.
-/
def transpose_transpose_Equiv (A B : C) : (B ⟶ Pow A) ≃ (A ⟶ Pow B) :=
  -- (transposeEquivSymm A B).symm.trans (transposeEquiv A B)
  Equiv.trans (transposeEquivSymm A B).symm (transposeEquiv A B)


-- not sure why this isn't computable either? It's just the composition of two maps.
def toPredicate {B A} (f : A ⟶ Pow B) : B ⨯ A ⟶ Ω C := (prod.map (𝟙 _) f) ≫ in_ B

/--
  The power object functor's action on arrows.
  Sends `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ Pow B ⟶ B ⨯ Pow B ⟶ Ω`.
-/
def Pow_map {B A : C} (h : A ⟶ B) : Pow B ⟶ Pow A :=
  P_transpose ((prod.map h (𝟙 (Pow B))) ≫ (in_ B))

lemma Pow_map_Powerizes {B : C} (h : A ⟶ B) : Powerizes (in_ A) ((prod.map h (𝟙 (Pow B))) ≫ (in_ B)) (Pow_map h) := by
  dsimp [Pow_map]
  apply Pow_powerizes

theorem Pow_map_square {B A : C} (h : A ⟶ B) : (prod.map h (𝟙 (Pow B))) ≫ (in_ B) = (prod.map (𝟙 A) (Pow_map h)) ≫ (in_ A) :=
  Pow_map_Powerizes h

/-- `Pow_map` sends the identity on an object `X` to the identity on `Pow X`. -/
lemma Pow_map_id {B : C} : Pow_map (𝟙 B) = 𝟙 (Pow B) := by
  apply Pow_unique; rfl



variable (C)

/--
  The Power object functor.
  Sends objects `B` to their power objects `Pow B`.
  Sends arrows `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ Pow B ⟶ B ⨯ Pow B ⟶ Ω`,
  which is the "preimage" morphism `P(h) : Pow B ⟶ Pow A`.
-/
def PowFunctor : Cᵒᵖ ⥤ C where
  obj := fun ⟨B⟩ ↦ Pow B
  map := fun ⟨h⟩ ↦ Pow_map h
  map_id := by
    intro _
    apply Pow_unique
    rfl
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩
    apply Pow_unique
    calc
      prod.map (g ≫ f)  (𝟙 (Pow X)) ≫ in_ X
        = (prod.map g (𝟙 (Pow X))) ≫ (prod.map f  (𝟙 (Pow X))) ≫ in_ X  := by rw [←assoc, ←prod.map_comp_id]
      _ = (prod.map g (𝟙 (Pow X))) ≫ (prod.map (𝟙 Y) (Pow_map f)) ≫ in_ Y := by rw [Pow_map_Powerizes]
      _ = (prod.map (𝟙 Z) (Pow_map f)) ≫ (prod.map g (𝟙 (Pow Y))) ≫ in_ Y := by repeat rw [prod.map_map_assoc, comp_id, id_comp]
      _ = (prod.map (𝟙 Z) (Pow_map f)) ≫ (prod.map (𝟙 Z) (Pow_map g)) ≫ in_ Z := by rw [Pow_map_Powerizes]
      _ = prod.map (𝟙 Z) (Pow_map f ≫ Pow_map g ) ≫ in_ Z  := by rw [←assoc, prod.map_id_comp]

def PowFunctorOp : C ⥤ Cᵒᵖ where
  obj := fun B ↦ ⟨Pow B⟩
  map := fun h ↦ ⟨Pow_map h⟩
  map_id := by
    intro _
    apply congrArg Opposite.op
    apply (PowFunctor C).map_id
  map_comp := by
    intro _ _ _ f g
    apply congrArg Opposite.op
    apply (PowFunctor C).map_comp

-- ## TODO
-- Prove the self-adjunction.
def PowSelfAdj : PowFunctorOp C ⊣ PowFunctor C := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  -- homEquiv step
  intro X ⟨Y⟩
  fapply Equiv.mk
  exact fun ⟨f⟩ => (transpose_transpose_Equiv X Y).toFun f
  exact fun g => ⟨(transpose_transpose_Equiv X Y).invFun g⟩
  intro ⟨f⟩
  simp only
  rw [Equiv.left_inv]
  intro g
  simp only
  rw [Equiv.right_inv]

  intro X' X ⟨Y⟩ f g
  simp
  have h : (PowFunctorOp C).map f ≫ { unop := (transpose_transpose_Equiv X Y).symm g }
    = { unop := (transpose_transpose_Equiv X Y).symm g ≫ (Pow_map f)} := rfl
  rw [h]

  have h' : (transpose_transpose_Equiv X' Y).symm (f ≫ g)
    = (transpose_transpose_Equiv X Y).symm g ≫ Pow_map f := by
      dsimp only [transpose_transpose_Equiv, transposeEquivSymm, transposeEquiv]
      simp
      dsimp only [P_transpose_symm, Pow_map]
      apply Pow_unique
      dsimp only [Powerizes]
      sorry
  rw [h']


  intro X ⟨Y⟩ ⟨Y'⟩ f_ g_
  dsimp only [transpose_transpose_Equiv, transposeEquiv, transposeEquivSymm]

  simp only [prod.lift_map_assoc, comp_id, Equiv.toFun_as_coe, Equiv.trans_apply,
    Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
    Equiv.symm_symm]

  have h : f_ ≫ g_ = Opposite.mk (g_.unop ≫ f_.unop) := rfl
  rw [h]
  simp only
  let ⟨f⟩ := f_
  let ⟨g⟩ := g_
  rw [prod.map_id_comp]

  save
  sorry

def PowerSelfAdj' : PowFunctorOp C ⊣ PowFunctor C where
  homEquiv := by
    intro X ⟨Y⟩
    fapply Equiv.mk
    exact fun ⟨f⟩ => (transpose_transpose_Equiv X Y).toFun f
    exact fun g => ⟨(transpose_transpose_Equiv X Y).invFun g⟩
    intro ⟨f⟩
    simp only
    rw [Equiv.left_inv]
    intro g
    simp only
    rw [Equiv.right_inv]
  unit := sorry
  counit := sorry
  homEquiv_unit := sorry
  homEquiv_counit := sorry

end
end Power
