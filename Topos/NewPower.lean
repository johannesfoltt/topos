import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Opposites
import Topos.NewClassifier

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject

namespace CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

instance : BraidedCategory C := BraidedCategory.ofCartesianMonoidalCategory

structure PowerObject (c : Classifier C) (X : C) where
  /-- The power object -/
  pow : C
  /-- The membership predicate -/
  in_ : X ⊗ pow ⟶ c.Ω
  /-- The transpose of a map -/
  transpose {Y : C} (f : X ⊗ Y ⟶ c.Ω) : Y ⟶ pow
  /-- the characterizing property of the transpose -/
  comm {Y : C} (f : X ⊗ Y ⟶ c.Ω) : ((𝟙 X) ⊗ (transpose f)) ≫ in_ = f
  /-- `transpose f` is the only map which satisfies the commutativity condition-/
  uniq {Y : C} {f : X ⊗ Y ⟶ c.Ω} {hat' : Y ⟶ pow} (hat'_comm : ((𝟙 X) ⊗ hat') ≫ in_ = f) : transpose f = hat'

abbrev PowerObjectChoice (c : Classifier C) := ∀ (X : C), PowerObject c X

namespace PowerObject

variable {c : Classifier C} {X : C} (p : PowerObject c X) {Y : C}

abbrev transposeInv (f : Y ⟶ p.pow) : X ⊗ Y ⟶ c.Ω :=
  ((𝟙 _) ⊗ f) ≫ p.in_

/-- Equivalence between Hom(B⨯A,Ω) and Hom(A,P(B)). -/
def transposeEquiv (Y) : (X ⊗ Y ⟶ c.Ω) ≃ (Y ⟶ p.pow) where
  toFun := p.transpose
  invFun := p.transposeInv
  left_inv := fun f ↦ p.comm f
  right_inv := by exact fun f ↦ p.uniq rfl

/-- `transposeInv` is a left inverse of `transpose`. -/
@[reassoc (attr := simp)]
lemma transpose_left_inv (f : X ⊗ Y ⟶ c.Ω) : p.transposeInv (p.transpose f) = f :=
  (transposeEquiv _ _).left_inv _

/-- `transposeInv` is a right inverse of `transpose`. -/
@[reassoc (attr := simp)]
lemma transpose_right_inv (f : Y ⟶ p.pow) : p.transpose (p.transposeInv f) = f :=
  (transposeEquiv _ _).right_inv _

/-- The map Hom(B⨯A,Ω) → Hom(B,P(A)).
This is currying the right argument.
-/
def transposeSymm (f : Y ⊗ X ⟶ c.Ω) : Y ⟶ p.pow :=
  p.transpose ((β_ X Y).hom ≫ f)

/-- Un-currying on the right. -/
abbrev transposeSymmInv (f : Y ⟶ p.pow) : Y ⊗ X ⟶ c.Ω :=
  (β_ X Y).inv ≫ (p.transposeInv f)

/-- Equivalence between Hom(B⨯A,Ω) and Hom(B,P(A)). -/
def transposeEquivSymm (Y) : (Y ⊗ X ⟶ c.Ω) ≃ (Y ⟶ p.pow) where
  toFun := p.transposeSymm
  invFun := p.transposeSymmInv
  left_inv := by
    intro f
    dsimp only [transposeSymm, transposeInv, transposeSymmInv]
    rw [comm, ←assoc, Iso.inv_hom_id, id_comp]
  right_inv := by {
    intro f
    unfold transposeSymm
    unfold transposeSymmInv
    simp
  }

/-- `transposeSymmInv` is the left inverse
of `transposeSymm`.
-/
@[simp]
lemma transpose_symm_left_inv (f : Y ⊗ X ⟶ c.Ω) :
    p.transposeSymmInv (p.transposeSymm f) = f :=
  (transposeEquivSymm _ _).left_inv _

/-- `transposeSymmInv` is the right inverse
of `transposeSymm`.
-/
@[simp]
lemma transpose_symm_right_inv (f : Y ⟶ p.pow) :
    p.transposeSymm (p.transposeSymmInv f) = f :=
  (transposeEquivSymm _ _).right_inv _

/-- Equivalence between Hom(A,P(B)) and Hom(B, P(A)).
This is just the composition of `transposeEquiv` and `transposeEquivSymm`.
-/
def transpose_transpose_Equiv (q : PowerObject c Y) : (Y ⟶ p.pow) ≃ (X ⟶ q.pow) :=
  Equiv.trans (p.transposeEquiv Y).symm (q.transposeEquivSymm X)

end PowerObject

namespace PowerObjectChoice

variable {c : Classifier C} (pc : PowerObjectChoice c)

/--
  The power object functor's action on arrows.
  Sends `h : X ⟶ Y` to the P-transpose of the map `h⨯1 ≫ ∈_Y : X × pow Y ⟶ Y × pow Y ⟶ Ω`.
-/
def inverseImage {X Y : C} (h : X ⟶ Y) : (pc Y).pow ⟶ (pc X).pow :=
  (pc X).transpose ((h ⊗ (𝟙 (pc Y).pow)) ≫ (pc Y).in_)

/-- The following diagram commutes:
```
    X ⨯ Pow Y ----(𝟙 X) ⨯ Pow_map h----> X ⨯ Pow X
      |                                    |
      |                                    |
    h ⨯ (𝟙 (Pow Y))                      in_ X
      |                                    |
      v                                    v
    Y ⨯ Pow Y ----------in_ Y-----------> Ω C
```
-/
lemma inverseImage_comm {X Y : C} (h : X ⟶ Y) : ((𝟙 X) ⊗ (pc.inverseImage h)) ≫ (pc X).in_ = (h ⊗ (𝟙 (pc Y).pow)) ≫ ((pc Y).in_) := by {
  unfold inverseImage
  exact (pc X).transpose_left_inv ((h ⊗ 𝟙 (pc Y).pow) ≫ (pc Y).in_)
}

/-- `powMap` sends the identity on an object `X` to the identity on `pow X`. -/
@[simp]
lemma inverseImage_id {X : C} : pc.inverseImage (𝟙 X) = 𝟙 ((pc X).pow) := by {
  unfold inverseImage
  apply (pc X).uniq
  simp
}

variable (C)

/--
  The power object functor.
  Sends objects `B` to their power objects `pow B`.
  Sends arrows `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ pow B ⟶ B ⨯ pow B ⟶ Ω`,
  which is the "preimage" morphism `pow B ⟶ pow A`.
-/

def powFunctor : Cᵒᵖ ⥤ C where
  obj := fun ⟨X⟩ ↦ (pc X).pow
  map := fun ⟨h⟩ ↦ pc.inverseImage h
  map_id := by {
    intro X
    apply (pc _).uniq
    rfl
  }
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩
    apply (pc _).uniq
    unfold inverseImage
    symm
    calc
      ((g ≫ f) ⊗ (𝟙 (pc X).pow)) ≫ (pc X).in_
        = (g ⊗ (𝟙 (pc X).pow)) ≫ (f ⊗ (𝟙 (pc X).pow)) ≫ (pc X).in_  :=
          comp_tensor_id_assoc g f (pc X).in_
      _ = (g ⊗ (𝟙 (pc X).pow)) ≫ ((𝟙 Y) ⊗ (pc.inverseImage f)) ≫ (pc Y).in_ := by rw [inverseImage_comm]
      _ = ((𝟙 Z) ⊗ (pc.inverseImage f)) ≫ (g ⊗ (𝟙 (pc Y).pow)) ≫ (pc Y).in_ := by rw [tensor_id_comp_id_tensor_assoc, id_tensor_comp_tensor_id_assoc]
      _ = ((𝟙 Z) ⊗ (pc.inverseImage f)) ≫ ((𝟙 Z) ⊗ (pc.inverseImage g)) ≫ (pc Z).in_ := by rw [inverseImage_comm]
      _ = ((𝟙 Z) ⊗ (pc.inverseImage f ≫ pc.inverseImage g)) ≫ (pc Z).in_  := by rw [id_tensor_comp_assoc]

/-- The power object functor, treated as a functor `C ⥤ Cᵒᵖ`. -/
def powFunctorOp : C ⥤ Cᵒᵖ where
  obj := fun B ↦ ⟨(pc B).pow⟩
  map := fun h ↦ ⟨pc.inverseImage h⟩
  map_id := by
    intro _
    apply congrArg Opposite.op
    apply (powFunctor C pc).map_id
  map_comp := by
    intros
    apply congrArg Opposite.op
    apply (powFunctor C pc).map_comp

/-- exhibiting that the pow functor is adjoint to itself on the right. -/
def powSelfAdj : powFunctorOp C pc ⊣ powFunctor C pc := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  -- homEquiv step
  · exact fun X ⟨Y⟩ => {
      toFun := fun ⟨f⟩ => ((pc X).transpose_transpose_Equiv (pc Y)).toFun f
      invFun := fun g => ⟨((pc X).transpose_transpose_Equiv (pc Y)).invFun g⟩
      left_inv := fun ⟨f⟩ => by simp
      right_inv := fun g => by simp
    }

  -- homEquiv_naturality_left_symm step
  · intro X' X ⟨Y⟩ f g
    simp
    congr
    show ((pc X').transpose_transpose_Equiv (pc Y)).symm (f ≫ g) =
      ((pc X).transpose_transpose_Equiv (pc Y)).symm g ≫ pc.inverseImage f
    dsimp only [PowerObject.transpose_transpose_Equiv, PowerObject.transposeEquivSymm, PowerObject.transposeEquiv]
    simp
    dsimp only [PowerObject.transposeSymm, PowerObject.transposeInv, inverseImage]
    apply (pc X').uniq
    rw [id_tensor_comp, assoc, (pc X').comm, ← assoc, ← tensor_comp, id_comp, comp_id, ←comp_id f, ←id_comp ((pc X).transpose _), tensor_comp, assoc, (pc _).comm]
    unfold PowerObject.transposeSymmInv
    unfold PowerObject.transposeInv
    simp

  -- homEquiv_naturality_right step
  · intro X ⟨Y⟩ ⟨Y'⟩ ⟨f⟩ ⟨g⟩
    dsimp only [PowerObject.transpose_transpose_Equiv, PowerObject.transposeEquiv, PowerObject.transposeEquivSymm]
    simp only [prod.lift_map_assoc, comp_id, Equiv.toFun_as_coe, Equiv.trans_apply,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
      Equiv.symm_symm]
    show (pc _).transpose ((β_ X Y').inv ≫ ((𝟙 X) ⊗ (g ≫ f)) ≫ (pc _).in_) = (pc _).transpose ((β_ X Y).inv ≫ ((𝟙 X) ⊗ f) ≫ (pc _).in_) ≫ pc.inverseImage g
    dsimp only [PowerObject.transposeInv, inverseImage]
    apply (pc _).uniq
    rw [id_tensor_comp_assoc, (pc _).comm, ← assoc, ← tensor_comp, id_comp, comp_id, ← comp_id g, ← id_comp ((pc Y).transpose _), tensor_comp]
    show ((g ⊗ 𝟙 X) ≫ ((𝟙 Y) ⊗ (pc Y).transpose ((β_ X Y).inv ≫ (𝟙 X ⊗ f) ≫ (pc X).in_))) ≫ (pc Y).in_ = (β_ X Y').inv ≫ (𝟙 X ⊗ (g ≫ (𝟙 Y)) ≫ f) ≫ (pc X).in_
    slice_lhs 2 4 => rw [(pc _).comm]
    aesop_cat


variable {C}

/-- The "singleton" map `X ⟶ Pow X`.
In Set, this map sends `x ∈ X` to the
singleton set containing just `x`.
-/
def singleton (X : C) : X ⟶ (pc X).pow := (pc X).transpose (Classifier.Predicate.eq c X)


/-- `singleton X : X ⟶ Pow X` is a monomorphism. -/
instance singletonMono (X : C) : Mono (pc.singleton X) where
  right_cancellation := by {
    intro Z b b' h
    rw [singleton] at h
    have h₁ : ((𝟙 _) ⊗ (b ≫ ((pc X).transpose (Classifier.Predicate.eq c X)))) ≫ (pc X).in_
    = ((𝟙 _) ⊗ (b' ≫ ((pc X).transpose (Classifier.Predicate.eq c X)))) ≫ (pc X).in_ := congrFun (congrArg CategoryStruct.comp (congrArg (tensorHom (𝟙 X)) h)) (pc X).in_
    rw [id_tensor_comp_assoc, (pc _).comm, id_tensor_comp_assoc, (pc _).comm] at h₁
    have comm : (b ≫ from_ _) ≫ c.t = lift b (𝟙 _) ≫ ((𝟙 _) ⊗ b) ≫ Classifier.Predicate.eq c _ := by {
      rw [comp_from, ←assoc, lift_map, comp_id, id_comp, Classifier.Predicate.lift_eq, Classifier.Predicate.true_]
    }
    rw [comp_from, h₁, ←assoc, lift_map, id_comp, comp_id] at comm
    exact Classifier.Predicate.eq_of_lift_eq c (id (Eq.symm comm))
  }


/-- The predicate on `Pow X` which picks out the subobject of "singletons".
-/
def Predicate.isSingleton (X : C) : (pc X).pow ⟶ c.Ω := c.char (pc.singleton X)


/-- The name ⌈φ⌉ : ⊤_ C ⟶ Pow B of a predicate `φ : X ⟶ Ω C`.
This is the global element of `Pow X` associated to a predicate
on `X`.
-/
def name {X : C} (φ : X ⟶ c.Ω) : ⊤_ ⟶ (pc X).pow := (pc X).transpose ((fst X ⊤_) ≫ φ)


/-- The inverse of `Name`, sending a global element of `Pow B`
to the corresponding predicate on `B`.
-/
def Predicate.fromName {X : C} (φ' : ⊤_ ⟶ (pc X).pow) : X ⟶ c.Ω :=
  (lift (𝟙 X) (from_ X)) ≫ (pc X).transposeInv φ'


/-- The condition from the definition of `Name`
as the `P_transpose` of a morphism.
-/

lemma Predicate.NameDef {X : C} (φ : X ⟶ c.Ω) : ((𝟙 _) ⊗ pc.name φ) ≫ ((pc X).in_) = (fst X ⊤_) ≫ φ :=
  (pc X).comm _


/-- The equivalence between morphisms `X ⟶ Ω C` and morphisms `⊤_ C ⟶ pow X`,
which comes from the more general equivalence between morphisms `Y ⨯ X ⟶ Ω C`
and morphisms `X ⟶ pow Y`.
-/
def Predicate.NameEquiv (X : C) : (X ⟶ c.Ω) ≃ (⊤_ ⟶ (pc X).pow) where
  toFun := pc.name
  invFun := Predicate.fromName pc
  left_inv := by
    intro φ
    dsimp [name, fromName]
    rw [PowerObject.transpose_left_inv, ←assoc, lift_fst, id_comp]
  right_inv := by
    intro φ'
    dsimp only [name, fromName]
    have h := (ρ_ X).hom_inv_id
    simp_rw [rightUnitor_hom, rightUnitor_inv, ← from_eq_toUnit, ← term_eq_Unit] at h
    rw [←assoc, h, id_comp, (pc X).transpose_right_inv]
