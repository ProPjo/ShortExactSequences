import Mathlib.Tactic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Algebra.Exact
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.Group.Subgroup.Map


-- Should have done this earlier
lemma congrHom {A B : Type*} [AddCommGroup A] [AddCommGroup B] {f g : A →+ B} (h : f = g) (x : A) : f x = g x := by
  have : f.toFun = g.toFun := by
    rw [h]
  apply congrFun this x

open CategoryTheory

def groupHomToGrpHom {A B : AddCommGrpCat} (f : A →+ B) : A ⟶ B := by
  use f
  exact f.map_add

@[simp]
lemma GrpHomZero {A B : AddCommGrpCat} : groupHomToGrpHom (0 : A →+ B) = 0 := by
  unfold groupHomToGrpHom
  rfl

@[simp]
lemma groupHomCompatible {A B : AddCommGrpCat} (f : A →+ B) : (groupHomToGrpHom f).hom' = f := by
  ext x
  unfold groupHomToGrpHom
  simp only [AddMonoidHom.mk_coe]

@[simp]
lemma groupHomCompatibleElt {A B : AddCommGrpCat} (f : A →+ B) : ∀ x, (groupHomToGrpHom f).hom' x = f x := by
  intro x
  exact congrHom (groupHomCompatible f) x


@[simp]
lemma compIsMonoidComp {A B C : AddCommGrpCat} {f : A ⟶ B} {g : B ⟶ C} : (f ≫ g) = groupHomToGrpHom (AddMonoidHom.comp g.hom' f.hom') := by
  rfl


lemma compIsMonoidComp₂ {A B C : AddCommGrpCat} {f : A ⟶ B} {g : B ⟶ C} : AddMonoidHom.comp g.hom' f.hom' = (f ≫ g).hom' := by
  rfl

@[simp]
theorem groupHomCompatibleComp {A B C : AddCommGrpCat} (g : B →+ C) (f : A →+ B) : ((groupHomToGrpHom f) ≫ (groupHomToGrpHom g)).hom' = g.comp f := by
  ext x
  simp only [compIsMonoidComp, groupHomCompatible, AddMonoidHom.coe_comp, Function.comp_apply]

@[simp]
theorem groupHomCompatibleComp₂ {A B C : AddCommGrpCat} (g : B →+ C) (f : A →+ B) : ∀ x, ((groupHomToGrpHom f) ≫ (groupHomToGrpHom g)).hom' x = g.comp f x:= by
  intro x
  exact congrHom (groupHomCompatibleComp g f) x

def inducedMapKer {A B C D : AddCommGrpCat} {f₁ : A ⟶ B} {f₂ : C ⟶ D} {g₁ : A ⟶ C} {g₂ : B ⟶ D} (comm : f₁ ≫ g₂ = g₁ ≫ f₂) : g₁.hom'.ker →+ g₂.hom'.ker := by
  have : ∀ x : g₁.hom'.ker, f₁.hom' x ∈ g₂.hom'.ker := by
    intro x
    have : (f₁ ≫ g₂).hom' = (g₁ ≫ f₂).hom' := by rw [comm]
    simp at this
    simp
    have : g₂.hom' (f₁.hom' x.1) = f₂.hom' (g₁.hom' x.1) := congrHom this x.1
    rw [this]
    rw [x.2, map_zero]
  apply AddMonoidHom.codRestrict (f₁.hom'.restrict g₁.hom'.ker) _ this

section Complexes

variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable {g : B →+ C} {f : A →+ B}

def GroupsToComplex (h : g.comp f = 0) : CategoryTheory.ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of A
  X₂ := AddCommGrpCat.of B
  X₃ := AddCommGrpCat.of C
  f := by
    use f
    simp only [ZeroHom.toFun_eq_coe, ZeroHom.coe_coe, map_add, implies_true]
  g := by
    use g
    simp only [ZeroHom.toFun_eq_coe, ZeroHom.coe_coe, map_add, implies_true]
  zero := by
    simp
    ext x
    simp only [AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
    have MonoidCompisFuncComp : g (f x) = (AddMonoidHom.comp g f) x := by
      rfl
    have compIsZero : g (f x) = 0 := by
      rw [MonoidCompisFuncComp, h]
      rfl
    apply compIsZero


@[simp]
lemma compIsZero (s : CategoryTheory.ShortComplex AddCommGrpCat) : s.g.hom'.comp s.f.hom' = 0 := by
  rw [compIsMonoidComp₂, s.zero]
  rfl

@[simp]
lemma compIsZeroElt (s : CategoryTheory.ShortComplex AddCommGrpCat) : ∀ x, s.g.hom' (s.f.hom' x) = 0 := by
  intro x
  have : s.g.hom' (s.f.hom' x) = s.g.hom'.comp s.f.hom' x := rfl
  rw [this, compIsZero]
  simp only [AddMonoidHom.zero_apply]

lemma compIsZeroFun (s : CategoryTheory.ShortComplex AddCommGrpCat) : s.g.hom'.toFun ∘ s.f.hom'.toFun = 0 := by
  have : s.g.hom'.toFun ∘ s.f.hom'.toFun = (AddMonoidHom.comp s.g.hom' s.f.hom').toFun := rfl
  rw [this, compIsZero]
  rfl


structure AddCommGroupSES extends CategoryTheory.ShortComplex AddCommGrpCat where
  injective : Function.Injective f.hom'
  middle : AddMonoidHom.ker g.hom' ≤ AddMonoidHom.range f.hom'
  surjective : Function.Surjective g.hom'


lemma rangeEqKerToCompEqZero (range_eq_ker : AddMonoidHom.range f = AddMonoidHom.ker g) : g.comp f = 0 := by
  ext x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply]
  have : f x ∈ f.range := by use x
  rw [range_eq_ker] at this
  apply this

lemma zeroOfMapZero (s : AddCommGroupSES) : ∀ x, s.f.hom' x = 0 → x = 0 := by
  apply (injective_iff_map_eq_zero s.f.hom').mp s.injective

def GroupsToComp₂ (range_eq_ker : AddMonoidHom.range f = AddMonoidHom.ker g) : CategoryTheory.ShortComplex AddCommGrpCat := GroupsToComplex (rangeEqKerToCompEqZero range_eq_ker)

def GroupsToSES (finj : f.toFun.Injective) (range_eq_ker : AddMonoidHom.range f = AddMonoidHom.ker g) (gsurj : g.toFun.Surjective) : AddCommGroupSES where
  __ := GroupsToComp₂ range_eq_ker
  injective := finj
  middle := le_of_eq range_eq_ker.symm
  surjective := gsurj


lemma RangeInKernel (s : AddCommGroupSES) : AddMonoidHom.range s.f.hom' ≤ AddMonoidHom.ker s.g.hom' := by
  rintro x hx
  rcases hx with ⟨w, hw⟩
  have : s.g.hom' (s.f.hom' w) = 0 := by
    apply congrFun (compIsZeroFun s.toShortComplex) w

  rw [hw] at this
  exact this

lemma RangeIsKernel (s : AddCommGroupSES) : s.f.hom'.range = s.g.hom'.ker := le_antisymm (RangeInKernel s) (s.middle)

lemma MiddleExact (s : AddCommGroupSES) : Function.Exact s.f.hom' s.g.hom' := AddMonoidHom.exact_iff.mpr (RangeIsKernel s).symm

lemma SameFibre {s : AddCommGroupSES} {x y : s.X₂} (fib : s.g.hom' x = s.g.hom' y) : ∃ w, s.f.hom' w = x - y := by
  suffices x - y ∈ s.f.hom'.range by exact this
  rw [RangeIsKernel s]
  simp [fib]

end Complexes

section Products

variable {I : Type*} {ι₁ ι₂ : I → Type*} [∀ i, AddCommGroup (ι₁ i)] [∀ i, AddCommGroup (ι₂ i)]

def productMap (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) : (∀ i, ι₁ i) →+ (∀ i, ι₂ i) where
  toFun := by
    intro x i
    apply (maps i).toFun (x i)
  map_zero' := by
    simp only [Pi.zero_apply, ZeroHom.toFun_eq_coe, map_zero]
    rfl
  map_add' := by
    intro x y
    ext i
    simp only [Pi.add_apply, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]

variable {ι₃ : I → Type*} [∀ i, AddCommGroup (ι₃ i)]

@[simp]
lemma ProductMapCompatible (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : (productMap maps₂).comp (productMap maps) = productMap (fun i ↦ (maps₂ i).comp (maps i)) := by
  ext x i
  unfold productMap
  simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply]

@[simp]
lemma ProductMapCompatibleFun (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : ((productMap maps₂).comp (productMap maps)).toFun = (productMap (fun i ↦ (maps₂ i).comp (maps i))).toFun := by
  ext x i
  unfold productMap
  simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply]

@[simp]
lemma ProductMapCompatibleElt (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : ∀ x, (productMap maps₂).comp (productMap maps) x = productMap (fun i ↦ (maps₂ i).comp (maps i)) x := by
  intro x
  apply congrFun (ProductMapCompatibleFun maps maps₂) x

@[simp]
lemma ProductMapCompatibleEltInd (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : ∀ x, ∀ i, (productMap maps₂).comp (productMap maps) x i = productMap (fun i ↦ (maps₂ i).comp (maps i)) x i := by
  intro x i
  apply congrFun (ProductMapCompatibleElt maps maps₂ x) i


lemma ProductMapKer {maps : ∀ i, (ι₁ i) →+ (ι₂ i)} : ∀ x, x ∈ (productMap maps).ker ↔ ∀ i, x i ∈ (maps i).ker := by
  intro x
  constructor
  · intro hx i
    unfold productMap at hx
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddMonoidHom.mem_ker,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hx
    apply congrFun hx i
  · intro hi
    ext i
    apply hi i

lemma ProductMapRange {maps : ∀ i, (ι₁ i) →+ (ι₂ i)} : ∀ x, x ∈ (productMap maps).range ↔ ∀ i, x i ∈ (maps i).range := by
  intro x
  constructor
  · intro this i
    unfold productMap at this
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddMonoidHom.mem_range,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rcases this with ⟨w,hw⟩
    use w i
    exact congrFun hw i
  · intro this
    have h : ∀ i, ∃ w, (maps i) w = x i:= by
      intro i
      apply this i

    use (fun i ↦ (h i).choose)
    ext i

    have : ∀ y, (productMap fun i ↦ maps i) y i = (maps i) (y i) := by
      intro y
      unfold productMap
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk]

    rw [this, Exists.choose_spec (h i)]


variable {I : Type*} (ι : ∀ (_ : I), AddCommGroupSES)

def productOfSESisSES : AddCommGroupSES where
  X₁ := AddCommGrpCat.of (∀ i, (ι i).X₁)
  X₂ := AddCommGrpCat.of (∀ i, (ι i).X₂)
  X₃ := AddCommGrpCat.of (∀ i, (ι i).X₃)
  f := by
    have : (∀ i, (ι i).X₁) →+ (∀ i, (ι i).X₂) := by
      apply productMap (fun i ↦ (ι i).f.hom')
    apply groupHomToGrpHom this
  g := by
    have : (∀ i, (ι i).X₂) →+ (∀ i, (ι i).X₃) := by
      apply productMap (fun i ↦ (ι i).g.hom')
    apply groupHomToGrpHom this
  zero := by
    simp only [compIsMonoidComp, groupHomCompatible, ProductMapCompatible, compIsZero]
    rfl
  injective := by
    intro x y eq
    simp at eq
    ext i
    apply (ι i).injective
    apply congrFun eq
  middle := by
    simp
    intro x hx
    rw [ProductMapKer] at hx
    have : ∀ i, x i ∈ (ι i).f.hom'.range := by
      intro i
      rw [RangeIsKernel]
      exact hx i

    exact (ProductMapRange x).mpr this
  surjective := by
    simp
    intro x
    have : ∀ i, x i ∈ (ι i).g.hom'.range := by
      intro i
      apply (ι i).surjective

    exact (ProductMapRange x).mpr this

end Products


section CommDiaOfSES

structure CommDiagramOfSES where
  s₁ : AddCommGroupSES
  s₂ : AddCommGroupSES
  v₁ : s₁.X₁ ⟶ s₂.X₁
  v₂ : s₁.X₂ ⟶ s₂.X₂
  v₃ : s₁.X₃ ⟶ s₂.X₃
  commleft : s₁.f ≫ v₂ = v₁ ≫ s₂.f
  commright : s₁.g ≫ v₃ = v₂ ≫ s₂.g

lemma CommLeft (dia : CommDiagramOfSES) : dia.v₂.hom'.comp dia.s₁.f.hom' = dia.s₂.f.hom'.comp dia.v₁.hom' := by
  repeat rw [compIsMonoidComp₂]
  suffices dia.s₁.f ≫ dia.v₂ = dia.v₁ ≫ dia.s₂.f by
    rw [this]
  apply dia.commleft

lemma CommLeftElt (dia : CommDiagramOfSES) : ∀ x, dia.v₂.hom'.comp dia.s₁.f.hom' x = dia.s₂.f.hom'.comp dia.v₁.hom' x := by
  intro x
  apply congrHom (CommLeft dia) x

lemma CommLeftElt₂ (dia : CommDiagramOfSES) : ∀ x, dia.v₂.hom' (dia.s₁.f.hom' x) = dia.s₂.f.hom' (dia.v₁.hom' x) := by
  intro x
  apply congrHom (CommLeft dia) x


lemma CommRight (dia : CommDiagramOfSES) : dia.v₃.hom'.comp dia.s₁.g.hom' = dia.s₂.g.hom'.comp dia.v₂.hom' := by
  repeat rw [compIsMonoidComp₂]
  suffices dia.s₁.g ≫ dia.v₃ = dia.v₂ ≫ dia.s₂.g by
    rw [this]
  apply dia.commright

lemma CommRightElt (dia : CommDiagramOfSES) : ∀ x, dia.v₃.hom'.comp dia.s₁.g.hom' x = dia.s₂.g.hom'.comp dia.v₂.hom' x := by
  intro x
  apply congrHom (CommRight dia) x

lemma CommRightElt₂ (dia : CommDiagramOfSES) : ∀ x, dia.v₃.hom' (dia.s₁.g.hom' x) = dia.s₂.g.hom' (dia.v₂.hom' x) := by
  intro x
  apply congrHom (CommRight dia) x


def inducedMap₁ (dia : CommDiagramOfSES) : dia.v₁.hom'.ker →+ dia.v₂.hom'.ker where
  toFun := by
    intro x
    use dia.s₁.f.hom' x
    have : dia.s₂.f.hom'.comp dia.v₁.hom' x = 0 := by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [x.2, map_zero]
    rw [<- CommLeftElt dia] at this
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
    exact this
  map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero, AddSubgroup.mk_eq_zero]
  map_add' := by
    simp
    intro a azero b bzero
    rfl


lemma induced₁ToKernel {dia : CommDiagramOfSES} : ∀ x : ↥dia.v₁.hom'.ker, dia.s₁.f.hom' x.1 ∈ dia.v₂.hom'.ker := by
  intro x
  have : dia.s₂.f.hom'.comp dia.v₁.hom' x = 0 := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [x.2]
    simp only [map_zero]
  rw [<- CommLeftElt] at this
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
  exact this

@[simp]
lemma induced₁Coincide {dia : CommDiagramOfSES} : ∀ x, (inducedMap₁ dia) x = ⟨dia.s₁.f.hom' x.1, induced₁ToKernel x⟩ := by
  unfold inducedMap₁
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, implies_true]


theorem inducedMap₁Injective {dia : CommDiagramOfSES} : Function.Injective (inducedMap₁ dia) := by
  intro x y hxy
  unfold inducedMap₁ at hxy
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Subtype.mk.injEq] at hxy
  apply dia.s₁.injective at hxy
  ext
  exact hxy


def inducedMap₂ (dia : CommDiagramOfSES) : dia.v₂.hom'.ker →+ dia.v₃.hom'.ker where
  toFun := by
    intro x
    use dia.s₁.g.hom' x
    have : dia.s₂.g.hom'.comp dia.v₂.hom' x = 0 := by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [x.2, map_zero]
    rw [<- CommRightElt dia] at this
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
    exact this
  map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero, AddSubgroup.mk_eq_zero]
  map_add' := by
    simp
    intro a azero b bzero
    rfl

lemma induced₂ToKernel {dia : CommDiagramOfSES} : ∀ x : ↥dia.v₂.hom'.ker, dia.s₁.g.hom' x.1 ∈ dia.v₃.hom'.ker := by
  intro x
  have : dia.s₂.g.hom'.comp dia.v₂.hom' x = 0 := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [x.2]
    simp only [map_zero]
  rw [<- CommRightElt] at this
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
  exact this

@[simp]
lemma induced₂Coincide {dia : CommDiagramOfSES} : ∀ x, inducedMap₂ dia x = ⟨dia.s₁.g.hom' x.1, induced₂ToKernel x⟩ := by
  unfold inducedMap₂
  simp

theorem inducedMap₁inducedMap₂Exact {dia : CommDiagramOfSES} : Function.Exact (inducedMap₁ dia) (inducedMap₂ dia) := by
  apply AddMonoidHom.exact_iff.mpr
  ext x
  constructor
  · intro hx
    have : x.1 ∈ dia.s₁.g.hom'.ker := by
      simp only [AddMonoidHom.mem_ker, induced₂Coincide, AddSubgroup.mk_eq_zero] at hx
      exact hx
    rw [<- RangeIsKernel] at this
    rcases this with ⟨w, hw⟩
    have : dia.v₂.hom'.comp dia.s₁.f.hom' w = 0 := by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [hw]
      exact x.2
    have : w ∈ dia.v₁.hom'.ker := by
      rw [CommLeftElt dia] at this
      simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
      apply zeroOfMapZero at this
      exact this
    use ⟨w, this⟩
    simp only [induced₁Coincide, hw, Subtype.coe_eta]
  · intro hx
    rcases hx with ⟨w,hw⟩
    rw [<- hw]
    simp only [induced₁Coincide, AddMonoidHom.mem_ker, induced₂Coincide, compIsZeroElt,
      AddSubgroup.mk_eq_zero]


theorem inducedMap₁RangeEqinducedMap₂Ker {dia : CommDiagramOfSES} : (inducedMap₁ dia).range = (inducedMap₂ dia).ker := by
  apply (AddMonoidHom.exact_iff.mp inducedMap₁inducedMap₂Exact).symm


lemma kernelExact {A B : AddCommGrpCat} (f : A ⟶ B) : Function.Exact f.hom'.ker.subtype f.hom' := by
  apply AddMonoidHom.exact_iff.mpr
  ext x
  constructor
  · intro hx
    use ⟨x, hx⟩
    rfl
  · intro hx
    rcases hx with ⟨w, hw⟩
    have : w.1 = x := by rw [<- hw]; rfl
    rw [<- this]
    exact w.2


@[reducible, inline]
def cokernel {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) := B ⧸ f.range

def cokernelHom {A B : AddCommGrpCat} (f : A ⟶ B) : B →+ (cokernel f.hom') := QuotientAddGroup.mk' f.hom'.range

lemma cokernelHomKer {A B : AddCommGrpCat} (f : A ⟶ B) : (cokernelHom f).ker = f.hom'.range := by
  ext x
  constructor
  · intro hx
    simp [cokernelHom] at hx
    exact hx
  . intro hx
    simp [cokernelHom]
    exact hx

lemma cokernelExistsOrig {A B : AddCommGrpCat} {f : A ⟶ B} (x : cokernel f.hom') : ∃ w, cokernelHom f w = x := QuotientAddGroup.mk_surjective x

lemma cokernelExact {A B : AddCommGrpCat} (f : A ⟶ B) : Function.Exact f.hom' (cokernelHom f) := by
  apply AddMonoidHom.exact_iff.mpr
  ext x
  constructor
  · intro hx
    rw [<- cokernelHomKer f]
    exact hx
  . intro hx
    rw [cokernelHomKer f]
    exact hx

def ModuleHomToGroupHom {R A B : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (f : A →ₗ[R] B) : A →+ B := by exact
  f.toAddMonoidHom

noncomputable def SnakeLemmaDelta (dia : CommDiagramOfSES) : dia.v₃.hom'.ker →+ cokernel dia.v₁.hom' := by
  let i₁ : dia.s₁.X₁ →ₗ[ℤ] dia.s₂.X₁ := dia.v₁.hom'.toIntLinearMap
  let i₂ : dia.s₁.X₂ →ₗ[ℤ] dia.s₂.X₂ := dia.v₂.hom'.toIntLinearMap
  let i₃ : dia.s₁.X₃ →ₗ[ℤ] dia.s₂.X₃ := dia.v₃.hom'.toIntLinearMap
  let f₁ : dia.s₁.X₁ →ₗ[ℤ] dia.s₁.X₂ := dia.s₁.f.hom'.toIntLinearMap
  let f₂ : dia.s₁.X₂ →ₗ[ℤ] dia.s₁.X₃ := dia.s₁.g.hom'.toIntLinearMap
  have hf : Function.Exact f₁ f₂ := by exact MiddleExact dia.s₁
  let g₁ : dia.s₂.X₁ →ₗ[ℤ] dia.s₂.X₂ := dia.s₂.f.hom'.toIntLinearMap
  let g₂ : dia.s₂.X₂ →ₗ[ℤ] dia.s₂.X₃ := dia.s₂.g.hom'.toIntLinearMap
  have hg : Function.Exact g₁ g₂ := by exact MiddleExact dia.s₂
  have h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁ := by
    ext x
    simp
    exact (CommLeftElt dia x).symm
  have h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂ := by
    ext x
    simp
    exact (CommRightElt dia x).symm
  let ι₃ : dia.v₃.hom'.ker →ₗ[ℤ] dia.s₁.X₃ := dia.v₃.hom'.ker.subtype.toIntLinearMap
  have hι₃ : Function.Exact ι₃ i₃ := kernelExact dia.v₃
  let π₁ : dia.s₂.X₁ →ₗ[ℤ] (cokernel dia.v₁.hom') := (cokernelHom dia.v₁).toIntLinearMap
  have hπ₁ : Function.Exact i₁ π₁ := cokernelExact dia.v₁
  have hf₂ : Function.Surjective f₂ := dia.s₁.surjective
  have hg₁ : Function.Injective g₁ := dia.s₂.injective
  apply (SnakeLemma.δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁).toAddMonoidHom

theorem DeltaExact (dia : CommDiagramOfSES) : Function.Exact (inducedMap₂ dia) (SnakeLemmaDelta dia) := by
  let i₁ : dia.s₁.X₁ →ₗ[ℤ] dia.s₂.X₁ := dia.v₁.hom'.toIntLinearMap
  let i₂ : dia.s₁.X₂ →ₗ[ℤ] dia.s₂.X₂ := dia.v₂.hom'.toIntLinearMap
  let i₃ : dia.s₁.X₃ →ₗ[ℤ] dia.s₂.X₃ := dia.v₃.hom'.toIntLinearMap
  let f₁ : dia.s₁.X₁ →ₗ[ℤ] dia.s₁.X₂ := dia.s₁.f.hom'.toIntLinearMap
  let f₂ : dia.s₁.X₂ →ₗ[ℤ] dia.s₁.X₃ := dia.s₁.g.hom'.toIntLinearMap
  have hf : Function.Exact f₁ f₂ := by exact MiddleExact dia.s₁
  let g₁ : dia.s₂.X₁ →ₗ[ℤ] dia.s₂.X₂ := dia.s₂.f.hom'.toIntLinearMap
  let g₂ : dia.s₂.X₂ →ₗ[ℤ] dia.s₂.X₃ := dia.s₂.g.hom'.toIntLinearMap
  have hg : Function.Exact g₁ g₂ := by exact MiddleExact dia.s₂
  have h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁ := by
    ext x
    simp
    exact (CommLeftElt dia x).symm
  have h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂ := by
    ext x
    simp
    exact (CommRightElt dia x).symm
  let ι₂ : dia.v₂.hom'.ker →ₗ[ℤ] dia.s₁.X₂ := dia.v₂.hom'.ker.subtype.toIntLinearMap
  have hι₂ : Function.Exact ι₂ i₂ := kernelExact dia.v₂
  let ι₃ : dia.v₃.hom'.ker →ₗ[ℤ] dia.s₁.X₃ := dia.v₃.hom'.ker.subtype.toIntLinearMap
  have hι₃ : Function.Exact ι₃ i₃ := kernelExact dia.v₃
  let π₁ : dia.s₂.X₁ →ₗ[ℤ] (cokernel dia.v₁.hom') := (cokernelHom dia.v₁).toIntLinearMap
  have hπ₁ : Function.Exact i₁ π₁ := cokernelExact dia.v₁
  have hf₂ : Function.Surjective f₂ := dia.s₁.surjective
  have hg₁ : Function.Injective g₁ := dia.s₂.injective
  let F : dia.v₂.hom'.ker →ₗ[ℤ] dia.v₃.hom'.ker := (inducedMap₂ dia).toIntLinearMap
  have hF : f₂ ∘ₗ ι₂ = ι₃ ∘ₗ F := by
    ext x
    simp [f₂, ι₂, ι₃, F]
  have h : Function.Injective ι₃ := by
    intro x y hxy
    simp [ι₃] at hxy
    exact hxy
  exact SnakeLemma.exact_δ'_right i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₂ hι₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁ F hF h

def inducedMap₄ (dia : CommDiagramOfSES) : (cokernel dia.v₁.hom') →+ (cokernel dia.v₂.hom') := by
  have : dia.v₁.hom'.range ≤ AddSubgroup.comap dia.s₂.f.hom' dia.v₂.hom'.range := by
    intro x hx
    rcases hx with ⟨w, hw⟩
    rw [<- hw]
    simp
    use dia.s₁.f.hom' w
    exact CommLeftElt dia w
  apply QuotientAddGroup.map _ _ _ this


lemma inducedMap₄Comm (dia : CommDiagramOfSES) : (inducedMap₄ dia).comp (cokernelHom dia.v₁) = (cokernelHom dia.v₂).comp dia.s₂.f.hom' := by
  ext x
  unfold inducedMap₄ cokernelHom
  simp

lemma inducedMap₄CommElt (dia : CommDiagramOfSES) : ∀ x, (inducedMap₄ dia) ((cokernelHom dia.v₁) x) = (cokernelHom dia.v₂) (dia.s₂.f.hom' x) := by
  intro x
  exact congrHom (inducedMap₄Comm dia) x

theorem DeltaExact₂ (dia : CommDiagramOfSES) : Function.Exact (SnakeLemmaDelta dia) (inducedMap₄ dia) := by
  let i₁ : dia.s₁.X₁ →ₗ[ℤ] dia.s₂.X₁ := dia.v₁.hom'.toIntLinearMap
  let i₂ : dia.s₁.X₂ →ₗ[ℤ] dia.s₂.X₂ := dia.v₂.hom'.toIntLinearMap
  let i₃ : dia.s₁.X₃ →ₗ[ℤ] dia.s₂.X₃ := dia.v₃.hom'.toIntLinearMap
  let f₁ : dia.s₁.X₁ →ₗ[ℤ] dia.s₁.X₂ := dia.s₁.f.hom'.toIntLinearMap
  let f₂ : dia.s₁.X₂ →ₗ[ℤ] dia.s₁.X₃ := dia.s₁.g.hom'.toIntLinearMap
  have hf : Function.Exact f₁ f₂ := by exact MiddleExact dia.s₁
  let g₁ : dia.s₂.X₁ →ₗ[ℤ] dia.s₂.X₂ := dia.s₂.f.hom'.toIntLinearMap
  let g₂ : dia.s₂.X₂ →ₗ[ℤ] dia.s₂.X₃ := dia.s₂.g.hom'.toIntLinearMap
  have hg : Function.Exact g₁ g₂ := by exact MiddleExact dia.s₂
  have h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁ := by
    ext x
    simp
    exact (CommLeftElt dia x).symm
  have h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂ := by
    ext x
    simp
    exact (CommRightElt dia x).symm
  let ι₃ : dia.v₃.hom'.ker →ₗ[ℤ] dia.s₁.X₃ := dia.v₃.hom'.ker.subtype.toIntLinearMap
  have hι₃ : Function.Exact ι₃ i₃ := kernelExact dia.v₃
  let π₁ : dia.s₂.X₁ →ₗ[ℤ] (cokernel dia.v₁.hom') := (cokernelHom dia.v₁).toIntLinearMap
  have hπ₁ : Function.Exact i₁ π₁ := cokernelExact dia.v₁
  let π₂ : dia.s₂.X₂ →ₗ[ℤ] (cokernel dia.v₂.hom') := (cokernelHom dia.v₂).toIntLinearMap
  have hπ₂ : Function.Exact i₂ π₂ := cokernelExact dia.v₂
  have hf₂ : Function.Surjective f₂ := dia.s₁.surjective
  have hg₁ : Function.Injective g₁ := dia.s₂.injective
  let G : (cokernel dia.v₁.hom') →ₗ[ℤ] (cokernel dia.v₂.hom') := (inducedMap₄ dia).toIntLinearMap
  have hF : G ∘ₗ π₁ = π₂ ∘ₗ g₁ := by -- Probably a typo in mathlib, this should probaby be name hG
    ext x
    simp [G, π₁, π₂, g₁]
    exact inducedMap₄CommElt dia x
  have h : Function.Surjective π₁ := QuotientAddGroup.mk'_surjective dia.v₁.hom'.range

  exact SnakeLemma.exact_δ'_left i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ π₂ hπ₂ hf₂ hg₁ G hF h



/- copy of inducedMap₄ with the correct indices -/
def inducedMap₅ (dia : CommDiagramOfSES) : (cokernel dia.v₂.hom') →+ (cokernel dia.v₃.hom') := by
  have : dia.v₂.hom'.range ≤ AddSubgroup.comap dia.s₂.g.hom' dia.v₃.hom'.range := by
    intro x hx
    rcases hx with ⟨w, hw⟩
    rw [<- hw]
    simp
    use dia.s₁.g.hom' w
    exact CommRightElt dia w
  apply QuotientAddGroup.map _ _ _ this


lemma inducedMap₅Comm (dia : CommDiagramOfSES) : (inducedMap₅ dia).comp (cokernelHom dia.v₂) = (cokernelHom dia.v₃).comp dia.s₂.g.hom' := by
  ext x
  unfold inducedMap₅ cokernelHom
  simp

lemma inducedMap₅CommElt (dia : CommDiagramOfSES) : ∀ x, (inducedMap₅ dia) ((cokernelHom dia.v₂) x) = (cokernelHom dia.v₃) (dia.s₂.g.hom' x) := by
  intro x
  exact congrHom (inducedMap₅Comm dia) x


theorem inducedMap₄inducedMap₅Exact (dia : CommDiagramOfSES) : Function.Exact (inducedMap₄ dia) (inducedMap₅ dia) := by
  apply AddMonoidHom.exact_iff.mpr
  ext x
  constructor
  · /- Some diagram chasing :) -/
    intro hx
    rcases (cokernelExistsOrig x) with ⟨w,hw⟩
    have : (inducedMap₅ dia) (cokernelHom dia.v₂ w) = 0 := by
      rw [hw, hx]
    have : (dia.s₂.g.hom' w) ∈ (cokernelHom dia.v₃).ker := by
      rw [inducedMap₅CommElt] at this
      exact this
    have : ∃ a, dia.v₃.hom' a = dia.s₂.g.hom' w := by
      rw [(AddMonoidHom.exact_iff.mp (cokernelExact dia.v₃))] at this
      exact this
    rcases this with ⟨a,ha⟩
    rcases dia.s₁.surjective a with ⟨b, hb⟩
    have : dia.v₃.hom' (dia.s₁.g.hom' b) = dia.v₃.hom'.comp dia.s₁.g.hom' b := rfl
    have : w - dia.v₂.hom' b ∈ dia.s₂.g.hom'.ker := by
      apply congr_arg dia.v₃.hom' at hb
      rw [ha, this, CommRightElt dia b] at hb
      simp at hb
      simp
      rw [hb, sub_self]
    rw [<- RangeIsKernel dia.s₂] at this
    rcases this with ⟨c, hc⟩
    use cokernelHom dia.v₁ c
    rw [inducedMap₄CommElt dia, hc, map_sub, hw]
    have : dia.v₂.hom' b ∈ dia.v₂.hom'.range := by use b
    rw [<- QuotientAddGroup.ker_mk' dia.v₂.hom'.range] at this
    unfold cokernelHom
    rw [this, sub_zero]
  · intro hx
    rcases hx with ⟨w,hw⟩
    rcases (cokernelExistsOrig w) with ⟨a,ha⟩
    rw [<- ha] at hw
    rw [inducedMap₄CommElt dia a] at hw
    have : cokernelHom dia.v₃ (dia.s₂.g.hom' (dia.s₂.f.hom' a)) = 0 := by
      suffices dia.s₂.g.hom' (dia.s₂.f.hom' a) = 0 by rw [this]; apply map_zero
      apply compIsZeroElt
    rw [<- inducedMap₅CommElt dia] at this
    rw [hw] at this
    exact this

theorem inducedMap₅Surjective (dia : CommDiagramOfSES) : Function.Surjective (inducedMap₅ dia) := by
  intro y
  rcases (cokernelExistsOrig y) with ⟨x,hx⟩
  rcases (dia.s₂.surjective x) with ⟨w, hw⟩
  use cokernelHom dia.v₂ w
  rw [inducedMap₅CommElt, hw, hx]


end CommDiaOfSES

lemma zeroOfZeroExactZero {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {f : A →+ B} {g : B →+ C} (Azero : ∀ x : A, x = 0) (Czero : ∀ x : C, x = 0) (exact : Function.Exact f g) : ∀ x : B, x = 0 := by
  intro x
  have : x ∈ g.ker := Czero (g x)
  rw [AddMonoidHom.exact_iff.mp exact] at this
  rcases this with ⟨a, ha⟩
  rw [Azero a] at ha
  rw [<- ha]
  apply map_zero


lemma surjectiveOfExactZero {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {f : A →+ B} {g : B →+ C} (Czero : ∀ x : C, x = 0) (exact : Function.Exact f g) : Function.Surjective f := by
  intro x
  have : x ∈ g.ker := Czero (g x)
  rw [AddMonoidHom.exact_iff.mp exact] at this
  exact this


theorem fiveLemma {dia : CommDiagramOfSES} (h₁ : Function.Bijective dia.v₁.hom') (h₃ : Function.Bijective dia.v₃.hom') : Function.Bijective dia.v₂.hom' := by
  constructor
  · apply (AddMonoidHom.ker_eq_bot_iff _).mp
    apply (AddSubgroup.eq_bot_iff_forall _).mpr
    rintro x hx
    simp at hx
    have : dia.s₂.g.hom'.comp dia.v₂.hom' x = 0 := by simp [hx]
    have h : x ∈ dia.s₁.g.hom'.ker := by
      rw [<- CommRightElt] at this
      simp at this
      rw [<- map_zero dia.v₃.hom'] at this
      apply h₃.1 at this
      exact this
    rw [<- RangeIsKernel dia.s₁] at h
    rcases h with ⟨w, hw⟩
    rw [<- hw, <- map_zero dia.s₁.f.hom']
    suffices w = 0 by simp [this]
    have : Function.Injective (dia.s₂.f.hom'.comp dia.v₁.hom') := by apply Function.Injective.comp dia.s₂.injective h₁.1
    have h : dia.s₂.f.hom'.comp dia.v₁.hom' w = dia.s₂.f.hom'.comp dia.v₁.hom' 0 := by
      rw [<- CommLeftElt dia]
      simp [hw, hx]
    exact this h
  · intro y
    have : ∃ x, dia.s₂.g.hom' (dia.v₂.hom' x) = dia.s₂.g.hom' y := by
      rcases h₃.2 (dia.s₂.g.hom' y) with ⟨z, hz⟩
      rcases dia.s₁.surjective z with ⟨x, hx⟩
      use x
      suffices (dia.s₂.g.hom'.comp dia.v₂.hom') x = dia.s₂.g.hom' y by apply this
      rw [<- CommRightElt]
      simp [hx, hz]
    rcases this with ⟨w, hw⟩
    rcases SameFibre hw.symm with ⟨a, ha⟩
    rcases h₁.2 a with ⟨x, hx⟩
    use dia.s₁.f.hom' x + w
    rw [map_add, CommLeftElt₂, hx, ha, sub_add_cancel]
