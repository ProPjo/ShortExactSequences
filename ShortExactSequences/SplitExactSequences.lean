import ShortExactSequences.ExactSequences
import Mathlib

structure hasSection (a : AddCommGroupSES) where
  s : a.X₃ →+ a.X₂
  isSection : a.g.hom'.comp s = AddMonoidHom.id a.X₃

structure hasRetraction (a : AddCommGroupSES) where
  r : a.X₂ →+ a.X₁
  isRetraction : r.comp a.f.hom' = AddMonoidHom.id a.X₁



lemma pullComp {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {f : A →+ B} {g : B →+ C} (x : A) : g (f x) = (g.comp f) x := by simp



@[simp]
lemma RetractElt (a : AddCommGroupSES) (hr : hasRetraction a) : ∀ x, hr.r (a.f x) = x := congrHom hr.isRetraction

@[simp]
lemma SectionElt (a : AddCommGroupSES) (hs : hasSection a) : ∀ x, a.g (hs.s x) = x := congrHom hs.isSection

lemma CategoryHomIsHom {X Y : AddCommGrpCat} (f : X ⟶ Y) : ∀ x, (AddCommGrpCat.Hom.hom f) x = f.hom' x := by intro x; rfl

lemma sectionFunctionFromRetractionExistence (a : AddCommGroupSES) (hr : hasRetraction a) : ∀ x, ∃ y, a.g y = x ∧ y - a.f (hr.r y) = y := by
  intro x
  rcases (a.surjective x) with ⟨y, hy⟩
  use (y - a.f (hr.r y))
  constructor
  · simp
    exact hy
  · simp

lemma sectionFunctionFromRetractionUniqueness (a : AddCommGroupSES) (hr : hasRetraction a) : ∀ x, ∃! y, a.g y = x ∧ y - a.f (hr.r y) = y:= by
  intro x
  apply existsUnique_of_exists_of_unique (sectionFunctionFromRetractionExistence a hr x)
  rintro y z ⟨hy, hy₂⟩ ⟨h₁, h₂⟩
  rw [CategoryHomIsHom] at hy
  have h : y - z ∈ a.g.hom'.ker := by
    rw [CategoryHomIsHom] at h₁
    simp [h₁, hy]

  rw [<- RangeIsKernel a] at h
  rcases h with ⟨w, hw⟩
  rw [<- CategoryHomIsHom] at hw
  rw [<- h₂]
  have hh : y - z = a.f (hr.r y) - a.f (hr.r z) := by
    simp [<- map_sub]
    rw [<- hw]
    simp
  rw [<- hy₂]
  calc
    y - (CategoryTheory.ConcreteCategory.hom a.f) (hr.r y) = y - z + z - (CategoryTheory.ConcreteCategory.hom a.f) (hr.r y) := by abel
    _ = (CategoryTheory.ConcreteCategory.hom a.f) (hr.r y) - (CategoryTheory.ConcreteCategory.hom a.f) (hr.r z) + z - (CategoryTheory.ConcreteCategory.hom a.f) (hr.r y) := by rw [hh]
    _ = z - (CategoryTheory.ConcreteCategory.hom a.f) (hr.r z) := by abel


lemma retractionFunctionFromSectionExistence (a : AddCommGroupSES) (hs : hasSection a) : ∀ x, ∃ w, a.f w = x - hs.s (a.g x) := by
  intro x
  suffices x - hs.s (a.g x) ∈ a.f.hom'.range by exact this
  rw [RangeIsKernel a]
  simp [<- CategoryHomIsHom]

lemma retractionFunctionFromSectionUniqueness (a : AddCommGroupSES) (hs : hasSection a) : ∀ x, ∃! w, a.f w = x - hs.s (a.g x) := by
  intro x
  apply existsUnique_of_exists_of_unique (retractionFunctionFromSectionExistence a hs x)
  intro v w hv hw
  rw [<- hw] at hv
  apply a.injective hv


noncomputable section

variable {a : AddCommGroupSES} (hr : hasRetraction a)

def sectionFunctionFromRetraction : a.X₃ → a.X₂ :=
  λx ↦ Exists.choose (sectionFunctionFromRetractionExistence a hr x)

@[simp]
lemma definedSectionIdentity : ∀ x, a.g (sectionFunctionFromRetraction hr x) = x :=
  λx ↦ (Exists.choose_spec (sectionFunctionFromRetractionExistence a hr x)).1

lemma definedSectionProperty : ∀ x, (sectionFunctionFromRetraction hr x) - a.f (hr.r (sectionFunctionFromRetraction hr x)) = (sectionFunctionFromRetraction hr x) :=
  λx ↦ (Exists.choose_spec (sectionFunctionFromRetractionExistence a hr x)).2

@[simp]
lemma frsIsZero : ∀ x, a.f (hr.r (sectionFunctionFromRetraction hr x)) = 0 := by
  intro x
  calc
    _ = -((sectionFunctionFromRetraction hr x) - (a.f (hr.r (sectionFunctionFromRetraction hr x)))) + (sectionFunctionFromRetraction hr x) := by abel
    _ = 0 := by rw [definedSectionProperty hr x]; abel

lemma definedSectionHom : ∀ x y, sectionFunctionFromRetraction hr (x + y) =
    sectionFunctionFromRetraction hr x + sectionFunctionFromRetraction hr y := by
    intro x y
    apply ExistsUnique.unique (sectionFunctionFromRetractionUniqueness a hr (a.g (sectionFunctionFromRetraction hr (x + y))))
    · simp
    · simp

def sectionHomFromRetraction : a.X₃ →+ a.X₂ := AddMonoidHom.mk' (sectionFunctionFromRetraction hr) (definedSectionHom hr)


def sectionFromRetraction : hasSection a where
  s := sectionHomFromRetraction hr
  isSection := by
    ext x
    simp [<- CategoryHomIsHom]
    apply definedSectionIdentity

end

------------------------------------------------------   -------------------------------------------------------------------

noncomputable section

variable {a : AddCommGroupSES} (hs : hasSection a)

def retractionFunctionFromSection : a.X₂ → a.X₁ :=
  λx ↦ Exists.choose (retractionFunctionFromSectionExistence a hs x)

notation "retraction" => retractionFunctionFromSection

@[simp]
lemma definedRetractionProperty : ∀ x, a.f ((retraction hs) x) = x - hs.s (a.g x) := λx ↦ Exists.choose_spec (retractionFunctionFromSectionExistence a hs x)

@[simp]
lemma definedRetractionIdentity : ∀ x, (retraction hs) (a.f x) = x := by
  intro x
  apply a.injective
  rw [<- CategoryHomIsHom]
  simp
  rfl

lemma definedRetractionHom : ∀ x y, (retraction hs) (x + y) = (retraction hs) x + (retraction hs) y := by
  intro x y
  apply a.injective
  simp [<- CategoryHomIsHom]
  abel

def retractionHomFromSection : a.X₂ →+ a.X₁ := AddMonoidHom.mk' (retraction hs) (definedRetractionHom hs)



def retractionFromSection : hasRetraction a where
  r := retractionHomFromSection hs
  isRetraction := by
    ext x
    simp [<- CategoryHomIsHom]
    apply definedRetractionIdentity


end


------------------------------------------------------   -------------------------------------------------------------------


noncomputable section

variable {dia  : CommDiagramOfSES}


def retractionFromRetraction (bij : Function.Bijective dia.v₁.hom') (r : hasRetraction dia.s₂) : hasRetraction dia.s₁ where
  r := (AddEquiv.ofBijective _ bij).symm.toAddMonoidHom.comp (r.r.comp dia.v₂.hom')
  isRetraction := by
    rw [AddMonoidHom.comp_assoc, AddMonoidHom.comp_assoc, CommLeft, <- AddMonoidHom.comp_assoc _ _ r.r, hasRetraction.isRetraction]
    rw [AddMonoidHom.id_comp]
    ext x
    simp
    apply (AddEquiv.ofBijective dia.v₁.hom' bij).symm.right_inv








end

------------------------------------------------------   -------------------------------------------------------------------

section

variable (A C : Ab)

def ds : Fin 2 → Type*
  | 0 => A
  | 1 => C

instance : ∀ i, AddCommGroup (ds A C i)
  | 0 => by unfold ds; infer_instance
  | 1 => by unfold ds; infer_instance


theorem zeroor1 : ∀ (x : Fin 2), x = 0 ∨ x = 1
  | 0 => by left; rfl
  | 1 => by right; rfl




def mapToProd {A C X : Ab} (f : X ⟶ A) (g : X ⟶ C) : X ⟶ AddCommGrpCat.of (DirectSum _ (ds A C)) :=
  groupHomToGrpHom ((DirectSum.of (ds A C) 0).comp f.hom' + (DirectSum.of (ds A C) 1).comp g.hom')

theorem mapToProdProj₁ {X : Ab} (f : X ⟶ A) (g : X ⟶ C) : ∀ x, (mapToProd f g) x 0 = f x := by
  intro x
  unfold mapToProd
  repeat rw [CategoryHomIsHom]
  simp
  rw [DirectSum.of_eq_of_ne 1 0 _ (by norm_num), add_zero]
  rfl

theorem mapToProdProj₂ {X : Ab} (f : X ⟶ A) (g : X ⟶ C) : ∀ x, (mapToProd f g) x 1 = g x := by
  intro x
  unfold mapToProd
  repeat rw [CategoryHomIsHom]
  simp
  rw [DirectSum.of_eq_of_ne 0 1 _ (by norm_num), zero_add]
  rfl


def trivialSplit : AddCommGroupSES where
  X₁ := AddCommGrpCat.of (ds A C 0)
  X₂ := AddCommGrpCat.of (DirectSum _ (ds A C))
  X₃ := AddCommGrpCat.of (ds A C 1)
  f := groupHomToGrpHom (DirectSum.of (ds A C) (0 : Fin 2))
  g := groupHomToGrpHom (DirectSum.component ℤ _ (ds A C) 1).toAddMonoidHom
  zero := by ext x; simp; rfl
  injective := by rw [groupHomCompatible]; apply DirectSum.of_injective 0
  middle := by
    rintro x hx
    use (DirectSum.component ℤ _ (ds A C) 0) x
    simp
    ext i
    rcases zeroor1 i with h | h
    · rw [h]
      rfl
    · have hh : x 1 = 0 := hx
      rw [h, hh]
      rfl
  surjective := by
    intro y
    use DirectSum.of (ds A C) 1 y
    rfl

end

section


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



lemma carrierConv {A B : Ab} (eq : A = B) : A.carrier = B.carrier := by rw [eq]

def grphomSubst {A B C : Ab} (eq : B = C) (f : A ⟶ B) : A ⟶ C := by rw [eq] at f; apply f

def mapSubst {A B C : Type} (eq : B = C) (f : A → B) : A → C := (cast eq) ∘ f

def mapSubst₂ {A B C : Type} (eq : B = C) (f : A → B) : A → C := by rw [eq] at f; apply f

lemma mapSubstCompatElt {A B C : Type} (eq : B = C) (f : A → B) : ∀ x, mapSubst eq f x = mapSubst₂ eq f x := by intro x; cases eq; rfl

lemma mapSubstCompat {A B C : Type} (eq : B = C) (f : A → B) : mapSubst eq f = mapSubst₂ eq f := funext (mapSubstCompatElt eq f)


lemma grphomSubstCompat {A B C : Ab} (eq : B = C) (f : A ⟶ B) : grphomSubst eq f = (cast (carrierConv eq)).comp f := by
  ext x
  unfold grphomSubst
  simp
  cases eq
  rfl


lemma grphomSubstCompatElt {A B C : Ab} (eq : B = C) (f : A ⟶ B) : ∀ x, (grphomSubst eq f).hom' x = cast (carrierConv eq) (f.hom' x):= by
  intro x
  unfold grphomSubst
  simp
  cases eq
  rfl


lemma grphomSubstCompos {A B C : Ab} {eq : B = C} (f : A ⟶ B) : grphomSubst eq.symm (grphomSubst eq f) = f := by
  unfold grphomSubst
  simp


lemma grphomSubstBij {A B C : Ab} (eq : B = C) (f : A ⟶ B) : Function.Bijective (grphomSubst eq f).hom' → Function.Bijective f.hom' := by
  intro h
  constructor
  · rintro x y hxy
    apply cast.congr_simp (carrierConv eq) _ _ at hxy
    repeat rw [<- grphomSubstCompatElt eq f] at hxy
    apply h.1 hxy
  · intro x
    rcases h.2 (cast (carrierConv eq) x) with ⟨w, hw⟩
    use w
    apply cast.congr_simp (carrierConv eq.symm) _ _ at hw
    simp at hw
    rw [<- hw, grphomSubstCompatElt eq]
    simp

lemma grphomSubstBij₂ {A B C : Ab} (eq : B = C) (f : A ⟶ B) : Function.Bijective f.hom' → Function.Bijective (grphomSubst eq f).hom'  := by
  intro h
  constructor
  · rintro x y hxy
    repeat rw [grphomSubstCompatElt eq f] at hxy
    apply cast.congr_simp (carrierConv eq.symm) _ _ at hxy
    simp at hxy
    apply h.1 hxy
  · intro x
    rcases h.2 (cast (carrierConv eq.symm) x) with ⟨w, hw⟩
    use w
    apply cast.congr_simp (carrierConv eq) _ _ at hw
    simp at hw
    rw [<- hw, grphomSubstCompatElt eq]



structure isSplit (a : AddCommGroupSES) where
  dia : CommDiagramOfSES
  topIsa : dia.s₁ = a
  botIsTriv : dia.s₂ = trivialSplit a.X₁ a.X₃
  eq1 : dia.s₁.X₁ = dia.s₂.X₁
  eq2 : dia.s₁.X₃ = dia.s₂.X₃
  identity1 : dia.v₁ = grphomSubst eq1 (groupHomToGrpHom <| AddMonoidHom.id dia.s₁.X₁)
  identity2 : dia.v₃ = grphomSubst eq2 (groupHomToGrpHom <| AddMonoidHom.id dia.s₁.X₃)


theorem isSplitBijection {a : AddCommGroupSES} (split : isSplit a) : Function.Bijective split.dia.v₂.hom' := by
  apply fiveLemma
  · rw [split.identity1]
    apply grphomSubstBij₂ split.eq1 (groupHomToGrpHom <| AddMonoidHom.id split.dia.s₁.X₁)
    simp
    exact Function.bijective_id
  · rw [split.identity2]
    apply grphomSubstBij₂ split.eq2 (groupHomToGrpHom <| AddMonoidHom.id split.dia.s₁.X₃)
    simp
    exact Function.bijective_id


def trivialSplitCommDiagram (A C : Ab) : CommDiagramOfSES where
  s₁ := trivialSplit A C
  s₂ := trivialSplit A C
  v₁ := grphomSubst (by rfl) (groupHomToGrpHom <| AddMonoidHom.id _)
  v₂ := grphomSubst (by rfl) (groupHomToGrpHom <| AddMonoidHom.id _)
  v₃ := grphomSubst (by rfl) (groupHomToGrpHom <| AddMonoidHom.id _)
  commleft := rfl
  commright := rfl

def trivialSplitIsSplit (A C : Ab) : isSplit (trivialSplit A C) where
  dia := trivialSplitCommDiagram A C
  topIsa := rfl
  botIsTriv := rfl
  eq1 := rfl
  eq2 := rfl
  identity1 := rfl
  identity2 := rfl

end
