module TLA.Def3 where


open import Prelude.Nat public
open import Prelude.Unit public
open import Prelude.Vec public
open import Prelude.Sum renaming (Either to _⊎_ ; right to u→_ ; left to _←u) public
open import Prelude.Product public
open import Agda.Primitive public

open import LTL.Core public
open import LTL.Stateless public


variable
  α : Level
  l : Nat
  el : Nat
  bl : Nat
  E : Set α
  B : Set α




VSet : (n : Nat) → Set (lsuc α)
VSet {α} n = Vec (Set α) (suc n)


_toPS : VSet {α} l → Set α
_toPS (E ∷ pd@(_ ∷ _)) = E × (pd toPS)
_toPS (E ∷ pd) = E

_toUS : VSet {α} l → Set α
_toUS (E ∷ pd@(_ ∷ _)) = E ⊎ (pd toUS)
_toUS (E ∷ pd) = E


System = _toPS


record Action {α n} (E : Set α) (vars : VSet {α} n) : Set (lsuc α) where
  field
    cond : E → (sys : System vars) → Set α
    resp : E → (sys : System vars) → (nsys : System vars) → Set α

open Action public


record ConAction {α n}  {E : Set α} {vars : VSet {α} n} (act : Action E vars) : Set (lsuc α) where
  field
    par : System vars → E
    impl : (sys : System vars) → (cnd : ((cond act) (par sys)) sys) → System vars
    safety : (sys : System vars) → (cnd : ((cond act) (par sys)) sys) → (resp act) (par sys) sys (impl sys cnd)
open ConAction public

variable
  vars : VSet {α} l
  act : Action  E vars
  


variable
  PE : VSet {α} el
  PB : VSet {α} bl

data Spec {α n} (vars : VSet {α} n) : ∀{sl} → (PE : VSet {α} sl) → Set (lsuc α) where
  _∷ₛₚ_ : (act : Action E vars) → (pspec : Spec vars PE) → Spec vars (E ∷ PE)
  _■ : (act : Action E vars) → Spec vars (E ∷ [])

variable
  spec : Spec _ _


Stut : (sys : System {α} vars) → (System {α} vars) → Set α
Stut sys nsys = sys ≡ nsys

TStut : (beh : (System {α} vars) ʷ) → (Set α) ʷ
TStut {vars = vars} beh = ⟨ Stut {vars = vars} ⟩ $ʷ beh $ʷ (○ beh)

<_>_$_ : (PE : VSet el) → (Spec {α} vars PE) → (pe : PE toUS) → (sys nsys : System vars) → Set α
(< E ∷ [] > act ■ $ e) sys nsys = cond act e sys × resp act e sys nsys
(< E ∷ _ ∷ _ > act ∷ₛₚ spec $ _←u e) sys nsys = cond act e sys × resp act e sys nsys
(< E ∷ PE@(_ ∷ _) > act ∷ₛₚ spec $ u→_ pe) sys nsys = (< PE > spec $ pe) sys nsys




<_>_$ₜ_ : (PE : VSet el) → (Spec {α} vars PE) → (pe : (PE toUS) ʷ) → (beh : (System vars) ʷ) → (Set α) ʷ
(< PE > spec $ₜ pe) beh = ⟨ < PE > spec $_ ⟩ $ʷ pe $ʷ beh $ʷ ○ beh

