module TLA.Def where


open import Prelude.Nat public
open import Prelude.Unit public
open import Prelude.Function using (case_of_)
open import Prelude.Vec public
open import Prelude.Sum renaming (Either to _⊎_) public
open import Prelude.Product public
open import Prelude.Empty public
open import Agda.Primitive public

open import LTL.Core public
open import LTL.Sum public
open import LTL.Stateless public


pattern u→_ pe = right pe
pattern _←u e  = left e

variable
  α : Level
  l : Nat
  l1 : Nat
  l2 : Nat
  el : Nat
  esl : Nat
  bl : Nat
  E : Set α
  B : Set α




VSet : (n : Nat) → Set (lsuc α)
VSet {α} n = Vec (Set α) n

V⊤ : (n : Nat) → VSet {lzero} n
V⊤ zero = []
V⊤ (suc n) = ⊤ ∷ V⊤ n

V⊤′ : (n : Nat) → VSet {α} n
V⊤′ zero = []
V⊤′ (suc n) = ⊤′ ∷ V⊤′ n

VS : Set α → (n : Nat) → VSet {α} n
VS A zero = []
VS A (suc n) = A ∷ VS A n

_toPS : VSet {α} l → Set α
_toPS (E ∷ pd) = E × (pd toPS)
_toPS [] = ⊤′

_toUS : VSet {α} l → Set α
_toUS (E ∷ pd) = E ⊎ (pd toUS)
_toUS [] = ⊥′


split : (PE : VSet {α} l1) → (PB : VSet {α} l2) → (PE v++ PB) toUS → (PE toUS) ⊎ (PB toUS)
split [] PB x = u→ x
split (E ∷ PE) PB (x ←u) = (x ←u) ←u
split (E ∷ PE) PB (u→ x)
  = case (split PE PB x) of
    λ { (x ←u) → (u→ x) ←u ; (u→ x) → u→ x}


System = _toPS




record Action {α n} (E : Set α) (vars : VSet {α} n) : Set (lsuc α) where
  field
    cond : (e : E) → (sys : System vars) → Set α
    resp : (e : E) → (sys : System vars) → (nsys : System vars) → Set α

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
  PEST : VSet {α} esl
  PB : VSet {α} bl

infixr 5 _∷ₛₚ_
data Spec {α n} (vars : VSet {α} n) : ∀{sl} → (PE : VSet {α} sl) → Set (lsuc α) where
  _∷ₛₚ_ : (act : Action E vars) → (pspec : Spec vars PE) → Spec vars (E ∷ PE)
  []ₛₚ : Spec vars []

variable
  spec : Spec _ _


Stut : (sys : System {α} vars) → (System {α} vars) → Set α
Stut sys nsys = sys ≡ nsys

TStut : (beh : (System {α} vars) ʷ) → (Set α) ʷ
TStut {vars = vars} beh = ⟨ Stut {vars = vars} ⟩ $ʷ beh $ʷ (○ beh)

<_>_$_ : (PE : VSet el) → (Spec {α} vars PE) → (pe : PE toUS) → (sys nsys : System vars) → Set α
(< E ∷ PE > act ∷ₛₚ spec $ (e ←u)) sys nsys = cond act e sys × resp act e sys nsys
(< E ∷ PE > act ∷ₛₚ spec $ (u→ pe)) sys nsys = (< PE > spec $ pe) sys nsys



<_>_$ₜ_ : (PE : VSet el) → (Spec {α} vars PE) → (pe : (PE toUS) ʷ) → (beh : (System vars) ʷ) → (Set α) ʷ
(< PE > spec $ₜ pe) beh = ⟨ < PE > spec $_ ⟩ $ʷ pe $ʷ beh $ʷ ○ beh


Restr : {PE : VSet el} → (spec : Spec {α} vars PE) → (beh : (System vars) ʷ) → (pe : (PE toUS) ʷ) → (Set α) ʷ
Restr {vars = vars} {PE = PE} spec beh pe = (< PE > spec $ₜ pe) beh ∨ TStut {vars = vars} beh
