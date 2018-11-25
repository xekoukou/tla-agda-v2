module TLA.Def where


open import Data.Nat hiding (_⊔_)
open import Data.Unit using (⊤)
open import Function using (case_of_)
open import Data.Vec hiding (split)
open import Data.Sum
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)

open import LTL.Core
open import LTL.Sum
open import LTL.Stateless


pattern u→_ pe = inj₂ pe
pattern _←u e  = inj₁ e

variable
  α : Level
  l : ℕ
  l1 : ℕ
  l2 : ℕ
  el : ℕ
  esl : ℕ
  bl : ℕ
  E : Set α
  B : Set α




VSet : (n : ℕ) → Set (lsuc α)
VSet {α} n = Vec (Set α) n

V⊤ : (n : ℕ) → VSet {lzero} n
V⊤ zero = []
V⊤ (suc n) = ⊤ ∷ V⊤ n

V⊤′ : (n : ℕ) → VSet {α} n
V⊤′ zero = []
V⊤′ (suc n) = ℓ↑ _ ⊤ ∷ V⊤′ n

VS : Set α → (n : ℕ) → VSet {α} n
VS A zero = []
VS A (suc n) = A ∷ VS A n

_toPS : VSet {α} l → Set α
_toPS (E ∷ pd) = E × (pd toPS)
_toPS [] = ℓ↑ _ ⊤

_toUS : VSet {α} l → Set α
_toUS (E ∷ pd) = E ⊎ (pd toUS)
_toUS [] = ℓ↑ _ ⊥


split : (PE : VSet {α} l1) → (PB : VSet {α} l2) → (PE ++ PB) toUS → (PE toUS) ⊎ (PB toUS)
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



_≡_all : ∀{n} → {PE : VSet {α} n} → System PE → System PE → Set α
_≡_all {PE = []} sys nsys = ℓ↑ _ ⊤
_≡_all {PE = x ∷ PE} sys nsys = fst sys ≡ fst nsys × (snd sys ≡ snd nsys all)



Stut : (sys : System {α} vars) → (System {α} vars) → Set α
Stut sys nsys = sys ≡ nsys all

TStut : (beh : (System {α} vars) ʷ) → (Set α) ʷ
TStut {vars = vars} beh = ⟨ Stut {vars = vars} ⟩ $ beh $ (○ beh)

infixr -20 _$ₛₚ_
_$ₛₚ_ : (Spec {α} vars PE) → (pe : PE toUS) → (sys nsys : System vars) → Set α
(act ∷ₛₚ spec $ₛₚ (e ←u)) sys nsys = cond act e sys × resp act e sys nsys
(act ∷ₛₚ spec $ₛₚ (u→ pe)) sys nsys = (spec $ₛₚ pe) sys nsys
([]ₛₚ $ₛₚ ()) sys nsys


infixr -20 _$ₛₚₜ_
_$ₛₚₜ_ : (Spec {α} vars PE) → (pe : (PE toUS) ʷ) → (beh : (System vars) ʷ) → (Set α) ʷ
(spec $ₛₚₜ pe) beh = ⟨ spec $ₛₚ_ ⟩ $ pe $ beh $ ○ beh


Restr : {PE : VSet el} → (spec : Spec {α} vars PE) → (beh : (System vars) ʷ) → (pe : (PE toUS) ʷ) → (Set α) ʷ
Restr {vars = vars} {PE = PE} spec beh pe = (spec $ₛₚₜ pe) beh ∨ TStut {vars = vars} beh
