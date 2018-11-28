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



VSet : ∀{α} → (n : ℕ) → Set (lsuc α)
VSet {α} n = Vec (Set α) n

V⊤ : (n : ℕ) → VSet {lzero} n
V⊤ zero = []
V⊤ (suc n) = ⊤ ∷ V⊤ n

V⊤′ : ∀{α} → (n : ℕ) → VSet {α} n
V⊤′ zero = []
V⊤′ (suc n) = ℓ↑ _ ⊤ ∷ V⊤′ n

VS : ∀{α} → Set α → (n : ℕ) → VSet {α} n
VS A zero = []
VS A (suc n) = A ∷ VS A n

_toPS : ∀{α l} → VSet {α} l → Set α
_toPS (E ∷ pd) = E × (pd toPS)
_toPS [] = ℓ↑ _ ⊤

_toUS : ∀{α l} → VSet {α} l → Set α
_toUS (E ∷ pd) = E ⊎ (pd toUS)
_toUS [] = ℓ↑ _ ⊥


split : ∀{α l1 l2} → (PE : VSet {α} l1) → (PB : VSet {α} l2) → (PE ++ PB) toUS → (PE toUS) ⊎ (PB toUS)
split [] PB x = u→ x
split (E ∷ PE) PB (x ←u) = (x ←u) ←u
split (E ∷ PE) PB (u→ x)
  = case (split PE PB x) of
    λ { (x ←u) → (u→ x) ←u ; (u→ x) → u→ x}


System = _toPS

_≡_all : ∀{α n} → {PE : VSet {α} n} → System PE → System PE → Set α
_≡_all {PE = []} sys nsys = ℓ↑ _ ⊤
_≡_all {PE = x ∷ PE} sys nsys = fst sys ≡ fst nsys × (snd sys ≡ snd nsys all)



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


stAction : ∀{α n} → (vars : VSet {α} n) → Action (ℓ↑ _ ⊤) vars
cond (stAction vars) e sys = ℓ↑ _ ⊤
resp (stAction vars) e sys nsys = sys ≡ nsys all


infixr 5 _∷ₛₚ_
data Spec {α n} (vars : VSet {α} n) : ∀{sl} → (PE : VSet {α} sl) → Set (lsuc α) where
  _∷ₛₚ_ : ∀{el E} → {PE : VSet el} → (act : Action E vars) → (pspec : Spec vars PE) → Spec vars (E ∷ PE)
  []ₛₚ : Spec vars []


_++ₛₚ_ : ∀{α n sl esl} → {vars : VSet {α} n} → {PE : VSet {α} sl} → {PEST : VSet {α} esl}
         → Spec vars PE → Spec vars PEST
         → Spec vars (PE ++ PEST)
(act ∷ₛₚ specA) ++ₛₚ specB = act ∷ₛₚ (specA ++ₛₚ specB)
[]ₛₚ ++ₛₚ specB = specB



infixr -20 _$ₛₚ_
_$ₛₚ_ : ∀{α l vars k PE} → (Spec {α} {l} vars {sl = k} PE) → (pe : PE toUS) → (sys nsys : System vars) → Set α
(act ∷ₛₚ spec $ₛₚ (e ←u)) sys nsys = cond act e sys × resp act e sys nsys
(act ∷ₛₚ spec $ₛₚ (u→ pe)) sys nsys = (spec $ₛₚ pe) sys nsys
([]ₛₚ $ₛₚ ()) sys nsys


infixr -20 _$ₛₚₜ_
_$ₛₚₜ_ : ∀{α l vars k PE} → (Spec {α} {l} vars {sl = k} PE) → (pe : (PE toUS) ʷ) → (beh : (System vars) ʷ) → (Set α) ʷ
(spec $ₛₚₜ pe) beh = ⟨ spec $ₛₚ_ ⟩ $ pe $ beh $ ○ beh
