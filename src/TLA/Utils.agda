module TLA.Utils where

open import TLA.Def
open import Data.Fin hiding (lift)
open import Data.Unit using (⊤ ; tt)
open import Level renaming (Lift to ℓ↑ ; lift to lift)
open import Data.Vec
open import Data.Nat hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

proj : ∀{α n} → {PE : VSet {α} n} → System PE → (i : Fin n) → lookup i PE 
proj {PE = []} sys ()
proj {PE = E ∷ PE} sys zero = fst sys
proj {PE = E ∷ PE} sys (suc i) = proj (snd sys) i


_except_!=_ : ∀{α n} → {PE : VSet {α} n} → System PE → (i : Fin n) → lookup i PE → System PE
_except_!=_ {PE = []} sys () nv
_except_!=_ {PE = E ∷ PE} sys zero nv = nv , snd sys
_except_!=_ {PE = E ∷ PE} sys (suc i) nv = fst sys , snd sys except i != nv 

-- _≡_all in TLA.Def to pointwise have equality for all.

refl-all : ∀{α n} → {varsB : VSet {α} n} → {sys : System varsB}
           → sys ≡ sys all
refl-all {varsB = []} {sys} = lift tt
refl-all {varsB = x ∷ varsB} {sys} = refl , refl-all {sys = snd sys}

pEq⇒Eq : ∀{α n} → {varsB : VSet {α} n} → {sys nsys : System varsB}
              → sys ≡ nsys all → sys ≡ nsys
pEq⇒Eq {varsB = []} {lift tt} {lift tt} eq = refl
pEq⇒Eq {varsB = _ ∷ varsB} {_ , sys} {x , nsys} (refl , sn) = cong (x ,_) (pEq⇒Eq sn)


_≡_except_ : ∀{α n} → {PE : VSet {α} n} → System PE → System PE → (i : Fin n) → Set α
_≡_except_ {PE = []} sys nsys ()
_≡_except_ {PE = E ∷ PE} sys nsys zero = snd sys ≡ snd nsys all
_≡_except_ {PE = E ∷ PE} sys nsys (suc i) = fst sys ≡ fst nsys × (snd sys ≡ snd nsys except i)


_at_ : ∀{α RM} → {A : Set α} → System (VS A RM) → Fin RM → A 
sys at zero = fst sys
sys at suc e = snd sys at e

