module TLA.Utils where

open import TLA.Def
open import Data.Fin hiding (lift)
open import Data.Unit using (⊤ ; tt)
open import Level renaming (Lift to ℓ↑ ; lift to lift ; suc to lsuc ; zero to lzero)
open import Data.List hiding (all)
open import Relation.Nullary
open import Data.Empty
open import Data.Nat hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

proj : ∀{α} → {PE : LSet {α}} → System PE → (i : Fin (length PE)) → lookup PE i
proj {PE = []} sys ()
proj {PE = E ∷ PE} sys zero = fst sys
proj {PE = E ∷ PE} sys (suc i) = proj (snd sys) i


_except_!=_ : ∀{α n} → {A : Set α} → System (VS A n) → (i : Fin n) → A → System (VS A n)
_except_!=_ sys zero nv = nv , snd sys
_except_!=_ sys (suc i) nv = fst sys , snd sys except i != nv 

-- _≡_all in TLA.Def to pointwise have equality for all.

refl-all : ∀{α} → {varsB : LSet {α}} → {sys : System varsB}
           → sys ≡ sys all
refl-all {varsB = []} {sys} = lift tt
refl-all {varsB = x ∷ varsB} {sys} = refl , refl-all {sys = snd sys}

pEq⇒Eq : ∀{α} → {varsB : LSet {α}} → {sys nsys : System varsB}
              → sys ≡ nsys all → sys ≡ nsys
pEq⇒Eq {varsB = []} {lift tt} {lift tt} eq = refl
pEq⇒Eq {varsB = _ ∷ varsB} {_ , sys} {x , nsys} (refl , sn) = cong (x ,_) (pEq⇒Eq sn)


_≡_Except_!=_ : ∀{α n} → {A : Set α} → System (VS A n) → System (VS A n) → (i : Fin n)
                → ((v : A) → (nv : A) → Set α) → Set α
_≡_Except_!=_ nsys sys zero A = A (fst sys) (fst nsys) × snd nsys ≡ snd sys all
_≡_Except_!=_ nsys sys (suc i) A = fst nsys ≡ fst sys × (snd nsys ≡ snd sys Except i != A)


_at_ : ∀{α n} → {A : Set α} → System (VS A n) → Fin n → A 
sys at zero = fst sys
sys at suc e = snd sys at e


≡allAt : ∀{α n} → {A : Set α} → {sys nsys : System (VS A n)} → (j : Fin n)
       → nsys ≡ sys all → nsys at j ≡ sys at j
≡allAt j x with pEq⇒Eq x
≡allAt j x | refl = refl

exceptEq : ∀{α n} → {A : Set α} → {sys nsys : System (VS A n)}
      → {P : (v : A) → (nv : A) → Set α} → (i j : Fin n) → i ≡ j
      → nsys ≡ sys Except i != P → P (sys at j) (nsys at j)
exceptEq zero zero eq exc = fst exc
exceptEq zero (suc j) () exc
exceptEq (suc i) zero () exc
exceptEq (suc i) (suc i) refl exc = exceptEq i i refl (snd exc)

exceptNEq : ∀{α n} → {A : Set α} → {sys nsys : System (VS A n)}
      → {P : (v : A) → (nv : A) → Set α} → (i j : Fin n) → ¬ i ≡ j
      → nsys ≡ sys Except i != P → nsys at j ≡ sys at j
exceptNEq zero zero neq exc = ⊥-elim (neq refl)
exceptNEq zero (suc j) neq exc = ≡allAt j (snd exc)
exceptNEq (suc i) zero neq exc = fst exc
exceptNEq (suc i) (suc j) neq exc = exceptNEq i j (λ x → neq (cong suc x)) (snd exc)


exceptP⇒Q :  ∀{α n} → {A : Set α} → {sys nsys : System (VS A n)} → {i : Fin n} 
      → {P Q : (v : A) → (nv : A) → Set α} → (∀ (v nv) → P v nv → Q v nv)
      → nsys ≡ sys Except i != P → nsys ≡ sys Except i != Q
exceptP⇒Q {i = zero} x y = x _ _ (fst y) , snd y
exceptP⇒Q {i = suc i} x y = fst y , exceptP⇒Q x (snd y)


except&at :  ∀{α n} → {A : Set α} → {sys nsys : System (VS A n)} → {i : Fin n} 
      → {P Q : (v : A) → (nv : A) → Set α} → Q (sys at i) (nsys at i)
      → nsys ≡ sys Except i != P → nsys ≡ sys Except i != λ v nv → P v nv × Q v nv
except&at {i = zero} q exc = (fst exc , q) , snd exc
except&at {i = suc i} q exc = fst exc , except&at q (snd exc)
