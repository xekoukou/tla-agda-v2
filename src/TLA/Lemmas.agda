module TLA.Lemmas where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Function.Inverse hiding (sym)
open import Data.Fin.Permutation
open import TLA.Def
open import TLA.Refine
open import Data.List
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)



actP : ∀{α n} → {vars : VSet {α} n} → (P : (sys nsys : System vars) → Set α) → Action (ℓ↑ _ ⊤) vars
cond (actP P) e sys = ℓ↑ _ ⊤
resp (actP P) e sys nsys = P sys nsys


act¬P : ∀{α n} → {vars : VSet {α} n} → (P : (sys nsys : System vars) → Set α) → Action (ℓ↑ _ ⊤) vars
cond (act¬P P) e sys = ℓ↑ _ ⊤
resp (act¬P P) e sys nsys = ¬ P sys nsys


specP : ∀{α n} → {vars : VSet {α} n} → (P : (sys nsys : System vars) → Set α) → Spec vars (V⊤′ 2)
specP P = actP P ∷ₛₚ act¬P P ∷ₛₚ []ₛₚ



RefActP : ∀{α n} → {varsA : VSet {α} n} 
          → (P : (sys nsys : System varsA) → Set α) → Set (lsuc α)
RefActP P = RefAction (λ x → x) (actP P)


RefAct¬P : ∀{α n} → {varsA : VSet {α} n} 
           → (P : (sys nsys : System varsA) → Set α) → Set (lsuc α)
RefAct¬P P = RefAction (λ x → x) (act¬P P)


record SetoidWithSym c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    sym           : Symmetric _≈_


open SetoidWithSym

specSetoidWS : ∀{α n sl} → {vars : VSet {α} n} → {PE : VSet {α} sl} → Spec vars PE → SetoidWithSym _ _
Carrier (specSetoidWS {vars = vars} spec) = System vars × System vars
_≈_ (specSetoidWS {vars = vars} {PE = PE} spec) (sysA , nsysA) (sysB , nsysB)
  = Σ (PE toUS) λ pe → (spec $ₛₚ pe) sysA nsysA × (spec $ₛₚ pe) sysB nsysB
sym (specSetoidWS spec) (pe , a , b) = pe , b , a





cndP : ∀{α k el} → {vars : VSet {α} k} → {PE : VSet {α} el} → (P : (sys nsys : System vars) → Set α)
       → RSpec (λ x → x) PE (specP P) → (sys nsys : System vars) → Set α
cndP P (ref m∷ᵣₛₚ rspec) sys nsys
  = let act = ract ref
    in (∃ λ pe → (cond act pe sys × resp act pe sys nsys)) ⊎ cndP P rspec sys nsys
cndP P (ref ∷ᵣₛₚ rspec) sys nsys
  = let act = ract ref
    in ∃ λ pe → cond act pe sys × resp act pe sys nsys


cnd¬P : ∀{α k el} → {vars : VSet {α} k} → {PE : VSet {α} el} → (P : (sys nsys : System vars) → Set α)
        → RSpec (λ x → x) PE (specP P) → (sys nsys : System vars) → Set α
cnd¬P P (ref m∷ᵣₛₚ rspec) sys nsys = cnd¬P P rspec sys nsys
cnd¬P P (pref ∷ᵣₛₚ (ref m∷ᵣₛₚ rspec)) sys nsys
  = let act = ract ref
    in (∃ λ pe → (cond act pe sys × resp act pe sys nsys)) ⊎ cnd¬P P (pref ∷ᵣₛₚ rspec) sys nsys
cnd¬P P (_ ∷ᵣₛₚ (ref ∷ᵣₛₚ []ᵣₛₚ)) sys nsys
  =  let act = ract ref
     in ∃ λ pe → (cond act pe sys × resp act pe sys nsys)


-- We should never have to use gcnd
P⇒cndP : ∀{α l vars el PE}  → (P : (sys nsys : System {_} {l} vars) → Set α)
     → (rspec : RSpec (λ x → x) {el = el} PE (specP P)) → (pe : PE toUS) → (sys nsys : System vars)
     → exGcond rspec pe sys
     → ((exSpec rspec) $ₛₚ pe) sys nsys → P sys nsys → cndP P rspec sys nsys
P⇒cndP P (ref m∷ᵣₛₚ rspec) (e ←u) sys nsys gcnd rst p = (e , rst) ←u
P⇒cndP P (ref m∷ᵣₛₚ rspec) (u→ pe) sys nsys gcnd rst p = u→ P⇒cndP P rspec pe sys nsys gcnd rst p
P⇒cndP P (pref ∷ᵣₛₚ rspec) (e ←u) sys nsys gcnd rst p = e , rst
P⇒cndP P rspec@(_ ∷ᵣₛₚ _) (u→ pe) sys nsys gcnd rst p with refTh rspec sys nsys (u→ pe) gcnd rst
P⇒cndP P (pref ∷ᵣₛₚ (ref m∷ᵣₛₚ rspec)) (u→ (e ←u)) sys nsys gcnd rst p | _ , ¬p = ⊥-elim (¬p p)
P⇒cndP P (pref ∷ᵣₛₚ (ref m∷ᵣₛₚ rspec)) (u→ (u→ pe)) sys nsys gcnd rst p | r
  = P⇒cndP P (pref ∷ᵣₛₚ rspec) (u→ pe) sys nsys gcnd rst p
P⇒cndP P (pref ∷ᵣₛₚ (ref ∷ᵣₛₚ []ᵣₛₚ)) (u→ (e ←u)) sys nsys gcnd rst p | _ , ¬p = ⊥-elim (¬p p)
P⇒cndP P (pref ∷ᵣₛₚ (ref ∷ᵣₛₚ []ᵣₛₚ)) (u→ (u→ (lift ()))) sys nsys gcnd rst p | r 



open Inverse

getPmVec : ∀{k} → Permutation′ k → Vec (Fin k) k
getPmVec {k} pm = getPmVec′ k where
  getPmVec′ : (n : ℕ) → Vec (Fin k) n
  getPmVec′ zero = {!(to pm)∷ []!}
  getPmVec′ (suc n) = {!!} 

permPE : ∀{α k} → Permutation′ k → Vec (Set α) k → Vec (Set α) k
permPE pm PE = {!!}


permSpec : ∀{α l vars k PE} → Spec {α} {l} vars {sl = k} PE → Spec {α} {l} vars {sl = k} {!!}
permSpec = {!!}
           
