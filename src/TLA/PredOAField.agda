module TLA.PredOAField where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (sym)
open import Relation.Nullary
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_)
open import Function.Inverse hiding (sym)
open import Data.Fin.Permutation
open import TLA.Def
open import TLA.Refine
open import Data.List
open import Data.List.Any
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Function
open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)


-- Using a Predicate over an action field can be used to find a section in the space of variables 
-- where the predicate is true. The general methodology is as follows.
-- a) Given two points of a behavior who are different from one another, there is a time s between them
-- were there was a change. This change could have only be done in an action.
-- b) We create a Predicate that tells that sys has the same value as the outside point and and nsys does not.
-- We identify the section of variables in which the predicate is true.
-- c) This means that at the point s, our behabior must be part of that section, and thus must be constrained by
-- conditions. We find the constrains with P⇒cndP or we prove that our original argument was impossible with P⇒∅


-- Another use of this is to prove Inductive Properties G sys by setting the predicate P to
-- G sys → G nsys

actP : ∀{α} → {vars : LSet {α}} → (P : (sys nsys : System vars) → Set α) → Action vars
E (actP P) = ℓ↑ _ ⊤
cond (actP P) e sys = ℓ↑ _ ⊤
resp (actP P) e sys nsys = P sys nsys


act¬P : ∀{α} → {vars : LSet {α}} → (P : (sys nsys : System vars) → Set α) → Action vars
E (act¬P P) = ℓ↑ _ ⊤
cond (act¬P P) e sys = ℓ↑ _ ⊤
resp (act¬P P) e sys nsys = ¬ P sys nsys

-- The order of actP is important for the definition of cndP.
specP : ∀{α} → {vars : LSet {α}} → (P : (sys nsys : System vars) → Set α) → Spec vars
specP P = actP P ∷ act¬P P ∷ []

specP∅ : ∀{α} → {vars : LSet {α}} → (P : (sys nsys : System vars) → Set α) → Spec vars
specP∅ P = act¬P P ∷ []

RefActP : ∀{α} → {varsA : LSet {α}} → ∀ actB
          → (P : (sys nsys : System varsA) → Set α) → Set (lsuc α)
RefActP actB P = RefAction (λ x → x) (λ _ → ℓ↑ _ ⊤) actB (actP P)


RefAct¬P : ∀{α} → {varsA : LSet {α}} → ∀ actB
           → (P : (sys nsys : System varsA) → Set α) → Set (lsuc α)
RefAct¬P actB P = RefAction (λ x → x) (λ _ → ℓ↑ _ ⊤) actB (act¬P P)


record SetoidWithSym c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    sym           : Symmetric _≈_


open SetoidWithSym

specSetoidWS : ∀{α} → {vars : LSet {α}} → Spec vars → SetoidWithSym _ _
Carrier (specSetoidWS {vars = vars} spec) = System vars × System vars
_≈_ (specSetoidWS {vars = vars} spec) (sysA , nsysA) (sysB , nsysB)
  = Σ (PE spec toUS) λ pe → (spec $ₛₚ pe) sysA nsysA × (spec $ₛₚ pe) sysB nsysB
sym (specSetoidWS spec) (pe , a , b) = pe , b , a





cndP : ∀{α} → {vars : LSet {α}} → ∀{specB} → (P : (sys nsys : System vars) → Set α)
       → RSpec (λ x → x) (λ _ → ℓ↑ _ ⊤) (specP P) specB → (sys nsys : System vars) → Set α
cndP P []ᵣ sys nsys = ℓ↑ _ ⊥
cndP P (_∷ᵣ_ {act = act} x rspec) sys nsys
  = case (bel x) of
      λ { (here _) → let ra = act
                     in (∃ λ pe → (cond ra pe sys × resp ra pe sys nsys)) ⊎ cndP P rspec sys nsys
        ; (there _) → cndP P rspec sys nsys}


cnd¬P : ∀{α} → {vars : LSet {α}} → ∀{specB} → (P : (sys nsys : System vars) → Set α)
       → RSpec (λ x → x) (λ _ → ℓ↑ _ ⊤) (specP P) specB → (sys nsys : System vars) → Set α
cnd¬P P []ᵣ sys nsys = ℓ↑ _ ⊥
cnd¬P P (_∷ᵣ_ {act = act} x rspec) sys nsys
  = case (bel x) of
      λ { (there _) → let ra = act
                     in (∃ λ pe → (cond ra pe sys × resp ra pe sys nsys)) ⊎ cndP P rspec sys nsys
        ; (here _) → cndP P rspec sys nsys}




P⇒cndP : ∀{α vars}  → ∀{specB} → (P : (sys nsys : System {_} vars) → Set α)
     → (rspec : RSpec (λ x → x) (λ _ → ℓ↑ _ ⊤) (specP P) specB) → (pe : PE specB toUS) → (sys nsys : System vars)
     → (specB $ₛₚ pe) sys nsys → P sys nsys → cndP P rspec sys nsys
P⇒cndP P []ᵣ (ℓ↑.lift ()) sys nsys rst p
P⇒cndP P (rsa act (here px) ref ∷ᵣ rspec) (e ←u) sys nsys rst p = (e , rst) ←u
P⇒cndP P (rsa .(act¬P P) (there (here refl)) ref ∷ᵣ rspec) (e ←u) sys nsys rst p = ⊥-elim (proj₂ (embed ref e sys nsys (ℓ↑.lift tt) rst) p)
P⇒cndP P (rsa act (there (there ())) ref ∷ᵣ rspec) (e ←u) sys nsys rst p
P⇒cndP P (rsa act (here px) ref ∷ᵣ rspec) (u→ pe) sys nsys rst p = u→ P⇒cndP P rspec pe sys nsys rst p
P⇒cndP P (rsa act (there bel) ref ∷ᵣ rspec) (u→ pe) sys nsys rst p = P⇒cndP P rspec pe sys nsys rst p


P⇒∅ : ∀{α vars}  → ∀{specB} → (P : (sys nsys : System {_} vars) → Set α)
      → (rspec : RSpec (λ x → x) (λ _ → ℓ↑ _ ⊤) (specP∅ P) specB) → (pe : PE specB toUS) → (sys nsys : System vars)
      → (specB $ₛₚ pe) sys nsys → P sys nsys → ⊥
P⇒∅ P []ᵣ (ℓ↑.lift ()) sys nsys rst p
P⇒∅ P (rsa .(act¬P P) (here refl) ref ∷ᵣ rspec) (e ←u) sys nsys rst p = proj₂ (embed ref e sys nsys (ℓ↑.lift tt) rst) p
P⇒∅ P (rsa act (there ()) ref ∷ᵣ rspec) (e ←u) sys nsys rst p
P⇒∅ P (rsa act bel ref ∷ᵣ rspec) (u→ pe) sys nsys rst p = P⇒∅ P rspec pe sys nsys rst p



