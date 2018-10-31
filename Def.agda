module Def where

open import Prelude.Vec public
open import Prelude.Nat public
open import Prelude.Empty public
open import Prelude.Product public
open import Prelude.Decidable public
open import Prelude.Sum renaming (Either to _⊎_) public
open import Prelude.Functor public
open import Prelude.Equality public

open import LTL.Core public
open import LTL.Stateless public

open import Agda.Primitive public


variable
  α β : Level
  n k : Nat


-- Non Termporal so as to be used by Actions.
System : Vec (Set α) (suc n) → Set α
System (x ∷ []) = x
System (x ∷ y ∷ xs) = x × System (y ∷ xs)



record Action {α n} (vars : Vec (Set α) (suc n)) : Set (lsuc α) where
  field
    cond : System vars → Set α
    -- First represent the current vars and the second, the next ones.
    resp : System vars → System vars → Set α

open Action public

variable
  vars varsA varsB : Vec (Set _) (suc _)
  act actA actB : Action _


-- The action will only be triggered when the condition is true, so there are multiple implementations with the same behavior,
-- it is best though to return the identity on all the other cases.
record ConAction {α n} {vars : Vec (Set α) (suc n)} (act : Action vars) : Set (lsuc α) where
  field
    impl : (x : System vars) → (cond act) x → ∃ (λ nx → resp act x nx)
open ConAction public


simpl : ConAction {vars = vars} act → ((x : System vars) → (cond act) x → System vars)
simpl cact x cnd = fst ((impl cact) x cnd)




Spec : (vars : Vec (Set α) (suc n)) → (k : Nat) → Set (lsuc α)
Spec {_} {_} vars k = Vec (Action vars) (suc k)

variable
  spec specA specB : Spec _ _
  beh behA behB :  (System _) ʷ


Vdecide : Vec (Set α) (suc n) → Set α
Vdecide (x ∷ []) = Dec x
Vdecide (x ∷ x₁ ∷ xs) = Dec x × Vdecide (x₁ ∷ xs)

VdecideP : (c : Vec (Set α) (suc n)) → Vec (Set α) (suc n) → Vdecide c → Set α
VdecideP (x ∷ []) (y ∷ []) (yes z) = y 
VdecideP (x ∷ []) y (no z) = ⊥′
VdecideP (x ∷ x₁ ∷ c) (y ∷ ys) (yes z , zs) = y ⊎ (VdecideP (x₁ ∷ c) ys zs)
VdecideP (x ∷ x₁ ∷ c) (y ∷ ys) (no z , zs) = VdecideP (x₁ ∷ c) ys zs


--The implementation permits stuttering.

Restr : Spec {α} vars k → (System vars) → (System vars) → Set α
Restr {vars = vars} spec sys nsys =
  let conds = fmap (λ sp → (cond sp) sys) spec
  in (vc : Vdecide conds) → 
     let resps = fmap (λ sp → (resp sp) sys nsys) spec
     in VdecideP conds resps vc ⊎ (sys ≡ nsys)
                                   


-- TODO Can we simplify this?
variable
  TRestr : (spec : Spec vars k) → (beh : (System vars) ʷ) → Restr spec (beh n) (beh (suc n))

-- IMPORTANT Due to non-determinism , we can never have a specific behavior. We assume that any implementation that performs the actions
-- of the specification, has behaviors that respect the temporal restriction.
-- The temporal restriction simply assumes that any action can be performed or none.

-- TRestr restricts the types of behaviors that are possible, thus allowing us to prove properties about them.



