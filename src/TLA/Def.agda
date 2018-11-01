module TLA.Def where

open import Prelude.Vec public
open import Prelude.Unit public
open import Prelude.Nat public
open import Prelude.Empty public
open import Prelude.Product public
open import Prelude.Decidable public
open import Prelude.Sum renaming (Either to _⊎_) public
open import Prelude.Functor public
open import Prelude.Equality public
open import Prelude.List public hiding ([_])

open import LTL.Core public
open import LTL.Stateless public

open import Agda.Primitive public


variable
  α β : Level
  n k m : Nat


-- Non Termporal so as to be used by Actions.
System : Vec (Set α) (suc n) → Set α
System (x ∷ []) = x
System (x ∷ y ∷ xs) = x × System (y ∷ xs)

toProd = System

variable
  vs vsA vsB :  System _

record Action {α n} (vars : Vec (Set α) (suc n)) : Set (lsuc α) where
  field
    cond : (vs : System vars) → Set α
    -- First represent the current vars and the second, the next ones.
    resp : (vs : System vars) → (cnd : cond vs) → (nvs : System vars) → Set α

open Action public

variable
  vars varsA varsB : Vec (Set _) (suc _)
  act actA actB : Action _


-- The action will only be triggered when the condition is true, so there are multiple implementations with the same behavior,
-- it is best though to return the identity on all the other cases.
record ConAction {α n} {vars : Vec (Set α) (suc n)} (act : Action vars) : Set (lsuc α) where
  field
    impl : (vs : System vars) → (cnd : (cond act) vs) → ∃ (λ nvs → resp act vs cnd nvs)
open ConAction public


simpl : ConAction {vars = vars} act → ((x : System vars) → (cond act) x → System vars)
simpl cact x cnd = fst ((impl cact) x cnd)




Spec : (vars : Vec (Set α) (suc n)) → Set (lsuc α)
Spec {_} {_} vars = List (Action vars)

variable
  spec specA specB : Spec _
  beh behA behB :  (System _) ʷ


ConSpec : Spec {α} vars → Set (lsuc α)
ConSpec [] = ⊤′
ConSpec (act ∷ []) = ConAction act
ConSpec (act ∷ spec@(_ ∷ _)) = ConAction act × ConSpec spec



vDec : List (Set α) → Set α
vDec [] = ⊤′
vDec (x ∷ xs) = Dec x × vDec xs


vP : (spec : Spec {α} vars) → (vs : System vars) → (nvs : System vars) →
        let conds = fmap (λ sp → (cond sp) vs) spec
        in vDec conds → Set α
vP [] vs nvs x = ⊥′
vP (act ∷ spec) vs nvs (yes x , snd) = resp act vs x nvs ⊎ vP spec vs nvs snd
vP (act ∷ spec) vs nvs (no x , snd) = vP spec vs nvs snd
  


DecF : (spec : Spec {α} vars) → Set α
DecF {vars = vars} spec =
  (sys : System vars) →
  let conds = fmap (λ sp → (cond sp) sys) spec
  in vDec conds


--The implementation permits stuttering.

Restr : (spec : Spec {α} vars) → (System vars) → (System vars) → DecF spec → Set α
Restr {vars = vars} spec sys nsys decF = vP spec sys nsys (decF sys) ⊎ (sys ≡ nsys)



TRestr : (spec : Spec {α} vars) → (beh : (System vars) ʷ) → DecF spec → (Set α) ʷ
TRestr spec beh decF = ⟨ Restr spec ⟩ $ʷ beh $ʷ (○ beh) $ʷ ⟨ decF ⟩



-- IMPORTANT Due to non-determinism , we can never have a specific behavior. We assume that any implementation that performs the actions
-- of the specification, has behaviors that respect the temporal restriction.
-- The temporal restriction simply assumes that any action can be performed or none.

-- TRestr restricts the types of behaviors that are possible, thus allowing us to prove properties about them.



