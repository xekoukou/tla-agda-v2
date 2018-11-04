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
  A : Set _
  B : Set _
  C : Set _


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

PAction : ∀{n} → (B : Set α) → (vars : Vec (Set α) (suc n)) → Set (lsuc α)
PAction B vars = B → Action vars 

variable
  vars varsA varsB : Vec (Set _) (suc _)
  act actA actB : Action _
  pact pactA pactB : PAction _ _


Lf : (act : Action vars) → PAction ⊤ vars
Lf act x = act


record ConAction {α n} {vars : Vec (Set α) (suc n)} (act : Action vars) : Set (lsuc α) where
  field
    impl : (vs : System vars) → (cnd : (cond act) vs) → ∃ (λ nvs → resp act vs cnd nvs)
open ConAction public


record PConAction {α n} {vars : Vec (Set α) (suc n)} {B : Set α} (pact : PAction B vars) : Set (lsuc α) where
  field
    par : B
    impl : (vs : System vars) → (cnd : (cond (pact par)) vs) → ∃ (λ nvs → resp (pact par) vs cnd nvs)
open PConAction public


psimpl : (cn : PConAction {vars = vars} pact) → ((x : System vars) → (cond (pact (par cn))) x → System vars)
psimpl cact x cnd = fst ((impl cact) x cnd)


-- From the point of view of refinement as will be defined in Refine, f should be simple,
-- like a projection. That way RefAction would suggest a local C that would be inversed to b ∈ B.
data PSpec {α n} (B : Set α) (vars : Vec (Set α) (suc n)) : Set (lsuc α) where
  spA : (act : Action vars) → (pspec : PSpec B vars) → PSpec B vars
  spPA : ∀{C : Set α} → (f : B → C) → (pact : PAction C vars) → (pspec : PSpec B vars) → PSpec B vars
  s∅ : PSpec B vars

Spec : (vars : Vec (Set α) (suc n)) → Set (lsuc α)
Spec vars = List (Action vars)

variable
  pspec pspecA pspecB : PSpec _ _
  spec specA specB : Spec _
  beh behA behB :  (System _) ʷ

-- Implementation of all (?) Actions. 
ConPSpec : (spec : PSpec {α} B vars) → Set (lsuc α)
ConPSpec (spA act spec) = ConAction act × ConPSpec spec 
ConPSpec (spPA f pact spec) = PConAction pact × ConPSpec spec
ConPSpec s∅ = ⊤′


ConSpec : (spec : Spec {α} vars) → Set (lsuc α)
ConSpec [] = ⊤′
ConSpec (act ∷ spec) = ConAction act × ConSpec spec


apSp : (spec : PSpec B vars) → (b : B) → Spec vars
apSp (spA act spec) b = act ∷ apSp spec b 
apSp (spPA f pact spec) b = pact (f b) ∷ apSp spec b
apSp s∅ b = []


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

PDecF : (B : Set α) → PSpec {α} B vars → Set α
PDecF B pspec = (b : B) → DecF (apSp pspec b)

--The implementation permits stuttering.

Restr : (spec : Spec {α} vars) → (System vars) → (System vars) → DecF spec → Set α
Restr {vars = vars} spec sys nsys decF = vP spec sys nsys (decF sys) ⊎ (sys ≡ nsys)


TRestr : (spec : Spec {α} vars) → (beh : (System vars) ʷ) → DecF spec → (Set α) ʷ
TRestr spec beh decF = ⟨ Restr spec ⟩ $ʷ beh $ʷ (○ beh) $ʷ ⟨ decF ⟩



FPTRestr : (B : Set α) → (pspec : PSpec {α} B vars) → (beh : (System vars) ʷ) → (pdecF : PDecF B pspec)
           → ((b : B ) → (Set α)) ʷ
FPTRestr B pspec beh pdecF n b = TRestr (apSp pspec b) beh (pdecF b) n


PTRestr : (B : Set α) → (pspec : PSpec {α} B vars) → (beh : (System vars) ʷ) → PDecF B pspec → (Set α) ʷ
PTRestr B pspec beh pdecF = ⟨ Σ B ⟩ $ʷ (FPTRestr B pspec beh pdecF)





