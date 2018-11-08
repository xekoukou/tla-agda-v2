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
open import LTL.Sum public
open import LTL.Stateless public

open import Agda.Primitive public


variable
  α β : Level
  n k m : Nat
  A : Set _
  B : Set _
  C : Set _
  D : Set _
  E : Set _


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


-- The system vars could determine par , check PRefActionC.
-- This should be generalized.
record PConAction {α n} {vars : Vec (Set α) (suc n)} {B : Set α} (pact : PAction B vars) : Set (lsuc α) where
  field
    par : System vars → B
    impl : (vs : System vars) → (cnd : (cond (pact (par vs))) vs) → ∃ (λ nvs → resp (pact (par vs)) vs cnd nvs)
open PConAction public


psimpl : (cn : PConAction {vars = vars} pact) → ((x : System vars) → (cond (pact (par cn x))) x → System vars)
psimpl cact x cnd = fst ((impl cact) x cnd)


data PSet α : Set (lsuc α) where
  _×ₚ_ : Set α → PSet α → PSet α
  ⊤ₚ   : PSet α


pToS : PSet α → Set α
pToS (S ×ₚ pd) = S × pToS pd
pToS ⊤ₚ = ⊤′

variable
  PA PB PC PD PE : PSet α


Spec : (vars : Vec (Set α) (suc n)) → Set (lsuc α)
Spec vars = List (Action vars)


data PSpec {α n} (vars : Vec (Set α) (suc n)) : (PB : PSet α) → Set (lsuc α) where
  spPA : (pact : PAction B vars) → (pspec : PSpec vars PB) → PSpec vars (B ×ₚ PB)
  s∅ : PSpec vars ⊤ₚ

-- Maybe turn this into a record.
data GSpec {α n} (vars : Vec (Set α) (suc n)) : (PB : PSet α) → Set (lsuc α) where
  gsp : (spec : Spec vars) → (pspec : PSpec vars PB) → GSpec vars PB

gToSpec : GSpec vars PB → Spec vars
gToSpec (gsp spec pspec) = spec


gToPSpec : GSpec vars PB → PSpec vars PB
gToPSpec (gsp spec pspec) = pspec

variable
  pspec pspecA pspecB : PSpec _ _
  spec specA specB : Spec _
  gspec gspecA gspecB : GSpec _ _
  beh behA behB :  (System _) ʷ

-- Implementation of some Actions
-- PSpec is assumed to be a subset of a PSpec.
-- TODO How do we split a PSpec and how do we compose Specs?
ConPSpec : (spec : PSpec {α} vars PB) → Set (lsuc α)
ConPSpec (spPA pact spec) = PConAction pact × ConPSpec spec
ConPSpec s∅ = ⊤′


ConSpec : (spec : Spec {α} vars) → Set (lsuc α)
ConSpec [] = ⊤′
ConSpec (act ∷ spec) = ConAction act × ConSpec spec

ConGSpec : (spec : GSpec {α} vars PB) → Set (lsuc α)
ConGSpec (gsp sp psp) = ConSpec sp × ConPSpec psp


apSp : (spec : PSpec vars PB) → (b : pToS PB) → Spec vars
apSp (spPA pact spec) b = pact (fst b) ∷ apSp spec (snd b)
apSp s∅ b = []


-- Is this needed ?
apGSp : (spec : GSpec vars PB) → (b : pToS PB) → Spec vars
apGSp (gsp sp psp) b = sp ++ (apSp psp b)



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


PDecF : (PB : PSet α) → PSpec {α} vars PB → Set α
PDecF PB pspec = (b : pToS PB) → DecF (apSp pspec b)

GDecF : (PB : PSet α) → GSpec {α} vars PB → Set α
GDecF PB (gsp sp psp) = DecF sp × PDecF PB psp

--The implementation permits stuttering.

Restr : (spec : Spec {α} vars) → (System vars) → (System vars) → DecF spec → Set α
Restr {vars = vars} spec sys nsys decF = vP spec sys nsys (decF sys) ⊎ (sys ≡ nsys)


TRestr : (spec : Spec {α} vars) → (beh : (System vars) ʷ) → DecF spec → (Set α) ʷ
TRestr spec beh decF = ⟨ Restr spec ⟩ $ʷ beh $ʷ (○ beh) $ʷ ⟨ decF ⟩



FPTRestr : (PB : PSet α) → (pspec : PSpec {α} vars PB) → (beh : (System vars) ʷ) → (pdecF : PDecF PB pspec)
           → ((b : pToS PB ) → (Set α)) ʷ
FPTRestr B pspec beh pdecF n b = TRestr (apSp pspec b) beh (pdecF b) n


PTRestr : (PB : PSet α) → (pspec : PSpec {α} vars PB) → (beh : (System vars) ʷ) → PDecF PB pspec → (Set α) ʷ
PTRestr PB pspec beh pdecF = ⟨ Σ (pToS PB) ⟩ $ʷ (FPTRestr PB pspec beh pdecF)

GTRestr : (PB : PSet α) → (gspec : GSpec {α} vars PB) → (beh : (System vars) ʷ) → GDecF PB gspec → (Set α) ʷ
GTRestr PB (gsp spec pspec) beh (decF , pdecF) = TRestr spec beh decF ∨ PTRestr PB pspec beh pdecF



-- -- Is this needed ? 
-- _×ₚₚ_ : PSet α → PSet α → PSet α
-- (x ×ₚ pe) ×ₚₚ pd = x ×ₚ (pe ×ₚₚ pd)
-- ⊤ₚ ×ₚₚ pd = pd


-- _andₚₛ_ : PSpec vars PB → PSpec vars PD → PSpec vars (PB ×ₚₚ PD)
-- spPA pact pa andₚₛ pb = spPA pact (pa andₚₛ pb)
-- s∅ andₚₛ pb = pb



-- vDec++ : {la : List (Set α)} → {lb : List (Set α)} → vDec la → vDec lb → vDec (la ++ lb)
-- vDec++ {la = []} vda vdb = vdb
-- vDec++ {la = A ∷ la} (a , vda) vdb = a , vDec++ vda vdb

-- fmap++ : {la lb : List A} → {f : A → B} → fmap f la ++ fmap f lb ≡ fmap f (la ++ lb)
-- fmap++ {la = []} {lb} = refl
-- fmap++ {la = x ∷ la} {lb} {f} = cong (f x ∷_) (fmap++ {la = la})


-- decF++ : (decFa : DecF specA) → (decFb : DecF specB) → DecF (specA ++ specB)
-- decF++ {specA = specA} {specB = specB} decFa decFb sys = transport vDec r (vDec++ (decFa sys) (decFb sys)) where
--   r = fmap++ {la = specA} {lb = specB} {(λ sp → cond sp sys)}

-- decF+++ : (decFa : DecF specA) → (decFb : DecF specB) → DecF (specA ++ specB)
-- decF+++ {specA = []} {specB} decFa decFb sys = decFb sys
-- decF+++ {specA = x ∷ specA} {specB} decFa decFb sys =
--   let (da , _) = decFa sys
--   in da , decF+++ (λ sys → snd ( decFa sys)) decFb sys


-- Restr++ : {speca specb : Spec {α} vars} → {sys : System vars} → {nsys : System vars} → {decFa : DecF speca} → {decFb : DecF specb} → {decFab : DecF (speca ++ specb)}
--           → (rsta : Restr speca sys nsys decFa) → (rstb : Restr specb sys nsys decFb) → Restr (speca ++ specb) sys nsys decFab
-- Restr++ {speca = []} {specb} {sys} {nsys} {_} {decFb} {decFab} rsta rstb with decFab sys | decFb sys | vP specb sys nsys (decFab sys) | vP specb sys nsys (decFb sys)
-- ... | r | g | e | q = {!!}
-- Restr++ {speca = x ∷ speca} {specb} {sys} rsta rstb = {!!}
