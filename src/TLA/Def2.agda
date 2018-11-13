module TLA.Def2 where

open import Prelude.Vec public
open import Prelude.Unit public
open import Prelude.Nat public
open import Prelude.Empty public
open import Prelude.Product public
open import Prelude.Decidable public
open import Prelude.Sum renaming (Either to _⊎_) public
open import Prelude.Functor public
open import Prelude.Equality public
open import Prelude.Maybe public
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



postulate IMPOSSIBLE : A


data PSet α : Set (lsuc α) where
  _×ₚ_ : (B : Set α) → (PB : PSet α) → PSet α
  _⊎⊥ : (B : Set α) → PSet α

data PESet α : Set (lsuc α) where
  _×ₑ_ : (B : Set α) → (EB : PESet α) → PESet α
  ⊤ₑ  : PESet α

pStoS : PESet α → Set α
pStoS (S ×ₑ pd) = S × pStoS pd
pStoS ⊤ₑ = ⊤′


_toMPESet : PESet α → PESet α
(B ×ₑ pset) toMPESet = Maybe B ×ₑ (pset toMPESet)
⊤ₑ toMPESet = ⊤ₑ


variable
  vars varsA varsB : PSet α
  PA PB PC PD PE : PESet α


-- Non Termporal so as to be used by Actions.
System : PSet α → Set α
System (B ×ₚ PB) = B × System PB
System (B ⊎⊥) = B


variable
  sys sysA sysB :  System _


record Action {α} (vars : PSet α) : Set (lsuc α) where
  field
    cond : (sys : System vars) → Set α
    resp : (sys : System vars) → (nsys : System vars) → Set α

open Action public


PAction : (B : Set α) → (vars : PSet α) → Set (lsuc α)
PAction B vars = B → Action vars 


variable
  act actA actB : Action _
  pact pactA pactB : PAction _ _


-- MPAction is a PAction that takes Maybe B as input.
-- This is necessary because we will not always have a B.
-- The presence of B is determined by the action taken at time t.
MPAction : (B : Set α) → (vars : PSet α) → Set (lsuc α)
MPAction B vars = Maybe B → Action vars


⊥-Action : Action vars
cond ⊥-Action sys = ⊥′
resp ⊥-Action sys nsys = ⊥′

_toMPAction : PAction B vars → MPAction B vars
(pa toMPAction) nothing  = ⊥-Action
(pa toMPAction) (just x) = pa x


record ConAction {α} {vars : PSet α} (act : Action vars) : Set (lsuc α) where
  field
    impl : (sys : System vars) → (cnd : (cond act) sys) → ∃ (λ nsys → resp act sys nsys)
open ConAction public

simpleAction : ConAction {vars = vars} act → (sys : System vars) → (cnd : (cond act) sys) → System vars
simpleAction cact sys cnd = fst (impl cact sys cnd)

record PConAction {α} {vars : PSet α} {B : Set α} (pact : PAction B vars) : Set (lsuc α) where
  field
    par : System vars → B
    impl : (sys : System vars) → (cnd : (cond (pact (par sys))) sys) → ∃ (λ nsys → resp (pact (par sys)) sys nsys)
open PConAction public


simplePAction : (cn : PConAction {vars = vars} pact) → ((sys : System vars) → (cond (pact (par cn sys))) sys → System vars)
simplePAction cact sys cnd = fst ((impl cact) sys cnd)



Spec : (vars : PSet α) → Set (lsuc α)
Spec vars = List (Action vars)


data PSpec {α} (vars : PSet α) : (PB : PESet α) → Set (lsuc α) where
  _+psp+_ : (pact : PAction B vars) → (pspec : PSpec vars PB) → PSpec vars (B ×ₑ PB)
  psp∅ : PSpec vars ⊤ₑ


record GSpec {α} (vars : PSet α) (PB : PESet α) : Set (lsuc α) where
  constructor gsp
  field
    sp : Spec vars
    psp : PSpec vars PB


open GSpec public

variable
  pspec pspecA pspecB : PSpec _ _
  spec specA specB : Spec _
  gspec gspecA gspecB : GSpec _ _
  beh behA behB :  (System _) ʷ



-- Implementation of some Actions
-- PSpec is assumed to be a subset of a PSpec.
-- TODO How do we split a PSpec and how do we compose Specs?
ConPSpec : (spec : PSpec {α} vars PB) → Set (lsuc α)
ConPSpec (pact +psp+ spec) = PConAction pact × ConPSpec spec
ConPSpec s∅ = ⊤′


ConSpec : (spec : Spec {α} vars) → Set (lsuc α)
ConSpec [] = ⊤′
ConSpec (act ∷ spec) = ConAction act × ConSpec spec

ConGSpec : (gspec : GSpec {α} vars PB) → Set (lsuc α)
ConGSpec gspec = ConSpec (sp gspec) × ConPSpec (psp gspec)


-- To restrict the general case of specification, we need to lift all PActions into
-- MActions.
_toMPSpec : PSpec vars PB → PSpec vars (PB toMPESet)
(pact +psp+ pspec) toMPSpec = (pact toMPAction) +psp+ (pspec toMPSpec)
psp∅ toMPSpec = psp∅


_toMGSpec : GSpec vars PB → GSpec vars (PB toMPESet)
sp (gspec toMGSpec) = sp gspec
psp (gspec toMGSpec) = (psp gspec) toMPSpec




_$ᵖˢ_ : (pspec : PSpec vars PB) → (b : pStoS PB) → Spec vars
(pact +psp+ spec) $ᵖˢ b = pact (fst b) ∷ (spec $ᵖˢ (snd b))
psp∅ $ᵖˢ b = []


_$ᵍˢ_ : (spec : GSpec vars PB) → (b : pStoS PB) → Spec vars
gspec $ᵍˢ b = ((psp gspec) $ᵖˢ b) ++ (sp gspec)


PrConds : (spec : Spec {α} vars) → (sys : System vars) → Set α
PrConds [] sys = ⊤′
PrConds (act ∷ spec) sys = Dec (cond act sys) × PrConds spec sys

UnResp : (spec : Spec {α} vars) → (sys : System vars) → (nsys : System vars) → (pCnds : PrConds spec sys) → Set α
UnResp [] sys nsys pCnds = ⊥′
UnResp (act ∷ spec) sys nsys (yes x , pcnds) = resp act sys nsys ⊎ UnResp spec sys nsys pcnds
UnResp (act ∷ spec) sys nsys (no x , pcnds) = UnResp spec sys nsys pcnds



Restr : (spec : Spec {α} vars) → (sys : System vars) → (nsys : System vars) → Set α
Restr spec sys nsys = (pcnds : PrConds spec sys) → UnResp spec sys nsys pcnds


Stut : (sys : System {α} vars) → (System {α} vars) → Set α
Stut sys nsys = sys ≡ nsys


TRestr : (spec : Spec {α} vars) → (beh : (System vars) ʷ) → (Set α) ʷ
TRestr spec beh = (⟨ Restr spec ⟩ $ʷ beh $ʷ (○ beh))

TStut : (beh : (System {α} vars) ʷ) → (Set α) ʷ
TStut {vars = vars} beh = ⟨ Stut {vars = vars} ⟩ $ʷ beh $ʷ (○ beh)


PRestr : (pspec : PSpec {α} vars PB) → (sys : System vars) → (nsys : System vars) → pStoS (PB toMPESet) → Set α
PRestr pspec sys nsys mpb = Restr ((pspec toMPSpec) $ᵖˢ mpb) sys nsys


TPRestr : (pspec : PSpec {α} vars PB) → (beh : (System vars) ʷ)
          → (tmpb : ( pStoS (PB toMPESet) ) ʷ) → (Set α ) ʷ
TPRestr pspec beh tmpb = ⟨ Restr ⟩ $ʷ (⟨ (pspec toMPSpec) $ᵖˢ_ ⟩ $ʷ tmpb) $ʷ beh $ʷ ○ beh

