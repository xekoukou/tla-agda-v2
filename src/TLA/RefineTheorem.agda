module TLA.RefineTheorem where

open import TLA.Refine2

-- This is used in the proof.
-- It has no other use.
record RefActionApp {α} {varsA : PSet α} {varsB : PSet α}
                 (refm : System varsB → System varsA) (actA : Action varsA) (sys : System varsB) : Set (lsuc α) where
  field
    ract : Action varsB
    dom-embed : (cnd : cond ract sys) → cond actA (refm sys)
    range-embed : (nsys : System varsB)
                  → (cnd : cond ract sys) → (rsp : resp ract sys nsys)
                  → resp actA (refm sys) (refm nsys)
open RefActionApp public



_toRefActionApp_ : {refm : System varsB → System varsA}
                  → RefAction {varsA = varsA} {varsB = varsB} refm actA
                  → (sys : System varsB)
                  → RefActionApp {varsA = varsA} {varsB = varsB} refm actA sys
ract (ref toRefActionApp sys) = ract ref
dom-embed (ref toRefActionApp sys) = (dom-embed ref) sys 
range-embed (ref toRefActionApp sys) = range-embed ref sys



⊥-RefActionApp : {refm : System varsB → System varsA} → {sys : System varsB}
                 → RefActionApp {varsA = varsA} {varsB = varsB} refm actA sys
ract ⊥-RefActionApp = ⊥-Action
dom-embed ⊥-RefActionApp ()
range-embed ⊥-RefActionApp nvs () rsp


PRefActionApp : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (actA : Action varsA)
             → (sys : System varsB) → Set (lsuc α)
PRefActionApp {varsB = varsB} B refm actA sys = (b : B) → RefActionApp {varsB = varsB} refm actA sys


_toMPRefActionApp_ : {refm : System varsB → System varsA} → PRefAction {varsA = varsA} {varsB = varsB} B refm actA
                 → (sys : System varsB) → PRefActionApp {varsA = varsA} {varsB = varsB} (Maybe B) refm actA sys
(pref toMPRefActionApp sys) nothing = ⊥-RefActionApp
(pref toMPRefActionApp sys) (just b) = (pref b) toRefActionApp sys



⊥-RefPAction : (par : System varsB → B) → {refm : System varsB → System varsA}
               → RefPAction {varsA = varsA} {varsB = varsB} {B = B} refm pactA
par (⊥-RefPAction par) = par
ract (⊥-RefPAction par) = ⊥-Action
dom-embed (⊥-RefPAction par) vs ()
range-embed (⊥-RefPAction par) vs nvs () rsp


_toRefPActionApp_ : {refm : System varsB → System varsA}
                     → (ref : RefPAction {varsA = varsA} {varsB = varsB} refm pactA) → (sys : System varsB)
                     → RefActionApp {varsA = varsA} {varsB = varsB} refm (pactA (par ref sys)) sys
ract (ref toRefPActionApp sys) = ract ref
dom-embed (ref toRefPActionApp sys) = dom-embed ref sys
range-embed (ref toRefPActionApp sys) = range-embed ref sys




_toPRefPActionApp_ : {refm : System varsB → System varsA}
                     → (ref : PRefPAction {varsA = varsA} {varsB = varsB} E refm pactA)
                     → (sys : System varsB) → (e : E)
                     → RefActionApp {varsA = varsA} {varsB = varsB} refm {!par (ref e) sys!} sys
(pref toPRefPActionApp sys) = {!!}

_toMPRefPActionApp_ : {refm : System varsB → System varsA}
                     → (ref : PRefPAction {varsA = varsA} {varsB = varsB} E refm pactA)
                     → (sys : System varsB) → (e : E)
                     → RefActionApp {varsA = varsA} {varsB = varsB} refm {!par (ref e) sys!} sys
(pref toMPRefPActionApp sys) = {!!}


⊥-RefStAction : {refm : System varsB → System varsA} → RefStAction {varsA = varsA} {varsB = varsB} refm
ract ⊥-RefStAction = ⊥-Action
isConst ⊥-RefStAction vs nvs () rsp

_toMPRefStAction : {refm : System varsB → System varsA} → PRefStAction {varsA = varsA} {varsB = varsB} B refm
                 → PRefStAction {varsA = varsA} {varsB = varsB} (Maybe B) refm
(refSt toMPRefStAction) nothing = ⊥-RefStAction
(refSt toMPRefStAction) (just b) = refSt b



_$ʳᶠ_ : {refm : System varsB → System varsA} → GRefSpec {varsB = varsB} refm PE gspec → (pe : pStoS (PE toMPESet)) → RefSpec {varsA = varsA} {varsB = varsB} refm (gspec $ᵍˢ pe)
rfA ref $ʳᶠ pe = ref
prfStA refSt gspec $ʳᶠ pe = {!!}
prfA prefA ind $ʳᶠ pe = {!!}
rfpA refPA ind $ʳᶠ pe = {!!}
prfpA prefPA ind $ʳᶠ pe = {!!}
