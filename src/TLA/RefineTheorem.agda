module TLA.RefineTheorem where

open import TLA.Refine2



record RefActionApp {α n k} {varsA : VSet {α} n} {varsB : VSet {α} k}
                 (refm : System varsB → System varsA) (actA : Action varsA) (sys : System varsB) : Set (lsuc α) where
  field
    ract : Action varsB
    dom-embed : (cnd : cond ract sys) → cond actA (refm sys)
    range-embed : (nsys : System varsB)
                  → (cnd : cond ract sys) → (rsp : resp ract sys nsys)
                  → resp actA (refm sys) (refm nsys)
open RefActionApp public



rf_apply_ : {refm : System varsB → System varsA}
             → RefAction {varsA = varsA} {varsB = varsB} refm actA
             → (sys : System varsB)
             → RefActionApp {varsA = varsA} {varsB = varsB} refm actA sys
ract (rf ref apply sys) = ract ref
dom-embed (rf ref apply sys) = (dom-embed ref) sys 
range-embed (rf ref apply sys) = range-embed ref sys



⊥-RefActionApp : {refm : System varsB → System varsA} → {sys : System varsB}
                 → RefActionApp {varsA = varsA} {varsB = varsB} refm actA sys
ract ⊥-RefActionApp = ⊥-Action
dom-embed ⊥-RefActionApp ()
range-embed ⊥-RefActionApp nvs () rsp


PRefActionApp : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (actA : Action varsA)
             → (sys : System varsB) → Set (lsuc α)
PRefActionApp {varsB = varsB} B refm actA sys = (b : B) → RefActionApp {varsB = varsB} refm actA sys


prf_apply_ : {refm : System varsB → System varsA} → PRefAction {varsA = varsA} {varsB = varsB} B refm actA
                 → (sys : System varsB) → PRefActionApp {varsA = varsA} {varsB = varsB} B refm actA sys
(prf pref apply sys) b = rf (pref b) apply sys


-- Is this necessary ? 
_toMPRApp : {refm : System varsB → System varsA} → {sys : System varsB}
                    →  PRefActionApp {varsA = varsA} {varsB = varsB} B refm actA sys
                    →  PRefActionApp {varsA = varsA} {varsB = varsB} (Maybe B) refm actA sys
(pref toMPRApp) nothing = ⊥-RefActionApp
(pref toMPRApp) (just b) = pref b


-- Remove if unnecessary.
⊥-RefPAction : (par : System varsB → B) → {refm : System varsB → System varsA}
               → RefPAction {varsA = varsA} {varsB = varsB} {B = B} refm pactA
par (⊥-RefPAction par) = par
ract (⊥-RefPAction par) = ⊥-Action
dom-embed (⊥-RefPAction par) vs ()
range-embed (⊥-RefPAction par) vs nvs () rsp


rfp_apply_ : {refm : System varsB → System varsA}
             → (ref : RefPAction {varsA = varsA} {varsB = varsB} refm pactA)
             → (sys : System varsB)
             → RefActionApp {varsA = varsA} {varsB = varsB} refm (pactA (par ref sys)) sys
ract (rfp ref apply sys) = ract ref
dom-embed (rfp ref apply sys) = dom-embed ref sys
range-embed (rfp ref apply sys) = range-embed ref sys




prfp_apply_ : {refm : System varsB → System varsA}
                     → (ref : PRefPAction {varsA = varsA} {varsB = varsB} E refm pactA)
                     → (sys : System varsB) → (e : E)
                     → RefActionApp {varsA = varsA} {varsB = varsB} refm (pactA (par (ref e) sys)) sys
(prfp pref apply sys) e = rfp (pref e) apply sys


-- Is this neccessary ? 
_toMPRPApp : {refm : System varsB → System varsA}
             → {ref : PRefPAction {varsA = varsA} {varsB = varsB} E refm pactA}
             → {sys : System varsB}
             → (refa : (e : E) → RefActionApp {varsA = varsA} {varsB = varsB} refm (pactA (par (ref e) sys)) sys)
             → (e : Maybe E)
             → RefActionApp {varsA = varsA} {varsB = varsB} refm (((λ e → pactA (par (ref e) sys)) toMPAction) e) sys
(ref toMPRPApp) nothing =  ⊥-RefActionApp
(ref toMPRPApp) (just e) = ref e



record RefStActionApp {α n k} {varsA : VSet {α} n} {varsB : VSet {α} k}
                 (refm : System varsB → System varsA) (sys : System varsB) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (nsys : System varsB) → (cnd : cond ract sys)
              → (rsp : resp ract sys nsys)
              → refm sys ≡ refm nsys
open RefStActionApp public


rfSt_apply : {refm : System varsB → System varsA} → (ref : RefStAction {varsA = varsA} {varsB = varsB} refm)
             → (sys : System varsB)
             → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys
ract (rfSt ref apply sys) = ract ref
isConst (rfSt ref apply sys) = isConst ref sys

PRefStActionApp : (E : Set α) → (refm : System {α} varsB → System {α} varsA)
                  → (sys : System varsB) → Set (lsuc α)
PRefStActionApp {varsA = varsA} {varsB = varsB} E refm sys
  = (e : E) → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys

prfSt_apply : {refm : System varsB → System varsA} → (ref : PRefStAction {varsA = varsA} {varsB = varsB} E refm)
              → (sys : System varsB)
              → PRefStActionApp {varsA = varsA} {varsB = varsB} E refm sys
ract (prfSt ref apply sys e) = ract (ref e)
isConst (prfSt ref apply sys e) = isConst (ref e) sys


⊥-RefStActionApp : {refm : System varsB → System varsA} → {sys : System varsB}
                   → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys
ract ⊥-RefStActionApp = ⊥-Action
isConst ⊥-RefStActionApp nsys () rsp

-- Is this neccessary ?
_toMPRStApp : {refm : System varsB → System varsA} → {sys : System varsB}
              → PRefStActionApp {varsA = varsA} {varsB = varsB} B refm sys
                 → PRefStActionApp {varsA = varsA} {varsB = varsB} (Maybe B) refm sys
(refSt toMPRStApp) nothing = ⊥-RefStActionApp
(refSt toMPRStApp) (just b) = refSt b


RefSpecApp : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA)
             → (sys : System varsB) → Set (lsuc α) 
RefSpecApp {varsA = varsA} {varsB = varsB} refm [] sys
  = List (RefStActionApp {varsA = varsA} {varsB = varsB} refm sys)
RefSpecApp {varsB = varsB} refm (act ∷ spec) sys
  = List (RefActionApp {varsB = varsB} refm act sys) × RefSpecApp {varsB = varsB} refm spec sys

refSpecApp∅ : {refm : System {α} varsB → System {α} varsA} → {spec : Spec varsA} → {sys : System varsB}
              → RefSpecApp {varsB = varsB} refm spec sys
refSpecApp∅ {spec = []} = []
refSpecApp∅ {spec = actA ∷ spec} = [] , refSpecApp∅


_addStApp_ : {refm : System {α} varsB → System {α} varsA} → {spec : Spec varsA} → {sys : System varsB}
        → RefSpecApp {varsB = varsB} refm spec sys → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys
        → RefSpecApp {varsB = varsB} refm spec sys
_addStApp_ {spec = []} ref rfa = rfa ∷ ref
_addStApp_ {spec = act ∷ spec} (rfas , ind) rfa = rfas , (ind addStApp rfa)


getPar : {refm : System varsB → System varsA}
         → (gref : GRefSpec {varsA = varsA} {varsB = varsB} refm {PB = PB} PE gspec)
         → (pe : pStoUS PE) → {sys nsys : System varsB}
         → let espec = (gextrSpec gref pe)
           in (pcnds : PrConds espec sys)
              → (rst : RestrWithSt espec sys nsys pcnds) → pStoUS PB

getPar gref pe pcnds (u→ rst) = u→∅
getPar {PE = ⊤ₚ} (rf ref) pe pcnds rst = unit
getPar {PE = ⊤ₚ} (rfp refPA ∷ (gref ←u)) pe {sys} (yes _ , pcnds) ((rst ←u) ←u) = (par refPA sys) ←u
getPar {PE = ⊤ₚ} (rfp refPA ∷ (gref ←u)) pe (yes _ , pcnds) ((u→ rst) ←u) = getPar gref pe pcnds (rst ←u)
getPar {PE = ⊤ₚ} (rfp refPA ∷ (gref ←u)) pe (no _ , pcnds) rst = getPar gref pe pcnds rst
getPar {PE = ⊤ₚ} (rfp refPA ∷ (u→ gref)) pe {sys} (yes _ , pcnds) ((rst ←u) ←u) = (par refPA sys) ←u
getPar {PE = ⊤ₚ} (rfp refPA ∷ (u→ gref)) pe (yes _ , pcnds) ((u→ rst) ←u) = u→ getPar gref pe pcnds (rst ←u)
getPar {PE = ⊤ₚ} (rfp refPA ∷ (u→ gref)) pe (no _ , pcnds) rst = u→ getPar gref pe pcnds rst
getPar {PE = E ×ₚ PE} (pst refSt ∷ gref) pe pcnds rst = unit
getPar {PE = E ×ₚ PE} (prf prefA ∷ gref) pe pcnds rst = unit
getPar {PE = E ×ₚ PE} (rfp refPA ∷ (gref ←u)) (e ←u) {sys} (yes _ , pcnds) ((rst ←u) ←u) = (par refPA sys) ←u
-- Identical to the previous definition. We simply have to split PE.
getPar {PE = E ×ₚ PE} (rfp refPA ∷ (gref ←u)) pe {sys} (yes d , pcnds) ((rst ←u) ←u) = (par refPA sys) ←u
getPar {PE = E ×ₚ PE} (rfp refPA ∷ (gref ←u)) pe (yes d , pcnds) ((u→ rst) ←u) = getPar gref pe pcnds (rst ←u)
getPar {PE = E ×ₚ PE} (rfp refPA ∷ (gref ←u)) pe (no d , pcnds) rst = getPar gref pe pcnds rst
getPar {PE = E ×ₚ PE} (rfp refPA ∷ (u→ gref)) pe {sys} (yes d , pcnds) ((rst ←u) ←u) = (par refPA sys) ←u
getPar {PE = E ×ₚ PE} (rfp refPA ∷ (u→ gref)) pe (yes d , pcnds) ((u→ rst) ←u) = u→ getPar gref pe pcnds (rst ←u)
getPar {PE = E ×ₚ PE} (rfp refPA ∷ (u→ gref)) pe (no d , pcnds) rst = u→ getPar gref pe pcnds rst
getPar {PE = E ×ₚ PE} (prfp prefPA ∷ (gref ←u)) (e ←u) {sys} (yes _ , pcnds) (rst ←u)
  = par (prefPA e) sys ←u
getPar {PE = E ×ₚ PE} (prfp prefPA ∷ (gref ←u)) (e ←u) (no _ , pcnds) (() ←u)
getPar {PE = E ×ₚ PE} (prfp prefPA ∷ (gref ←u)) (u→ pe) pcnds (rst ←u) = getPar gref pe pcnds (rst ←u)
getPar {PE = E ×ₚ PE} (prfp prefPA ∷ (u→ gref)) (e ←u) {sys} (yes x , pcnds) ((rst ←u) ←u)
  = par (prefPA e) sys ←u
getPar {PE = E ×ₚ PE} (prfp prefPA ∷ (u→ gref)) (e ←u) (yes x , pcnds) ((u→ rst) ←u) = u→∅
getPar {PE = E ×ₚ PE} (prfp prefPA ∷ (u→ gref)) (e ←u) (no x , pcnds) (() ←u)
getPar {PE = E ×ₚ PE} (prfp prefPA ∷ (u→ gref)) (u→ pe) pcnds (rst ←u) = u→ getPar gref pe pcnds (rst ←u)


-- One needs to check that all refine records are turned into RefActionsApp
-- Otherwise the extension of the refTheorem to GrefSpec will not hold.
_$ʳᶠ : {refm : System varsB → System varsA} → (gref : GRefSpec {varsA = varsA} {varsB = varsB} refm PE gspec)
       → (pe : pStoUS PE) → (sys nsys : System varsB)
       → let espec = (gextrSpec gref pe)
         in (pcnds : PrConds espec sys)
            → (rst : RestrWithSt espec sys nsys pcnds)
       → RefSpecApp {varsA = varsA} {varsB = varsB} refm (gspec $ᵍˢ getPar gref pe pcnds rst) sys
(ref $ʳᶠ) pe sys nsys pcnds (u→ rst) = refSpecApp∅
-- Is there a way to remove more refSt ? Probably not.
_$ʳᶠ {gspec = gsp [] .psp∅} (rf ref) pe sys nsys pcnds (rst ←u) = fmap (λ refSt → rfSt refSt apply sys) ref
_$ʳᶠ {gspec = gsp (actA ∷ sp) .psp∅} (rf ([] , ref)) pe sys nsys pcnds (rst ←u)
  = [] , ((rf ref $ʳᶠ) pe sys nsys pcnds (rst ←u))
_$ʳᶠ {gspec = gsp (actA ∷ sp) .psp∅} (rf (refA ∷ lref , ref)) pe sys nsys (yes x , pcnds) ((rst ←u) ←u)
  = rf refA apply sys ∷ [] , refSpecApp∅
_$ʳᶠ {gspec = gsp (actA ∷ sp) .psp∅} (rf (refA ∷ lref , ref)) pe sys nsys (yes x , pcnds) ((u→ rst) ←u)
  = (rf (lref , ref) $ʳᶠ) pe sys nsys pcnds (rst ←u)
_$ʳᶠ {gspec = gsp (actA ∷ sp) .psp∅} (rf (refA ∷ lref , ref)) pe sys nsys (no x , pcnds) (rst ←u)
  = (rf (lref , ref) $ʳᶠ) pe sys nsys pcnds (rst ←u)
((pst refSt ∷ gref) $ʳᶠ) (e ←u) sys nsys (yes x , _) (rst ←u) = refSpecApp∅ addStApp (prfSt refSt apply sys e)
((pst refSt ∷ gref) $ʳᶠ) (e ←u) sys nsys (no x , _) (() ←u)
((pst refSt ∷ gref) $ʳᶠ) (u→ pe) sys nsys pcnds (rst ←u) = (gref $ʳᶠ) pe sys nsys pcnds (rst ←u)
((prf prefA ∷ (gref ←u)) $ʳᶠ) (e ←u) sys nsys (yes x , _) (rst ←u)
  = ((prf prefA apply sys) e ∷ []) , refSpecApp∅
((prf prefA ∷ (gref ←u)) $ʳᶠ) (e ←u) sys nsys (no x , _) rst = {!!}
((prf prefA ∷ (gref ←u)) $ʳᶠ) (u→ pe) sys nsys pcnds rst = {!!}
((prf prefA ∷ (u→ gref)) $ʳᶠ) pe sys nsys pcnds rst = {!!}
((rfp refPA ∷ (gref ←u)) $ʳᶠ) pe sys nsys pcnds rst = {!!}
((rfp refPA ∷ (u→ gref)) $ʳᶠ) pe sys nsys pcnds rst = {!!}
((prfp prefPA ∷ gref) $ʳᶠ) pe sys nsys pcnds rst = {!!}
