module TLA.Refine where

open import TLA.Def

open import Prelude.List hiding ([_])

data _∈ₗ_ {α} {A : Set α} (a : A) : List A → Set α where
  instance
    zero : ∀ {x xs} → a ∈ₗ (x ∷ xs)
    suc : ∀ {x xs} (i : a ∈ₗ xs) → a ∈ₗ (x ∷ xs)






variable
  refm refmA refmB : System _ → System _

record RefAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 (refm : System varsB → System varsA) (actA : Action varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond actA (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
                  → (cndA : cond actA (refm vs)) → (rsp : resp ract vs cnd nvs)
                  → resp actA (refm vs) cndA (refm nvs)
open RefAction public


record PRefActionC {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 {C : Set α} (refm : System varsB → System varsA) (pactA : PAction C varsA) : Set (lsuc α) where
  field
    par : System varsB → C
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond (pactA (par vs)) (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
                  → (cndA : cond (pactA (par vs)) (refm vs)) → (rsp : resp ract vs cnd nvs)
                  → resp (pactA (par vs)) (refm vs) cndA (refm nvs)
open PRefActionC public


PRefAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction C varsA)
             → Set (lsuc α)
PRefAction {varsB = varsB} B refm pactA = (b : B) → PRefActionC {varsB = varsB} refm pactA


record RefStAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
              → (rsp : resp ract vs cnd nvs)
              → refm vs ≡ refm nvs
open RefStAction public

PRefStAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA)
               → Set (lsuc α)
PRefStAction {varsA = varsA} {varsB = varsB} B refm = (b : B) → RefStAction {varsA = varsA} {varsB = varsB} refm


RefSpec : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA) → Set (lsuc α) 
RefSpec {varsA = varsA} {varsB = varsB} refm [] = List (RefStAction {varsA = varsA} {varsB = varsB} refm)
RefSpec {varsB = varsB} refm (act ∷ spec)
  = List (RefAction {varsB = varsB} refm act) × RefSpec {varsB = varsB} refm spec


variable
  refSp : RefSpec {varsA = _} {varsB = _} _ _



exSp : {refm : System varsB → System varsA} → RefSpec {varsA = varsA} {varsB = varsB} refm spec → Spec varsB
exSp {spec = []} rsp = map ract rsp
exSp {spec = act ∷ spec} (lra , rsp) =  (map ract lra) ++ exSp rsp




data PRefSpec {α n k varsA varsB} (refm : System {α} {n} varsB → System {α} {k} varsA)
              : ∀{PB} (PE : PSet α) (pspec : PSpec varsA PB) → Set (lsuc α) where
  rfAm : ∀{PB act pspec} → (rct : RefAction {varsB = varsB} refm act) → (prsp : PRefSpec {varsB = varsB} refm {PB = PB} PE (spA act pspec))
         → PRefSpec refm PE (spA act pspec)
  rfA : ∀{PB act pspec} → (rct : RefAction {varsB = varsB} refm act) → (prsp : PRefSpec {varsB = varsB} refm {PB = PB} PE pspec)
        → PRefSpec refm PE (spA act pspec)
  rfPACm : ∀{C pact pspec} → (rpctC : PRefActionC {varsB = varsB} refm pact)
           → (prsp : PRefSpec {varsB = varsB} refm PE (spPA pact pspec)) → PRefSpec refm PE (spPA {C = C} {PB = PB} pact pspec)
  rfPAC : ∀{C pact pspec} → (rpctC : PRefActionC {varsB = varsB} refm pact)
          → (prsp : PRefSpec {varsB = varsB} refm {PB = PB} PE pspec) → PRefSpec refm PE (spPA {C = C} pact pspec)
  rfPAm : ∀{C D pact pspec} → (rpct : PRefAction {varsB = varsB} D refm pact)
          → (prsp : PRefSpec {varsB = varsB} refm PE (spPA pact pspec)) → PRefSpec refm {PB = (C ×ₚ PB)} (D ×ₚ PE) (spPA pact pspec)
  rfPA : ∀{C D pact pspec} → (rpct : PRefAction {varsB = varsB} D refm pact)
         → (prsp : PRefSpec {varsB = varsB} refm {PB = PB} PE pspec) → PRefSpec refm {PB = (C ×ₚ PB)} (D ×ₚ PE) (spPA pact pspec)
  rfStA : (rfSt : RefStAction {varsA = varsA} {varsB = varsB} refm)
          → (prsp : PRefSpec {varsA = varsA} {varsB = varsB} refm PE s∅) → PRefSpec refm PE s∅
  rfPStA : (rfSt : PRefStAction {varsA = varsA} {varsB = varsB} D refm)
           → (prsp : PRefSpec {varsA = varsA} {varsB = varsB} refm PE s∅) → PRefSpec refm (D ×ₚ PE) s∅
  rf∅ : PRefSpec refm ⊤ₚ s∅



exPSp : {refm : System varsB → System varsA} → PRefSpec {varsA = varsA} {varsB = varsB} refm PE pspec
        → PSpec varsB PE
exPSp {pspec = spA act pspec} (rfAm rct rsp) = spA (ract rct) (exPSp rsp)
exPSp {pspec = spA act pspec} (rfA rct rsp) = spA (ract rct) (exPSp rsp)
exPSp {pspec = spPA pact pspec} (rfPACm rpctC rsp) = spA (ract rpctC) (exPSp rsp)
exPSp {pspec = spPA pact pspec} (rfPAC rpctC rsp) = spA (ract rpctC) (exPSp rsp)
exPSp {pspec = spPA pact pspec} (rfPAm rpct rsp) = spPA (λ k → ract (rpct k)) (exPSp rsp)
exPSp {pspec = spPA pact pspec} (rfPA rpct rsp) = spPA (λ k → ract (rpct k)) (exPSp rsp)
exPSp {pspec = s∅} (rfStA rfSt rsp) = spA (ract rfSt) (exPSp rsp)
exPSp {pspec = s∅} (rfPStA prfSt rsp) = spPA (λ k → ract (prfSt k)) (exPSp rsp)
exPSp {pspec = s∅} rf∅ = s∅



trefm : (refm : System varsB → System varsA) → (System varsB)ʷ → (System varsA)ʷ
trefm refm beh = ⟨ refm ⟩ $ʷ beh



refStLemma : (refm : System varsB → System varsA) → (beh : (System varsB)ʷ) → (refSp : RefSpec {varsA = varsA} {varsB = varsB} refm []) → (decFp : DecF (exSp refSp)) 
             → [ TRestr (exSp refSp) beh decFp ⇒ ⟨ _≡_ ⟩ $ʷ (⟨ refm ⟩ $ʷ beh) $ʷ (⟨ refm ⟩ $ʷ (○ beh)) ]
refStLemma refm beh [] decFp n (left rst) = ⊥′-elim rst
refStLemma refm beh (ract ∷ refSp) decFp n (left rst) with decFp (beh n) | refStLemma refm beh refSp (λ sys → snd (decFp sys)) n
refStLemma refm beh (ract ∷ refSp) decFp n (left (left rst)) | yes d , snd | g = isConst ract (beh n) (beh (suc n)) d rst 
refStLemma refm beh (ract ∷ refSp) decFp n (left (right rst)) | yes d , snd | g = g (left rst)
refStLemma refm beh (ract ∷ refSp) decFp n (left rst) | no d , snd | g = g (left rst)
refStLemma refm beh refSp decFp n (right rst) = cong refm rst

--- Theorem
--- A behavior beh induces a behavior ⟨ refm ⟩ $ʷ beh through the refinement mapping that respects the restrictions of the more abstract model.

refTheorem : (refm : System varsB → System varsA) → (spec : Spec varsA) → (beh : (System varsB)ʷ) → (refSp : RefSpec {varsB = varsB} refm spec) → (decFp : DecF (exSp refSp)) → (decF : DecF spec)
             → [ TRestr (exSp refSp) beh decFp ⇒ TRestr spec ( ⟨ refm ⟩ $ʷ beh ) decF ]
refTheorem refm [] beh refSp decFp decF n rst = right (refStLemma refm beh refSp decFp n rst)
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst with decF (refm (beh n)) | refTheorem refm spec beh refSp decFp (λ sys → snd (decF sys)) n rst
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst | yes d , snd | left ind = left (right ind)
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst | yes d , snd | right ind = right ind
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst | no d , snd | g = g
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (right rst) = right (cong refm rst)
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) with decFp (beh n) | refTheorem refm (act ∷ spec) beh (rs , refSp) (λ sys → snd (decFp sys)) decF n
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | yes dra , sndra | g with decF (refm (beh n))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left (left rst)) | yes dra , sndra | g | yes da , snda = left (left (range-embed ract (beh n) (beh (suc n)) dra da rst))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left (right rst)) | yes dra , sndra | g | yes da , snda = g (left rst)
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | yes dra , sndra | g | no da , snda =  ⊥-elim (da (dom-embed ract (beh n) dra))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | no dra , sndra | g = g (left rst)



refPTheorem : (refm : System varsB → System varsA) → (pspec : PSpec varsA PB) → (beh : (System varsB)ʷ)
              → (prefSp : PRefSpec {varsB = varsB} refm PE pspec) → (pdecFp : PDecF PE (exPSp prefSp)) → (pdecF : PDecF PB pspec)
              → [ PTRestr PE (exPSp prefSp) beh pdecFp ⇒ PTRestr PB pspec ( ⟨ refm ⟩ $ʷ beh ) pdecF ]
refPTheorem refm (spA act pspec) beh prefSp pdecFp pdecF n x = {!!}
refPTheorem refm (spPA pact pspec) beh prefSp pdecFp pdecF n x = {!!}
refPTheorem refm s∅ beh prefSp pdecFp pdecF n x = {!!} -- unit , right (refStLemma refm beh {!!} {!!} {!!} {!!})







-- -- TODO They are not needed , I think.
-- record RefActionCov {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
--                     (refm : System varsB → System varsA) (actA : Action varsA) : Set (lsuc α) where
--   field
--     racts : List (RefAction {varsB = varsB} refm actA)
--     covering : (vs : System varsA) → (cnd : cond actA vs) → ∃ λ refAct → (refAct ∈ₗ racts) × ∃ (λ pvs → (cond (ract refAct) pvs) × refm pvs ≡ vs)


-- RefSpecCov : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA m) → Set (lsuc α) 
-- RefSpecCov {varsB = varsB} refm (act ∷ []) = RefActionCov {varsB = varsB} refm act
-- RefSpecCov {varsB = varsB} refm (act ∷ spec@(_ ∷ _))
--   = RefActionCov {varsB = varsB} refm act × RefSpecCov {varsB = varsB} refm spec


