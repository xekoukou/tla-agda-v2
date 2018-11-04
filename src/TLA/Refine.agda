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



PRefAction : (B : Set α) → (f : B → C) → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction C varsA)
             → Set (lsuc α)
PRefAction {varsB = varsB} B f refm pactA = (b : B) → RefAction {varsB = varsB} refm (pactA (f b))

PRefActionC : C → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction C varsA)
             → Set (lsuc α)
PRefActionC {varsB = varsB} c refm pactA = RefAction {varsB = varsB} refm (pactA c)


record RefStAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
              → (rsp : resp ract vs cnd nvs)
              → refm vs ≡ refm nvs
open RefStAction public


PRefStAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → Set (lsuc α)
PRefStAction {varsA = varsA} {varsB = varsB} B refm = (b : B) → RefStAction {varsA = varsA} {varsB = varsB} refm




RefSpec : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA) → Set (lsuc α) 
RefSpec {varsA = varsA} {varsB = varsB} refm [] = List (RefStAction {varsA = varsA} {varsB = varsB} refm)
RefSpec {varsB = varsB} refm (act ∷ spec)
  = List (RefAction {varsB = varsB} refm act) × RefSpec {varsB = varsB} refm spec


data PRefSpec {α n k varsB varsA B} (refm : System {α} {n} varsB → System {α} {k} varsA)
              : (pspec : PSpec B varsA) → Set (lsuc α) where
  rfA : ∀{act pspec} → RefAction {varsB = varsB} refm act → PRefSpec {varsB = varsB} refm pspec
        → PRefSpec refm (spA act pspec)
  rfPA : ∀{C f pact pspec} → PRefAction {C = C} {varsB = varsB} B f refm pact → PRefSpec {varsB = varsB} refm pspec
         → PRefSpec refm (spPA f pact pspec)
  rfPAC : ∀{C c f pact pspec} → PRefActionC {C = C} {varsB = varsB} c refm pact → PRefSpec {varsB = varsB} refm pspec
          → PRefSpec refm (spPA f pact pspec)
  rf∅ : PRefSpec refm s∅

variable
  refSp : RefSpec {varsA = _} {varsB = _} _ _

exSp : {refm : System varsB → System varsA} → RefSpec {varsA = varsA} {varsB = varsB} refm spec → Spec varsB
exSp {spec = []} rsp = map ract rsp
exSp {spec = act ∷ spec} (lra , rsp) =  (map ract lra) ++ exSp rsp


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


