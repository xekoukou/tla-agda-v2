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
                  → (refm vs ≡ refm nvs) ⊎ resp actA (refm vs) cndA (refm nvs)
open RefAction public



RefSpec : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA) → Set (lsuc α) 
RefSpec {varsB = varsB} refm [] = ⊤′
RefSpec {varsB = varsB} refm (act ∷ spec)
  = List (RefAction {varsB = varsB} refm act) × RefSpec {varsB = varsB} refm spec


variable
  refSp : RefSpec {varsA = _} {varsB = _} _ _

eSp : {refm : System varsB → System varsA} → RefSpec {varsA = varsA} {varsB = varsB} refm spec → Spec varsB
eSp {spec = []} rsp = [] 
eSp {spec = act ∷ spec} (lra , rsp) =  (map ract lra) ++ eSp rsp


trefm : (refm : System varsB → System varsA) → (System varsB)ʷ → (System varsA)ʷ
trefm refm beh = ⟨ refm ⟩ $ʷ beh


--- Theorem
--- A behavior beh induces a behavior ⟨ refm ⟩ $ʷ beh through the refinement mapping that respects the restrictions of the more abstract model.

refTheorem : {refm : System varsB → System varsA} → {spec : Spec varsA} → {beh : (System varsB)ʷ} → {refSp : RefSpec {varsB = varsB} refm spec} → {decFp : DecF (eSp refSp)} → {decF : DecF spec}
             → [ TRestr (eSp refSp) beh decFp ⇒ TRestr spec ( ⟨ refm ⟩ $ʷ beh ) decF ]
refTheorem {spec = []} n (left x) = ⊥′-elim x
refTheorem {refm = refm} {[]} n (right rst) = right (cong refm rst)
refTheorem {refm = refm} {act ∷ spec} {beh} {[] , refSp} {decFp} {decF} n rst with decF (refm (beh n)) | refTheorem {beh = beh} {refSp = refSp} {decFp} {λ sys → snd (decF sys)} n rst
refTheorem {refm = refm} {act ∷ spec} {beh} {[] , refSp} {decFp} {decF} n rst | yes x , snd | left x₁ = left (right x₁) 
refTheorem {refm = refm} {act ∷ spec} {beh} {[] , refSp} {decFp} {decF} n rst | yes x , snd | right x₁ = right x₁ 
refTheorem {refm = refm} {act ∷ spec} {beh} {[] , refSp} {decFp} {decF} n rst | no x , snd | g = g
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n rst with decFp (beh n) | refTheorem {beh = beh} {refSp = fst , refSp} {λ sys → snd (decFp sys)} {decF} n
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n (left resp) | yes x₁ , snd1 | g with decF (refm (beh n))
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n (left (left resp)) | yes x₁ , snd1 | g | yes x₂ , snd₁ with range-embed x (beh n) (beh (suc n)) x₁ x₂ resp
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n (left (left resp)) | yes x₁ , snd1 | g | yes x₂ , snd₁ | left x₃ = right x₃
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n (left (left resp)) | yes x₁ , snd1 | g | yes x₂ , snd₁ | right x₃ = left (left x₃)
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n (left (right resp)) | yes x₁ , snd1 | g | yes x₂ , snd₁ = g (left resp)
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n (left resp) | yes x₁ , snd1 | g | no x₂ , snd₁ = ⊥-elim (x₂ (dom-embed x (beh n) x₁))
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n (right rst) | yes x₁ , snd1 | g = g (right rst)
refTheorem {refm = refm} {act ∷ spec} {beh} {x ∷ fst , refSp} {decFp} {decF} n rst | no x₁ , snd1 | g = g rst 



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


