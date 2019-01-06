module TLA.Fairness where


open import Relation.Nullary
open import TLA.Def
open import LTL.Core
open import LTL.Stateless
open import LTL.Future
open import LTL.Sum
open import LTL.Product
open import LTL.Globally

WF : ∀{α} → {vars : LSet {α}} → (act : Action vars) → (e : E act)
     → (beh : (System vars) ʷ ) → (Set α) ʷ
WF act e beh
  = □ᶠ (◇ᶠ (⟨ ¬_ ⟩ $ (⟨ (cond act) e ⟩ $ beh))
       ∨ ◇ᶠ ((⟨ (cond act) e ⟩ $ beh) ∧ (⟨ (resp act) e ⟩ $ beh $ (○ beh))))


SF : ∀{α} → {vars : LSet {α}}
     → (act : Action vars) → (e : E act) → (beh : (System vars) ʷ ) → (Set α) ʷ
SF act e beh
  = □ᶠ (◇ᶠ (□ᶠ (⟨ ¬_ ⟩ $ (⟨ (cond act) e ⟩ $ beh)))
       ∨ ◇ᶠ ((⟨ (cond act) e ⟩ $ beh) ∧ (⟨ (resp act) e ⟩ $ beh $ (○ beh))))
