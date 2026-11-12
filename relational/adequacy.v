(** Relational adequacy.

    [hypercryptis_adequacy] turns a ReLoC refinement between two protocols,
    as functions of the relational channel [lrel_channel], into a statement
    about executions: for any attackers [adv] and [adv'] related at
    [lrel_attacker], if the left protocol run against [adv] terminates then
    the right protocol run against [adv'] has a terminating execution whose
    result is related as specified.  [hypercryptis_ctx_refinement] turns the
    same refinement into a contextual refinement between the two games. *)

From reloc Require Import reloc.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import with_cryptis attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma hypercryptis_adequacy Σ `{!relocPreG Σ, !publicGpreS Σ}
    (adv adv' : expr) (f f' : val) (P : val → val → Prop) σ :
  (∀ `{!relocG Σ, !publicGS Σ},
      hypercryptis_ctx -∗ REL adv << adv' : lrel_attacker) →
  (∀ `{!relocG Σ, !publicGS Σ},
      hypercryptis_ctx -∗
      REL f << f' : lrel_channel → LRel (λ v v', ⌜P v v'⌝)) →
  adequate NotStuck (run_network adv f) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([run_network adv' f'], σ) (of_val v' :: thp', h) ∧
       P v v').
Proof.
move=> Hadv Hf.
apply: (refines_adequate Σ (λ _, LRel (λ v v', ⌜P v v'⌝)%I)).
- by move=> ? v v'; iIntros "%".
- move=> ?.
  iMod (publicGS_alloc ⊤ _) as (Hpub) "#Hctx".
  iApply (refines_app with "[] []"); last by iApply (Hf with "Hctx").
  iApply (refines_app with "[] []"); last by iApply (Hadv with "Hctx").
  iApply run_network_refinement.
Qed.

Lemma hypercryptis_ctx_refinement Σ `{!relocPreG Σ, !publicGpreS Σ}
    (adv adv' : expr) (f f' : val) τ :
  (∀ `{!relocG Σ, !publicGS Σ},
      hypercryptis_ctx -∗ REL adv << adv' : lrel_attacker) →
  (∀ `{!relocG Σ, !publicGS Σ} Δ,
      hypercryptis_ctx -∗
      REL f << f' : lrel_channel → interp τ Δ) →
  ∅ ⊨ run_network adv f ≤ctx≤ run_network adv' f' : τ.
Proof.
move=> Hadv Hf.
apply: (refines_sound Σ) => Hreloc Δ.
iMod (publicGS_alloc ⊤ _) as (Hpub) "#Hctx".
iApply (refines_app with "[] []"); last by iApply (Hf with "Hctx").
iApply (refines_app with "[] []"); last by iApply (Hadv with "Hctx").
iApply run_network_refinement.
Qed.
