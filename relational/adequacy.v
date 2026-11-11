(** Relational adequacy.

    [hypercryptis_adequacy] turns a ReLoC refinement between two protocols,
    as functions of the relational channel [lrel_channel], into a statement
    about executions: for any valid attacker [adv], if the game against [adv]
    terminates on the left then it has a terminating execution on the right
    whose result is related as specified.  [hypercryptis_ctx_refinement]
    turns the same refinement into a contextual refinement between the two
    games run against [adv]. *)

From reloc Require Import reloc.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import with_cryptis attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma hypercryptis_adequacy Σ `{!relocPreG Σ, !publicGpreS Σ}
    (adv : expr) (f f' : val) (P : val → val → Prop) σ :
  attacker_valid adv →
  (∀ `{!relocG Σ, !publicGS Σ},
      hypercryptis_ctx -∗
      REL f << f' : lrel_channel → LRel (λ v v', ⌜P v v'⌝)) →
  adequate NotStuck (run_network adv f) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([run_network adv f'], σ) (of_val v' :: thp', h) ∧
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
    (adv : expr) (f f' : val) τ :
  attacker_valid adv →
  (∀ `{!relocG Σ, !publicGS Σ} Δ,
      hypercryptis_ctx -∗
      REL f << f' : lrel_channel → interp τ Δ) →
  ∅ ⊨ run_network adv f ≤ctx≤ run_network adv f' : τ.
Proof.
move=> Hadv Hf.
apply: (refines_sound Σ) => Hreloc Δ.
iMod (publicGS_alloc ⊤ _) as (Hpub) "#Hctx".
iApply (refines_app with "[] []"); last by iApply (Hf with "Hctx").
iApply (refines_app with "[] []"); last by iApply (Hadv with "Hctx").
iApply run_network_refinement.
Qed.
