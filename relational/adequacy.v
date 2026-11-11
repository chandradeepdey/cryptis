(** Relational adequacy.

    [cryptis_rel_adequacy] turns a ReLoC refinement between two protocols,
    as functions of the relational channel [lrel_channel], into a statement
    about executions: for any valid attacker [adv], if the game against [adv]
    terminates on the left then it has a terminating execution on the right
    whose result is related as specified.  [cryptis_ctx_refinement] turns the
    same refinement into a contextual refinement between the two games run
    against [adv]. *)

From reloc Require Import reloc.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import with_cryptis attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma cryptis_rel_adequacy Σ `{!relocPreG Σ, !public_relGpreS Σ}
    (adv : expr) (f f' : val) (P : val → val → Prop) σ :
  attacker_valid adv →
  (∀ `{!relocG Σ, !public_relGS Σ},
      cryptis_rel_ctx -∗
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
  iMod (public_relGS_alloc ⊤ _) as (Hpub) "#Hctx".
  iApply (refines_run_network with "[] []").
  + by iApply (Hadv with "Hctx").
  + iIntros (c c') "#Hc".
    iApply (refines_app with "[] []"); last by rel_values.
    by iApply (Hf with "Hctx").
Qed.

Lemma cryptis_ctx_refinement Σ `{!relocPreG Σ, !public_relGpreS Σ}
    (adv : expr) (f f' : val) τ :
  attacker_valid adv →
  (∀ `{!relocG Σ, !public_relGS Σ} Δ,
      cryptis_rel_ctx -∗
      REL f << f' : lrel_channel → interp τ Δ) →
  ∅ ⊨ run_network adv f ≤ctx≤ run_network adv f' : τ.
Proof.
move=> Hadv Hf.
apply: (refines_sound Σ) => Hreloc Δ.
iMod (public_relGS_alloc ⊤ _) as (Hpub) "#Hctx".
iApply (refines_run_network with "[] []").
- by iApply (Hadv with "Hctx").
- iIntros (c c') "#Hc".
  iApply (refines_app with "[] []"); last by rel_values.
  by iApply (Hf with "Hctx").
Qed.
