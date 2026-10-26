(** Relational adequacy.

    [cryptis_rel_adequacy] turns a ReLoC refinement between two protocols,
    proved against the relational channel [channel_rel], into a statement
    about executions: for any valid attacker [adv], if the game against [adv]
    terminates on the left then it has a terminating execution on the right
    whose result is related as specified.  [cryptis_ctx_refinement] turns the
    same refinement into a contextual refinement between the two games run
    against [adv].  In both, [Σ] is any set of ghost state that contains
    ReLoC's and [PUB]'s, so that the refinement may use ghost state of its
    own; the contextual refinement itself does not mention [Σ].

    Dependency position: after [primitives/attacker_spec.v]; used by the
    relational case studies (e.g. [examples/ind_cpa.v]). *)

From reloc Require Import reloc.
From reloc.typing Require Import types interp.
From cryptis Require Import lib cryptis.
From cryptis.core Require Import term.
From cryptis.hyper.core Require Import rel.
From cryptis.hyper.primitives Require Import with_cryptis_spec attacker_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma cryptis_rel_adequacy Σ `{!relocPreG Σ, !public_relGpreS Σ}
    (adv : expr) (f f' : val) (P : val → val → Prop) σ :
  attacker_valid adv →
  (∀ `{!relocG Σ, !public_relGS Σ} c c',
      cryptis_rel_ctx -∗
      channel_rel c c' -∗
      REL f c << f' c' : (λ v v', ⌜P v v'⌝)) →
  adequate NotStuck (run_network_rel adv f) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([run_network_rel adv f'], σ) (of_val v' :: thp', h) ∧
       P v v').
Proof.
move=> Hadv Hf.
apply: (refines_adequate Σ (λ _, LRel (λ v v', ⌜P v v'⌝)%I)).
- by move=> ? v v'; iIntros "%".
- move=> ?.
  iMod (public_relGS_alloc ⊤ _) as (Hpub) "#Hctx".
  iApply (rel_run_network_rel with "[] []").
  + by iApply (Hadv with "Hctx").
  + iIntros (c c') "#Hc". by iApply (Hf with "Hctx Hc").
Qed.

Lemma cryptis_ctx_refinement Σ `{!relocPreG Σ, !public_relGpreS Σ}
    (adv : expr) (f f' : val) τ :
  attacker_valid adv →
  (∀ `{!relocG Σ, !public_relGS Σ} Δ c c',
      cryptis_rel_ctx -∗
      channel_rel c c' -∗
      REL f c << f' c' : interp τ Δ) →
  ∅ ⊨ run_network_rel adv f ≤ctx≤ run_network_rel adv f' : τ.
Proof.
move=> Hadv Hf.
apply: (refines_sound Σ) => Hreloc Δ.
iMod (public_relGS_alloc ⊤ _) as (Hpub) "#Hctx".
iApply (rel_run_network_rel with "[] []").
- by iApply (Hadv with "Hctx").
- iIntros (c c') "#Hc". by iApply (Hf with "Hctx Hc").
Qed.
