(** Relational adequacy.

    [cryptis_rel_adequacy] turns a ReLoC refinement between two protocol
    runs, proved against the relational channel [channel_rel], into a
    statement about executions: for any attacker [adv] that is self-related at
    [attacker_rel], if the left game terminates then the right game has a
    terminating execution whose result is related as specified.  The attacker
    is arbitrary code; see [attacker_spec.v] for why the typing assumption
    prevents it from inspecting term representations.

    [cryptis_ctx_refinement] turns the same refinement into a contextual
    refinement between the two games seen as functions of the attacker, so
    that the attacker is an arbitrary well-typed context.

    [attacker_rel_typed] discharges the self-relatedness assumption for any
    attacker that is syntactically well typed at [attacker_ty], via ReLoC's
    fundamental theorem.

    Dependency position: after [primitives/attacker_spec.v]; used by the
    relational case studies (e.g. [examples/ind_cpa.v]). *)

From reloc Require Import reloc.
From reloc.typing Require Import types interp fundamental.
From cryptis Require Import lib cryptis.
From cryptis.core Require Import term rel.
From cryptis.primitives Require Import with_cryptis_spec attacker_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma cryptis_rel_adequacy Σ `{!relocPreG Σ, !public_relGpreS Σ}
    (adv f f' : val) (P : val → val → Prop) σ :
  (∀ `{!relocG Σ}, ⊢ REL adv << adv : attacker_rel) →
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
  iApply (rel_run_network_rel with "Hctx [] []").
  + iApply Hadv.
  + iIntros (c c') "#Hc". by iApply (Hf with "Hctx Hc").
Qed.

(** * Syntactically typed attackers *)

(** The System F type of the exported primitives, with [#0] standing for the
    abstract term type; it mirrors [attacker_prims_rel]. *)
Definition attacker_prims_ty : type :=
  ((TNat → #0) *
  ((#0 → () + TNat) *
  ((#0 → #0 → #0) *
  ((#0 → () + #0 * #0) *
  ((#0 → #0) *
  ((#0 → #0) *
  ((#0 → #0) *
  ((#0 → #0) *
  ((#0 → #0) *
  ((#0 → #0) *
  ((#0 → #0 → #0) *
  ((#0 → #0 → () + #0) *
  ((#0 → #0) *
  ((() → #0) *
   (#0 → #0 → TBool)))))))))))))))%ty.

Definition chan_ty : type := ((#0 → ()) * (() → #0))%ty.

Definition attacker_ty : type := (∀: attacker_prims_ty → chan_ty → ())%ty.

Lemma attacker_rel_typed `{!relocG Σ} (adv : val) :
  ∅ ⊢ₜ adv : attacker_ty →
  ⊢ REL adv << adv : attacker_rel.
Proof.
move=> Hty. iPoseProof (refines_typed attacker_ty [] adv Hty) as "H".
iApply (refines_wand with "H"). iIntros (v v') "Hv !>".
iExact "Hv".
Qed.

(** * Contextual refinement

    Here the attacker is the context.  A game [λ: "adv", run_network_rel "adv" f]
    has type [attacker_ty → τ] and may be plugged into any well-typed
    context, which in particular may apply it to any well-typed attacker and
    observe the result.  The hypothesis is the same protocol refinement as for
    [cryptis_rel_adequacy]; the two contexts may even hand different (but
    related) attackers to the two games.  The statement mentions no [Σ]: the
    ghost state is fixed internally to [#[relocΣ; public_relΣ]]. *)
Lemma cryptis_ctx_refinement (f f' : val) τ :
  (∀ Σ `{!relocG Σ, !public_relGS Σ} Δ c c',
      cryptis_rel_ctx -∗
      channel_rel c c' -∗
      REL f c << f' c' : interp τ Δ) →
  ∅ ⊨ (λ: "adv", run_network_rel "adv" f)
      ≤ctx≤ (λ: "adv", run_network_rel "adv" f') : (attacker_ty → τ)%ty.
Proof.
move=> Hf.
apply: (refines_sound #[relocΣ; public_relΣ]) => Hreloc Δ.
iMod (public_relGS_alloc ⊤ _) as (Hpub) "#Hctx".
rel_pures_l. rel_pures_r.
iApply refines_arrow_val. iIntros "!> %adv %adv' #Hadv".
rel_pures_l. rel_pures_r.
iApply (rel_run_network_rel with "Hctx [] []").
- by rel_values.
- iIntros (c c') "#Hc". by iApply (Hf with "Hctx Hc").
Qed.
