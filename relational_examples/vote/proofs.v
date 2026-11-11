(** Proofs of the voting case study, one file per role. *)

From cryptis.hyper.examples.vote.proofs Require Export base voter arbitrator.
From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import simple with_cryptis.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.vote Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

Lemma election_of_refinement c c' cands votes votes' :
  votes ≡ₚ votes' →
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  REL election_of cands votes c << election_of cands votes' c' : ().
Proof.
iIntros (Hperm) "#Hctx #Hc".
have Hlen := Permutation_length Hperm.
rewrite /election_of. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (mk_arb_key_refinement with "Hctx"). iIntros (skT skT') "#HT" => /=.
rel_pures.
rel_apply_l refines_pkey_l. rel_apply_r refines_pkey_r.
rel_pures.
rel_bind_l (mk_voters _). rel_bind_r (mk_voters _).
iApply (refines_bind with "[]"); first by iApply (mk_voters_refinement skT skT' with "Hctx").
iIntros (? ?) "(%ks & %ks' & -> & -> & %Hk & %Hk' & #Hkeys & toks)" => /=.
rel_pures.
rel_apply_l refines_pkeys_l; first lia. rel_apply_r refines_pkeys_r; first lia.
rel_pures.
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind.
{ iApply (refines_send with "Hc"). iNext. by iDestruct "HT" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_pures.
rel_apply_l refines_term_of_list_l. rel_apply_r refines_term_of_list_r.
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind.
{ iApply (refines_send with "Hc"). iNext.
  iApply publicly_related_of_list. by iApply pub_pkeys. }
iIntros (? ?) "[-> ->]" => /=. rel_pures.
rel_bind_l (fork_voters _ _ _). rel_bind_r (fork_voters _ _ _).
iApply (refines_bind with "[toks]").
{ iApply (fork_voters_refinement with "Hctx Hc HT Hkeys toks"); lia. }
iIntros (? ?) "_" => /=. rel_pures.
iApply (arbitrator_refinement with "Hctx Hc Hkeys") => //; lia.
Qed.

End Proofs.
