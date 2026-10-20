From cryptis.hyper.examples.vote.proofs Require Export base voter arbitrator.
From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import rel.
From cryptis.hyper.primitives Require Import simple_spec with_cryptis_spec.
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

Lemma rel_election_of c c' cands votes votes' :
  votes ≡ₚ votes' →
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL election_of cands votes c << election_of cands votes' c' : ().
Proof.
iIntros (Hperm) "#Hctx #Hc".
have Hlen := Permutation_length Hperm.
rewrite /election_of. rel_pures_l. rel_pures_r.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (rel_mk_arb_key with "Hctx"). iIntros (skT skT') "#HT" => /=.
rel_pures_l. rel_pures_r.
rel_apply_l rel_pkey_l. rel_apply_r rel_pkey_r.
rel_pures_l. rel_pures_r.
rel_bind_l (mk_voters _). rel_bind_r (mk_voters _).
iApply (refines_bind with "[]"); first by iApply (rel_mk_voters skT skT' with "Hctx").
iIntros (? ?) "(%ks & %ks' & -> & -> & %Hk & %Hk' & #Hkeys & toks)" => /=.
rel_pures_l. rel_pures_r.
rel_apply_l rel_pkeys_l; first lia. rel_apply_r rel_pkeys_r; first lia.
rel_pures_l. rel_pures_r.
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind.
{ iApply (rel_send with "Hc"). iNext. by iDestruct "HT" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_pures_l. rel_pures_r.
rel_apply_l rel_term_of_list_l. rel_apply_r rel_term_of_list_r.
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind.
{ iApply (rel_send with "Hc"). iNext. iApply pub_of_list. by iApply pub_pkeys. }
iIntros (? ?) "[-> ->]" => /=. rel_pures_l. rel_pures_r.
rel_bind_l (fork_voters _ _ _). rel_bind_r (fork_voters _ _ _).
iApply (refines_bind with "[toks]").
{ iApply (rel_fork_voters with "Hctx Hc HT Hkeys toks"); lia. }
iIntros (? ?) "_" => /=. rel_pures_l. rel_pures_r.
iApply (rel_arbitrator with "Hctx Hc Hkeys") => //; lia.
Qed.

End Proofs.
