(** Relational attacker model.

    In the unary development ([attacker.v]) the attacker is a fixed program
    that applies every Dolev-Yao operation to the terms on the network.  In
    the relational development we instead let the attacker be an *arbitrary*
    program, and only assume that it is self-related at a type that abstracts
    over the representation of terms:

      ∀ termT, attacker_prims_rel termT → chan_lrel termT → ()

    The attacker receives the exported primitives [attacker_prims] and the
    network channel, both at the abstract type [termT].  Since the attacker
    must be related at *every* [termT], it cannot inspect the representation
    of a term (e.g. tell a ciphertext from a nonce); it can only combine terms
    through the exported primitives.  This is exactly the guarantee needed to
    instantiate [termT] with [PUB⟨·,·⟩]: every exported primitive preserves
    [PUB], so any attacker preserves it too.  By ReLoC's fundamental theorem,
    any attacker that is syntactically well typed at this type is self-related
    ([attacker_rel_typed] in [rel_adequacy.v]).

    Dependency position: after [with_cryptis_spec.v]; used by [rel_adequacy.v]. *)

From reloc Require Import reloc.
From cryptis Require Import lib cryptis.
From cryptis.core Require Import term minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.primitives Require Import pre_term simple comp with_cryptis.
From cryptis Require Import lib_spec.
From cryptis.primitives Require Import simple_spec comp_spec with_cryptis_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The primitives exported to the attacker.  Binary primitives are
    eta-expanded so that, after the two beta steps performed by the
    relational proof, the underlying primitive is applied syntactically and
    the specs of [simple_spec.v] and [comp_spec.v] apply.  Diffie–Hellman
    primitives are not exported yet: the corresponding cases of
    [publicly_related] are still work in progress. *)
Definition attacker_prims : val :=
  (tint,
  (to_int,
  ((λ: "t1" "t2", tuple "t1" "t2"),
  (untuple,
  (key AEnc,
  (key ADec,
  (key Sign,
  (key Verify,
  (key SEnc,
  (pkey,
  ((λ: "k" "t", seal "k" "t"),
  ((λ: "k" "t", open "k" "t"),
  (hash,
  (mk_nonce,
   (λ: "t1" "t2", eq_term "t1" "t2")))))))))))))))%V.

(** Run a protocol [f] against an attacker [adv].  The attacker is
    instantiated at the abstract term type (the [#()] argument is ReLoC's
    encoding of type application), handed the primitives and the channel, and
    forked before the protocol runs. *)
Definition run_network_rel : val := λ: "adv" "f",
  let: "c" := mk_channel_rel #() in
  Fork ("adv" #() attacker_prims "c");;
  "f" "c".

Section AttackerTypes.

Context `{!relocG Σ}.

Implicit Types A : lrel Σ.

(** The interface seen by the attacker, at an abstract term type [A].  The
    order matches [attacker_prims]. *)
Definition attacker_prims_rel A : lrel Σ :=
  ((lrel_int → A) *
  ((A → () + lrel_int) *
  ((A → A → A) *
  ((A → () + A * A) *
  ((A → A) *
  ((A → A) *
  ((A → A) *
  ((A → A) *
  ((A → A) *
  ((A → A) *
  ((A → A → A) *
  ((A → A → () + A) *
  ((A → A) *
  ((() → A) *
   (A → A → lrel_bool)))))))))))))))%lrel.

(** A network channel at an abstract term type: a sender and a receiver. *)
Definition chan_lrel A : lrel Σ := ((A → ()) * (() → A))%lrel.

(** The type of attackers. *)
Definition attacker_rel : lrel Σ :=
  (∀ A, attacker_prims_rel A → chan_lrel A → ())%lrel.

End AttackerTypes.

Section Proofs.

Context `{!relocG Σ, !public_relGS Σ}.

Implicit Types t : term.
Implicit Types v : val.

(** Terms related by [PUB⟨·,·⟩], as a semantic type. *)
Definition lrel_term : lrel Σ := LRel (λ v v',
  ∃ t t' : term, ⌜v = t⌝ ∗ ⌜v' = t'⌝ ∗ PUB⟨t, t'⟩)%I.

Lemma lrel_term_intro t t' : PUB⟨t, t'⟩ -∗ lrel_term t t'.
Proof. iIntros "#H". iExists t, t'. by eauto. Qed.

Lemma channel_rel_chan_lrel c c' :
  channel_rel c c' -∗ chan_lrel lrel_term c c'.
Proof.
iDestruct 1 as (sf rf sf' rf') "(-> & -> & #Hs & #Hr)".
iExists sf, sf', rf, rf'. do 2 (iSplit; first done). iSplit.
- iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
  by iApply ("Hs" with "Ht").
- iIntros "!> %v %v' [-> ->]".
  iApply "Hr". iIntros "%t %t' #Ht". by iApply lrel_term_intro.
Qed.

(** * Closure of [PUB] under the exported primitives *)

Lemma rel_prim_tint : ⊢ (lrel_int → lrel_term)%lrel tint tint.
Proof.
iIntros "!> %v %v' (%n & %e & %e')". subst v v'.
rel_apply_l rel_tint_l. rel_apply_r rel_tint_r.
rel_values. iModIntro. iApply lrel_term_intro.
by rewrite publicly_related_TInt.
Qed.

Lemma rel_prim_to_int : ⊢ (lrel_term → () + lrel_int)%lrel to_int to_int.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l rel_to_int_l. rel_apply_r rel_to_int_r.
rel_values. iModIntro.
case: (Spec.to_intP t) => [n ->|Hne].
- iDestruct (publicly_related_TInt_term with "Ht") as %->.
  iExists #n, #n. iRight. do 2 (iSplit; first done). by iExists n.
- case: (Spec.to_intP t') => [n' ->|_].
  { iDestruct (publicly_related_term_TInt with "Ht") as %e.
    by case: (Hne _ e). }
  iExists #(), #(). iLeft. by do 2 (iSplit; first done).
Qed.

Lemma rel_prim_tuple :
  ⊢ (lrel_term → lrel_term → lrel_term)%lrel
      (λ: "t1" "t2", tuple "t1" "t2")%V (λ: "t1" "t2", tuple "t1" "t2")%V.
Proof.
iIntros "!> %v1 %v1' (%t1 & %t1' & -> & -> & #H1)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t2 & %t2' & -> & -> & #H2)".
rel_pures_l. rel_pures_r.
rel_apply_l rel_tuple_l. rel_apply_r rel_tuple_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite publicly_related_TPair. by iSplit.
Qed.

Lemma rel_prim_untuple :
  ⊢ (lrel_term → () + lrel_term * lrel_term)%lrel untuple untuple.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l rel_untuple_l. rel_apply_r rel_untuple_r.
rel_values. iModIntro.
case: t => [n|t1 t2|a|kt s|k b|s|pt wf nf].
all: try (
  iAssert ⌜Spec.untuple t' = None⌝%I as %->;
  [ case: t' => //= t1' t2'; by iDestruct "Ht" as "(_ & _ & [])"
  | iExists #(), #(); iLeft; by do 2 (iSplit; first done) ]).
iDestruct (publicly_related_TPair_term with "Ht") as %(t1' & t2' & ->).
rewrite publicly_related_TPair. iDestruct "Ht" as "[H1 H2]".
iExists (t1, t2)%V, (t1', t2')%V. iRight. do 2 (iSplit; first done).
iExists t1, t1', t2, t2'. do 2 (iSplit; first done).
iSplit; by iApply lrel_term_intro.
Qed.

Lemma rel_prim_key kt : ⊢ (lrel_term → lrel_term)%lrel (key kt) (key kt).
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l rel_key_l. rel_apply_r rel_key_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite publicly_related_TKey. iSplit; first done.
case: kt; try (by iLeft); done.
Qed.

Lemma rel_prim_pkey : ⊢ (lrel_term → lrel_term)%lrel pkey pkey.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l rel_pkey_l. rel_apply_r rel_pkey_r.
rel_values. iModIntro. iApply lrel_term_intro.
by iApply publicly_related_pkey.
Qed.

Lemma rel_prim_seal :
  ⊢ (lrel_term → lrel_term → lrel_term)%lrel
      (λ: "k" "t", seal "k" "t")%V (λ: "k" "t", seal "k" "t")%V.
Proof.
iIntros "!> %v1 %v1' (%k & %k' & -> & -> & #Hk)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t & %t' & -> & -> & #Ht)".
rel_pures_l. rel_pures_r.
rel_apply_l rel_seal_l. rel_apply_r rel_seal_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite publicly_related_TSeal. iLeft. by iSplit.
Qed.

Lemma rel_prim_open :
  cryptis_rel_ctx -∗
  (lrel_term → lrel_term → () + lrel_term)%lrel
    (λ: "k" "t", open "k" "t")%V (λ: "k" "t", open "k" "t")%V.
Proof.
iIntros "#Hctx !> %v1 %v1' (%k & %k' & -> & -> & #Hk)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t & %t' & -> & -> & #Ht)".
rel_pures_l. rel_pures_r.
rel_apply_l rel_open_l. rel_apply_r rel_open_r.
rel_values.
iMod (publicly_related_open_fupd (E:=⊤) k k' t t' ltac:(solve_ndisj)
        with "Hctx Hk Ht") as %Hiff.
iModIntro.
case e: (Spec.open k t) Hiff => [t1|] Hiff;
case e': (Spec.open k' t') Hiff => [t1'|] Hiff.
- iExists t1, t1'. iRight. do 2 (iSplit; first done).
  iApply lrel_term_intro. by iApply (publicly_related_open e e' with "Hk Ht").
- exfalso. apply: is_Some_None. apply Hiff. by eapply mk_is_Some.
- exfalso. apply: is_Some_None. apply Hiff. by eapply mk_is_Some.
- iExists #(), #(). iLeft. by do 2 (iSplit; first done).
Qed.

Lemma rel_prim_hash : ⊢ (lrel_term → lrel_term)%lrel hash hash.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l rel_hash_l. rel_apply_r rel_hash_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite publicly_related_THash. by iLeft.
Qed.

(** Attacker nonces are fresh on both sides and publicly related. *)
Lemma rel_prim_mk_nonce :
  cryptis_rel_ctx -∗ (() → lrel_term)%lrel mk_nonce mk_nonce.
Proof.
iIntros "#Hctx !> %v %v' [-> ->]".
rel_apply_l (rel_mk_nonce_l _ _ (λ n, {[n]}) with "[//]").
{ iIntros "%t". rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
iIntros (n) "%Hn #mint_n Htt". rewrite big_sepS_singleton.
rel_apply_r (rel_mk_nonce_r _ _ (λ n, {[n]}) with "[//]").
{ iIntros "%t". rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
iIntros (n') "%Hn' #mint_spec_n' Htts". rewrite big_sepS_singleton.
rewrite (term_token_difference n (↑cryptisN.@"public_rel".@"flow") ⊤) //.
iDestruct "Htt" as "[Htt_flow Htt]".
rewrite (term_token_difference n (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "Htt" as "[Htt_map _]".
rewrite (term_token_spec_difference n' (↑cryptisN.@"public_rel".@"flow") ⊤) //.
iDestruct "Htts" as "[Htts_flow Htts]".
rewrite (term_token_spec_difference n' (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "Htts" as "[Htts_map _]".
iMod (public_rel_flow_l_extend (E:=⊤) n ltac:(solve_ndisj)
        with "Hctx Htt_flow Htt_map") as "[prot_n Htt_map]".
iMod (public_rel_flow_r_extend (E:=⊤) n' ltac:(solve_ndisj)
        with "Hctx Htts_flow Htts_map") as "[prot_n' Htts_map]".
iMod (public_rel_extend (E:=⊤) n n' ltac:(solve_ndisj)
        with "Hctx [] prot_n prot_n' Htt_map Htts_map") as "#Hel".
{ iIntros "#Hel". rewrite (publicly_related_nonce Hn Hn'). by iSplit; last iSplit. }
rel_values. iModIntro. iApply lrel_term_intro.
rewrite (publicly_related_nonce Hn Hn'). by iSplit; last iSplit.
Qed.

(** Equality tests agree on both sides because [PUB] is a partial
    bijection. *)
Lemma rel_prim_eq_term :
  cryptis_rel_ctx -∗
  (lrel_term → lrel_term → lrel_bool)%lrel
    (λ: "t1" "t2", eq_term "t1" "t2")%V (λ: "t1" "t2", eq_term "t1" "t2")%V.
Proof.
iIntros "#Hctx !> %v1 %v1' (%t1 & %t1' & -> & -> & #H1)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t2 & %t2' & -> & -> & #H2)".
rel_pures_l. rel_pures_r.
rel_apply_l rel_eq_term_l. rel_apply_r rel_eq_term_r.
rel_values.
iMod (publicly_related_part_bij' (E:=⊤) t1 t1' t2 t2' ltac:(solve_ndisj)
        with "Hctx H1 H2") as %Hiff.
iModIntro. iExists (bool_decide (t1 = t2)). iPureIntro. split; first done.
do 2 f_equal. apply bool_decide_ext. by rewrite Hiff.
Qed.

Lemma rel_attacker_prims :
  cryptis_rel_ctx -∗
  REL attacker_prims << attacker_prims : attacker_prims_rel lrel_term.
Proof.
iIntros "#Hctx". rel_values. iModIntro.
rewrite /attacker_prims /attacker_prims_rel.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_tint.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_to_int.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_tuple.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_untuple.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_key.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_key.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_key.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_key.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_key.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_pkey.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_seal.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first by iApply rel_prim_open.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first iApply rel_prim_hash.
iExists _, _, _, _. do 2 (iSplit; first done). iSplit; first by iApply rel_prim_mk_nonce.
by iApply rel_prim_eq_term.
Qed.

(** * Running a protocol against an arbitrary attacker *)

Lemma rel_run_network_rel (adv adv' f f' : val) (A : val → val → iProp Σ) :
  cryptis_rel_ctx -∗
  (REL adv << adv' : attacker_rel) -∗
  (∀ c c', channel_rel c c' -∗ REL f c << f' c' : A) -∗
  REL run_network_rel adv f << run_network_rel adv' f' : A.
Proof.
iIntros "#Hctx Hadv Hf". rewrite /run_network_rel.
rel_pures_l. rel_pures_r.
rel_bind_l (mk_channel_rel #()). rel_bind_r (mk_channel_rel #()).
iApply refines_bind; first iApply rel_mk_channel_rel.
iIntros (c c') "#Hc /=". rel_pures_l. rel_pures_r.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply (refines_bind with "[Hadv]").
{ iApply refines_fork.
  iApply (refines_app _ _ _ _ (chan_lrel lrel_term) with "[Hadv] []"); last first.
  { rel_values. iModIntro. by iApply channel_rel_chan_lrel. }
  iApply (refines_app _ _ _ _ (attacker_prims_rel lrel_term) with "[Hadv] []"); last first.
  { by iApply rel_attacker_prims. }
  iApply (refines_app _ _ _ _ (lrel_unit) with "[Hadv] []"); last first.
  { rel_values. }
  iApply (refines_wand with "Hadv").
  iIntros (v v') "H !>". iSpecialize ("H" $! lrel_term). iExact "H". }
iIntros (? ?) "_ /=". rel_pures_l. rel_pures_r.
by iApply "Hf".
Qed.

End Proofs.
