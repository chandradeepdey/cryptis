(** * The attacker

The attacker is a program that builds network channels, each a pair of
functions that the protocol calls to send and to receive a term.  The protocol
opens a channel for each of its parties.  The attacker reads every message,
and it delivers, withholds, replays or forges messages at will.  Two attackers
[adv] and [adv'] are valid ([attacker_valid]) when they are related, as
programs that build related channels.

- [Network] runs a protocol against the attacker ([run_network_refinement]),
  and opens a channel ([refines_new_channel]).
- [Primitives] gives each primitive of the attacker a contract in the style
  of a type.  These types keep terms abstract, so the attacker cannot look
  inside them.
- [Typed]: every well-typed attacker is valid ([attacker_valid_typed]). *)

From reloc.typing Require Import fundamental.
From cryptis.core Require Import term.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.proofmode Require Import updates.
From cryptis.primitives Require Import pre_term simple with_cryptis.
From cryptis.hyper.primitives Require Import simple comp with_cryptis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition run_network : val := λ: "adv" "f",
  "f" "adv".

Section Network.

Context `{!relocG Σ, !publicGS Σ}.

Definition lrel_attacker : lrel Σ := (() → lrel_channel)%lrel.

Lemma refines_new_channel adv adv' :
  lrel_attacker adv adv' -∗ REL adv #() << adv' #() : lrel_channel.
Proof.
iIntros "#Hadv". iApply (refines_app _ _ _ _ ()%lrel); by rel_values.
Qed.

Lemma refines_run_network (adv adv' : expr) (f f' : val) (A : val → val → iProp Σ) :
  (REL adv << adv' : lrel_attacker) -∗
  (∀ adv adv', lrel_attacker adv adv' -∗ REL f adv << f' adv' : A) -∗
  REL run_network adv f << run_network adv' f' : A.
Proof.
iIntros "Hadv Hf". rewrite /run_network.
rel_bind_l adv. rel_bind_r adv'.
iApply (refines_bind with "Hadv"). iIntros (a a') "#Ha /=".
rel_pures_l. rel_pures_r. by iApply "Hf".
Qed.

Lemma run_network_refinement (A : lrel Σ) :
  ⊢ REL run_network << run_network : lrel_attacker → (lrel_attacker → A) → A.
Proof.
rel_arrow_val. iIntros (adv adv') "#Hadv".
rewrite /run_network. rel_pures_l. rel_pures_r.
rel_arrow_val. iIntros (f f') "#Hf".
rel_pures_l. rel_pures_r.
iApply (refines_app _ _ _ _ lrel_attacker); by rel_values.
Qed.

End Network.

Definition attacker_valid (adv adv' : expr) : Prop :=
  ∀ Σ `(!relocG Σ, !publicGS Σ),
    ⊢ hypercryptis_ctx -∗ REL adv << adv' : lrel_attacker.

Section Primitives.

(** Binary primitives are eta-expanded so that the specs of [simple.v]
    and [comp.v], which match saturated applications, apply. *)
Definition attacker_prims : val :=
  (tint, to_int, (λ: "t1" "t2", tuple "t1" "t2")%V, untuple,
   derive_aenc_key, derive_sign_key, derive_senc_key, pkey,
   (λ: "k" "t", seal "k" "t")%V, (λ: "k" "t", open "k" "t")%V,
   hash, mk_nonce, (λ: "t1" "t2", eq_term "t1" "t2")%V)%V.

Definition prims_ty : type :=
  ((TNat → #0) * (#0 → () + TNat) * (#0 → #0 → #0) * (#0 → () + #0 * #0) *
   (#0 → #0) * (#0 → #0) * (#0 → #0) * (#0 → #0) *
   (#0 → #0 → #0) * (#0 → #0 → () + #0) *
   (#0 → #0) * (() → #0) * (#0 → #0 → TBool))%ty.

Context `{!relocG Σ, !publicGS Σ}.

Lemma tint_refinement : ⊢ (lrel_int → lrel_term)%lrel tint tint.
Proof.
iIntros "!> %v %v' (%n & %e & %e')". subst v v'.
rel_apply_l refines_tint_l. rel_apply_r refines_tint_r.
rel_values. iModIntro. iApply lrel_term_intro.
by rewrite public_TInt.
Qed.

Lemma to_int_refinement : ⊢ (lrel_term → () + lrel_int)%lrel to_int to_int.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l refines_to_int_l. rel_apply_r refines_to_int_r.
rel_values. iModIntro.
case: (Spec.to_intP t) => [n ->|Hne].
- iDestruct (public_TInt_term with "Ht") as %->.
  iExists #n, #n. iRight. do 2 (iSplit; first done). by iExists n.
- case: (Spec.to_intP t') => [n' ->|_].
  { iDestruct (public_term_TInt with "Ht") as %e.
    by case: (Hne _ e). }
  iExists #(), #(). iLeft. by do 2 (iSplit; first done).
Qed.

Lemma tuple_refinement :
  ⊢ (lrel_term → lrel_term → lrel_term)%lrel
      (λ: "t1" "t2", tuple "t1" "t2")%V (λ: "t1" "t2", tuple "t1" "t2")%V.
Proof.
iIntros "!> %v1 %v1' (%t1 & %t1' & -> & -> & #H1)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t2 & %t2' & -> & -> & #H2)".
rel_pures_l. rel_pures_r.
rel_apply_l refines_tuple_l. rel_apply_r refines_tuple_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite public_TPair. by iSplit.
Qed.

Lemma untuple_refinement :
  ⊢ (lrel_term → () + lrel_term * lrel_term)%lrel untuple untuple.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l refines_untuple_l. rel_apply_r refines_untuple_r.
rel_values. iModIntro.
case: t => [n|t1 t2|a|kt s|k b|s|pt wf nf].
all: try (
  iAssert ⌜Spec.untuple t' = None⌝%I as %->;
  [ case: t' => //= t1' t2';
    by iDestruct "Ht" as "(_ & _ & [[]|(_ & [[]|[_ []]])])"
  | iExists #(), #(); iLeft; by do 2 (iSplit; first done) ]).
iDestruct (public_TPair_term with "Ht") as %(t1' & t2' & ->).
rewrite public_TPair. iDestruct "Ht" as "[H1 H2]".
iExists (t1, t2)%V, (t1', t2')%V. iRight. do 2 (iSplit; first done).
iExists t1, t1', t2, t2'. do 2 (iSplit; first done).
iSplit; by iApply lrel_term_intro.
Qed.

Lemma key_refinement kt : ⊢ (lrel_term → lrel_term)%lrel (key kt) (key kt).
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l refines_key_l. rel_apply_r refines_key_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite public_TKey. iSplit; first done.
case: kt; try (by iLeft); done.
Qed.

Lemma derive_aenc_key_refinement :
  ⊢ (lrel_term → lrel_term)%lrel derive_aenc_key derive_aenc_key.
Proof.
iIntros "!> %v %v' Hv". rel_rec_l. rel_rec_r.
iApply (refines_app with "[] [Hv]"); [rel_values; iApply key_refinement|by rel_values].
Qed.

Lemma derive_sign_key_refinement :
  ⊢ (lrel_term → lrel_term)%lrel derive_sign_key derive_sign_key.
Proof.
iIntros "!> %v %v' Hv". rel_rec_l. rel_rec_r.
iApply (refines_app with "[] [Hv]"); [rel_values; iApply key_refinement|by rel_values].
Qed.

Lemma derive_senc_key_refinement :
  ⊢ (lrel_term → lrel_term)%lrel derive_senc_key derive_senc_key.
Proof.
iIntros "!> %v %v' Hv". rel_rec_l. rel_rec_r.
iApply (refines_app with "[] [Hv]"); [rel_values; iApply key_refinement|by rel_values].
Qed.

Lemma pkey_refinement : ⊢ (lrel_term → lrel_term)%lrel pkey pkey.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l refines_pkey_l. rel_apply_r refines_pkey_r.
rel_values. iModIntro. iApply lrel_term_intro.
by iApply public_pkey.
Qed.

Lemma seal_refinement :
  ⊢ (lrel_term → lrel_term → lrel_term)%lrel
      (λ: "k" "t", seal "k" "t")%V (λ: "k" "t", seal "k" "t")%V.
Proof.
iIntros "!> %v1 %v1' (%k & %k' & -> & -> & #Hk)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t & %t' & -> & -> & #Ht)".
rel_pures_l. rel_pures_r.
rel_apply_l refines_seal_l. rel_apply_r refines_seal_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite public_TSeal. iLeft. by iSplit.
Qed.

Lemma open_refinement :
  hypercryptis_ctx -∗
  (lrel_term → lrel_term → () + lrel_term)%lrel
    (λ: "k" "t", open "k" "t")%V (λ: "k" "t", open "k" "t")%V.
Proof.
iIntros "#Hctx !> %v1 %v1' (%k & %k' & -> & -> & #Hk)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t & %t' & -> & -> & #Ht)".
rel_pures_l. rel_pures_r.
rel_apply_l refines_open_l. rel_apply_r refines_open_r.
rel_values.
iMod (public_open_fupd (E:=⊤) k k' t t' ltac:(solve_ndisj)
        with "Hctx Hk Ht") as %Hiff.
case e: (Spec.open k t) Hiff => [t1|] Hiff;
case e': (Spec.open k' t') Hiff => [t1'|] Hiff; last iModIntro.
- iMod (public_open (E:=⊤) ltac:(solve_ndisj) e e' with "Hctx Hk Ht") as "#Ht1".
  iModIntro. iExists t1, t1'. iRight. do 2 (iSplit; first done).
  by iApply lrel_term_intro.
- exfalso. apply: is_Some_None. apply Hiff. by eapply mk_is_Some.
- exfalso. apply: is_Some_None. apply Hiff. by eapply mk_is_Some.
- iExists #(), #(). iLeft. by do 2 (iSplit; first done).
Qed.

Lemma hash_refinement : ⊢ (lrel_term → lrel_term)%lrel hash hash.
Proof.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
rel_apply_l refines_hash_l. rel_apply_r refines_hash_r.
rel_values. iModIntro. iApply lrel_term_intro.
rewrite public_THash. by iLeft.
Qed.

Lemma mk_nonce_refinement :
  hypercryptis_ctx -∗ (() → lrel_term)%lrel mk_nonce mk_nonce.
Proof.
iIntros "#Hctx !> %v %v' [-> ->]".
rel_apply_l (refines_mk_nonce_l _ _ (λ n, {[n]}) with "[//]").
{ iIntros "%t". rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
iIntros (n) "%Hn #mint_n Htt". rewrite big_sepS_singleton.
rel_apply_r (refines_mk_nonce_r _ _ (λ n, {[n]}) with "[//]").
{ iIntros "%t". rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
iIntros (n') "%Hn' #mint_spec_n' Htts". rewrite big_sepS_singleton.
iDestruct (term_token_public_token_l with "Htt") as "(Htt & _ & _)";
  first by move: Hn => /is_nonceP [? ->].
iDestruct (term_token_public_token_r with "Htts") as "(Htts & _ & _)";
  first by move: Hn' => /is_nonceP [? ->].
iMod (public_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] [] [] Htt Htts") as "[_ #Hpub]";
  [|by move: Hn {Hn'} => /is_nonceP [? ->]|by move: Hn' {Hn} => /is_nonceP [? ->]|].
{ iIntros "!> #Hel". rewrite (public_nonce Hn Hn'). by iSplit; last iSplit. }
rel_values. iModIntro. by iApply lrel_term_intro.
Qed.

Lemma eq_term_refinement :
  hypercryptis_ctx -∗
  (lrel_term → lrel_term → lrel_bool)%lrel
    (λ: "t1" "t2", eq_term "t1" "t2")%V (λ: "t1" "t2", eq_term "t1" "t2")%V.
Proof.
iIntros "#Hctx !> %v1 %v1' (%t1 & %t1' & -> & -> & #H1)".
rel_pures_l. rel_pures_r. rel_arrow_val.
iIntros "%v2 %v2' (%t2 & %t2' & -> & -> & #H2)".
rel_pures_l. rel_pures_r.
rel_apply_l refines_eq_term_l. rel_apply_r refines_eq_term_r.
rel_values.
iMod (public_part_bij' (E:=⊤) t1 t1' t2 t2' ltac:(solve_ndisj)
        with "Hctx H1 H2") as %Hiff.
iModIntro. iExists (bool_decide (t1 = t2)). iPureIntro. split; first done.
do 2 f_equal. apply bool_decide_ext. by rewrite Hiff.
Qed.

Lemma attacker_prims_refinement Δ :
  hypercryptis_ctx -∗
  interp prims_ty (lrel_term :: Δ) attacker_prims attacker_prims.
Proof.
iIntros "#Hctx". rewrite /prims_ty /attacker_prims /=.
repeat (iExists _, _, _, _; do 2 (iSplit; first done); iSplit).
- iApply tint_refinement.
- iApply to_int_refinement.
- iApply tuple_refinement.
- iApply untuple_refinement.
- iApply derive_aenc_key_refinement.
- iApply derive_sign_key_refinement.
- iApply derive_senc_key_refinement.
- iApply pkey_refinement.
- iApply seal_refinement.
- by iApply open_refinement.
- iApply hash_refinement.
- by iApply mk_nonce_refinement.
- by iApply eq_term_refinement.
Qed.

End Primitives.

Section Typed.

Definition channel_ty : type := ((#0 → ()) * (() → #0))%ty.

Definition network_ty : type := (() → channel_ty)%ty.

Definition attacker_ty : type := (prims_ty → network_ty)%ty.

Lemma attacker_valid_typed e :
  ∅ ⊢ₜ e : attacker_ty →
  attacker_valid (e attacker_prims) (e attacker_prims).
Proof.
move=> /(fundamental [lrel_term]) He Σ ? ?. iIntros "#Hctx".
iPoseProof (He $! ∅ with "[]") as "H"; first by rewrite /env_ltyped2 fmap_empty.
rewrite fmap_empty subst_map_empty.
iApply (refines_app with "H"). rel_values. iModIntro.
iPoseProof (attacker_prims_refinement [] with "Hctx") as "Hp". iExact "Hp".
Qed.

End Typed.
