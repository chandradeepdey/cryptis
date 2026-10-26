(** Relational attacker model.

    The attacker is a program [adv] that [init_network_rel] forks on a fresh
    network channel, as [init_network] does in the unary development.  It is
    valid ([attacker_valid]) when it is self-related at [attacker_rel], which
    maps related channels to related computations; the security theorems of
    [rel_adequacy.v] hold for every valid attacker.

    The [rel_prim_*] lemmas give the unary primitives type-like contracts over
    [lrel_term], the terms related by [PUB⟨·,·⟩], and over [lrel_channel].
    They are what a validity proof uses when the attacker calls a primitive.
    [attacker_valid_typed] packages them: an attacker that refers to the
    primitives by their names in [attacker_prims] and is well typed at
    [attacker_ty] in [attacker_prims_ty], with [#0] standing for terms and
    [#1] for the channel, is valid.  These type variables are free, so the
    attacker cannot inspect the representation of a term or of the channel;
    the proof is ReLoC's fundamental theorem with [#0] interpreted as
    [lrel_term] and [#1] as [lrel_channel].

    Dependency position: after [with_cryptis_spec.v]; used by [rel_adequacy.v]. *)

From reloc Require Import reloc.
From reloc.typing Require Import types interp fundamental.
From cryptis Require Import lib cryptis.
From cryptis.core Require Import term.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.primitives Require Import pre_term simple comp with_cryptis.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition init_network_rel : val := λ: "adv",
  let: "c" := mk_channel_rel #() in
  Fork ("adv" "c");;
  "c".

Definition run_network_rel : val := λ: "adv" "f",
  "f" (init_network_rel "adv").

Section Proofs.

Context `{!relocG Σ, !public_relGS Σ}.

Implicit Types t : term.
Implicit Types v : val.

Definition lrel_term : lrel Σ := LRel (λ v v',
  ∃ t t' : term, ⌜v = t⌝ ∗ ⌜v' = t'⌝ ∗ PUB⟨t, t'⟩)%I.

Definition lrel_channel : lrel Σ := LRel channel_rel.

Definition attacker_rel : lrel Σ := (lrel_channel → ())%lrel.

Lemma lrel_term_intro t t' : PUB⟨t, t'⟩ -∗ lrel_term t t'.
Proof. iIntros "#H". iExists t, t'. by eauto. Qed.

(** * Contracts of the primitives *)

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

Lemma rel_prim_derive_aenc_key :
  ⊢ (lrel_term → lrel_term)%lrel derive_aenc_key derive_aenc_key.
Proof.
iIntros "!> %v %v' Hv". rel_rec_l. rel_rec_r.
iApply (refines_app with "[] [Hv]"); [rel_values; iApply rel_prim_key|by rel_values].
Qed.

Lemma rel_prim_derive_sign_key :
  ⊢ (lrel_term → lrel_term)%lrel derive_sign_key derive_sign_key.
Proof.
iIntros "!> %v %v' Hv". rel_rec_l. rel_rec_r.
iApply (refines_app with "[] [Hv]"); [rel_values; iApply rel_prim_key|by rel_values].
Qed.

Lemma rel_prim_derive_senc_key :
  ⊢ (lrel_term → lrel_term)%lrel derive_senc_key derive_senc_key.
Proof.
iIntros "!> %v %v' Hv". rel_rec_l. rel_rec_r.
iApply (refines_app with "[] [Hv]"); [rel_values; iApply rel_prim_key|by rel_values].
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
        with "Hctx Htt_flow") as "prot_n".
iMod (public_rel_flow_r_extend (E:=⊤) n' ltac:(solve_ndisj)
        with "Hctx Htts_flow") as "prot_n'".
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

Lemma rel_prim_send :
  ⊢ (lrel_channel → lrel_term → ())%lrel send send.
Proof.
iIntros "!> %c %c' Hc".
iDestruct "Hc" as (sf rf sf' rf') "(-> & -> & #Hs & _)".
rewrite /send. rel_pures_l. rel_pures_r. rel_values. iModIntro.
iIntros "!> %v %v' (%t & %t' & -> & -> & #Ht)".
by iApply ("Hs" with "Ht").
Qed.

Lemma rel_prim_recv :
  ⊢ (lrel_channel → lrel_term)%lrel recv recv.
Proof.
iIntros "!> %c %c' Hc".
iApply (rel_recv with "Hc"). iIntros "%t %t' #Ht". by iApply lrel_term_intro.
Qed.

Lemma rel_run_network_rel (adv adv' : expr) (f f' : val) (A : val → val → iProp Σ) :
  (REL adv << adv' : attacker_rel) -∗
  (∀ c c', channel_rel c c' -∗ REL f c << f' c' : A) -∗
  REL run_network_rel adv f << run_network_rel adv' f' : A.
Proof.
iIntros "Hadv Hf". rewrite /run_network_rel.
rel_bind_l adv. rel_bind_r adv'.
iApply (refines_bind with "Hadv"). iIntros (a a') "#Ha /=".
rel_pures_l. rel_pures_r. rewrite /init_network_rel. rel_pures_l. rel_pures_r.
rel_bind_l (mk_channel_rel #()). rel_bind_r (mk_channel_rel #()).
iApply refines_bind; first iApply rel_mk_channel_rel.
iIntros (c c') "#Hc /=". rel_pures_l. rel_pures_r.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply refines_bind.
{ iApply refines_fork.
  iApply (refines_app _ _ _ _ lrel_channel); by rel_values. }
iIntros (? ?) "_ /=". rel_pures_l. rel_pures_r.
by iApply "Hf".
Qed.

End Proofs.

Definition attacker_valid (adv : expr) : Prop :=
  ∀ Σ (Hreloc : relocG Σ) (Hpub : public_relGS Σ),
    ⊢ cryptis_rel_ctx -∗ REL adv << adv : attacker_rel.

(** * Syntactically typed attackers *)

(** Binary primitives are eta-expanded so that the specs of [simple_spec.v]
    and [comp_spec.v], which match saturated applications, apply. *)
Definition attacker_prims : gmap string val :=
  <["tint" := tint]> $
  <["to_int" := to_int]> $
  <["tuple" := (λ: "t1" "t2", tuple "t1" "t2")%V]> $
  <["untuple" := untuple]> $
  <["derive_aenc_key" := derive_aenc_key]> $
  <["derive_sign_key" := derive_sign_key]> $
  <["derive_senc_key" := derive_senc_key]> $
  <["pkey" := pkey]> $
  <["seal" := (λ: "k" "t", seal "k" "t")%V]> $
  <["open" := (λ: "k" "t", open "k" "t")%V]> $
  <["hash" := hash]> $
  <["mk_nonce" := mk_nonce]> $
  <["eq_term" := (λ: "t1" "t2", eq_term "t1" "t2")%V]> $
  <["send" := send]> $
  <["recv" := recv]> ∅.

Definition attacker_prims_ty : gmap string type :=
  <["tint" := (TNat → #0)%ty]> $
  <["to_int" := (#0 → () + TNat)%ty]> $
  <["tuple" := (#0 → #0 → #0)%ty]> $
  <["untuple" := (#0 → () + #0 * #0)%ty]> $
  <["derive_aenc_key" := (#0 → #0)%ty]> $
  <["derive_sign_key" := (#0 → #0)%ty]> $
  <["derive_senc_key" := (#0 → #0)%ty]> $
  <["pkey" := (#0 → #0)%ty]> $
  <["seal" := (#0 → #0 → #0)%ty]> $
  <["open" := (#0 → #0 → () + #0)%ty]> $
  <["hash" := (#0 → #0)%ty]> $
  <["mk_nonce" := (() → #0)%ty]> $
  <["eq_term" := (#0 → #0 → TBool)%ty]> $
  <["send" := (#1 → #0 → ())%ty]> $
  <["recv" := (#1 → #0)%ty]> ∅.

Definition attacker_ty : type := (#1 → ())%ty.

Section Typed.

Context `{!relocG Σ, !public_relGS Σ}.

Lemma attacker_prims_env :
  cryptis_rel_ctx -∗
  ⟦ (λ τ, interp τ [lrel_term; lrel_channel]) <$> attacker_prims_ty ⟧*
    ((λ v, (v, v)) <$> attacker_prims).
Proof.
iIntros "#Hctx".
rewrite /attacker_prims_ty /attacker_prims !fmap_insert !fmap_empty /env_ltyped2.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_tint.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_to_int.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_tuple.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_untuple.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_derive_aenc_key.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_derive_sign_key.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_derive_senc_key.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_pkey.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_seal.
iApply (big_sepM2_insert_2 with "[]"); first by iApply rel_prim_open.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_hash.
iApply (big_sepM2_insert_2 with "[]"); first by iApply rel_prim_mk_nonce.
iApply (big_sepM2_insert_2 with "[]"); first by iApply rel_prim_eq_term.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_send.
iApply (big_sepM2_insert_2 with "[]"); first iApply rel_prim_recv.
by rewrite big_sepM2_empty.
Qed.

Lemma rel_attacker_typed e :
  attacker_prims_ty ⊢ₜ e : attacker_ty →
  cryptis_rel_ctx -∗
  REL subst_map attacker_prims e << subst_map attacker_prims e : attacker_rel.
Proof.
move=> /(fundamental [lrel_term; lrel_channel]) He. iIntros "#Hctx".
iPoseProof (He with "[]") as "H"; first by iApply attacker_prims_env.
rewrite -!map_fmap_compose !map_fmap_id. iExact "H".
Qed.

End Typed.

Lemma attacker_valid_typed e :
  attacker_prims_ty ⊢ₜ e : attacker_ty →
  attacker_valid (subst_map attacker_prims e).
Proof. move=> He Σ ? ?. by iApply rel_attacker_typed. Qed.
