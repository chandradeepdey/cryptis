(** * The attacker

The attacker is a program [adv] that runs on a fresh network channel.  It is
valid ([attacker_valid]) when it is related to itself, as a function from
related channels to related computations.  The security theorems of
[adequacy.v] hold for every valid attacker.

- [Network] runs the attacker on a fresh channel ([run_network_refinement]).
  - [Contracts] gives each primitive a contract in the style of a type.  A
    proof that an attacker is valid uses them whenever the attacker calls a
    primitive.
- [Typed]: every well-typed attacker is valid ([attacker_valid_typed]).  Its
  types keep terms and the channel abstract, so the attacker cannot look
  inside them. *)

From reloc.typing Require Import fundamental.
From cryptis.core Require Import term.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.proofmode Require Import updates.
From cryptis.primitives Require Import pre_term simple with_cryptis.
From cryptis.hyper.primitives Require Import simple comp with_cryptis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition init_network : val := λ: "adv",
  let: "c" := mk_channel #() in
  Fork ("adv" "c");;
  "c".

Definition run_network : val := λ: "adv" "f",
  "f" (init_network "adv").

Section Network.

Context `{!relocG Σ, !publicGS Σ}.

Implicit Types t : term.
Implicit Types v : val.

Definition lrel_attacker : lrel Σ := (lrel_channel → ())%lrel.

Section Contracts.

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
  first exact: is_nonce_not_TSeal.
iDestruct (term_token_public_token_r with "Htts") as "(Htts & _ & _)";
  first exact: is_nonce_not_TSeal.
iMod (public_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] Htt Htts") as "[_ #Hpub]".
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

Lemma send_refinement :
  ⊢ (lrel_channel → lrel_term → ())%lrel send send.
Proof.
iIntros "!> %c %c' Hc".
iDestruct "Hc" as (sf sf' rf rf') "(-> & -> & #Hs & _)".
rewrite /send. rel_pures_l. rel_pures_r. rel_values.
Qed.

Lemma recv_refinement :
  ⊢ (lrel_channel → lrel_term)%lrel recv recv.
Proof.
iIntros "!> %c %c' Hc".
iApply (refines_recv with "Hc"). iIntros "%t %t' #Ht". by iApply lrel_term_intro.
Qed.

End Contracts.

Lemma init_network_refinement :
  ⊢ REL init_network << init_network : lrel_attacker → lrel_channel.
Proof.
rel_arrow_val. iIntros (a a') "#Ha".
rewrite /init_network. rel_pures_l. rel_pures_r.
rel_bind_l (mk_channel #()). rel_bind_r (mk_channel #()).
iApply refines_bind; first iApply mk_channel_refinement.
iIntros (c c') "#Hc /=". rel_pures_l. rel_pures_r.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply refines_bind.
{ iApply refines_fork.
  iApply (refines_app _ _ _ _ lrel_channel); by rel_values. }
iIntros (? ?) "_ /=". rel_pures_l. rel_pures_r.
by rel_values.
Qed.

Lemma refines_run_network (adv adv' : expr) (f f' : val) (A : val → val → iProp Σ) :
  (REL adv << adv' : lrel_attacker) -∗
  (∀ c c', lrel_channel c c' -∗ REL f c << f' c' : A) -∗
  REL run_network adv f << run_network adv' f' : A.
Proof.
iIntros "Hadv Hf". rewrite /run_network.
rel_bind_l adv. rel_bind_r adv'.
iApply (refines_bind with "Hadv"). iIntros (a a') "#Ha /=".
rel_pures_l. rel_pures_r.
rel_bind_l (init_network _). rel_bind_r (init_network _).
iApply refines_bind.
{ iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
  iApply init_network_refinement. }
iIntros (c c') "#Hc /=". by iApply "Hf".
Qed.

Lemma run_network_refinement (A : lrel Σ) :
  ⊢ REL run_network << run_network : lrel_attacker → (lrel_channel → A) → A.
Proof.
rel_arrow_val. iIntros (a a') "#Ha".
rewrite /run_network. rel_pures_l. rel_pures_r.
rel_arrow_val. iIntros (f f') "#Hf".
rel_pures_l. rel_pures_r.
iApply (refines_app _ _ _ _ lrel_channel); first by rel_values.
iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
iApply init_network_refinement.
Qed.

End Network.

Definition attacker_valid (adv : expr) : Prop :=
  ∀ Σ (Hreloc : relocG Σ) (Hpub : publicGS Σ),
    ⊢ hypercryptis_ctx -∗ REL adv << adv : lrel_attacker.

Section Typed.

Context `{!relocG Σ, !publicGS Σ}.

(** Binary primitives are eta-expanded so that the specs of [simple.v]
    and [comp.v], which match saturated applications, apply. *)
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

Lemma attacker_prims_env :
  hypercryptis_ctx -∗
  ⟦ (λ τ, interp τ [lrel_term; lrel_channel]) <$> attacker_prims_ty ⟧*
    ((λ v, (v, v)) <$> attacker_prims).
Proof.
iIntros "#Hctx".
rewrite /attacker_prims_ty /attacker_prims !fmap_insert !fmap_empty /env_ltyped2.
iApply (big_sepM2_insert_2 with "[]"); first iApply tint_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply to_int_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply tuple_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply untuple_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply derive_aenc_key_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply derive_sign_key_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply derive_senc_key_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply pkey_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply seal_refinement.
iApply (big_sepM2_insert_2 with "[]"); first by iApply open_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply hash_refinement.
iApply (big_sepM2_insert_2 with "[]"); first by iApply mk_nonce_refinement.
iApply (big_sepM2_insert_2 with "[]"); first by iApply eq_term_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply send_refinement.
iApply (big_sepM2_insert_2 with "[]"); first iApply recv_refinement.
by rewrite big_sepM2_empty.
Qed.

Lemma refines_attacker_typed e :
  attacker_prims_ty ⊢ₜ e : attacker_ty →
  hypercryptis_ctx -∗
  REL subst_map attacker_prims e << subst_map attacker_prims e : lrel_attacker.
Proof.
move=> /(fundamental [lrel_term; lrel_channel]) He. iIntros "#Hctx".
iPoseProof (He with "[]") as "H"; first by iApply attacker_prims_env.
rewrite -!map_fmap_compose !map_fmap_id. iExact "H".
Qed.

End Typed.

Lemma attacker_valid_typed e :
  attacker_prims_ty ⊢ₜ e : attacker_ty →
  attacker_valid (subst_map attacker_prims e).
Proof. move=> He Σ ? ?. by iApply refines_attacker_typed. Qed.
