From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap reservation_map.
From iris.base_logic.lib Require Import invariants saved_prop.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool.
From cryptis Require Import term.
From cryptis.primitives Require Import notations pre_term comp.

From reloc Require Import reloc.
From cryptis.primitives Require Import simple.
From cryptis Require Import lib_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.

Lemma tp_tint E j (n : Z) :
  nclose specN ⊆ E →
  refines_right j (tint #n) ={E}=∗
  refines_right j (TInt n).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
move=> ?; iIntros "_"; iApply twp_tint => //.
Qed.

Lemma tp_to_int E j t :
  nclose specN ⊆ E →
  refines_right j (to_int t) ={E}=∗
  refines_right j (repr (Spec.to_int t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_to_int => //.
apply term_pure.
Qed.

Lemma tp_tuple E j t1 t2 :
  nclose specN ⊆ E →
  refines_right j (tuple t1 t2) ={E}=∗
  refines_right j (TPair t1 t2).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_tuple => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_untuple E j t :
  nclose specN ⊆ E →
  refines_right j (untuple t) ={E}=∗
  refines_right j (repr (Spec.untuple t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_untuple => //.
apply term_pure.
Qed.

Lemma tp_term_of_list E j ts :
  nclose specN ⊆ E →
  refines_right j (term_of_list (repr ts)) ={E}=∗
  refines_right j (repr (Spec.of_list ts)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_term_of_list => //.
rewrite !andb_True; repeat split; first by apply term_pure.
elim: ts => [| t ts' IHts']; rewrite repr_list_unseal => //=.
rewrite andb_True; split; first by apply term_pure.
by rewrite -repr_list_unseal.
Qed.

Lemma tp_list_of_term E j t :
  nclose specN ⊆ E →
  refines_right j (list_of_term t) ={E}=∗
  refines_right j (repr (Spec.to_list t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_list_of_term => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma tp_list `{!Repr A} E j (xs : list A) :
  nclose specN ⊆ E →
  refines_right j (list_to_expr xs) ={E}=∗
  refines_right j (repr xs).
Proof.
move=> HE.
elim: xs j => [|x xs IHxs] j /=; iIntros "Hj";
first by iPoseProof (tp_nil with "Hj") as ">Hj" => //=.
tp_bind j (list_to_expr _).
rewrite refines_right_bind.
set j' := RefId _ _.
iPoseProof (IHxs with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
clear j'.
iPoseProof (tp_cons with "Hj") as ">Hj" => //=.
Qed.

Lemma tp_tag E j (N : term) t :
  nclose specN ⊆ E →
  refines_right j (tag N t) ={E}=∗
  refines_right j (repr (Spec.tag N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_tag => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_untag E j (N : term) t :
  nclose specN ⊆ E →
  refines_right j (untag N t) ={E}=∗
  refines_right j (repr (Spec.untag N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_untag => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_key kt E j (k : term) :
  nclose specN ⊆ E →
  refines_right j (key kt k) ={E}=∗
  refines_right j (TKey kt k : val).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_key => //.
apply term_pure.
Qed.

Lemma tp_seal E j t1 t2 :
  nclose specN ⊆ E →
  refines_right j (seal t1 t2) ={E}=∗
  refines_right j (TSeal t1 t2).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_seal => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_hash E j t :
  nclose specN ⊆ E →
  refines_right j (hash t) ={E}=∗
  refines_right j (THash t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_hash => //.
apply term_pure.
Qed.

Lemma tp_derive_aenc_key E j t :
  nclose specN ⊆ E →
  refines_right j (derive_aenc_key t) ={E}=∗
  refines_right j (AEncKey t : term).
Proof.
move=> HE.
iIntros "Hj".
tp_lam j.
iPoseProof (tp_key with "Hj") as ">Hj" => //.
by have <- : AEncKey t = TKey ADec t :> term by rewrite [term_of_aenc_key]unlock.
Qed.

Lemma tp_derive_senc_key E j t :
  nclose specN ⊆ E →
  refines_right j (derive_senc_key t) ={E}=∗
  refines_right j (SEncKey t : term).
Proof.
move=> HE.
iIntros "Hj".
tp_lam j.
iPoseProof (tp_key with "Hj") as ">Hj" => //.
by have <- : SEncKey t = TKey SEnc t :> term by rewrite [term_of_senc_key]unlock.
Qed.

Lemma tp_derive_sign_key E j t :
  nclose specN ⊆ E →
  refines_right j (derive_sign_key t) ={E}=∗
  refines_right j (SignKey t : term).
Proof.
move=> HE.
iIntros "Hj".
tp_lam j.
iPoseProof (tp_key with "Hj") as ">Hj" => //.
by have <- : SignKey t = TKey Sign t :> term by rewrite [term_of_sign_key]unlock.
Qed.

Lemma tp_to_key E j t :
  nclose specN ⊆ E →
  refines_right j (to_key t) ={E}=∗
  refines_right j (repr (Spec.to_key t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_to_key => //.
apply term_pure.
Qed.

Lemma tp_open_key E j t :
  nclose specN ⊆ E →
  refines_right j (open_key t) ={E}=∗
  refines_right j (repr (Spec.open_key t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_open_key => //.
apply term_pure.
Qed.

Lemma tp_open E j t1 t2 :
  nclose specN ⊆ E →
  refines_right j (open t1 t2) ={E}=∗
  refines_right j (repr (Spec.open t1 t2)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_open => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_enc E j (k N : term) t :
  nclose specN ⊆ E →
  refines_right j (enc k N t) ={E}=∗
  refines_right j (Spec.enc k N t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_enc => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma tp_dec E j (k N : term) t :
  nclose specN ⊆ E →
  refines_right j (dec k N t) ={E}=∗
  refines_right j (repr (Spec.dec k N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_dec => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma tp_aenc' E j (pk N : term) t :
  nclose specN ⊆ E →
  refines_right j (aenc pk N t) ={E}=∗
  refines_right j (Spec.enc pk N t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_aenc' => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma twp_adec' (sk : aenc_key) N t Ψ :
  (∀ t', ⌜t = TSeal (Spec.pkey sk) (Spec.tag N t')⌝ -∗
         ⌜Spec.dec sk N t = Some t'⌝ -∗
         Ψ (SOMEV t')) ∧
  (⌜Spec.dec sk N t = None⌝ → Ψ NONEV) ⊢
  WP adec sk N t [{ Ψ }].
Proof.
iIntros "post". wp_lam; wp_pures. wp_apply twp_dec.
case: Spec.decP => [k_t t' /Spec.open_key_aencK -> ->|].
- iDestruct "post" as "[post _]". by iApply "post".
- iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma wp_adec' (sk : aenc_key) N t Ψ :
  ▷ ((∀ t', ⌜t = TSeal (Spec.pkey sk) (Spec.tag N t')⌝ -∗
            ⌜Spec.dec sk N t = Some t'⌝ -∗
         Ψ (SOMEV t')) ∧
     (⌜Spec.dec sk N t = None⌝ → Ψ NONEV)) ⊢
  WP adec sk N t {{ Ψ }}.
Proof.
iIntros "post". wp_lam; wp_pures. wp_apply wp_dec.
case: Spec.decP => [k_t t' /Spec.open_key_aencK -> ->|].
- iDestruct "post" as "[post _]". by iApply "post".
- iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma twp_senc' E k N t Ψ :
  Ψ (Spec.enc k N t) ⊢
  WP senc k N t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /senc /Spec.enc; wp_pures.
by wp_apply twp_enc.
Qed.

Lemma wp_senc' E k N t Ψ :
  ▷ Ψ (Spec.enc k N t) ⊢
  WP senc k N t @ E {{ Ψ }}.
Proof.
iIntros "post"; rewrite /senc /Spec.enc; wp_pures.
by wp_apply wp_enc.
Qed.

Lemma twp_sdec' E (k : senc_key) N t Ψ :
  ((∀ t', ⌜t = TSeal k (Spec.tag N t')⌝ -∗
          ⌜Spec.dec k N t = Some t'⌝ -∗
     Ψ (SOMEV t')) ∧
   (⌜Spec.dec k N t = None⌝ → Ψ NONEV)) ⊢
  WP sdec k N t @ E [{ Ψ }].
Proof.
iIntros "post". wp_lam; wp_pures. wp_apply twp_dec.
case: Spec.decP => [k_t t' /Spec.open_key_sencK -> ->|].
- iDestruct "post" as "[post _]". by iApply "post".
- iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma wp_sdec' E (k : senc_key) N t Ψ :
  ▷ ((∀ t', ⌜t = TSeal k (Spec.tag N t')⌝ -∗
            ⌜Spec.dec k N t = Some t'⌝ -∗
     Ψ (SOMEV t')) ∧
     (⌜Spec.dec k N t = None⌝ → Ψ NONEV)) ⊢
  WP sdec k N t @ E {{ Ψ }}.
Proof.
iIntros "post". wp_lam; wp_pures. wp_apply wp_dec.
case: Spec.decP => [k_t t' /Spec.open_key_sencK -> ->|].
- iDestruct "post" as "[post _]". by iApply "post".
- iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma twp_sign' k N t Ψ :
  Ψ (Spec.enc k N t) ⊢
  WP sign k N t [{ Ψ }].
Proof.
iIntros "?". wp_lam; wp_pures. by wp_apply twp_enc.
Qed.

Lemma wp_sign' k N t Ψ :
  ▷ Ψ (Spec.enc k N t) ⊢
  WP sign k N t {{ Ψ }}.
Proof.
iIntros "?". wp_lam; wp_pures. by wp_apply wp_enc.
Qed.

Lemma twp_verify' (sk : sign_key) N t Ψ :
  (∀ t', ⌜t = TSeal sk (Spec.tag N t')⌝ -∗
         ⌜Spec.dec (Spec.pkey sk) N t = Some t'⌝ -∗
         Ψ (SOMEV t')) ∧
  (⌜Spec.dec (Spec.pkey sk) N t = None⌝ → Ψ NONEV) ⊢
  WP verify (Spec.pkey sk) N t [{ Ψ }].
Proof.
iIntros "post". wp_lam; wp_pures. wp_apply twp_dec.
case: Spec.decP => [k_t t' /Spec.open_key_signK -> ->|].
- iDestruct "post" as "[post _]". by iApply "post".
- iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma wp_verify' (sk : sign_key) N t Ψ :
  ▷ ((∀ t', ⌜t = TSeal sk (Spec.tag N t')⌝ -∗
            ⌜Spec.dec (Spec.pkey sk) N t = Some t'⌝ -∗ Ψ (SOMEV t')) ∧
     (⌜Spec.dec (Spec.pkey sk) N t = None⌝ → Ψ NONEV)) ⊢
  WP verify (Spec.pkey sk) N t {{ Ψ }}.
Proof.
iIntros "post". wp_lam; wp_pures. wp_apply wp_dec.
case: Spec.decP => [k_t t' /Spec.open_key_signK -> ->|].
- iDestruct "post" as "[post _]". by iApply "post".
- iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma twp_pkey k Ψ : Ψ (Spec.pkey k) ⊢ WP pkey k [{ Ψ }].
Proof.
iIntros "H"; rewrite /Spec.pkey.
wp_lam; wp_apply twp_to_key.
case: k; try by move=> *; wp_pures.
move=> kt t; wp_pures.
by case: kt; wp_pures; try wp_apply twp_key.
Qed.

Lemma wp_pkey k Ψ : Ψ (Spec.pkey k) ⊢ WP pkey k {{ Ψ }}.
Proof. iIntros "?". iApply twp_wp. by iApply twp_pkey. Qed.

Lemma twp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) ⊢
  WP is_key t @ E [{ Ψ }].
Proof.
rewrite /Spec.is_key.
iIntros "?"; wp_lam.
wp_apply twp_to_key.
by case: t=> *; wp_pures.
Qed.

Lemma wp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) ⊢
  WP is_key t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_is_key. Qed.

Lemma twp_has_key_type kt t Ψ :
  Ψ #(Spec.has_key_type kt t) ⊢
  WP has_key_type (repr kt) t [{ Ψ }].
Proof.
iIntros "H". wp_lam; wp_pures.
wp_apply twp_is_key. rewrite /Spec.has_key_type.
case: Spec.is_key => [kt'|] //=; wp_pures => //.
by case: kt kt' => [] [] /=.
Qed.

Lemma wp_has_key_type kt t Ψ :
  Ψ #(Spec.has_key_type kt t) ⊢
  WP has_key_type (repr kt) t {{ Ψ }}.
Proof.
iIntros "H". iApply twp_wp. by iApply twp_has_key_type.
Qed.

End Proofs.
