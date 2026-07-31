From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.core Require Import term.
From cryptis.primitives Require Import simple.
From cryptis Require Import lib_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types t : term.
Implicit Types x : Z.

Lemma tp_tint E j x :
  ↑specN ⊆ E →
  refines_right j (tint #x) ={E}=∗
  refines_right j (TInt x).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
move=> ?; iIntros "_"; iApply twp_tint => //.
Qed.

Lemma tp_to_int E j t :
  ↑specN ⊆ E →
  refines_right j (to_int t) ={E}=∗
  refines_right j (repr (Spec.to_int t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_to_int => //.
apply term_pure.
Qed.

Lemma tp_tuple E j t1 t2 :
  ↑specN ⊆ E →
  refines_right j (tuple t1 t2) ={E}=∗
  refines_right j (TPair t1 t2).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_tuple => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_untuple E j t :
  ↑specN ⊆ E →
  refines_right j (untuple t) ={E}=∗
  refines_right j (repr (Spec.untuple t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_untuple => //.
apply term_pure.
Qed.

Lemma rel_term_of_list_l E K e ts Ψ :
  (REL fill K (repr (Spec.of_list ts) : expr) << e @ E : Ψ) -∗
  REL fill K (term_of_list (repr ts)) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_term_of_list => //.
rewrite !andb_True; repeat split; first by apply term_pure.
elim: ts => [| t ts' IHts']; rewrite repr_list_unseal => //=.
rewrite andb_True; split; first by apply term_pure.
by rewrite -repr_list_unseal.
Qed.

Lemma rel_term_of_list_r E K e ts Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.of_list ts) : expr) @ E : Ψ) -∗
  REL e << fill K (term_of_list (repr ts)) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_term_of_list => //.
rewrite !andb_True; repeat split; first by apply term_pure.
elim: ts => [| t ts' IHts']; rewrite repr_list_unseal => //=.
rewrite andb_True; split; first by apply term_pure.
by rewrite -repr_list_unseal.
Qed.

Lemma tp_list_of_term E j t :
  ↑specN ⊆ E →
  refines_right j (list_of_term t) ={E}=∗
  refines_right j (repr (Spec.to_list t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_list_of_term => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma rel_list_l `{!Repr A} K e (xs : list A) Ψ :
  (REL fill K (repr xs : expr) << e : Ψ) -∗
  REL fill K (list_to_expr xs) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_list. Qed.

Lemma rel_list_r `{!Repr A} K e (xs : list A) Ψ :
  (REL e << fill K (repr xs : expr) : Ψ) -∗
  REL e << fill K (list_to_expr xs) : Ψ.
Proof.
elim: xs K => [|x xs IH] /= K; iIntros "H".
  by rel_apply_r rel_nil_r.
rel_bind_r (list_to_expr _); iApply IH.
by rel_apply_r rel_cons_r.
Qed.

Lemma tp_tag E j (N : term) t :
  ↑specN ⊆ E →
  refines_right j (tag N t) ={E}=∗
  refines_right j (repr (Spec.tag N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_tag => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_untag E j (N : term) t :
  ↑specN ⊆ E →
  refines_right j (untag N t) ={E}=∗
  refines_right j (repr (Spec.untag N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_untag => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma rel_key_l K e kt (k : term) Ψ :
  (REL fill K (TKey kt k : expr) << e : Ψ) -∗
  REL fill K (key kt k) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_key. Qed.

Lemma rel_key_r K e kt (k : term) Ψ :
  (REL e << fill K (TKey kt k : expr) : Ψ) -∗
  REL e << fill K (key kt k) : Ψ.
Proof.
rewrite val_of_term_unseal /=.
by iIntros "post"; rel_rec_r; rel_pures_r.
Qed.

Lemma tp_seal E j t1 t2 :
  ↑specN ⊆ E →
  refines_right j (seal t1 t2) ={E}=∗
  refines_right j (TSeal t1 t2).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_seal => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma tp_hash E j t :
  ↑specN ⊆ E →
  refines_right j (hash t) ={E}=∗
  refines_right j (THash t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_hash => //.
apply term_pure.
Qed.

Lemma rel_derive_aenc_key_l K e t Ψ :
  ▷ (REL fill K (AEncKey t : expr) << e : Ψ) -∗
  REL fill K (derive_aenc_key t) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_derive_aenc_key. Qed.

Lemma rel_derive_aenc_key_r K e t Ψ :
  (REL e << fill K (AEncKey t : expr) : Ψ) -∗
  REL e << fill K (derive_aenc_key t) : Ψ.
Proof.
iIntros "post". rel_rec_r. rel_apply_r rel_key_r.
have <- : AEncKey t = TKey ADec t :> term by rewrite [term_of_aenc_key]unlock.
by iApply "post".
Qed.

Lemma rel_derive_senc_key_l K e t Ψ :
  ▷ (REL fill K (SEncKey t : expr) << e : Ψ) -∗
  REL fill K (derive_senc_key t) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_derive_senc_key. Qed.

Lemma rel_derive_senc_key_r K e t Ψ :
  (REL e << fill K (SEncKey t : expr) : Ψ) -∗
  REL e << fill K (derive_senc_key t) : Ψ.
Proof.
iIntros "post". rel_rec_r. rel_apply_r rel_key_r.
have <- : SEncKey t = TKey SEnc t :> term by rewrite [term_of_senc_key]unlock.
by iApply "post".
Qed.

Lemma rel_derive_sign_key_l K e t Ψ :
  ▷ (REL fill K (SignKey t : expr) << e : Ψ) -∗
  REL fill K (derive_sign_key t) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_derive_sign_key. Qed.

Lemma rel_derive_sign_key_r K e t Ψ :
  (REL e << fill K (SignKey t : expr) : Ψ) -∗
  REL e << fill K (derive_sign_key t) : Ψ.
Proof.
iIntros "post". rel_rec_r. rel_apply_r rel_key_r.
have <- : SignKey t = TKey Sign t :> term by rewrite [term_of_sign_key]unlock.
by iApply "post".
Qed.

Lemma rel_to_key_l K e t Ψ :
  (REL fill K (repr (Spec.to_key t) : expr) << e : Ψ) -∗
  REL fill K (to_key t) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; iApply twp_wp; wp_apply twp_to_key. Qed.

Lemma rel_to_key_r K e t Ψ :
  (REL e << fill K (repr (Spec.to_key t) : expr) : Ψ) -∗
  REL e << fill K (to_key t) : Ψ.
Proof.
iIntros "H".
rewrite /repr /repr_option /repr /repr_prod.
rewrite /repr /repr_term !val_of_term_unseal.
case: t => [n|t1 t2|a|kt k|k m|h|pt wf nf]; try by rel_rec_r; rel_pures_r.
by case: pt wf nf => [o|[kt2||] operand|[||] b e'|ts] wf nf //=; rel_rec_r; rel_pures_r.
Qed.

Lemma tp_open_key E j t :
  ↑specN ⊆ E →
  refines_right j (open_key t) ={E}=∗
  refines_right j (repr (Spec.open_key t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_open_key => //.
apply term_pure.
Qed.

Lemma tp_open E j t1 t2 :
  ↑specN ⊆ E →
  refines_right j (open t1 t2) ={E}=∗
  refines_right j (repr (Spec.open t1 t2)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_open => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma rel_enc_l E K e k N t Ψ :
  (REL fill K (Spec.enc k N t : expr) << e @ E : Ψ) -∗
  REL fill K (enc k N t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l=> //=;
last by move=> ?; iIntros "_"; iApply twp_enc => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma rel_enc_r E K e k N t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (Spec.enc k N t : expr) @ E : Ψ) -∗
  REL e << fill K (enc k N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r=> //=;
last by move=> ?; iIntros "_"; iApply twp_enc => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma tp_dec E j (k N : term) t :
  ↑specN ⊆ E →
  refines_right j (dec k N t) ={E}=∗
  refines_right j (repr (Spec.dec k N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_dec => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma tp_aenc' E j (pk N : term) t :
  ↑specN ⊆ E →
  refines_right j (aenc pk N t) ={E}=∗
  refines_right j (Spec.enc pk N t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_aenc' => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma adec_tseal (sk : aenc_key) N t :
  ∀ t', Spec.dec sk N t = Some t' →
  t = TSeal (Spec.pkey sk) (Spec.tag N t').
Proof.
case: Spec.decP => [k_t t' H -> _ [<-]|t'] => //.
by move: H => /Spec.open_key_aencK => ->.
Qed.

Lemma tp_adec' E j (sk : aenc_key) (N : term) t :
  ↑specN ⊆ E →
  refines_right j (adec sk N t) ={E}=∗
  refines_right j (repr (Spec.dec sk N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=.
rewrite !andb_True; repeat split; by apply term_pure.
move=> ?; iIntros "_".
wp_lam. wp_pures.
by wp_apply twp_dec.
Qed.

Lemma tp_senc' E j (k N : term) t :
  ↑specN ⊆ E →
  refines_right j (senc k N t) ={E}=∗
  refines_right j (Spec.enc k N t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_senc' => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma sdec_tseal (k : senc_key) N t :
  ∀ t', Spec.dec k N t = Some t' →
  t = TSeal k (Spec.tag N t').
Proof.
case: Spec.decP => [k_t t' H -> _ [<-]|t'] => //.
by move: H => /Spec.open_key_sencK => ->.
Qed.

Lemma tp_sdec' E j (k : senc_key) (N : term) t :
  ↑specN ⊆ E →
  refines_right j (sdec k N t) ={E}=∗
  refines_right j (repr (Spec.dec k N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=.
rewrite !andb_True; repeat split; by apply term_pure.
move=> ?; iIntros "_".
wp_lam. wp_pures.
by wp_apply twp_dec.
Qed.

Lemma tp_sign' E j (k N : term) t :
  ↑specN ⊆ E →
  refines_right j (sign k N t) ={E}=∗
  refines_right j (Spec.enc k N t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_sign' => //.
rewrite !andb_True; repeat split; by apply term_pure.
Qed.

Lemma verify_tseal (sk : sign_key) N t :
  ∀ t', Spec.dec (Spec.pkey sk) N t = Some t' →
  t = TSeal sk (Spec.tag N t').
Proof.
case: Spec.decP => [k_t t' H -> _ [<-]|t'] => //.
by move: H => /Spec.open_key_signK => ->.
Qed.

Lemma tp_verify' E j (sk : sign_key) (N : term) t :
  ↑specN ⊆ E →
  refines_right j (verify (Spec.pkey sk) N t) ={E}=∗
  refines_right j (repr (Spec.dec (Spec.pkey sk) N t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=.
rewrite !andb_True; repeat split; by apply term_pure.
move=> ?; iIntros "_".
wp_lam. wp_pures.
by wp_apply twp_dec.
Qed.

Lemma tp_pkey E j (k : term) :
  ↑specN ⊆ E →
  refines_right j (pkey k) ={E}=∗
  refines_right j (Spec.pkey k).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_pkey => //.
apply term_pure.
Qed.

Lemma rel_pkey_l K (k: term) (e: expr) Ψ :
  (REL fill K (Spec.pkey k : expr) << e : Ψ) -∗
  REL fill K (pkey k) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_pkey. Qed.

Lemma rel_pkey_r K (k: term) (e: expr) Ψ :
  (REL e << fill K (Spec.pkey k : expr) : Ψ) -∗
  REL e << fill K (pkey k) : Ψ.
Proof.
iIntros "H"; rewrite /Spec.pkey.
rel_rec_r; rel_apply_r rel_to_key_r.
case: k; try by move=> *; rel_pures_r.
move=> kt t; rel_pures_r.
by case: kt; rel_pures_r; try rel_apply_r rel_key_r.
Qed.

Lemma tp_is_key E j t :
  ↑specN ⊆ E →
  refines_right j (is_key t) ={E}=∗
  refines_right j (repr (Spec.is_key t)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_is_key => //.
apply term_pure.
Qed.

Lemma tp_has_key_type E j kt t :
  ↑specN ⊆ E →
  refines_right j (has_key_type (repr kt) t) ={E}=∗
  refines_right j #(Spec.has_key_type kt t).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_has_key_type => //.
apply term_pure.
Qed.

End Proofs.
