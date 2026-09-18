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
Implicit Types Ψ : val → val → iProp Σ.

(** Discharge the [pure_expr] side condition of [pure_twp_rel_{l,r}]. *)
Ltac solve_pure_expr :=
  rewrite /= ?andb_True; repeat split; apply: term_pure.

Lemma rel_tint_l E K e x Ψ :
  (REL fill K (TInt x : expr) << e @ E : Ψ) -∗
  REL fill K (tint #x) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=.
move=> ?; iIntros "_"; iApply twp_tint => //.
Qed.

Lemma rel_tint_r E K e x Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TInt x : expr) @ E : Ψ) -∗
  REL e << fill K (tint #x) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=.
move=> ?; iIntros "_"; iApply twp_tint => //.
Qed.

Lemma rel_to_int_l E K e t Ψ :
  (REL fill K (repr (Spec.to_int t) : expr) << e @ E : Ψ) -∗
  REL fill K (to_int t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_to_int => //.
solve_pure_expr.
Qed.

Lemma rel_to_int_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.to_int t) : expr) @ E : Ψ) -∗
  REL e << fill K (to_int t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_to_int => //.
solve_pure_expr.
Qed.

Lemma rel_tuple_l E K e t1 t2 Ψ :
  (REL fill K (TPair t1 t2 : expr) << e @ E : Ψ) -∗
  REL fill K (tuple t1 t2) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_tuple => //.
solve_pure_expr.
Qed.

Lemma rel_tuple_r E K e t1 t2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TPair t1 t2 : expr) @ E : Ψ) -∗
  REL e << fill K (tuple t1 t2) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_tuple => //.
solve_pure_expr.
Qed.

Lemma rel_untuple_l E K e t Ψ :
  (REL fill K (repr (Spec.untuple t) : expr) << e @ E : Ψ) -∗
  REL fill K (untuple t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_untuple => //.
solve_pure_expr.
Qed.

Lemma rel_untuple_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.untuple t) : expr) @ E : Ψ) -∗
  REL e << fill K (untuple t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_untuple => //.
solve_pure_expr.
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

Lemma rel_list_of_term_l E K e t Ψ :
  (REL fill K (repr (Spec.to_list t) : expr) << e @ E : Ψ) -∗
  REL fill K (list_of_term t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_list_of_term => //.
solve_pure_expr.
Qed.

Lemma rel_list_of_term_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.to_list t) : expr) @ E : Ψ) -∗
  REL e << fill K (list_of_term t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_list_of_term => //.
solve_pure_expr.
Qed.

Lemma rel_list_l `{!Repr A} E K e (xs : list A) Ψ :
  (REL fill K (repr xs : expr) << e @ E : Ψ) -∗
  REL fill K (list_to_expr xs) << e @ E : Ψ.
Proof.
elim: xs K => [|x xs IH] /= K; iIntros "post".
  by rel_apply_l rel_nil_l.
rel_bind_l (list_to_expr _); iApply IH.
by rel_apply_l rel_cons_l.
Qed.

Lemma rel_list_r `{!Repr A} E K e (xs : list A) Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr xs : expr) @ E : Ψ) -∗
  REL e << fill K (list_to_expr xs) @ E : Ψ.
Proof.
move=> ?.
elim: xs K => [|x xs IH] /= K; iIntros "H".
  by rel_apply_r rel_nil_r.
rel_bind_r (list_to_expr _); iApply IH.
by rel_apply_r rel_cons_r.
Qed.

Lemma rel_tag_l E K e (N : term) t Ψ :
  (REL fill K (repr (Spec.tag N t) : expr) << e @ E : Ψ) -∗
  REL fill K (tag N t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_tag => //.
solve_pure_expr.
Qed.

Lemma rel_tag_r E K e (N : term) t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.tag N t) : expr) @ E : Ψ) -∗
  REL e << fill K (tag N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_tag => //.
solve_pure_expr.
Qed.

Lemma rel_untag_l E K e (N : term) t Ψ :
  (REL fill K (repr (Spec.untag N t) : expr) << e @ E : Ψ) -∗
  REL fill K (untag N t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_untag => //.
solve_pure_expr.
Qed.

Lemma rel_untag_r E K e (N : term) t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.untag N t) : expr) @ E : Ψ) -∗
  REL e << fill K (untag N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_untag => //.
solve_pure_expr.
Qed.

Lemma rel_key_l E K e kt (k : term) Ψ :
  (REL fill K (TKey kt k : expr) << e @ E : Ψ) -∗
  REL fill K (key kt k) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_key => //.
apply term_pure.
Qed.

Lemma rel_key_r E K e kt (k : term) Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TKey kt k : expr) @ E : Ψ) -∗
  REL e << fill K (key kt k) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_key => //.
apply term_pure.
Qed.

Lemma rel_seal_l E K e t1 t2 Ψ :
  (REL fill K (TSeal t1 t2 : expr) << e @ E : Ψ) -∗
  REL fill K (seal t1 t2) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_seal => //.
solve_pure_expr.
Qed.

Lemma rel_seal_r E K e t1 t2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TSeal t1 t2 : expr) @ E : Ψ) -∗
  REL e << fill K (seal t1 t2) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_seal => //.
solve_pure_expr.
Qed.

Lemma rel_hash_l E K e t Ψ :
  (REL fill K (THash t : expr) << e @ E : Ψ) -∗
  REL fill K (hash t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_hash => //.
solve_pure_expr.
Qed.

Lemma rel_hash_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (THash t : expr) @ E : Ψ) -∗
  REL e << fill K (hash t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_hash => //.
solve_pure_expr.
Qed.

Lemma rel_derive_aenc_key_l K e t Ψ :
  ▷ (REL fill K (AEncKey t : expr) << e : Ψ) -∗
  REL fill K (derive_aenc_key t) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_derive_aenc_key. Qed.

Lemma rel_derive_aenc_key_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (AEncKey t : expr) @ E : Ψ) -∗
  REL e << fill K (derive_aenc_key t) @ E : Ψ.
Proof.
iIntros (?) "post". rel_rec_r. rel_apply_r rel_key_r.
have <- : AEncKey t = TKey ADec t :> term by rewrite [term_of_aenc_key]unlock.
by iApply "post".
Qed.

Lemma rel_derive_senc_key_l K e t Ψ :
  ▷ (REL fill K (SEncKey t : expr) << e : Ψ) -∗
  REL fill K (derive_senc_key t) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_derive_senc_key. Qed.

Lemma rel_derive_senc_key_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (SEncKey t : expr) @ E : Ψ) -∗
  REL e << fill K (derive_senc_key t) @ E : Ψ.
Proof.
iIntros (?) "post". rel_rec_r. rel_apply_r rel_key_r.
have <- : SEncKey t = TKey SEnc t :> term by rewrite [term_of_senc_key]unlock.
by iApply "post".
Qed.

Lemma rel_derive_sign_key_l K e t Ψ :
  ▷ (REL fill K (SignKey t : expr) << e : Ψ) -∗
  REL fill K (derive_sign_key t) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_derive_sign_key. Qed.

Lemma rel_derive_sign_key_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (SignKey t : expr) : Ψ) -∗
  REL e << fill K (derive_sign_key t) : Ψ.
Proof.
iIntros (?) "post". rel_rec_r. rel_apply_r rel_key_r.
have <- : SignKey t = TKey Sign t :> term by rewrite [term_of_sign_key]unlock.
by iApply "post".
Qed.

Lemma rel_to_key_l E K e t Ψ :
  (REL fill K (repr (Spec.to_key t) : expr) << e @ E : Ψ) -∗
  REL fill K (to_key t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_to_key => //.
apply term_pure.
Qed.

Lemma rel_to_key_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.to_key t) : expr) @ E : Ψ) -∗
  REL e << fill K (to_key t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_to_key => //.
apply term_pure.
Qed.

Lemma rel_open_key_l E K e t Ψ :
  (REL fill K (repr (Spec.open_key t) : expr) << e @ E : Ψ) -∗
  REL fill K (open_key t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_open_key => //.
solve_pure_expr.
Qed.

Lemma rel_open_key_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.open_key t) : expr) @ E : Ψ) -∗
  REL e << fill K (open_key t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_open_key => //.
solve_pure_expr.
Qed.

Lemma rel_open_l E K e t1 t2 Ψ :
  (REL fill K (repr (Spec.open t1 t2) : expr) << e @ E : Ψ) -∗
  REL fill K (open t1 t2) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_open => //.
solve_pure_expr.
Qed.

Lemma rel_open_r E K e t1 t2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.open t1 t2) : expr) @ E : Ψ) -∗
  REL e << fill K (open t1 t2) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_open => //.
solve_pure_expr.
Qed.

Lemma rel_enc_l E K e k N t Ψ :
  (REL fill K (Spec.enc k N t : expr) << e @ E : Ψ) -∗
  REL fill K (enc k N t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l=> //=;
last by move=> ?; iIntros "_"; iApply twp_enc => //.
solve_pure_expr.
Qed.

Lemma rel_enc_r E K e k N t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (Spec.enc k N t : expr) @ E : Ψ) -∗
  REL e << fill K (enc k N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r=> //=;
last by move=> ?; iIntros "_"; iApply twp_enc => //.
solve_pure_expr.
Qed.

Lemma rel_dec_l E K e (k N : term) t Ψ :
  (REL fill K (repr (Spec.dec k N t) : expr) << e @ E : Ψ) -∗
  REL fill K (dec k N t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_dec => //.
solve_pure_expr.
Qed.

Lemma rel_dec_r E K e (k N : term) t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.dec k N t) : expr) @ E : Ψ) -∗
  REL e << fill K (dec k N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_dec => //.
solve_pure_expr.
Qed.

Lemma rel_aenc'_l K e pk N t Ψ :
  ▷ (REL fill K (Spec.enc pk N t : expr) << e : Ψ) -∗
  REL fill K (aenc pk N t) << e : Ψ.
Proof. iIntros "?". iApply refines_wp_l; by wp_apply wp_aenc'. Qed.

Lemma rel_aenc'_r E K e pk N t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (Spec.enc pk N t : expr) @ E : Ψ) -∗
  REL e << fill K (aenc pk N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_aenc' => //.
solve_pure_expr.
Qed.

Lemma adec_tseal (sk : aenc_key) N t :
  ∀ t', Spec.dec sk N t = Some t' →
  t = TSeal (Spec.pkey sk) (Spec.tag N t').
Proof.
case: Spec.decP => [k_t t' H -> _ [<-]|t'] => //.
by move: H => /Spec.open_key_aencK => ->.
Qed.

Lemma rel_adec'_l K e (sk : aenc_key) N t Ψ :
  ▷ ((∀ t', ⌜t = TSeal (Spec.pkey sk) (Spec.tag N t')⌝ -∗
            ⌜Spec.dec sk N t = Some t'⌝ -∗
            REL fill K (SOMEV t' : expr) << e : Ψ) ∧
     (⌜Spec.dec sk N t = None⌝ → REL fill K (NONEV : expr) << e : Ψ)) -∗
  REL fill K (adec sk N t) << e : Ψ.
Proof. iIntros "?". iApply refines_wp_l; by wp_apply wp_adec'. Qed.

Lemma rel_adec'_r E K e (sk : aenc_key) N t Ψ :
  ↑specN ⊆ E →
  (∀ t', ⌜t = TSeal (Spec.pkey sk) (Spec.tag N t')⌝ -∗
         ⌜Spec.dec sk N t = Some t'⌝ -∗
         REL e << fill K (SOMEV t' : expr) @ E : Ψ) ∧
  (⌜Spec.dec sk N t = None⌝ → REL e << fill K (NONEV : expr) @ E : Ψ) -∗
  REL e << fill K (adec sk N t) @ E : Ψ.
Proof.
move=> ?; iIntros "post".
iApply (pure_twp_rel_r _ _ _ _ _ _ (repr (Spec.dec sk N t)) with "[post]") => //=.
- solve_pure_expr.
- move=> ?; iIntros "_". wp_lam; wp_pures. by wp_apply twp_dec.
- case: Spec.decP => [k_t t' /Spec.open_key_aencK -> ->|].
  + iDestruct "post" as "[post _]". by iApply "post".
  + iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma rel_senc'_l K e (k N : term) t Ψ :
  ▷ (REL fill K (Spec.enc k N t : expr) << e : Ψ) -∗
  REL fill K (senc k N t) << e : Ψ.
Proof. iIntros "?". iApply refines_wp_l; by wp_apply wp_senc'. Qed.

Lemma rel_senc'_r E K e (k N : term) t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (Spec.enc k N t : expr) @ E : Ψ) -∗
  REL e << fill K (senc k N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_senc' => //.
solve_pure_expr.
Qed.

Lemma sdec_tseal (k : senc_key) N t :
  ∀ t', Spec.dec k N t = Some t' →
  t = TSeal k (Spec.tag N t').
Proof.
case: Spec.decP => [k_t t' H -> _ [<-]|t'] => //.
by move: H => /Spec.open_key_sencK => ->.
Qed.

Lemma rel_sdec'_l K e (k : senc_key) N t Ψ :
  ▷ ((∀ t', ⌜t = TSeal k (Spec.tag N t')⌝ -∗
            ⌜Spec.dec k N t = Some t'⌝ -∗
            REL fill K (SOMEV t' : expr) << e : Ψ) ∧
     (⌜Spec.dec k N t = None⌝ → REL fill K (NONEV : expr) << e : Ψ)) -∗
  REL fill K (sdec k N t) << e : Ψ.
Proof. iIntros "?". iApply refines_wp_l; by wp_apply wp_sdec'. Qed.

Lemma rel_sdec'_r E K e (k : senc_key) N t Ψ :
  ↑specN ⊆ E →
  (∀ t', ⌜t = TSeal k (Spec.tag N t')⌝ -∗
         ⌜Spec.dec k N t = Some t'⌝ -∗
         REL e << fill K (SOMEV t' : expr) @ E : Ψ) ∧
  (⌜Spec.dec k N t = None⌝ → REL e << fill K (NONEV : expr) @ E : Ψ) -∗
  REL e << fill K (sdec k N t) @ E : Ψ.
Proof.
move=> ?; iIntros "post".
iApply (pure_twp_rel_r _ _ _ _ _ _ (repr (Spec.dec k N t)) with "[post]") => //=.
- solve_pure_expr.
- move=> ?; iIntros "_". wp_lam; wp_pures. by wp_apply twp_dec.
- case: Spec.decP => [k_t t' /Spec.open_key_sencK -> ->|].
  + iDestruct "post" as "[post _]". by iApply "post".
  + iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma rel_sign'_l K e (k N : term) t Ψ :
  ▷ (REL fill K (Spec.enc k N t : expr) << e : Ψ) -∗
  REL fill K (sign k N t) << e : Ψ.
Proof. iIntros "?". iApply refines_wp_l; by wp_apply wp_sign'. Qed.

Lemma rel_sign'_r E K e (k N : term) t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (Spec.enc k N t : expr) @ E : Ψ) -∗
  REL e << fill K (sign k N t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_sign' => //.
solve_pure_expr.
Qed.

Lemma verify_tseal (sk : sign_key) N t :
  ∀ t', Spec.dec (Spec.pkey sk) N t = Some t' →
  t = TSeal sk (Spec.tag N t').
Proof.
case: Spec.decP => [k_t t' H -> _ [<-]|t'] => //.
by move: H => /Spec.open_key_signK => ->.
Qed.

Lemma rel_verify'_l K e (sk : sign_key) N t Ψ :
  ▷ ((∀ t', ⌜t = TSeal sk (Spec.tag N t')⌝ -∗
            ⌜Spec.dec (Spec.pkey sk) N t = Some t'⌝ -∗
            REL fill K (SOMEV t' : expr) << e : Ψ) ∧
     (⌜Spec.dec (Spec.pkey sk) N t = None⌝ →
      REL fill K (NONEV : expr) << e : Ψ)) -∗
  REL fill K (verify (Spec.pkey sk) N t) << e : Ψ.
Proof. iIntros "?". iApply refines_wp_l; by wp_apply wp_verify'. Qed.

Lemma rel_verify'_r E K e (sk : sign_key) N t Ψ :
  ↑specN ⊆ E →
  (∀ t', ⌜t = TSeal sk (Spec.tag N t')⌝ -∗
         ⌜Spec.dec (Spec.pkey sk) N t = Some t'⌝ -∗
         REL e << fill K (SOMEV t' : expr) @ E : Ψ) ∧
  (⌜Spec.dec (Spec.pkey sk) N t = None⌝ →
   REL e << fill K (NONEV : expr) @ E : Ψ) -∗
  REL e << fill K (verify (Spec.pkey sk) N t) @ E : Ψ.
Proof.
move=> ?; iIntros "post".
iApply (pure_twp_rel_r _ _ _ _ _ _ (repr (Spec.dec (Spec.pkey sk) N t))
          with "[post]") => //=.
- solve_pure_expr.
- move=> ?; iIntros "_". wp_lam; wp_pures. by wp_apply twp_dec.
- case: Spec.decP => [k_t t' /Spec.open_key_signK -> ->|].
  + iDestruct "post" as "[post _]". by iApply "post".
  + iDestruct "post" as "[_ post]". by iApply "post".
Qed.

Lemma rel_pkey_l E K e k Ψ :
  (REL fill K (Spec.pkey k : expr) << e @ E : Ψ) -∗
  REL fill K (pkey k) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_pkey => //.
apply term_pure.
Qed.

Lemma rel_pkey_r E K e k Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (Spec.pkey k : expr) @ E : Ψ) -∗
  REL e << fill K (pkey k) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_pkey => //.
apply term_pure.
Qed.

Lemma rel_is_key_l E K e t Ψ :
  (REL fill K (repr (Spec.is_key t) : expr) << e @ E : Ψ) -∗
  REL fill K (is_key t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_is_key => //.
solve_pure_expr.
Qed.

Lemma rel_is_key_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.is_key t) : expr) @ E : Ψ) -∗
  REL e << fill K (is_key t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_is_key => //.
solve_pure_expr.
Qed.

Lemma rel_has_key_type_l E K e kt t Ψ :
  (REL fill K (#(Spec.has_key_type kt t) : expr) << e @ E : Ψ) -∗
  REL fill K (has_key_type (repr kt) t) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_has_key_type => //.
solve_pure_expr.
Qed.

Lemma rel_has_key_type_r E K e kt t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (#(Spec.has_key_type kt t) : expr) @ E : Ψ) -∗
  REL e << fill K (has_key_type (repr kt) t) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_has_key_type => //.
solve_pure_expr.
Qed.

End Proofs.
