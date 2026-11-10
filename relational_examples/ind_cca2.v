(** IND-CCA2 for randomized asymmetric encryption. *)

From iris.heap_lang.lib Require Import nondet_bool.
From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper Require Import rel_adequacy proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation ind_cca2N := (nroot.@"ind_cca2").
Abbreviation storeN := (ind_cca2N.@"store").
Abbreviation cellN := (ind_cca2N.@"cell").

Section CCA2.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t u : term).
Implicit Types (skA : aenc_key).

Variable N : namespace.

(**
[[
A --> *: pkA
* --> A: msg_0
* --> A: msg_1
A --> *: {nonce, msg_b}@pkA
* --> A: guess
]]

The oracle answers every query [t] with the payload of [t] under [skA],
except for the challenge ciphertext. *)

Definition oracle : val := rec: "loop" "c" "sk" "chal" :=
  let: "t" := recv "c" in
  (match: open "sk" "t" with
     SOME "u" =>
       if: (match: !"chal" with SOME "ct" => eq_term "ct" "t" | NONE => #false end)
       then send "c" (TInt 0) else send "c" "u"
   | NONE => send "c" (TInt 0)
   end);;
  "loop" "c" "sk" "chal".

Definition alice (b : bool) : val := λ: "c",
  let: "skA" := mk_aenc_key #() in
  let: "pkA" := pkey "skA" in
  let: "chal" := ref NONE in
  Fork (oracle "c" "skA" "chal");;
  send "c" "pkA";;
  let: "msg_0" := recv "c" in
  let: "msg_1" := recv "c" in
  let: "msg" := if: #b then "msg_0" else "msg_1" in
  let: "ct" := random_aenc "pkA" (Tag $ N.@"m") "msg" in
  "chal" <- SOME "ct";;
  send "c" "ct";;
  let: "guess" := recv "c" in
  eq_term (TInt 1) "guess".

Definition alice_guess_wrapped : val := λ: "c",
  let: "b" := nondet_bool #() in
  ("b", if: "b" then alice true "c" else alice false "c").

Local Abbreviation challenge_ns skA pl :=
  (seal_ns (Spec.pkey skA) (Spec.tag (Tag (N.@"m")) pl)).

Definition cell_inv skA skA' (l l' : loc) : iProp :=
  (l ↦ NONEV ∗ l' ↦ₛ NONEV ∗
   term_token (seed_of_aenc_key skA) (↑cryptisN.@"public_rel".@"seal") ∗
   term_token_spec (seed_of_aenc_key skA') (↑cryptisN.@"public_rel".@"seal")) ∨
  (∃ pl pl',
    l ↦ SOMEV (Spec.enc (Spec.pkey skA) (Tag (N.@"m")) pl) ∗
    l' ↦ₛ SOMEV (Spec.enc (Spec.pkey skA') (Tag (N.@"m")) pl') ∗
    term_token (seed_of_aenc_key skA)
      (↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA pl) ∗
    term_token_spec (seed_of_aenc_key skA')
      (↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA' pl') ∗
    publicly_linked (Spec.enc (Spec.pkey skA) (Tag (N.@"m")) pl)
      (Spec.enc (Spec.pkey skA') (Tag (N.@"m")) pl') ∗
    term_meta (seed_of_aenc_key skA) storeN () ∗
    PUB⟨Spec.enc (Spec.pkey skA) (Tag (N.@"m")) pl,
        Spec.enc (Spec.pkey skA') (Tag (N.@"m")) pl'⟩).

Lemma cell_unsealed_l E skA t t' u :
  ↑cryptisN ⊆ E →
  Spec.open skA t = Some u →
  cryptis_rel_ctx -∗
  term_token (seed_of_aenc_key skA) (↑cryptisN.@"public_rel".@"seal") -∗
  publicly_linked t t' ={E}=∗ False.
Proof.
move=> HE /Spec.open_aenc_key_Some ->. rewrite Spec.aenc_key_pkey.
iIntros "#ctx tok #[Hl _]".
iApply (linked_in_l_map_token_fupd _ _ HE with "ctx [Hl] [tok]").
- by iApply publicly_linked_in_l_linked_in_l.
- rewrite /map_token_l /=. iApply (term_token_drop with "tok"). rewrite /seal_ns. solve_ndisj.
Qed.

Lemma cell_unsealed_r E skA' t t' u' :
  ↑cryptisN ⊆ E →
  Spec.open skA' t' = Some u' →
  cryptis_rel_ctx -∗
  term_token_spec (seed_of_aenc_key skA') (↑cryptisN.@"public_rel".@"seal") -∗
  publicly_linked t t' ={E}=∗ False.
Proof.
move=> HE /Spec.open_aenc_key_Some ->. rewrite Spec.aenc_key_pkey.
iIntros "#ctx tok #[_ Hl]".
iApply (linked_in_r_map_token_fupd _ _ HE with "ctx [Hl] [tok]").
- by iApply publicly_linked_in_r_linked_in_r.
- rewrite /map_token_r /=. iApply (term_token_spec_drop with "tok"). rewrite /seal_ns. solve_ndisj.
Qed.

Lemma challenge_ns_disj skA pl u :
  u ≠ Spec.tag (Tag (N.@"m")) pl →
  (↑seal_ns (Spec.pkey skA) u.@"map" : coPset) ⊆
  ↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA pl.
Proof.
move=> ne. apply subseteq_difference_r; last by rewrite /seal_ns; solve_ndisj.
have Hd : (↑seal_ns (Spec.pkey skA) u : coPset) ## ↑challenge_ns skA pl.
{ rewrite /seal_ns. apply ndot_ne_disjoint. by case. }
have : ↑seal_ns (Spec.pkey skA) u.@"map" ⊆ (↑seal_ns (Spec.pkey skA) u : coPset)
  by solve_ndisj.
set_solver.
Qed.

Lemma cell_challenge_l E skA pl t t' u :
  ↑cryptisN ⊆ E →
  Spec.open skA t = Some u →
  cryptis_rel_ctx -∗
  term_token (seed_of_aenc_key skA)
    (↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA pl) -∗
  publicly_linked t t' ={E}=∗
  ⌜u = Spec.tag (Tag (N.@"m")) pl⌝ ∗
  term_token (seed_of_aenc_key skA)
    (↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA pl).
Proof.
move=> HE Ho. case: (decide (u = Spec.tag (Tag (N.@"m")) pl)) => [-> | ne].
{ by iIntros "_ $ _". }
have Hsub := challenge_ns_disj (skA:=skA) ne.
move/Spec.open_aenc_key_Some: Ho => ->. rewrite Spec.aenc_key_pkey in Hsub *.
iIntros "#ctx tok #[Hl _]".
iMod (linked_in_l_map_token_fupd _ _ HE with "ctx [Hl] [tok]") as "[]".
- by iApply publicly_linked_in_l_linked_in_l.
- rewrite /map_token_l /=. by iApply (term_token_drop with "tok").
Qed.

Lemma cell_challenge_r E skA' pl' t t' u' :
  ↑cryptisN ⊆ E →
  Spec.open skA' t' = Some u' →
  cryptis_rel_ctx -∗
  term_token_spec (seed_of_aenc_key skA')
    (↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA' pl') -∗
  publicly_linked t t' ={E}=∗
  ⌜u' = Spec.tag (Tag (N.@"m")) pl'⌝ ∗
  term_token_spec (seed_of_aenc_key skA')
    (↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA' pl').
Proof.
move=> HE Ho. case: (decide (u' = Spec.tag (Tag (N.@"m")) pl')) => [-> | ne].
{ by iIntros "_ $ _". }
have Hsub := challenge_ns_disj (skA:=skA') ne.
move/Spec.open_aenc_key_Some: Ho => ->. rewrite Spec.aenc_key_pkey in Hsub *.
iIntros "#ctx tok #[_ Hl]".
iMod (linked_in_r_map_token_fupd _ _ HE with "ctx [Hl] [tok]") as "[]".
- by iApply publicly_linked_in_r_linked_in_r.
- rewrite /map_token_r /=. by iApply (term_token_spec_drop with "tok").
Qed.

Lemma rel_oracle_open skA skA' (l l' : loc) t t' :
  cryptis_rel_ctx -∗
  inv cellN (cell_inv skA skA' l l') -∗
  PUB⟨Spec.pkey skA, Spec.pkey skA'⟩ -∗
  publicly_linked (Spec.pkey skA) (Spec.pkey skA') -∗
  PUB⟨t, t'⟩ ={⊤}=∗
  ⌜Spec.open skA t = None ∧ Spec.open skA' t' = None⌝ ∨
  ∃ u u', ⌜Spec.open skA t = Some u ∧ Spec.open skA' t' = Some u'⌝ ∗
    (PUB⟨u, u'⟩ ∨ publicly_linked t t').
Proof.
iIntros "#Hctx #Hcell #Hpk #Hlink #Ht".
iMod (publicly_related_open_aenc_fupd with "Hctx Hpk Hlink Ht") as "#Ho";
  first solve_ndisj.
case eL: (Spec.open skA t) => [u|];
case eR: (Spec.open skA' t') => [u'|]; iSimpl in "Ho".
- iModIntro. iRight. iExists u, u'. by iSplit; first by iPureIntro; split.
- iDestruct "Ho" as "[Hl _]".
  iInv "Hcell" as "[(_ & _ & >tok & _)|(%pl & %pl' & _ & _ & >tok & _ & >#Hct & _)]".
  + by iMod (cell_unsealed_l (E:=⊤ ∖ ↑cellN) _ ltac:(solve_ndisj) eL with "Hctx tok Hl") as "[]".
  + iMod (cell_challenge_l (E:=⊤ ∖ ↑cellN) _ _ ltac:(solve_ndisj) eL with "Hctx tok Hl") as "[%Hu _]".
    move/Spec.open_aenc_key_Some: (eL) => Ht. subst t u.
    iDestruct "Hl" as "[Hl _]". iDestruct "Hct" as "[Hct _]".
    iDestruct (publicly_linked_in_l_agree with "Hl Hct") as %->.
    by rewrite (proj2 (Spec.open_aenc_key_Some _ _ _) eq_refl) in eR.
- iDestruct "Ho" as "[Hl _]".
  iInv "Hcell" as "[(_ & _ & _ & >tok)|(%pl & %pl' & _ & _ & _ & >tok & >#Hct & _)]".
  + by iMod (cell_unsealed_r (E:=⊤ ∖ ↑cellN) _ ltac:(solve_ndisj) eR with "Hctx tok Hl") as "[]".
  + iMod (cell_challenge_r (E:=⊤ ∖ ↑cellN) _ _ ltac:(solve_ndisj) eR with "Hctx tok Hl") as "[%Hu _]".
    move/Spec.open_aenc_key_Some: (eR) => Ht'. subst t' u'.
    iDestruct "Hl" as "[_ Hl]". iDestruct "Hct" as "[_ Hct]".
    iDestruct (publicly_linked_in_r_agree with "Hl Hct") as %->.
    by rewrite (proj2 (Spec.open_aenc_key_Some _ _ _) eq_refl) in eL.
- iModIntro. iLeft. by iPureIntro; split.
Qed.

Lemma rel_send_fail c c' :
  lrel_channel c c' -∗
  REL send c (TInt 0) << send c' (TInt 0) : ().
Proof.
iIntros "#Hc". iApply (rel_send with "Hc"). iNext. by rewrite publicly_related_TInt.
Qed.

Lemma rel_oracle c c' skA skA' (l l' : loc) :
  cryptis_rel_ctx -∗
  inv cellN (cell_inv skA skA' l l') -∗
  lrel_channel c c' -∗
  PUB⟨Spec.pkey skA, Spec.pkey skA'⟩ -∗
  publicly_linked (Spec.pkey skA) (Spec.pkey skA') -∗
  REL oracle c skA #l << oracle c' skA' #l' : ().
Proof.
iIntros "#Hctx #Hcell #Hc #Hpk #Hlink".
iLöb as "IH".
rel_rec_l. rel_rec_r. rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (t t') "#Ht"=> /=.
rel_prims.
iMod (rel_oracle_open with "Hctx Hcell Hpk Hlink Ht")
  as "[[-> ->]|(%u & %u' & [%eL %eR] & #Hu)]".
- rel_pures.
  rel_apply (rel_send_fail with "Hc").
  iIntros (? ?) "[-> ->]"=> /=.
  rel_pures. by iApply "IH".
- rewrite eL eR. rel_pures.
  rel_load_l_atomic.
  iInv cellN as "[(Hl & Hl' & >seals & >seals')|(%pl & %pl' & Hl & Hl' & >seals & >seals' & >#Hsu & >#Hstore & #Hct)]" "Hclose".
  + iDestruct "Hu" as "[#Hu|#Hin]"; last first.
    { by iMod (cell_unsealed_l (E:=⊤ ∖ ↑cellN) _ ltac:(solve_ndisj) eL with "Hctx seals Hin") as "[]". }
    iModIntro. iExists _. iFrame "Hl". iIntros "!> Hl".
    rel_load_r.
    iMod ("Hclose" with "[Hl Hl' seals seals']") as "_".
    { iNext. iLeft. iFrame. }
    rel_pures.
    rel_apply (rel_send with "Hc Hu").
    iIntros (? ?) "[-> ->]"=> /=.
    rel_pures. by iApply "IH".
  + set ct := Spec.enc (Spec.pkey skA) (Tag (N.@"m")) pl.
    set ct' := Spec.enc (Spec.pkey skA') (Tag (N.@"m")) pl'.
    iAssert (|={⊤ ∖ ↑cellN}=> (⌜ct = t⌝ ∨ (⌜ct ≠ t⌝ ∗ PUB⟨u, u'⟩)) ∗
      term_token (seed_of_aenc_key skA)
        (↑cryptisN.@"public_rel".@"seal" ∖ ↑challenge_ns skA pl))%I
      with "[seals]" as ">[#Hcase seals]".
    { iDestruct "Hu" as "[#Hu|#Hin]".
      - iFrame. iModIntro. case: (decide (ct = t)) => [e|ne]; first by iLeft.
        iRight. by iSplit.
      - iMod (cell_challenge_l (E:=⊤ ∖ ↑cellN) _ _ ltac:(solve_ndisj) eL with "Hctx seals Hin") as "[-> $]".
        iLeft. iPureIntro. move/Spec.open_aenc_key_Some: eL => ->.
        by rewrite /ct /Spec.enc. }
    iModIntro. iExists _. iFrame "Hl". iIntros "!> Hl".
    rel_load_r.
    iMod ("Hclose" with "[Hl Hl' seals seals']") as "_".
    { iNext. iRight. iExists pl, pl'. by iFrame "#∗". }
    rel_prims.
    iMod (publicly_related_part_bij' ct ct' t t' ltac:(solve_ndisj)
            with "Hctx Hct Ht") as %Hiff.
    iDestruct "Hcase" as "[%e|[%ne #Hu']]".
    * have e' : ct' = t' by apply Hiff.
      rewrite !bool_decide_eq_true_2 //.
      rel_pures.
      rel_apply (rel_send_fail with "Hc").
      iIntros (? ?) "[-> ->]"=> /=.
      rel_pures. by iApply "IH".
    * have ne' : ct' ≠ t' by rewrite -Hiff.
      rewrite !bool_decide_eq_false_2 //.
      rel_pures.
      rel_apply (rel_send with "Hc Hu'").
      iIntros (? ?) "[-> ->]"=> /=.
      rel_pures. by iApply "IH".
Qed.

Lemma rel_alice c c' (b b' : bool) :
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  REL alice b c << alice b' c' : lrel_bool.
Proof.
iIntros "#Hctx #Hc". rewrite /alice.
rel_pures.
have Hdisj : ∀ sk : aenc_key,
    seed_of_aenc_key sk ∉ (∅ : gset term) ∧
    seed_of_aenc_key sk ∉ ({[Spec.pkey sk]} : gset term) ∧
    (∅ : gset term) ## ({[Spec.pkey sk]} : gset term).
{ move=> sk. rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
  have Hne : ∀ kt (t : term), t ≠ TKey kt t.
  { move=> kt t H. have := f_equal tsize H.
    rewrite (tsize_eq (TKey kt t)). lia. }
  set_solver. }
rel_apply_l (rel_mk_aenc_key_l _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skA) "%Hnonce_a #mint_skA token_a _ token_pkA".
rel_apply_r (rel_mk_aenc_key_r _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skA') "%Hnonce_a' #mint_spec_skA' token_spec_a _ token_spec_pkA'".
split_term_tokens. rel_prims.
iMod (public_rel_secret_seals_l (E:=⊤) Hnonce_a ltac:(solve_ndisj)
        with "Hctx token_a") as "(#secret_a & seals_a & _ & token_a)".
rewrite (term_token_difference (seed_of_aenc_key skA) (↑storeN)
           (⊤ ∖ ↑cryptisN.@"public_rel")); last solve_ndisj.
iDestruct "token_a" as "[token_store _]".
iMod (public_rel_secret_seals_r (E:=⊤) Hnonce_a' ltac:(solve_ndisj)
        with "Hctx token_spec_a") as "(#secret_a' & seals_a' & _ & _)".
iDestruct (term_token_rel_token_l with "token_pkA") as "(token_pkA & _ & _)";
  first solve_not_TSeal.
iDestruct (term_token_rel_token_r with "token_spec_pkA'") as "(token_spec_pkA' & _ & _)";
  first solve_not_TSeal.
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj)
        with "Hctx [] token_pkA token_spec_pkA'") as "[#elem_pkA #Hpub]".
{ iIntros "!> #elem". rewrite publicly_related_aenc_key. iRight.
  do 3 (iSplit; first done).
  iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r]. }
rel_alloc_l l as "Hl". rel_alloc_r l' as "Hl'".
rel_pures.
iMod (inv_alloc cellN _ (cell_inv skA skA' l l') with "[Hl Hl' seals_a seals_a']") as "#Hcell".
{ iNext. iLeft. iFrame. }
rel_apply refines_fork.
{ iApply (rel_oracle with "Hctx Hcell Hc Hpub elem_pkA"). }
iIntros (? ?) "_" => /=.
rel_pures.
rel_apply (rel_send with "Hc Hpub").
iIntros (? ?) "[-> ->]"=> /=.
rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (msg_0 msg_0') "#Hmsg_0"=> /=.
rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (msg_1 msg_1') "#Hmsg_1"=> /=.
rel_pures.
rel_bind_l (if: _ then _ else _)%E.
rel_bind_r (if: _ then _ else _)%E.
iApply (refines_bind _ _ _ (λ v v', ∃ m m' : term, ⌜v = m⌝ ∧ ⌜v' = m'⌝ ∧ minted m ∧ minted_spec m')%I).
{ rewrite (publicly_related_minted msg_0) (publicly_related_minted msg_1).
  iDestruct "Hmsg_0" as "[? ?]".
  iDestruct "Hmsg_1" as "[? ?]".
  case: b; case: b'; rel_pures; rel_values.
  - iExists msg_0, msg_0'; iFrame "#"; eauto.
  - iExists msg_0, msg_1'; iFrame "#"; eauto.
  - iExists msg_1, msg_0'; iFrame "#"; eauto.
  - iExists msg_1, msg_1'; iFrame "#"; eauto. }
iIntros (? ?) "(%msg & %msg' & -> & -> & #mint_msg & #mint_spec_msg')"=> /=.
rel_pures.
rel_apply (rel_random_aenc (λ _, ∅) (λ _, ∅) skA skA'
  with "Hctx [//] mint_skA mint_spec_skA' elem_pkA secret_a mint_msg mint_spec_msg' [] [] [] []").
{ iPureIntro. set_solver. }
{ iPureIntro. set_solver. }
{ by iIntros (?); rewrite big_sepS_empty. }
{ by iIntros (?); rewrite big_sepS_empty. }
iIntros (n n') "_ _ _ _ _ _ _ _ link". iModIntro. rel_pures.
(* Store the challenge and link it. *)
rel_store_l_atomic.
iInv cellN as "[(Hl & Hl' & >seals & >seals')|(%pl0 & %pl0' & Hl & Hl' & _ & _ & _ & >#Hstore0 & _)]" "Hclose";
  last first.
{ by iDestruct (term_meta_token with "token_store Hstore0") as "[]". }
iMod (term_meta_set storeN () (↑storeN) (seed_of_aenc_key skA) ltac:(done)
        with "token_store") as "#Hstore".
iMod ("link" $! (⊤ ∖ ↑cellN) (↑cryptisN.@"public_rel".@"seal")
        (↑cryptisN.@"public_rel".@"seal")
        with "[] [] [] [$seals $seals']") as "([seals seals'] & #Hsu & #Hct)";
  [iPureIntro; solve_ndisj | iPureIntro; apply nclose_subseteq..|].
iModIntro. iExists _. iFrame "Hl". iIntros "!> Hl".
rel_store_r.
iMod ("Hclose" with "[Hl Hl' seals seals']") as "_".
{ iNext. iRight. iExists (TPair n msg), (TPair n' msg'). by iFrame "#∗". }
rel_pures.
rel_apply (rel_send with "Hc Hct").
iIntros (? ?) "[-> ->]"=> /=.
rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (guess guess') "#Hguess"=> /=.
rel_prims.
rel_values.
iMod (publicly_related_part_bij' (E:=⊤) (TInt 1) (TInt 1) guess guess'
        ltac:(solve_ndisj)
        with "Hctx [] Hguess") as %H.
{ by rewrite publicly_related_TInt. }
iModIntro. iExists (bool_decide (TInt 1 = guess)). iPureIntro.
split; first done. do 2 f_equal. by apply bool_decide_ext.
Qed.

Lemma rel_alice_guess_wrapped c c' :
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  REL alice_guess_wrapped c << alice_guess_wrapped c' : λ p1 p2,
    ⌜∃ b g b' g' : bool,
    p1 = (#b, #g)%V ∧ p2 = (#b', #g')%V ∧ b' = negb b ∧ g = g'⌝.
Proof.
iIntros "#Hctx #Hc". rewrite /alice_guess_wrapped.
rel_pures.
rel_apply_l rel_nondet_bool_l. iIntros (choice).
rel_apply_r (rel_nondet_bool_r _ _ (negb choice)).
case: choice; rel_pures.
- rel_apply (rel_alice with "Hctx Hc").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists true, g, false, g.
- rel_apply (rel_alice with "Hctx Hc").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists false, g, true, g.
Qed.

End CCA2.

Definition ind_cca2_game N (b : bool) (adv : expr) : expr :=
  (run_network adv (alice N b))%E.

(** IND-CCA2 as a contextual equivalence: against any valid attacker with a
    decryption oracle for every ciphertext but the challenge, no well-typed
    context can tell which of the attacker's two messages Alice encrypts. *)
Theorem ind_cca2_ctx_equiv N b b' adv :
  attacker_valid adv →
  ∅ ⊨ ind_cca2_game N b adv =ctx= ind_cca2_game N b' adv : TBool.
Proof.
by move=> Hadv; split;
  apply: (cryptis_ctx_refinement (Σ:=#[relocΣ; public_relΣ])) => // ? ? Δ c c';
  iApply rel_alice.
Qed.

Theorem ind_cca2_secure Σ `{!relocPreG Σ, !public_relGpreS Σ} N (adv : expr) σ :
  attacker_valid adv →
  adequate NotStuck (run_network adv (alice_guess_wrapped N)) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([run_network adv (alice_guess_wrapped N)], σ)
         (of_val v' :: thp', h) ∧
       ∃ b g b' g' : bool,
         v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> Hadv. apply: cryptis_rel_adequacy => // ? ? c c'.
iApply rel_alice_guess_wrapped.
Qed.
