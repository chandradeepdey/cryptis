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

Section CPA.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t : term).
Implicit Types (skA : aenc_key).

Variable N : namespace.

(*

* --> A: msg_0
* --> A: msg_1
A --> *: if b then {nonce, msg_0}@pkA else {nonce, msg_1}@pkA

*)

Definition alice (b : bool) : val := λ: "c",
  let: "skA" := mk_aenc_key #() in
  let: "pkA" := pkey "skA" in
  send "c" "pkA";;
  let: "msg_0" := recv "c" in
  let: "msg_1" := recv "c" in
  let: "msg" := if: #b then "msg_0" else "msg_1" in
  send "c" (random_aenc "pkA" (Tag $ N.@"m") "msg");;
  let: "guess" := recv "c" in
  eq_term (TInt 1) "guess".

Definition alice_guess_wrapped : val := λ: "c",
  let: "b" := nondet_bool #() in
  ("b", if: "b" then alice true "c" else alice false "c").

Lemma rel_alice c c' (b b' : bool) :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL alice b c << alice b' c' : lrel_bool.
Proof.
iIntros "#Hctx #Hc". rewrite /alice. rel_pures.
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
(* The seeds never become public. *)
iMod (public_rel_secret_seals_l (E:=⊤) Hnonce_a ltac:(solve_ndisj)
        with "Hctx token_a") as "(#secret_a & seals_a & _ & _)".
iMod (public_rel_secret_seals_r (E:=⊤) Hnonce_a' ltac:(solve_ndisj)
        with "Hctx token_spec_a") as "(#secret_a' & seals_a' & _ & _)".
(* The public keys are publicly related. *)
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj)
        with "Hctx [] token_pkA token_spec_pkA'") as "[#elem_pkA #Hpub]".
{ iIntros "!> #elem". rewrite publicly_related_aenc_key. iRight.
  do 3 (iSplit; first done).
  iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r]. }
rel_apply (rel_send with "Hc Hpub").
iIntros (? ?) "[-> ->]"=> /=. rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (msg_0 msg_0') "#Hmsg_0"=> /=. rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (msg_1 msg_1') "#Hmsg_1"=> /=. rel_pures.
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
iIntros (n n') "_ _ _ _ _ _ upd".
iMod ("upd" $! ⊤ with "[//] seals_a seals_a'") as "(seals_a & seals_a' & #Hcmsg)".
iModIntro.
rel_apply (rel_send with "Hc Hcmsg").
iIntros (? ?) "[-> ->]"=> /=. rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (guess guess') "#Hguess"=> /=.
rel_prims. rel_values.
iMod (publicly_related_part_bij' (E:=⊤) (TInt 1) (TInt 1) guess guess'
        ltac:(solve_ndisj)
        with "Hctx [] Hguess") as %H.
{ by rewrite publicly_related_TInt. }
iModIntro. iExists (bool_decide (TInt 1 = guess)). iPureIntro.
split; first done. do 2 f_equal. by apply bool_decide_ext.
Qed.

Lemma rel_alice_guess_wrapped c c' :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
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

End CPA.

Definition ind_cpa_game N (b : bool) (adv : expr) : expr :=
  (run_network_rel adv (alice N b))%E.

(** IND-CPA as a contextual equivalence: against any valid attacker, no
    well-typed context can tell which of the attacker's two messages Alice
    encrypts. *)
Theorem ind_cpa_ctx_equiv N b b' adv :
  attacker_valid adv →
  ∅ ⊨ ind_cpa_game N b adv =ctx= ind_cpa_game N b' adv : TBool.
Proof.
by move=> Hadv; split;
  apply: (cryptis_ctx_refinement (Σ:=#[relocΣ; public_relΣ])) => // ? ? Δ c c';
  iApply rel_alice.
Qed.

(** The same fact as an adequacy statement for the nondeterministic game:
    whenever a run terminates with a bit [b] and a guess [g], the run where
    Alice picked the other bit can terminate with the same guess. *)
Theorem ind_cpa_secure Σ `{!relocPreG Σ, !public_relGpreS Σ} N (adv : expr) σ :
  attacker_valid adv →
  adequate NotStuck (run_network_rel adv (alice_guess_wrapped N)) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([run_network_rel adv (alice_guess_wrapped N)], σ)
         (of_val v' :: thp', h) ∧
       ∃ b g b' g' : bool,
         v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> Hadv. apply: cryptis_rel_adequacy => // ? ? c c'.
iApply rel_alice_guess_wrapped.
Qed.
