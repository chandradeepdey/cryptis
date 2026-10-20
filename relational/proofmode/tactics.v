(** Tactics for relational proofs.

  Creating a nonce or a key with [rel_mk_nonce_l] or [rel_mk_aenc_key_l]
  leaves side conditions about the token set, the set of terms whose tokens
  the proof wants to receive along with the fresh term.  These are discharged
  by:
  - [solve_minted_iff], which shows that each term of the set is minted
    exactly when the fresh term is.  This holds whenever the fresh term is a
    subterm and the other components are already minted.
  - [split_term_tokens], which separates the tokens of the set into one
    hypothesis per term.  This needs the terms to be pairwise different,
    which [solve_term_disj] shows by unfolding the term constructors and the
    nonce equations and letting [set_solver] finish.
  - [solve_immediate_subterm] and [solve_subterm], which show that one term
    occurs in another, looking through tags, encryptions and lists.

  Running the programs:
  - [rel_pures] is [rel_pures_l] followed by [rel_pures_r].
  - [rel_later] strips a later, which the one-sided steps of the primitives
    leave behind.
  - [rel_apply lem] applies a two-sided specification such as [rel_send] or
    a protocol lemma to the subexpressions both programs are about to run,
    binding the continuations when the specification covers only part of the
    programs. *)

From iris.proofmode Require Import environments reduction spec_patterns.
From reloc Require Import reloc.
From cryptis Require Import lib cryptis.
From cryptis.hyper.lib Require Import refines.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel.

Ltac minted_simpl :=
  rewrite /Spec.random_aenc /Spec.enc
    ?(minted_TSeal, minted_tag, minted_of_list, minted_TPair,
      minted_spec_TSeal, minted_spec_tag, minted_spec_of_list, minted_spec_TPair) /=.

Ltac unfold_sets := repeat match goal with x := _ |- _ => subst x end.

Ltac solve_subterm :=
  unfold_sets;
  rewrite /Spec.random_aenc /Spec.enc ?[Spec.tag]unlock ?[Spec.of_list]unlock /=;
  eauto 20 using STRefl, STPair1, STPair2, STKey, STSeal1, STSeal2, STHash.

Ltac solve_immediate_subterm :=
  unfold_sets;
  rewrite /Spec.random_aenc /Spec.enc ?[Spec.tag]unlock ?[Spec.of_list]unlock /=;
  first [exact: SubtermPairL | exact: SubtermPairR].

Ltac unfold_nonces :=
  repeat match goal with
  | H : context[is_nonce ?n] |- context[?n] =>
    lazymatch n with TNonce _ => fail | _ => idtac end;
    let a := fresh "a" in let e := fresh "e" in
    case/is_nonceP: (H) => a e; rewrite e
  end.

Ltac solve_term_disj :=
  unfold_sets;
  unfold_nonces;
  rewrite /Spec.random_aenc /Spec.enc ?[Spec.tag]unlock ?[Spec.of_list]unlock ?[Tag]unlock /=;
  set_solver.

Ltac split_term_tokens :=
  rewrite ?big_sepS_union ?big_sepS_singleton ?big_sepS_empty;
  try match goal with |- _ ## _ => solve_term_disj end.

Ltac solve_minted_iff_elem :=
  iModIntro; iSplit; iIntros "#H";
  [ minted_simpl; by iFrame "#"
  | first [ iApply (subterm_minted with "H")
          | iApply (subterm_minted_spec with "H") ];
    solve_subterm ].

Ltac solve_minted_iff :=
  iIntros (?) "/="; rewrite big_sepS_forall;
  let t := fresh "t" in let Ht := fresh "Ht" in
  iIntros (t Ht);
  set_unfold in Ht; destruct_or? Ht; first [by destruct Ht | subst t];
  solve_minted_iff_elem.

Ltac rel_later :=
  try match goal with |- envs_entails _ (bi_later _) => iModIntro end.

Ltac rel_pures := rel_pures_l; rel_pures_r.

Tactic Notation "rel_apply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H =>
    rel_reshape_cont_l ltac:(fun K e =>
      rel_reshape_cont_r ltac:(fun K' e' =>
        rel_bind_ctx_l K; rel_bind_ctx_r K';
        first [ iApplyHyp H
              | iApply refines_bind'; iApplyHyp H
              | iApply (refines_bind with
                  [SGoal (SpecGoal GSpatial false [] [H] false)]);
                first iApplyHyp H ]))
    || lazymatch iTypeOf H with
       | Some (_, ?P) => fail "rel_apply: Cannot apply" P
       end);
  try (pm_prettify; iEval (cbv beta; simpl fill)).
