From iris.algebra Require Import auth.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive state :=
  | Private (t : term)
  | Public (t : term)
  | Secret
  | Invalid.

Definition not_Public st : Prop :=
  match st with
  | Public _ => False
  | _ => True
  end.

Section StateCmra.

  Context {SI : sidx}.

  Canonical Structure stateO := leibnizO state.

  #[global] Instance stateO_discrete : OfeDiscrete state.
  Proof. apply _. Qed.

  #[local] Instance state_op_instance : Op state := λ s1 s2,
    match s1, s2 with
    | Private t1, Private t2 =>
      if bool_decide (t1 = t2) then Private t1 else Secret
    | Private t1, Public t2 | Public t2, Private t1 =>
      if bool_decide (t1 = t2) then Public t2 else Invalid
    | Public t1, Public t2 =>
      if bool_decide (t1 = t2) then Public t1 else Invalid
    | Private _, Secret | Secret, Private _ | Secret, Secret => Secret
    | _, _ => Invalid
    end.

  #[local] Instance state_pcore_instance : PCore state := Some.

  #[local] Instance state_valid_instance : Valid state := λ s,
    match s with
    | Invalid => False
    | _ => True
    end.

  Lemma state_op st1 st2 : st1 ⋅ st2 = state_op_instance st1 st2.
  Proof. by []. Qed.

  Lemma state_ra_mixin : RAMixin state.
  Proof.
  split.
  - solve_proper.
  - naive_solver.
  - solve_proper.
  - intros [] [] [];
    rewrite /op /state_op_instance;
    repeat (case_bool_decide; simplify_eq/=); congruence.
  - intros [] [];
    rewrite /op /state_op_instance;
    repeat (case_bool_decide; simplify_eq/=); congruence.
  - intros [] ? [= <-];
    rewrite /op /state_op_instance;
    repeat (case_bool_decide; simplify_eq/=); congruence.
  - by move=> [] [].
  - rewrite /pcore /state_pcore_instance.
    move=> ? ? ? ? H.
    apply Some_inj in H as ->; eauto.
  - by move=> [] [].
  Qed.

  Canonical Structure stateR := discreteR state state_ra_mixin.

  #[global] Instance stateR_discrete : CmraDiscrete stateR.
  Proof. by split; first apply _. Qed.

  #[global] Instance state_core_id (st : state) : CoreId st.
  Proof. by constructor. Qed.

  #[global] Instance stateR_total : CmraTotal stateR.
  Proof. by move=> st; exists st. Qed.

  Lemma Private_included_Public t : Private t ≼ Public t.
  Proof. exists (Public t). rewrite state_op /=. by case_bool_decide. Qed.

  Lemma Private_included_Secret t : Private t ≼ Secret.
  Proof. by exists Secret. Qed.

  Lemma Private_included t st :
    ✓ st → Private t ≼ st → st = Private t ∨ st = Secret ∨ st = Public t.
  Proof.
  move=> Hval [z Heq]. fold_leibniz. subst st. move: Hval. rewrite state_op.
  case: z => [t1|t1||] //=; repeat (case_bool_decide; simplify_eq/=); try done; eauto.
  Qed.

  Lemma Public_included t st : ✓ st → Public t ≼ st → st = Public t.
  Proof.
  move=> Hval [z Heq]. fold_leibniz. subst st. move: Hval. rewrite state_op.
  case: z => [t1|t1||] //=; repeat (case_bool_decide; simplify_eq/=); try done; eauto.
  Qed.

  Lemma Secret_included st : ✓ st → Secret ≼ st → st = Secret.
  Proof.
  move=> Hval [z Heq]. fold_leibniz. subst st. move: Hval. rewrite state_op. by case: z.
  Qed.

  Lemma Public_Public_valid t1 t2 : ✓ (Public t1 ⋅ Public t2) → t1 = t2.
  Proof. rewrite state_op /=. by case_bool_decide. Qed.

  Lemma Private_Public_valid t1 t2 : ✓ (Private t1 ⋅ Public t2) → t1 = t2.
  Proof. rewrite state_op /=. by case_bool_decide. Qed.

  Lemma Secret_Public_valid t : ✓ (Secret ⋅ Public t) → False.
  Proof. by rewrite state_op. Qed.

End StateCmra.

Section StateUpdates.

  Context {SI : sidx}.

  Lemma state_local_update_lock_Public t :
    (● Some (Private t) ⋅ ◯ Some (Private t),
     ● Some (Private t) ⋅ ◯ Some (Private t)) ~l~>
    (● Some (Public t) ⋅ ◯ Some (Public t),
     ● Some (Public t) ⋅ ◯ Some (Public t)).
  Proof.
  apply auth_local_update=> //. apply local_update_discrete.
  move=> mz Hval Heq; split; first done.
  case: mz Hval Heq => [[[t1|t1||]|]|] //= Hval Heq;
    rewrite -!Some_op !state_op /= in Heq *; fold_leibniz;
    repeat (case_bool_decide; simplify_eq/=); done.
  Qed.

  Lemma state_local_update_lock_Secret t :
    (● Some (Private t) ⋅ ◯ Some (Private t),
     ● Some (Private t) ⋅ ◯ Some (Private t)) ~l~>
    (● Some Secret ⋅ ◯ Some Secret,
     ● Some Secret ⋅ ◯ Some Secret).
  Proof.
  apply auth_local_update=> //. apply local_update_discrete.
  move=> mz Hval Heq; split; first done.
  case: mz Hval Heq => [[[t1|t1||]|]|] //= Hval Heq;
    rewrite -!Some_op !state_op /= in Heq *; fold_leibniz;
    repeat (case_bool_decide; simplify_eq/=); done.
  Qed.

  Lemma state_core_id_local_update (st : state) :
    (● Some st ⋅ ◯ Some st, ● Some st) ~l~>
    (● Some st ⋅ ◯ Some st, ● Some st ⋅ ◯ Some st).
  Proof.
  apply core_id_local_update; first apply _.
  by rewrite auth_frag_included.
  Qed.

End StateUpdates.
