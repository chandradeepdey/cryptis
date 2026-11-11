(** What the invariant of [base.v] knows about a term.

- [Pending t']: the runs treat the term as [t'] in the other run.
- [PublicLink t']: the same, and the attacker may see the term.
- [Secret]: the attacker never sees the term.

A [Pending t'] term can later become [PublicLink t'] or [Secret].  After that it
never changes. *)

From iris.algebra Require Import auth.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module State.

Inductive state :=
  | Pending (t : term)
  | PublicLink (t : term)
  | Secret
  | Invalid.

Definition not_PublicLink st : Prop :=
  match st with
  | PublicLink _ => False
  | _ => True
  end.

Section StateCmra.

Context {SI : sidx}.

Canonical Structure stateO := leibnizO state.

#[global] Instance stateO_discrete : OfeDiscrete state.
Proof. apply _. Qed.

#[local] Instance state_op_instance : Op state := λ s1 s2,
  match s1, s2 with
  | Pending t1, Pending t2 =>
    if bool_decide (t1 = t2) then Pending t1 else Secret
  | Pending t1, PublicLink t2 | PublicLink t2, Pending t1 =>
    if bool_decide (t1 = t2) then PublicLink t2 else Invalid
  | PublicLink t1, PublicLink t2 =>
    if bool_decide (t1 = t2) then PublicLink t1 else Invalid
  | Pending _, Secret | Secret, Pending _ | Secret, Secret => Secret
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
- move=> [?|?||] [?|?||] [?|?||];
  rewrite /op /state_op_instance;
  repeat (case_bool_decide; simplify_eq/=); congruence.
- move=> [?|?||] [?|?||];
  rewrite /op /state_op_instance;
  repeat (case_bool_decide; simplify_eq/=); congruence.
- move=> [?|?||] ? [<-];
  rewrite /op /state_op_instance;
  repeat (case_bool_decide; simplify_eq/=); congruence.
- by move=> [] [].
- rewrite /pcore /state_pcore_instance.
  move=> ? ? ? ? e. apply Some_inj in e as ->; eauto.
- by move=> [] [].
Qed.

Canonical Structure stateR := discreteR state state_ra_mixin.

#[global] Instance stateR_discrete : CmraDiscrete stateR.
Proof. by split; first apply _. Qed.

#[global] Instance state_core_id (st : state) : CoreId st.
Proof. by constructor. Qed.

#[global] Instance stateR_total : CmraTotal stateR.
Proof. by move=> st; exists st. Qed.

Lemma Pending_included_PublicLink t : Pending t ≼ PublicLink t.
Proof. exists (PublicLink t). rewrite state_op /=. by case_bool_decide. Qed.

Lemma Pending_included_Secret t : Pending t ≼ Secret.
Proof. by exists Secret. Qed.

Lemma Pending_included t st :
  ✓ st → Pending t ≼ st → st = Pending t ∨ st = Secret ∨ st = PublicLink t.
Proof.
move=> Hval [z Heq]. fold_leibniz. subst st. move: Hval. rewrite state_op.
case: z => [t1|t1||] //=; repeat (case_bool_decide; simplify_eq/=); try done; eauto.
Qed.

Lemma PublicLink_included t st : ✓ st → PublicLink t ≼ st → st = PublicLink t.
Proof.
move=> Hval [z Heq]. fold_leibniz. subst st. move: Hval. rewrite state_op.
case: z => [t1|t1||] //=; repeat (case_bool_decide; simplify_eq/=); try done; eauto.
Qed.

Lemma Secret_included st : ✓ st → Secret ≼ st → st = Secret.
Proof.
move=> Hval [z Heq]. fold_leibniz. subst st. move: Hval. rewrite state_op. by case: z.
Qed.

Lemma PublicLink_PublicLink_valid t1 t2 : ✓ (PublicLink t1 ⋅ PublicLink t2) → t1 = t2.
Proof. rewrite state_op /=. by case_bool_decide. Qed.

Lemma Pending_PublicLink_valid t1 t2 : ✓ (Pending t1 ⋅ PublicLink t2) → t1 = t2.
Proof. rewrite state_op /=. by case_bool_decide. Qed.

Lemma Secret_PublicLink_valid t : ✓ (Secret ⋅ PublicLink t) → False.
Proof. by rewrite state_op. Qed.

End StateCmra.

Section StateUpdates.

Context {SI : sidx}.

Lemma state_local_update_lock_PublicLink t :
  (● Some (Pending t) ⋅ ◯ Some (Pending t),
   ● Some (Pending t) ⋅ ◯ Some (Pending t)) ~l~>
  (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t),
   ● Some (PublicLink t) ⋅ ◯ Some (PublicLink t)).
Proof.
apply auth_local_update=> //. apply local_update_discrete.
move=> mz Hval Heq; split; first done.
case: mz Hval Heq => [[[t1|t1||]|]|] //= Hval Heq;
  rewrite -!Some_op !state_op /= in Heq *; fold_leibniz;
  repeat (case_bool_decide; simplify_eq/=); done.
Qed.

Lemma state_local_update_lock_Secret t :
  (● Some (Pending t) ⋅ ◯ Some (Pending t),
   ● Some (Pending t) ⋅ ◯ Some (Pending t)) ~l~>
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

End State.
