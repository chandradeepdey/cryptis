From reloc Require Import reloc.
From stdpp Require Import sorting list lexico.
From cryptis.lib Require Import repr list list_sort.

Section ListLemmas.

Context `{!Repr A, !Repr B, !relocG Σ}.

Implicit Types (x : A) (xs : list A).

Lemma rel_get_list_l E K e (l: list A) (n: nat) Ψ :
  (REL fill K (repr (l !! n)%stdpp : expr) << e @ E : Ψ) -∗
  REL fill K (repr l !! #n) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal.
elim: n l => [|n IH] [|x l] /=; iIntros "H";
rel_rec_l; rel_pures_l; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma rel_get_list_r E K e (l: list A) (n: nat) Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (l !! n)%stdpp : expr) @ E : Ψ) -∗
  REL e << fill K (repr l !! #n) @ E : Ψ.
Proof.
move=> ?.
rewrite /= repr_list_unseal.
elim: n l => [|n IH] [|x l] /=; iIntros "H";
rel_rec_r; rel_pures_r; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma rel_nil_l E K e Ψ :
  (REL fill K (repr (@nil A) : expr) << e @ E : Ψ) -∗
  REL fill K (Val []%V) << e @ E : Ψ .
Proof. by rewrite /NILV /= repr_list_unseal; iIntros "?"; rel_pures_l. Qed.

Lemma rel_nil_r E K e Ψ :
  (REL e << fill K (repr (@nil A) : expr) @ E : Ψ) -∗
  REL e << fill K (Val []%V) @ E : Ψ .
Proof. by rewrite /NILV /= repr_list_unseal; iIntros "?"; rel_pures_r. Qed.

Lemma rel_cons_l E K e x xs Ψ :
  (REL fill K (repr (x :: xs)%list : expr) << e @ E : Ψ) -∗
  REL fill K (repr x :: repr xs) << e @ E : Ψ.
Proof. by rewrite /= repr_list_unseal; iIntros "?"; rewrite /CONS; rel_pures_l. Qed.

Lemma rel_cons_r E K e x xs Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (x :: xs)%list : expr) @ E : Ψ) -∗
  REL e << fill K (repr x :: repr xs) @ E : Ψ.
Proof.
move=> ?.
by rewrite /= repr_list_unseal; iIntros "?"; rewrite /CONS; rel_pures_r.
Qed.

Lemma rel_eq_list_l `{EqDecision A} E K e (f : val) (l1 l2 : list A) Ψ :
  (∀ K (x1 x2 : A) Ψ,
      x1 ∈ l1 →
      (REL fill K (#(bool_decide (x1 = x2)) : expr) << e @ E : Ψ) -∗
      REL fill K (f (repr x1) (repr x2)) << e @ E : Ψ) →
  (REL fill K (#(bool_decide (l1 = l2)) : expr) << e @ E : Ψ) -∗
  REL fill K (eq_list f (repr l1) (repr l2)) << e @ E : Ψ.
Proof.
rewrite repr_list_unseal /=.
elim: l1 l2 Ψ => [|x1 l1 IH] [|x2 l2] Ψ rel_f_l /=;
  iIntros "post" ; rel_rec_l; rel_pures_l; do 1?by iApply "post".
rel_bind_l (f _ _). iApply (rel_f_l _ x1 x2); first by set_solver.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2] /=; rel_pures_l; last first.
  rewrite bool_decide_decide decide_False; by [iApply "post"|congruence].
iApply IH; first by move=> *; iApply rel_f_l; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

Lemma rel_eq_list_r `{EqDecision A} E K e (f : val) (l1 l2 : list A) Ψ :
  ↑specN ⊆ E →
  (∀ K (x1 x2 : A),
      ↑specN ⊆ E →
      x1 ∈ l1 →
      (REL e << fill K (#(bool_decide (x1 = x2)) : expr) @ E : Ψ) -∗
      REL e << fill K (f (repr x1) (repr x2)) @ E : Ψ) →
  (REL e << fill K (#(bool_decide (l1 = l2)) : expr) @ E : Ψ) -∗
  REL e << fill K (eq_list f (repr l1) (repr l2)) @ E : Ψ.
Proof.
move=> HE.
rewrite repr_list_unseal /=.
elim: l1 l2 Ψ => [|x1 l1 IH] [|x2 l2] Ψ rel_f_r /=;
  iIntros "post" ; rel_rec_r; rel_pures_r; do 1?by iApply "post".
rel_bind_r (f _ _). iApply (rel_f_r _ x1 x2 HE); first by set_solver.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2] /=; rel_pures_r; last first.
  rewrite bool_decide_decide decide_False; by [iApply "post"|congruence].
iApply IH; first by move=> *; iApply rel_f_r; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

(** Higher-order list functions.  The behaviour of the functional argument is
    specified by a hypothesis of the same [REL]-shape as the conclusion, so
    that the lemma can be instantiated with any [rel_*] lemma.

    Proof pattern: [rel_rec_l; rel_pures_l] unfolds one iteration and stops
    at calls of the abstract function and at the (named, hence not
    [AsRecV]-unfoldable) recursive call.  After [rel_bind_l] + [iApply IH]
    the goal has the shape [REL fill (Ki :: K) (Val v) << ...], whose next
    redex is formed together with [Ki]; [rel_pures_l] only searches the
    expression, so a [rewrite /=] is needed to refold the context first. *)

Lemma rel_scan_list_l E K e φ ψ (f : val) (l : list A) Ψ :
  □ (∀ K (x : A),
       ψ NONEV -∗ φ x -∗
       (∀ r : option val, ψ (repr r) -∗
          REL fill K (repr r : expr) << e @ E : Ψ) -∗
       REL fill K (f (repr x)) << e @ E : Ψ) -∗
  ψ NONEV -∗
  ([∗ list] x ∈ l, φ x) -∗
  (∀ r : option val, ψ (repr r) -∗ REL fill K (repr r : expr) << e @ E : Ψ) -∗
  REL fill K (scan_list f (repr l)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal.
iIntros "#Hf". iInduction l as [|x l] "IH" forall (K); iIntros "Hψ Hφ post".
- rel_rec_l; rel_pures_l. by iApply ("post" $! None with "Hψ").
- iDestruct "Hφ" as "[Hφ_x Hφ_l]". rel_rec_l; rel_pures_l.
  rel_bind_l (f _). iApply ("Hf" with "Hψ Hφ_x"). iIntros (r) "Hψ".
  case: r => [r|] /=; rel_pures_l.
  + by iApply ("post" $! (Some r) with "Hψ").
  + by iApply ("IH" with "Hψ Hφ_l post").
Qed.

Lemma rel_scan_list_r E K e φ ψ (f : val) (l : list A) Ψ :
  ↑specN ⊆ E →
  □ (∀ K (x : A),
       ψ NONEV -∗ φ x -∗
       (∀ r : option val, ψ (repr r) -∗
          REL e << fill K (repr r : expr) @ E : Ψ) -∗
       REL e << fill K (f (repr x)) @ E : Ψ) -∗
  ψ NONEV -∗
  ([∗ list] x ∈ l, φ x) -∗
  (∀ r : option val, ψ (repr r) -∗ REL e << fill K (repr r : expr) @ E : Ψ) -∗
  REL e << fill K (scan_list f (repr l)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal.
iIntros "#Hf". iInduction l as [|x l] "IH" forall (K); iIntros "Hψ Hφ post".
- rel_rec_r; rel_pures_r. by iApply ("post" $! None with "Hψ").
- iDestruct "Hφ" as "[Hφ_x Hφ_l]". rel_rec_r; rel_pures_r.
  rel_bind_r (f _). iApply ("Hf" with "Hψ Hφ_x"). iIntros (r) "Hψ".
  case: r => [r|] /=; rel_pures_r.
  + by iApply ("post" $! (Some r) with "Hψ").
  + by iApply ("IH" with "Hψ Hφ_l post").
Qed.

Lemma rel_find_list_l E K e (f : A → bool) (fimpl : val) (l : list A) Ψ :
  (∀ K (x : A), x ∈ l →
     (REL fill K (#(f x) : expr) << e @ E : Ψ) -∗
     REL fill K (fimpl (repr x)) << e @ E : Ψ) →
  (REL fill K (repr (find f l) : expr) << e @ E : Ψ) -∗
  REL fill K (find_list fimpl (repr l)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal.
elim: l K => [|x l IH] K rel_f /=; iIntros "post"; rel_rec_l; rel_pures_l.
- by iApply "post".
- rel_bind_l (fimpl _). iApply (rel_f _ x); first by set_solver.
  case: (f x) => /=; rel_pures_l; first by iApply "post".
  iApply (IH with "post") => K' y y_l. by apply: rel_f; set_solver.
Qed.

Lemma rel_find_list_r E K e (f : A → bool) (fimpl : val) (l : list A) Ψ :
  ↑specN ⊆ E →
  (∀ K (x : A), x ∈ l →
     (REL e << fill K (#(f x) : expr) @ E : Ψ) -∗
     REL e << fill K (fimpl (repr x)) @ E : Ψ) →
  (REL e << fill K (repr (find f l) : expr) @ E : Ψ) -∗
  REL e << fill K (find_list fimpl (repr l)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal.
elim: l K => [|x l IH] K rel_f /=; iIntros "post"; rel_rec_r; rel_pures_r.
- by iApply "post".
- rel_bind_r (fimpl _). iApply (rel_f _ x); first by set_solver.
  case: (f x) => /=; rel_pures_r; first by iApply "post".
  iApply (IH with "post") => K' y y_l. by apply: rel_f; set_solver.
Qed.

Lemma rel_filter_list_l E K e (f : A → bool) (fimpl : val) (l : list A) Ψ :
  (∀ K (x : A), x ∈ l →
     (REL fill K (#(f x) : expr) << e @ E : Ψ) -∗
     REL fill K (fimpl (repr x)) << e @ E : Ψ) →
  (REL fill K (repr (List.filter f l) : expr) << e @ E : Ψ) -∗
  REL fill K (filter_list fimpl (repr l)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal.
elim: l K => [|x l IH] K rel_f /=; iIntros "post"; rel_rec_l; rel_pures_l.
- by iApply "post".
- rel_bind_l (filter_list _ _).
  iApply IH; first by move=> K' y y_l; apply: rel_f; set_solver.
  rewrite /=. rel_pures_l. rel_bind_l (fimpl _). iApply (rel_f _ x); first by set_solver.
  case: (f x) => /=; rel_pures_l; by iApply "post".
Qed.

Lemma rel_filter_list_r E K e (f : A → bool) (fimpl : val) (l : list A) Ψ :
  ↑specN ⊆ E →
  (∀ K (x : A), x ∈ l →
     (REL e << fill K (#(f x) : expr) @ E : Ψ) -∗
     REL e << fill K (fimpl (repr x)) @ E : Ψ) →
  (REL e << fill K (repr (List.filter f l) : expr) @ E : Ψ) -∗
  REL e << fill K (filter_list fimpl (repr l)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal.
elim: l K => [|x l IH] K rel_f /=; iIntros "post"; rel_rec_r; rel_pures_r.
- by iApply "post".
- rel_bind_r (filter_list _ _).
  iApply IH; first by move=> K' y y_l; apply: rel_f; set_solver.
  rewrite /=. rel_pures_r. rel_bind_r (fimpl _). iApply (rel_f _ x); first by set_solver.
  case: (f x) => /=; rel_pures_r; by iApply "post".
Qed.

Lemma rel_append_lists_l E K e (l1 l2 : list A) Ψ :
  (REL fill K (repr (l1 ++ l2) : expr) << e @ E : Ψ) -∗
  REL fill K (append_lists (repr l1) (repr l2)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal.
elim: l1 K => [|x l1 IH] K /=; iIntros "post"; rel_rec_l; rel_pures_l.
- by iApply "post".
- rel_bind_l (append_lists _ _). iApply IH. rewrite /=. rel_pures_l.
  by iApply "post".
Qed.

Lemma rel_append_lists_r E K e (l1 l2 : list A) Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (l1 ++ l2) : expr) @ E : Ψ) -∗
  REL e << fill K (append_lists (repr l1) (repr l2)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal.
elim: l1 K => [|x l1 IH] K /=; iIntros "post"; rel_rec_r; rel_pures_r.
- by iApply "post".
- rel_bind_r (append_lists _ _). iApply IH. rewrite /=. rel_pures_r.
  by iApply "post".
Qed.

Lemma rel_map_list_l E K e (f : A → B) (fimpl : val) (xs : list A) Ψ :
  (∀ K (x : A), x ∈ xs →
     (REL fill K (repr (f x) : expr) << e @ E : Ψ) -∗
     REL fill K (fimpl (repr x)) << e @ E : Ψ) →
  (REL fill K (repr (map f xs) : expr) << e @ E : Ψ) -∗
  REL fill K (map_list fimpl (repr xs)) << e @ E : Ψ.
Proof.
rewrite /= !repr_list_unseal.
elim: xs K => [|x xs IH] K rel_f /=; iIntros "post"; rel_rec_l; rel_pures_l.
- by iApply "post".
- rel_bind_l (map_list _ _).
  iApply IH; first by move=> K' y y_xs; apply: rel_f; set_solver.
  rewrite /=. rel_bind_l (fimpl _). iApply (rel_f _ x); first by set_solver.
  rewrite /=. rel_pures_l. by iApply "post".
Qed.

Lemma rel_map_list_r E K e (f : A → B) (fimpl : val) (xs : list A) Ψ :
  ↑specN ⊆ E →
  (∀ K (x : A), x ∈ xs →
     (REL e << fill K (repr (f x) : expr) @ E : Ψ) -∗
     REL e << fill K (fimpl (repr x)) @ E : Ψ) →
  (REL e << fill K (repr (map f xs) : expr) @ E : Ψ) -∗
  REL e << fill K (map_list fimpl (repr xs)) @ E : Ψ.
Proof.
move=> HE. rewrite /= !repr_list_unseal.
elim: xs K => [|x xs IH] K rel_f /=; iIntros "post"; rel_rec_r; rel_pures_r.
- by iApply "post".
- rel_bind_r (map_list _ _).
  iApply IH; first by move=> K' y y_xs; apply: rel_f; set_solver.
  rewrite /=. rel_bind_r (fimpl _). iApply (rel_f _ x); first by set_solver.
  rewrite /=. rel_pures_r. by iApply "post".
Qed.

Lemma rel_foldr_list_l E K e (f : B → A → A) (fimpl : val) (l : list B) (x : A) Ψ :
  (∀ K (b : B) (a : A), b ∈ l →
     (REL fill K (repr (f b a) : expr) << e @ E : Ψ) -∗
     REL fill K (fimpl (repr b) (repr a)) << e @ E : Ψ) →
  (REL fill K (repr (foldr f x l) : expr) << e @ E : Ψ) -∗
  REL fill K (foldr_list fimpl (repr x) (repr l)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal.
elim: l K => [|b l IH] K rel_f /=; iIntros "post"; rel_rec_l; rel_pures_l.
- by iApply "post".
- rel_bind_l (foldr_list _ _ _).
  iApply IH; first by move=> K' b' a b'_l; apply: rel_f; set_solver.
  rewrite /=. rel_bind_l (fimpl _ _). iApply (rel_f _ b); first by set_solver.
  by iApply "post".
Qed.

Lemma rel_foldr_list_r E K e (f : B → A → A) (fimpl : val) (l : list B) (x : A) Ψ :
  ↑specN ⊆ E →
  (∀ K (b : B) (a : A), b ∈ l →
     (REL e << fill K (repr (f b a) : expr) @ E : Ψ) -∗
     REL e << fill K (fimpl (repr b) (repr a)) @ E : Ψ) →
  (REL e << fill K (repr (foldr f x l) : expr) @ E : Ψ) -∗
  REL e << fill K (foldr_list fimpl (repr x) (repr l)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal.
elim: l K => [|b l IH] K rel_f /=; iIntros "post"; rel_rec_r; rel_pures_r.
- by iApply "post".
- rel_bind_r (foldr_list _ _ _).
  iApply IH; first by move=> K' b' a b'_l; apply: rel_f; set_solver.
  rewrite /=. rel_bind_r (fimpl _ _). iApply (rel_f _ b); first by set_solver.
  by iApply "post".
Qed.

End ListLemmas.

Section ListLemmasEq.

Context `{!EqDecision A, !Repr A, !relocG Σ}.

Implicit Types (v x : A) (l : list A).

Lemma rel_mem_list_l E K e (eqImpl : val) v l Ψ :
  (∀ K x y,
     (REL fill K (#(bool_decide (x = y)) : expr) << e @ E : Ψ) -∗
     REL fill K (eqImpl (repr x) (repr y)) << e @ E : Ψ) →
  (REL fill K (#(bool_decide (v ∈ l)) : expr) << e @ E : Ψ) -∗
  REL fill K (mem_list eqImpl (repr v) (repr l)) << e @ E : Ψ.
Proof.
move=> rel_eq; iIntros "post".
rel_rec_l; rel_pures_l.
rel_bind_l (find_list _ _).
iApply (rel_find_list_l _ _ _ (λ x, bool_decide (v = x))).
{ move=> K' x _; iIntros "post'"; rel_pures_l.
  by iApply (rel_eq with "post'"). }
rewrite find_if_in.
case: (List.find (λ x, bool_decide (v = x)) l) => [x|] /=; rel_pures_l;
  by iApply "post".
Qed.

Lemma rel_mem_list_r E K e (eqImpl : val) v l Ψ :
  ↑specN ⊆ E →
  (∀ K x y,
     (REL e << fill K (#(bool_decide (x = y)) : expr) @ E : Ψ) -∗
     REL e << fill K (eqImpl (repr x) (repr y)) @ E : Ψ) →
  (REL e << fill K (#(bool_decide (v ∈ l)) : expr) @ E : Ψ) -∗
  REL e << fill K (mem_list eqImpl (repr v) (repr l)) @ E : Ψ.
Proof.
move=> HE rel_eq; iIntros "post".
rel_rec_r; rel_pures_r.
rel_bind_r (find_list _ _).
iApply (rel_find_list_r _ _ _ (λ x, bool_decide (v = x))) => //.
{ move=> K' x _; iIntros "post'"; rel_pures_r.
  by iApply (rel_eq with "post'"). }
rewrite find_if_in.
case: (List.find (λ x, bool_decide (v = x)) l) => [x|] /=; rel_pures_r;
  by iApply "post".
Qed.

Lemma rel_rem_list_l E K e (eqImpl : val) v l Ψ :
  (∀ K x y,
     (REL fill K (#(bool_decide (x = y)) : expr) << e @ E : Ψ) -∗
     REL fill K (eqImpl (repr x) (repr y)) << e @ E : Ψ) →
  (REL fill K (repr (rem v l) : expr) << e @ E : Ψ) -∗
  REL fill K (rem_list eqImpl (repr v) (repr l)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal => rel_eq.
elim: l K => [|x l IH] K /=; iIntros "post"; rel_rec_l; rel_pures_l.
- by iApply "post".
- rel_bind_l (eqImpl _ _). iApply (rel_eq _ x v).
  rewrite (_ : bool_decide (v = x) = bool_decide (x = v)); last first.
    by apply: bool_decide_ext; split; congruence.
  case: (bool_decide (x = v)) => /=; rel_pures_l; first by iApply "post".
  rel_bind_l (rem_list _ _ _). iApply IH. rewrite /=. rel_pures_l.
  by iApply "post".
Qed.

Lemma rel_rem_list_r E K e (eqImpl : val) v l Ψ :
  ↑specN ⊆ E →
  (∀ K x y,
     (REL e << fill K (#(bool_decide (x = y)) : expr) @ E : Ψ) -∗
     REL e << fill K (eqImpl (repr x) (repr y)) @ E : Ψ) →
  (REL e << fill K (repr (rem v l) : expr) @ E : Ψ) -∗
  REL e << fill K (rem_list eqImpl (repr v) (repr l)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal => rel_eq.
elim: l K => [|x l IH] K /=; iIntros "post"; rel_rec_r; rel_pures_r.
- by iApply "post".
- rel_bind_r (eqImpl _ _). iApply (rel_eq _ x v).
  rewrite (_ : bool_decide (v = x) = bool_decide (x = v)); last first.
    by apply: bool_decide_ext; split; congruence.
  case: (bool_decide (x = v)) => /=; rel_pures_r; first by iApply "post".
  rel_bind_r (rem_list _ _ _). iApply IH. rewrite /=. rel_pures_r.
  by iApply "post".
Qed.

End ListLemmasEq.

Section DoUntil.

Context `{!relocG Σ}.

Lemma rel_do_until (f f' : val) φ Ψ :
  □ (φ -∗ REL f' #() << f #() : (fun o1 o2 =>
    ⌜o1 = NONEV⌝ ∗ ⌜o2 = NONEV⌝ ∗ φ ∨
    ∃ (v v' : val), ⌜o1 = SOMEV v⌝ ∗ ⌜o2 = SOMEV v'⌝ ∗
    Ψ v v')) -∗
  φ -∗
  REL do_until f' << do_until f : Ψ.
Proof.
iIntros "#Hf Hφ". iLöb as "IH".
rel_rec_l; rel_rec_r.
rel_bind_l (f' _); rel_bind_r (f _).
iApply (refines_bind with "[Hφ] []").
by iApply "Hf".
iIntros (v v') "Hv" => /=.
iDestruct "Hv" as "[(-> & -> & Hφ)| (%v1 & %v2 & -> & -> & HΨ)]";
rel_pures_l; rel_pures_r; first by iApply "IH".
rel_values.
Qed.

Lemma rel_do_until' (f f' : val) Ψ :
  □ (REL f' #() << f #() : (fun o1 o2 =>
    ⌜o1 = NONEV⌝ ∗ ⌜o2 = NONEV⌝ ∨
    ∃ (v v' : val), ⌜o1 = SOMEV v⌝ ∗ ⌜o2 = SOMEV v'⌝ ∗
    Ψ v v')) -∗
  REL do_until f' << do_until f : Ψ.
Proof.
iIntros "#Hf".
iApply (rel_do_until _ _ True%I) => //.
iIntros "!> _".
iApply refines_wand => //.
iIntros (v v') "[(-> & ->)|(%v1 & %v2 & HΨ)]"; eauto.
Qed.

End DoUntil.

Section Ordered.

Context {A : Type}.
Context (R : relation A)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{A}) R}.
Context `{!Repr A, !relocG Σ}.

Implicit Types (x y z : A) (l : list A).

Lemma rel_insert_sorted_l E K e (f : val) x l Ψ :
  StronglySorted R l →
  (∀ K y z,
     (REL fill K (#(bool_decide (R y z)) : expr) << e @ E : Ψ) -∗
     REL fill K (f (repr y) (repr z)) << e @ E : Ψ) →
  (∀ l', ⌜StronglySorted R l'⌝ -∗ ⌜l' ≡ₚ x :: l⌝ -∗
         REL fill K (repr l' : expr) << e @ E : Ψ) -∗
  REL fill K (insert_sorted f (repr x) (repr l)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal => sorted_l rel_f.
elim: l sorted_l K => [|y l IH] sorted_l K /=; iIntros "post";
  rel_rec_l; rel_pures_l.
- iApply ("post" $! [x]); iPureIntro; last done.
  by repeat constructor.
- move: (sorted_l) => /StronglySorted_cons [Ry_l sorted_l'].
  move/(_ sorted_l') in IH.
  rel_bind_l (f _ _). iApply (rel_f _ x y).
  case: (bool_decide_reflect (R x y)) => [Rxy|nRxy] /=; rel_pures_l.
  + iApply ("post" $! (x :: y :: l)); iPureIntro; last done.
    apply/StronglySorted_cons; split; last exact: sorted_l.
    constructor; first exact: Rxy.
    apply: (Forall_impl _ _ _ Ry_l) => z Ryz; exact: (transitivity Rxy Ryz).
  + rel_bind_l (insert_sorted _ _ _). iApply IH.
    iIntros (l') "%ss' %perm'". rewrite /=. rel_pures_l.
    iApply ("post" $! (y :: l')); iPureIntro; last first.
      by rewrite perm'; exact: Permutation_swap.
    apply/StronglySorted_cons; split; last exact: ss'.
    apply/Forall_forall => z; rewrite perm' elem_of_cons => - [->|z_l].
      exact: (total_not _ _ nRxy).
    by move/Forall_forall: Ry_l; apply.
Qed.

Lemma rel_insert_sorted_r E K e (f : val) x l Ψ :
  ↑specN ⊆ E →
  StronglySorted R l →
  (∀ K y z,
     (REL e << fill K (#(bool_decide (R y z)) : expr) @ E : Ψ) -∗
     REL e << fill K (f (repr y) (repr z)) @ E : Ψ) →
  (∀ l', ⌜StronglySorted R l'⌝ -∗ ⌜l' ≡ₚ x :: l⌝ -∗
         REL e << fill K (repr l' : expr) @ E : Ψ) -∗
  REL e << fill K (insert_sorted f (repr x) (repr l)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal => sorted_l rel_f.
elim: l sorted_l K => [|y l IH] sorted_l K /=; iIntros "post";
  rel_rec_r; rel_pures_r.
- iApply ("post" $! [x]); iPureIntro; last done.
  by repeat constructor.
- move: (sorted_l) => /StronglySorted_cons [Ry_l sorted_l'].
  move/(_ sorted_l') in IH.
  rel_bind_r (f _ _). iApply (rel_f _ x y).
  case: (bool_decide_reflect (R x y)) => [Rxy|nRxy] /=; rel_pures_r.
  + iApply ("post" $! (x :: y :: l)); iPureIntro; last done.
    apply/StronglySorted_cons; split; last exact: sorted_l.
    constructor; first exact: Rxy.
    apply: (Forall_impl _ _ _ Ry_l) => z Ryz; exact: (transitivity Rxy Ryz).
  + rel_bind_r (insert_sorted _ _ _). iApply IH.
    iIntros (l') "%ss' %perm'". rewrite /=. rel_pures_r.
    iApply ("post" $! (y :: l')); iPureIntro; last first.
      by rewrite perm'; exact: Permutation_swap.
    apply/StronglySorted_cons; split; last exact: ss'.
    apply/Forall_forall => z; rewrite perm' elem_of_cons => - [->|z_l].
      exact: (total_not _ _ nRxy).
    by move/Forall_forall: Ry_l; apply.
Qed.

Lemma rel_insertion_sort_l E K e (f : val) l Ψ :
  (∀ K x y,
     (REL fill K (#(bool_decide (R x y)) : expr) << e @ E : Ψ) -∗
     REL fill K (f (repr x) (repr y)) << e @ E : Ψ) →
  (REL fill K (repr (merge_sort R l) : expr) << e @ E : Ψ) -∗
  REL fill K (insertion_sort f (repr l)) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal => rel_f.
elim: l K => [|y l IH] K; iIntros "post"; rel_rec_l; rel_pures_l.
- by iApply "post".
- rel_bind_l (insertion_sort _ _). iApply IH.
  rewrite /= -repr_list_unseal.
  rel_apply_l (rel_insert_sorted_l _ _ _ _ _ _ _ (merge_sort_sorted R l) rel_f).
  iIntros (l') "%ss' %perm'".
  have -> : merge_sort R (y :: l) = l'.
    apply: (StronglySorted_unique R); [exact: merge_sort_sorted|exact: ss'|].
    by rewrite merge_sort_Permutation perm' merge_sort_Permutation.
  by iApply "post".
Qed.

Lemma rel_insertion_sort_r E K e (f : val) l Ψ :
  ↑specN ⊆ E →
  (∀ K x y,
     (REL e << fill K (#(bool_decide (R x y)) : expr) @ E : Ψ) -∗
     REL e << fill K (f (repr x) (repr y)) @ E : Ψ) →
  (REL e << fill K (repr (merge_sort R l) : expr) @ E : Ψ) -∗
  REL e << fill K (insertion_sort f (repr l)) @ E : Ψ.
Proof.
move=> HE. rewrite /= repr_list_unseal => rel_f.
elim: l K => [|y l IH] K; iIntros "post"; rel_rec_r; rel_pures_r.
- by iApply "post".
- rel_bind_r (insertion_sort _ _). iApply IH.
  rewrite /= -repr_list_unseal.
  rel_apply_r (rel_insert_sorted_r _ _ _ _ _ _ _ HE (merge_sort_sorted R l) rel_f).
  iIntros (l') "%ss' %perm'".
  have -> : merge_sort R (y :: l) = l'.
    apply: (StronglySorted_unique R); [exact: merge_sort_sorted|exact: ss'|].
    by rewrite merge_sort_Permutation perm' merge_sort_Permutation.
  by iApply "post".
Qed.

End Ordered.

Section Lexicographic.

Context `{!EqDecision A, !Lexico A,
          !StrictOrder (@lexico A _), !TrichotomyT (@lexico A _),
          !Repr A, !relocG Σ}.

Implicit Types (x : A) (l : list A).

Lemma rel_leq_list_l E K e (feq fle : val) l1 l2 Ψ :
  (∀ K x1 x2,
     (REL fill K (#(bool_decide (x1 = x2)) : expr) << e @ E : Ψ) -∗
     REL fill K (feq (repr x1) (repr x2)) << e @ E : Ψ) →
  (∀ K x1 x2, x1 ∈ l1 →
     (REL fill K (#(bool_decide (x1 = x2 ∨ lexico x1 x2)) : expr) << e @ E : Ψ) -∗
     REL fill K (fle (repr x1) (repr x2)) << e @ E : Ψ) →
  (REL fill K (#(bool_decide (l1 = l2 ∨ lexico l1 l2)) : expr) << e @ E : Ψ) -∗
  REL fill K (leq_list feq fle (repr l1) (repr l2)) << e @ E : Ψ.
Proof.
move=> rel_feq. rewrite /= repr_list_unseal.
elim: l1 l2 K => [|x1 l1 IH] [|x2 l2] K rel_fle; iIntros "post";
  rel_rec_l; rel_pures_l; rewrite bool_decide_lexico_le; try by iApply "post".
rel_bind_l (feq _ _). iApply (rel_feq _ x1 x2).
case: (bool_decide_reflect (x1 = x2)) => [ex|ne] /=; rel_pures_l.
- iApply (IH with "post") => K' x1' x2' x1'_in; apply: rel_fle.
  by apply: list_elem_of_further.
- by iApply (rel_fle _ _ _ (list_elem_of_here x1 l1) with "post").
Qed.

Lemma rel_leq_list_r E K e (feq fle : val) l1 l2 Ψ :
  ↑specN ⊆ E →
  (∀ K x1 x2,
     (REL e << fill K (#(bool_decide (x1 = x2)) : expr) @ E : Ψ) -∗
     REL e << fill K (feq (repr x1) (repr x2)) @ E : Ψ) →
  (∀ K x1 x2, x1 ∈ l1 →
     (REL e << fill K (#(bool_decide (x1 = x2 ∨ lexico x1 x2)) : expr) @ E : Ψ) -∗
     REL e << fill K (fle (repr x1) (repr x2)) @ E : Ψ) →
  (REL e << fill K (#(bool_decide (l1 = l2 ∨ lexico l1 l2)) : expr) @ E : Ψ) -∗
  REL e << fill K (leq_list feq fle (repr l1) (repr l2)) @ E : Ψ.
Proof.
move=> HE rel_feq. rewrite /= repr_list_unseal.
elim: l1 l2 K => [|x1 l1 IH] [|x2 l2] K rel_fle; iIntros "post";
  rel_rec_r; rel_pures_r; rewrite bool_decide_lexico_le; try by iApply "post".
rel_bind_r (feq _ _). iApply (rel_feq _ x1 x2).
case: (bool_decide_reflect (x1 = x2)) => [ex|ne] /=; rel_pures_r.
- iApply (IH with "post") => K' x1' x2' x1'_in; apply: rel_fle.
  by apply: list_elem_of_further.
- by iApply (rel_fle _ _ _ (list_elem_of_here x1 l1) with "post").
Qed.

End Lexicographic.
