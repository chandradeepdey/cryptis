(** Generic ReLoC lemmas that are missing upstream.  Nothing here is specific
    to Cryptis; the file only depends on ReLoC itself. *)

From reloc Require Import reloc.

Section Refines.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types A : val → val → iProp Σ.

(** [refines_bind] with the postcondition of the prefix spelled out as a
    refinement of the continuations. *)
Lemma refines_bind' K K' E A (e e' : expr) :
  (REL e << e' @ E : λ v v',
              (REL fill K (of_val v) << fill K' (of_val v') : A)) -∗
  REL fill K e << fill K' e' @ E : A.
Proof.
iIntros "H".
iApply (refines_bind with "H").
eauto.
Qed.

(** Reduce the left-hand side [e] to [e'] using a WP-level implication.
    Unlike [refines_wp_l], [e'] need not be a value and the mask is
    arbitrary; this lets us reuse unary [wp_*] lemmas whose result is an
    expression (e.g. [wp_list_match]). *)
Lemma refines_wp_l_gen E K (e e' : expr) t A :
  (∀ Φ, WP e' {{ Φ }} ⊢ WP e {{ Φ }}) →
  (REL fill K e' << t @ E : A) -∗
  REL fill K e << t @ E : A.
Proof.
move=> Hwp. rewrite refines_eq /refines_def.
iIntros "H %j Hj". iMod ("H" with "Hj") as "H". iModIntro.
iApply wp_bind. iApply Hwp. by iApply wp_bind_inv.
Qed.

(** Reduce the right-hand side [e] to [e'] using an update on the
    specification thread.  Unlike [refines_step_r], [e'] need not be a
    value. *)
Lemma refines_step_r_gen E K (e e' : expr) t A :
  (∀ k, refines_right k e ={E}=∗ refines_right k e') -∗
  (REL t << fill K e' @ E : A) -∗
  REL t << fill K e @ E : A.
Proof.
rewrite refines_eq /refines_def.
iIntros "Hstep H %j Hj /=". rewrite refines_right_bind.
iMod ("Hstep" with "Hj") as "Hj". rewrite -refines_right_bind.
by iApply "H".
Qed.

End Refines.
