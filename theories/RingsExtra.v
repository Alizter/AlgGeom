From HoTT Require Import Basics Types Algebra.Rings.

(** * Extra lemmas about rings *)

(** These should probably go in the main library. *)

Section ExtraLemmas.

  Context {R : CRing} (x y z : R).

  Lemma rng_mult_move_left_assoc : x * y * z = y * x * z.
  Proof.
    f_ap; apply rng_mult_comm.
  Defined.

  Lemma rng_mult_move_right_assoc : x * (y * z) = y * (x * z).
  Proof.
    refine (rng_mult_assoc _ _ _ @ _ @ (rng_mult_assoc _ _ _)^).
    apply rng_mult_move_left_assoc.
  Defined.

  Definition rng_negate_plus : - (x + y) = - x - y := negate_plus_distr _ _.

  Definition rng_negate_zero : - 0 = 0 :> R := negate_0.

  Lemma rng_dist_l_negate : x * (y - z) = x * y - x * z.
  Proof.
    by rewrite rng_dist_l, rng_mult_negate_r.
  Defined.

End ExtraLemmas.
