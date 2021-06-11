From HoTT Require Import Basics Types Algebra.Rings Spaces.Nat.
From HoTT Require Import Colimits.Quotient.
Require Import Invertible.
Require Import RingsExtra.

Local Open Scope nat_scope.
Local Open Scope mc_scope.

(** * Localization of rings *)

(** ** Multiplicative subsets *)

(** *** Definitions *)

(** Multiplicative subsets of a ring [R] consist of: *)
Class IsMultiplicativeSubset {R : CRing} (S : R -> Type) : Type := {
  (** Being a hprop *)
  mss_ishprop : forall x, IsHProp (S x) ;
  (** Contains one *)
  mss_one : S 1 ;
  (** Closed under multiplication *)
  mss_mult : forall x y, S x -> S y -> S (x * y) ;
}.

Arguments mss_one {R _ _}.
Arguments mss_mult {R _ _ _ _}.

(** *** Examples *)

(** The multplicative subset of powers of a ring element. *)
Global Instance ismultiplicative_powers (R : CRing) (x : R)
  : IsMultiplicativeSubset (fun r => hexists (fun n : nat => rng_power x n = r)).
Proof.
  srapply Build_IsMultiplicativeSubset.
  1: by apply tr; exists 0%nat.
  intros a b np mq.
  strip_truncations.
  destruct np as [n p], mq as [m q].
  apply tr; exists (n + m)%nat.
  refine ((rng_power_mult_law _ _ _)^ @ _).
  f_ap.
Defined.

(** Invertible elements of a ring form a multiplicative subset. *)
Global Instance ismultiplicative_isinvertible (R : CRing)
  : IsMultiplicativeSubset (@IsInvertible R) := {}.

(** TODO: Property of being a localization. *)

(** ** Construction of localization. *)

Section Localization.

  (** We now construct the localization of a ring at a multiplicative subset as the following HIT:
  
  HIT Localization_type (R : CRing) (S : R -> Type)
    `{IsMultiplicativeSubset R} :=
  | loc_frac (n d : R) (p : S d) : Localization R S
  | loc_frac_eq (n1 d1 n2 d2 : R) (p1 : S d1) (p2 : S d2)
      (x : R) (q : S x) (r : x * (d2 * n1 - n2 * d1) = 0)
      : loc_frac n1 d1 p1 = loc_frac n2 d2 p2
  .
  *)

  Context (R : CRing) (S : R -> Type) `{!IsMultiplicativeSubset S}.

  (** *** Construction of underlying Localization type *)

  Record Fraction := {
    numerator : R ;
    denominator : R ;
    in_mult_subset_denominator : S denominator ;
  }.

  Definition fraction_eq : Relation Fraction.
  Proof.
    intros [n1 d1 ?] [n2 d2 ?].
    refine (exists (x : R), S x /\ _).
    exact (x * (n1 * d2 - n2 * d1) = 0).
  Defined.

  (** It is convenient to produce elements of this relation specalised to when the scaling factor is 1 *)
  Lemma fraction_eq_simple f1 f2
    (p : numerator f1 * denominator f2 = numerator f2 * denominator f1)
    : fraction_eq f1 f2.
  Proof.
    exists 1.
    refine (mss_one ,_).
    refine (rng_mult_one_l _ @ _).
    by apply rng_moveL_0M^-1.
  Defined.

  Lemma fraction_eq_refl f1 : fraction_eq f1 f1.
  Proof.
    apply fraction_eq_simple.
    reflexivity.
  Defined.

  Definition Localization_type : Type := Quotient fraction_eq.

  Definition loc_frac : Fraction -> Localization_type
    := class_of fraction_eq.

  Definition loc_frac_eq {f1 f2 : Fraction} (p : fraction_eq f1 f2)
    : loc_frac f1 = loc_frac f2
    := qglue p.

  Definition Localization_type_ind (Q : Localization_type -> Type)
    `{forall x, IsHSet (Q x)}
    (frac : forall f, Q (loc_frac f))
    (eq : forall f1 f2 p, loc_frac_eq p # frac f1 = frac f2)
    : forall x, Q x
    := Quotient_ind _ Q frac eq.

  Definition Localization_type_ind_hprop (Q : Localization_type -> Type)
    `{forall x, IsHProp (Q x)} (f : forall f, Q (loc_frac f))
    : forall x, Q x
    := Quotient_ind_hprop _ Q f.

  Definition Localization_type_rec (Q : Type) `{IsHSet Q}
    (f : Fraction -> Q)
    (t : forall f1 f2, fraction_eq f1 f2 -> f f1 = f f2)
    : Localization_type -> Q
    := Quotient_rec _ Q f t.

  Arguments loc_frac : simpl never.
  Arguments loc_frac_eq : simpl never.

  (** Now that we have defined the HIT as above, we can define the ring structure. *)

  (** *** Addition operation *)

  (** Fraction addition *)
  Definition frac_add : Fraction -> Fraction -> Fraction :=
    fun '(Build_Fraction n1 d1 p1) '(Build_Fraction n2 d2 p2)
      => Build_Fraction (n1 * d2 + n2 * d1) (d1 * d2) (mss_mult p1 p2).

  (** Fraction addition is well-defined upto equality of fractions. *)

  (** It is easier to prove well-definedness of both arguments at once. *)
  Lemma frac_add_wd (f1 f1' f2 f2' : Fraction)
    (p : fraction_eq f1 f1') (q : fraction_eq f2 f2')
    : fraction_eq (frac_add f1 f2) (frac_add f1' f2').
  Proof.
    destruct f1 as [a s ss], f1' as [a' s' ss'],
      f2 as [b t st], f2' as [b' t' st'],
      p as [x [sx p]], q as [y [sy q]].
    refine (x * y ; (mss_mult sx sy, _)).
    simpl.
    rewrite rng_dist_l_negate.
    rewrite 2 rng_dist_r.
    rewrite 2 rng_dist_l.
    rewrite <- rng_plus_assoc.
    rewrite (rng_plus_comm _ (- _)).
    rewrite rng_negate_plus.
    rewrite 2 rng_plus_assoc.
    rewrite <- (rng_plus_assoc _ (- _)).
    rewrite (rng_plus_comm (- _)).
    rewrite <- 2 rng_dist_l_negate.
    rewrite <- ? rng_mult_assoc.
    rewrite 2 (rng_mult_move_right_assoc a').
    rewrite (rng_mult_comm a' t).
    rewrite (rng_mult_move_right_assoc s).
    rewrite (rng_mult_comm s a').
    rewrite (rng_mult_move_right_assoc t).
    rewrite (rng_mult_comm t t').
    rewrite <- 2 (rng_mult_move_right_assoc t').
    rewrite <- (rng_dist_l_negate t').
    rewrite (rng_mult_comm _ t).
    rewrite (rng_mult_move_right_assoc _ t).
    rewrite <- (rng_dist_l_negate t).
    rewrite <- 2 (rng_mult_move_right_assoc t').
    rewrite <- 2 (rng_mult_move_right_assoc t).
    rewrite (rng_mult_move_right_assoc x).
    rewrite p.
    rewrite 3 rng_mult_zero_r.
    rewrite rng_plus_zero_l.
    rewrite 2 (rng_mult_move_right_assoc b).
    rewrite 2 (rng_mult_move_right_assoc b').
    rewrite (rng_mult_move_right_assoc s).
    rewrite <- 2 rng_dist_l_negate.
    rewrite 2 (rng_mult_move_right_assoc y).
    rewrite q.
    by rewrite 3 rng_mult_zero_r.
  Qed.

  Lemma frac_add_wd_l (f1 f1' f2 : Fraction) (p : fraction_eq f1 f1')
    : fraction_eq (frac_add f1 f2) (frac_add f1' f2).
  Proof.
    pose (fraction_eq_refl f2).
    by apply frac_add_wd.
  Defined.

  Lemma frac_add_wd_r (f1 f2 f2' : Fraction) (p : fraction_eq f2 f2')
    : fraction_eq (frac_add f1 f2) (frac_add f1 f2').
  Proof.
    pose (fraction_eq_refl f1).
    by apply frac_add_wd.
  Defined.

  (** The addition operation for fractions is the usual fraction addition. Most of the work is spent showing that this is well-defined. *)
  Instance plus_localization_type : Plus Localization_type.
  Proof.
    intros x; srapply Localization_type_rec.
    { intros f2; revert x.
      srapply Localization_type_rec.
      { intros f1.
        apply loc_frac.
        exact (frac_add f1 f2). }
      intros f1 f1' p.
      by apply loc_frac_eq, frac_add_wd_l. }
    intros f2 f2' p; revert x; cbn.
    srapply Localization_type_ind_hprop.
    intros f1.
    by apply loc_frac_eq, frac_add_wd_r.
  Defined.

  (** *** Multiplication operation *)

  Definition frac_mult : Fraction -> Fraction -> Fraction :=
    fun '(Build_Fraction n1 d1 p1) '(Build_Fraction n2 d2 p2)
      => Build_Fraction (n1 * n2) (d1 * d2) (mss_mult p1 p2).

  Lemma frac_mult_wd_l f1 f1' f2 (p : fraction_eq f1 f1')
    : fraction_eq (frac_mult f1 f2) (frac_mult f1' f2).
  Proof.
    destruct p as [x [s p]].
    refine (x; (s, _)); simpl.
    rewrite rng_dist_l.
    rewrite rng_dist_l in p.
    rewrite rng_mult_negate_r.
    rewrite rng_mult_negate_r in p.
    apply rng_moveL_0M in p.
    apply rng_moveL_0M^-1.
    rewrite 2 (rng_mult_comm _ (numerator f2)).
    rewrite 2 (rng_mult_comm _ (denominator f2)).
    rewrite <- 2 (rng_mult_assoc (numerator f2)).
    rewrite 2 (rng_mult_comm (numerator _) (denominator f2 * _)).
    rewrite ? (rng_mult_assoc (numerator f2)).
    rewrite <- ? (rng_mult_assoc (numerator f2 * denominator f2)).
    rewrite 2 (rng_mult_comm (denominator _) (numerator _)).
    rewrite 2 (rng_mult_comm (numerator f2 * denominator f2)).
    rewrite 2 (rng_mult_assoc x (numerator _ * denominator _)).
    f_ap.
  Defined.

  Lemma frac_mult_wd_r f1 f2 f2' (p : fraction_eq f2 f2')
    : fraction_eq (frac_mult f1 f2) (frac_mult f1 f2').
  Proof.
    destruct p as [x [s p]].
    refine (x; (s, _)); simpl.
    rewrite rng_dist_l.
    rewrite rng_dist_l in p.
    rewrite rng_mult_negate_r.
    rewrite rng_mult_negate_r in p.
    apply rng_moveL_0M in p.
    apply rng_moveL_0M^-1.
    rewrite 2 (rng_mult_comm (numerator f1)).
    rewrite <- 2 rng_mult_assoc.
    rewrite 2 (rng_mult_comm (numerator f1)).
    rewrite <- ? rng_mult_assoc.
    rewrite 2 (rng_mult_move_right_assoc (denominator f1)).
    rewrite ? rng_mult_assoc.
    rewrite ? rng_mult_assoc in p.
    do 2 f_ap.
  Defined.

  Instance mult_localization_type : Mult Localization_type.
  Proof.
    intros x; srapply Localization_type_rec.
    { intros f2; revert x.
      srapply Localization_type_rec.
      { intros f1.
        apply loc_frac.
        exact (frac_mult f1 f2). }
      intros f1 f1' p.
      by apply loc_frac_eq, frac_mult_wd_l. }
    intros f2 f2' p; revert x.
    srapply Localization_type_ind_hprop.
    intros f1.
    by apply loc_frac_eq, frac_mult_wd_r.
  Defined.

  (** *** Zero element *)

  Instance zero_localization_type : Zero Localization_type :=
    loc_frac (Build_Fraction 0 1 mss_one).

  (** *** One element *)

  Instance one_localization_type : One Localization_type :=
    loc_frac (Build_Fraction 1 1 mss_one).

  (** *** Negation operation *)

  Definition frac_negate : Fraction -> Fraction :=
    fun '(Build_Fraction n d p) => Build_Fraction (- n) d p.

  Lemma frac_negate_wd f1 f2 (p : fraction_eq f1 f2)
    : fraction_eq (frac_negate f1) (frac_negate f2).
  Proof.
    destruct p as [x [s p]].
    refine (x; (s,_)); simpl.
    rewrite 2 rng_mult_negate_l.
    rewrite <- rng_negate_plus.
    rewrite rng_mult_negate_r.
    rewrite p.
    apply rng_negate_zero.
  Defined.

  Instance negate_localization_type : Negate Localization_type.
  Proof.
    srapply Localization_type_rec.
    { intros f.
      apply loc_frac.
      exact (frac_negate f). }
    intros f1 f2 p.
    by apply loc_frac_eq, frac_negate_wd.
  Defined.

  (** *** Ring laws *)

  (** Left additive identity *)
  Instance leftidentity_plus_localization_type
    : LeftIdentity plus_localization_type zero_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap.
    - rewrite rng_mult_zero_l.
      rewrite rng_plus_zero_l.
      apply rng_mult_one_r.
    - symmetry.
      apply rng_mult_one_l.
  Defined.

  Instance rightidentity_plus_localization_type
    : RightIdentity plus_localization_type zero_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap.
    - rewrite rng_mult_zero_l.
      rewrite rng_plus_zero_r.
      apply rng_mult_one_r.
    - symmetry.
      apply rng_mult_one_r.
  Defined.

  Instance leftinverse_plus_localization_type
    : LeftInverse plus_localization_type negate_localization_type zero_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    refine (rng_mult_one_r _ @ _).
    refine (_ @ (rng_mult_zero_l _)^).
    rewrite rng_mult_negate_l.
    apply rng_plus_negate_l.
  Defined.

  Instance rightinverse_plus_localization_type
    : RightInverse plus_localization_type negate_localization_type zero_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    refine (rng_mult_one_r _ @ _).
    refine (_ @ (rng_mult_zero_l _)^).
    rewrite rng_mult_negate_l.
    apply rng_plus_negate_r.
  Defined.

  Instance associative_plus_localization_type
    : Associative plus_localization_type.
  Proof.
    intros x y; srapply Localization_type_ind_hprop; intros z; revert y.
    srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple.
    simpl.
    rewrite ? rng_dist_r.
    rewrite ? rng_mult_assoc.
    rewrite ? rng_plus_assoc.
    do 4 f_ap.
    all: rewrite <- ? rng_mult_assoc.
    all: f_ap.
    2: apply rng_mult_comm.
    rewrite rng_mult_assoc.
    apply rng_mult_comm.
  Defined.

  Instance commutative_plus_localization_type
    : Commutative plus_localization_type.
  Proof.
    intros x; srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    rewrite (rng_mult_comm (denominator y) (denominator x)).
    f_ap; apply rng_plus_comm.
  Defined.

  Instance leftidentity_mult_localization_type
    : LeftIdentity mult_localization_type one_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap; [|symmetry]; apply rng_mult_one_l.
  Defined.

  Instance rightidentity_mult_localization_type
    : RightIdentity mult_localization_type one_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap; [|symmetry]; apply rng_mult_one_r.
  Defined.

  Instance associative_mult_localization_type
    : Associative mult_localization_type.
  Proof.
    intros x y; srapply Localization_type_ind_hprop; intros z; revert y.
    srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple.
    f_ap; [|symmetry]; apply rng_mult_assoc.
  Defined.

  Instance commutative_mult_localization_type
    : Commutative mult_localization_type.
  Proof.
    intros x; srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap; rapply rng_mult_comm.
  Defined.

  Instance leftdistribute_localization_type
    : LeftDistribute mult_localization_type plus_localization_type.
  Proof.
    intros x y; srapply Localization_type_ind_hprop; intros z; revert y.
    srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple.
    simpl.
    rewrite ? rng_dist_l, ? rng_dist_r.
    rewrite ? rng_mult_assoc.
    do 2 f_ap.
    all: rewrite <- ? rng_mult_assoc.
    all: do 2 f_ap.
    all: rewrite ? rng_mult_assoc.
    all: rewrite (rng_mult_comm (_ x)).
    all: rewrite <- ? rng_mult_assoc.
    all: f_ap.
    all: rewrite (rng_mult_comm _ (_ y)).
    all: rewrite <- ? rng_mult_assoc.
    all: f_ap.
  Defined.

  Instance isring_localization_type : IsRing Localization_type
    := ltac:(repeat split; exact _).

  Definition RingLocalization : CRing :=
    Build_CRing Localization_type _ _ _ _ _ _.

End Localization.

(** TODO: Show construction is a localization. *)
