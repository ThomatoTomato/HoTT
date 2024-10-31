Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Sequence.
Require Import WildCat.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Types.
Require Import PushoutPath.Interleaving.

(** * Work towards characterizing the path types in a pushout of a span [R : A -> B -> Type]. *)

(** The goal here is to work in half-steps, so that each construction only happens once. *)

(** [C] will be used to denote a type that might be [A] or [B].  We think of a term of [Family C] as being the family [fun c => a0 squiggle_t c]. *)
Definition Family (C : Type) := C -> Type.

(** Here [P a] should be thought of as [a_0 squiggle_t a] and [Q b] as [a_0 squiggle_{t+1} b].  This describes the type of the "dot" operation [- ._t -]. This will also be used with [A] and [B] swapped and [R] flipped. *)
Definition Dot {A B : Type} (R : A -> B -> Type) (P : Family A) (Q : Family B)
  := forall (a : A) (b : B) (r : R a b) (p : P a), Q b.

Section InductiveStep.

  (** Given two families [P] and [Q] and a dot map from [P] to [Q], we define one more family [P'], a stage map from [Q] to [P'] (relative to the flipped relation), and a fiberwise map iota from [P] to [P']. Note that [flip R] has type [B -> A -> Type]. *)

  Context {A B : Type} (R : A -> B -> Type).
  Context {P : Family A} {Q : Family B} (dot : Dot R P Q).

  (** We define the new type family as the pushout. *)
  Definition family_step : Family A.
  Proof.
    intro a.
    snrapply (@Pushout ({b : B & R a b} * P a) (P a) {b : B & (R a b * Q b)}).
    - exact snd.
    - intros [[b r] p].
      exact (b; (r, dot a b r p)).
  Defined.

  (** We define the next "dot" map as [pushr]. *)
  Definition dot_step : Dot (flip R) Q family_step
:= fun b a r q => pushr (b; (r, q)).

  (** We define iota as [pushl]. *)
  Definition iota_step : forall a, P a -> family_step a
    := fun a p => pushl p.

  (** We define the homotopy showing that the composition of the two dot maps is iota. *)
  Definition homotopy_step : forall (a : A) (b : B) (r : R a b), 
    (iota_step a) == (dot_step b a r) o (dot a b r) 
    := fun a b r p => (pglue ((b ; r) , p)).
End InductiveStep.

Section Sequence.
  Context {A B : Type} (R : A -> B -> Type) (a0 : A).

  (** Use a record type for a full step to avoid the interleaved sequence and `flip R`. *)
  Record zigzag_type : Type := {
    Pp : A -> Type; (** Stored from previous step *)
    Qp : B -> Type; (** Stored from previous step *)
    glueQPp (b : B) (a : A) (r : R a b) (q : Qp b) : Pp a; (** Stored from previous step *)
    Q : B -> Type; (** Paths of length t *)
    gluePQ (a : A) (b : B) (r : R a b) (p : Pp a) : Q b; (** t-1 -> t *)
    iotaQ (b : B) (x : Qp b) : Q b; (** t-2 -> t *)
    P : A -> Type; (** Paths of length t+1 *)
    glueQP (b : B) (a : A) (r : R a b) (q : Q b) : P a; (** t -> t+1 *)
    iotaP (a : A) (x : Pp a) : P a; (** t-1 -> t+1 *)
    glueQPQ (b : B) (a : A) (r : R a b) 
      : iotaQ b == (gluePQ a b r) o (glueQPp b a r);
    gluePQP (a : A) (b : B) (r : R a b) 
      : iotaP a == (glueQP b a r) o (gluePQ a b r);
  }.

  Definition zigzag_step : zigzag_type -> zigzag_type.
  Proof.
    intro z.
    destruct z.
    (* Naming them all seems to be necessary for Coq to not reorder goals. *)
  snrapply (let Pp:=_ in let Qp :=_ in let glueQPp :=_ in let Q:=_ in let gluePQ:=_ in let iotaQ:=_ in let P:=_ in let glueQP:=_ in let iotaP:=_ in let glueQPQ:=_ in let gluePQP:=_ in Build_zigzag_type Pp Qp glueQPp Q gluePQ iotaQ P glueQP iotaP glueQPQ gluePQP).
    - exact P0.
    - exact Q0.
    - exact glueQP0.
    - exact (family_step (flip R) glueQP0).
    - exact (dot_step (flip R) glueQP0).
    - exact (iota_step (flip R) glueQP0).
    - exact (family_step R gluePQ).
    - exact (dot_step R gluePQ).
    - exact (iota_step R gluePQ).
    - exact (homotopy_step (flip R) glueQP0).
    - exact (homotopy_step R gluePQ).
  Defined.

  Definition identity_zigzag_initial : zigzag_type.
  Proof.
    snrapply Build_zigzag_type.
    - exact (fun a => Empty).
    - exact (fun b => Empty).
    - intros b a r q; destruct q.
    - exact (fun b => Empty). (** Define Q0 := Empty *)
    - intros a b r q; destruct q.
    - intros b q; destruct q.
    - exact (fun a => a0 = a). (** Define P0 := Id a0 *)
    - intros b a r q; destruct q. (** Define Q0 -> P_0 *)
    - intros a q; destruct q. (** Define P_{-1} -> P0 *)
    - intros; intro q; destruct q.
    - intros; intro q; destruct q.
  Defined.

  Definition identity_zigzag : nat -> zigzag_type
    := fun n => nat_iter n zigzag_step identity_zigzag_initial.

  Definition identity_zigzag_P : A -> Sequence.
  Proof.
    intro a.
    snrapply Build_Sequence.
    - intro n; exact ((identity_zigzag n).(P) a).
    - intro n; exact ((identity_zigzag (S n)).(iotaP) a).
  Defined.

  Definition identity_zigzag_Q : B -> Sequence.
  Proof.
    intro b.
    snrapply Build_Sequence.
    - intro n; exact ((identity_zigzag n).(Q) b).
    - intro n; exact ((identity_zigzag (S n)).(iotaQ) b).
  Defined.

  Definition identity_zigzag_gluePQ {a : A} {b : B} (r : R a b) (n : nat)
    : identity_zigzag_P a n -> identity_zigzag_Q b (S n)
    := (identity_zigzag (S n)).(gluePQ) a b r.

  Definition identity_zigzag_glueQP {a : A} {b : B} (r : R a b) (n : nat)
    : identity_zigzag_Q b n -> identity_zigzag_P a n
    := (identity_zigzag n).(glueQP) b a r.

  Definition identity_zigzag_gluePQP {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : identity_zigzag_P a n) => x^+) == identity_zigzag_glueQP r (S n) o identity_zigzag_gluePQ r n
    := (identity_zigzag (S n)).(gluePQP) a b r.

  Definition identity_zigzag_glueQPQ {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : identity_zigzag_Q b n) => x^+) == identity_zigzag_gluePQ r n o identity_zigzag_glueQP r n
    := (identity_zigzag (S n)).(glueQPQ) b a r.

  Definition identity_zigzag_gluePQ_seq {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_P a) (succ_seq (identity_zigzag_Q b))
    := zigzag_glue_map_inv (identity_zigzag_glueQP r) (identity_zigzag_gluePQ r) (identity_zigzag_glueQPQ r) (identity_zigzag_gluePQP r).

  Definition identity_zigzag_glueQP_seq {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_Q b) (identity_zigzag_P a)
    := zigzag_glue_map (identity_zigzag_glueQP r) (identity_zigzag_gluePQ r) (identity_zigzag_glueQPQ r) (identity_zigzag_gluePQP r).

  (** The colimit of paths starting and ending in A. *)
  Definition identity_zigzag_Pinf (a : A) : Type
    := Colimit (identity_zigzag_P a).

  (** Our candidate for reflexivity: the colimit of reflexivity. *)
  Definition identity_zigzag_refl : identity_zigzag_Pinf a0
    := @colim _ (identity_zigzag_P a0) 0%nat idpath.

  (** The colimit of paths starting in A and ending in B. *)
  Definition identity_zigzag_Qinf (b : B) : Type 
    := Colimit (identity_zigzag_Q b).

  Context {a : A} {b : B} (r : R a b) `{Funext}.

  (** The gluing equivalence. *)
  Definition equiv_identity_zigzag_glueinf
    : (identity_zigzag_Qinf b) <~> (identity_zigzag_Pinf a)
    := equiv_interleaved_colim _ _ (identity_zigzag_glueQP r) (identity_zigzag_gluePQ r) (identity_zigzag_glueQPQ r) (identity_zigzag_gluePQP r).

  Definition identity_zigzag_gluePQinf : identity_zigzag_Pinf a -> identity_zigzag_Qinf b
    := (equiv_identity_zigzag_glueinf)^-1.

  Definition identity_zigzag_glueQPinf : identity_zigzag_Qinf b -> identity_zigzag_Pinf a
    := equiv_identity_zigzag_glueinf.

  Definition identity_zigzag_gluePQinf_comm 
    (n : nat) (p : identity_zigzag_P a n)
    : identity_zigzag_gluePQinf (@colim _ (identity_zigzag_P a) n p) = (@colim _ (identity_zigzag_Q b) (S n) (identity_zigzag_gluePQ r n p)).
  Proof.
  Admitted.
End Sequence.

Section ZigzagIdentity.
  Context {A : Type} {B : Type} (R : A -> B -> Type).

  Definition relation_total : Type
    := {x : A * B | R (fst x) (snd x)}.

  Definition relation_pushout : Type.
  Proof.
    snrapply Pushout.
    + exact relation_total.
    + exact A.
    + exact B.
    + exact (fst o pr1).
    + exact (snd o pr1).
  Defined.

  (** The candidate for the identity type. *)
  Context `{Univalence}.
  Definition identity_zigzag_family_half (a0 : A) 
    : relation_pushout -> Type.
  Proof.
    snrapply Pushout_rec.
    + intro a; exact (identity_zigzag_Pinf R a0 a).
    + intro b; exact (identity_zigzag_Qinf R a0 b).
    + intros [[a b] r].
      apply path_universe_uncurried.
      symmetry.
      exact (equiv_identity_zigzag_glueinf R a0 r).
  Defined.

  (** Contruct the half-induction principle from Kraus-von Raumer. *)
  Context (a0 : A) 
    (P : forall (a : A) (p : identity_zigzag_family_half a0 (pushl a)), Type)
    (Q : forall (b : B) (q : identity_zigzag_family_half a0 (pushr b)), Type)
    (r : P a0 (identity_zigzag_refl R a0))
    (e : forall (a : A) (b : B) (r : R a b) (p : identity_zigzag_family_half a0 (pushl a)), P a p <~> Q b (identity_zigzag_gluePQinf R a0 r p)).

  (** The equivalence involving the inverse gluing map. *)
  Let einv : forall (a : A) (b : B) (r : R a b) (q : identity_zigzag_family_half a0 (pushr b)), Q b q <~> P a (identity_zigzag_glueQPinf R a0 r q).
  Proof.
    intros a b r' q.
    symmetry.
    transitivity (Q b (identity_zigzag_gluePQinf R a0 r' (identity_zigzag_glueQPinf R a0 r' q))).
    + exact (e a b r' (identity_zigzag_glueQPinf R a0 r' q)).
    + exact (equiv_transport (fun x => Q b x) (eissect (equiv_identity_zigzag_glueinf R a0 r') q)).
  Defined.

  Let colimL {a : A} {n : nat} (p : identity_zigzag_P R a0 a n) : identity_zigzag_Pinf R a0 a
    := @colim _ (identity_zigzag_P R a0 a) n p.

  Let colimR {b : B} {n : nat} (q : identity_zigzag_Q R a0 b n) : identity_zigzag_Qinf R a0 b
    := @colim _ (identity_zigzag_Q R a0 b) n q.

  Record zigzag_identity_record (n : nat) : Type := {
    indR (b : B) (q : identity_zigzag_Q R a0 b n) : Q b (colimR q);
    indL (a : A) (p : identity_zigzag_P R a0 a n) : P a (colimL p);
  }.
  
  Definition zigzag_identity_ind (n : nat) : zigzag_identity_record n.
  Proof.
    induction n.
    + snrapply Build_zigzag_identity_record.
      - intros b [].
      - intros a p; destruct p; exact r.
    + destruct IHn as [indRp indLp].
      snrapply Build_zigzag_identity_record.
      - intro b.
        snrapply Pushout_ind.
        * (* Construct a map (p : a0 ~>n b) -> Q b (colim q^+) using indRp *)
          intro q.
          simpl.
          snrapply (transport (fun y => Q b y)). 
          1: exact (colimR q). 
          1: exact (@colimp _ (identity_zigzag_Q R a0 b) n (S n) idpath q)^.
          exact (indRp b q).
        * (* Construct a map (q : a0 ~>n+1 a) -> Q b (colim (p * r')) using indLp *)
          intros [a [r' p]].
          Check (e a b r' (colimL p)).

          

          
  Admitted.


