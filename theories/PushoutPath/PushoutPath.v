Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Sequence.
Require Import WildCat.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Graph.
Require Import Types.
Require Import PushoutPath.Interleaving.

(** * Work towards characterizing the path types in a pushout of a span [R : A -> B -> Type]. The goal here is to work in half-steps, so that each construction only happens once. [C] will be used to denote a type that might be [A] or [B].  We think of a term of [Family C] as being the family [fun c => a0 squiggle_t c]. *)
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

  (** Use a record type for a full step to avoid the interleaved sequence and [flip R]. *)
  (* jdc: rename to Zig? *)
  Record zigzag_type : Type := {
    P : Family A;
    Q : Family B;
    concatQP : Dot (flip R) Q P;
  }.

  Definition Qsucc (Z : zigzag_type) : Family B
    := family_step (flip R) (concatQP Z).

  Definition concatPQ (Z : zigzag_type) : Dot R (P Z) (Qsucc Z)
    := dot_step (flip R) (concatQP Z).

  Definition Psucc (Z : zigzag_type) : Family A
    := family_step R (concatPQ Z).

  Definition concatQPsucc (Z : zigzag_type) : Dot (flip R) (Qsucc Z) (Psucc Z)
    := dot_step R (concatPQ Z).

  Definition zigzag_step (Z : zigzag_type) : zigzag_type
    := Build_zigzag_type (Psucc Z) (Qsucc Z) (concatQPsucc Z).

  Definition identity_zigzag_initial : zigzag_type.
  Proof.
    snrapply Build_zigzag_type.
    - exact (fun a => a0 = a). (** Define [P0 := Id a0] *)
    - exact (fun b => Empty). (** Define [Q0 := Empty] *)
    - intros b a r q; destruct q. (** Define [Q0 -> P_0] *)
  Defined.

  Definition identity_zigzag : nat -> zigzag_type
    := fun n => nat_iter n zigzag_step identity_zigzag_initial.

  Definition identity_zigzag_P : A -> Sequence.
  Proof.
    intro a.
    snrapply Build_Sequence.
    - intro n; exact (P (identity_zigzag n) a).
    - intro n. cbn. apply iota_step.
  Defined.

  Definition identity_zigzag_Q : B -> Sequence.
  Proof.
    intro b.
    snrapply Build_Sequence.
    - intro n; exact (Q (identity_zigzag n) b).
    - intro n. cbn. apply iota_step.
  Defined.

  Definition identity_zigzag_gluePQ {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_P a) (succ_seq (identity_zigzag_Q b)).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatPQ (identity_zigzag n) a b r).
    - intros n m g x.
      destruct g.
      lhs nrapply homotopy_step.
      apply ap.
      symmetry.
      apply homotopy_step.
  Defined.

  Definition identity_zigzag_glueQP {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_Q b) (identity_zigzag_P a).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatQP (identity_zigzag n) b a r).
    - intros n m g x.
      destruct g.
      lhs nrapply homotopy_step.
      apply ap.
      symmetry.
      apply homotopy_step.
  Defined.

  Definition identity_zigzag_gluePQP {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : identity_zigzag_P a n) => x^+) == identity_zigzag_glueQP r (S n) o identity_zigzag_gluePQ r n
    := (homotopy_step R _ a b r).

  Definition identity_zigzag_glueQPQ {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : identity_zigzag_Q b n) => x^+) == identity_zigzag_gluePQ r n o identity_zigzag_glueQP r n
    := (homotopy_step (flip R) _ b a r).

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
    : (identity_zigzag_Pinf a) <~> (identity_zigzag_Qinf b)
    := equiv_zigzag_glue (identity_zigzag_glueQP r) (identity_zigzag_gluePQ r) (identity_zigzag_glueQPQ r) (identity_zigzag_gluePQP r).

  Definition identity_zigzag_gluePQinf : identity_zigzag_Pinf a -> identity_zigzag_Qinf b
    := equiv_identity_zigzag_glueinf.

  Definition identity_zigzag_glueQPinf : identity_zigzag_Qinf b -> identity_zigzag_Pinf a
    := equiv_identity_zigzag_glueinf^-1.

  Definition identity_zigzag_gluePQinf_comm 
    (n : nat) (p : identity_zigzag_P a n)
    : identity_zigzag_gluePQinf (@colim _ (identity_zigzag_P a) n p) = (@colim _ (identity_zigzag_Q b) (S n) (identity_zigzag_gluePQ r n p)).
  Proof.
    unfold identity_zigzag_gluePQinf.
    unfold equiv_identity_zigzag_glueinf.
    reflexivity.
  Defined.
End Sequence.

Section InverseEquivCoh.
  Context {A B : Type} {P : A -> Type} {Q : B -> Type} (e : A <~> B) (f : forall (a : A), P a <~> Q (e a)).

  Definition finv : forall (b : B), Q b <~> P (e^-1 b).
  Proof.
    intro b.
    transitivity (Q (e (e^-1 b))).
    - snrapply equiv_transport.
      exact (eisretr e b)^.
    - symmetry.
      exact (f (e^-1 b)).
  Defined.

  Definition finv_f : forall (a : A), (finv (e a)) o (f a) == transport (fun y => P y) (eissect e a)^.
  Proof.
    intros a x.
    simpl.
    rewrite (eisadj e a).
    snrapply (moveR_equiv_V' (f (e^-1 (e a)))).
    rewrite (ap_V e (eissect e a))^.
    generalize (eissect e a)^.
    intros [].
    reflexivity.
  Defined.

  Definition f_finv : forall (b : B), (f (e^-1 b)) o (finv b) == transport (fun y => Q y) (eisretr e b)^.
  Proof.
    intros b x.
    snrapply (moveR_equiv_M' (f (e^-1 b))).
    reflexivity.
  Defined.
End InverseEquivCoh.

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
      exact (equiv_identity_zigzag_glueinf R a0 r).
  Defined.

  (** Contruct the half-induction principle from Kraus-von Raumer. *)
  Context (a0 : A) 
    (P : forall (a : A) (p : identity_zigzag_family_half a0 (pushl a)), Type)
    (Q : forall (b : B) (q : identity_zigzag_family_half a0 (pushr b)), Type)
    (refl : P a0 (identity_zigzag_refl R a0))
    (e : forall (a : A) (b : B) (r : R a b) (p : identity_zigzag_family_half a0 (pushl a)), P a p <~> Q b (identity_zigzag_gluePQinf R a0 r p)).

  Let colimL {a : A} {n : nat} (p : identity_zigzag_P R a0 a n) : identity_zigzag_Pinf R a0 a
    := @colim _ (identity_zigzag_P R a0 a) n p.

  Let colimR {b : B} {n : nat} (q : identity_zigzag_Q R a0 b n) : identity_zigzag_Qinf R a0 b
    := @colim _ (identity_zigzag_Q R a0 b) n q.

  Let colimpL {a : A} {n : nat} (p : identity_zigzag_P R a0 a n) 
    := @colimp _ (identity_zigzag_P R a0 a) n (S n) idpath p.

  Let colimpR {b : B} {n : nat} (q : identity_zigzag_Q R a0 b n) 
    := @colimp _ (identity_zigzag_Q R a0 b) n (S n) idpath q.

  Let einv (a : A) (b : B) (r : R a b) (q : identity_zigzag_Qinf R a0 b) : Q b q <~> P a (identity_zigzag_glueQPinf R a0 r q)
    := finv (equiv_identity_zigzag_glueinf R a0 r) (e a b r) q.

  Let gluePQ {a : A} {b : B} (r : R a b) (n : nat) := identity_zigzag_gluePQ R a0 r n.

  Let glueQP {a : A} {b : B} (r : R a b) (n : nat) := identity_zigzag_glueQP R a0 r n.

  Let gluePQinf {a : A} {b : B} (r : R a b) := identity_zigzag_gluePQinf R a0 r.

  Let glueQPinf {a : A} {b : B} (r : R a b) := identity_zigzag_glueQPinf R a0 r.

  Let iotaP {a : A} (n : nat) := (seq_to_succ_seq (identity_zigzag_P R a0 a) n).

  Let iotaQ {b : B} (n : nat) := (seq_to_succ_seq (identity_zigzag_Q R a0 b) n).

  Let Pn (n : nat) (a : A) (p : identity_zigzag_P R a0 a n)
    := P a (colimL p).

  Let Qn (n : nat) (b : B) (q : identity_zigzag_Q R a0 b n)
    := Q b (colimR q).

  (** These are the maps used in the pushout defining [P_{n+1}] in the identity zigzag *)
  Let pushfP (a : A) (n : nat) : forall (c : ({b : B | R a b} * (identity_zigzag_P R a0 a n))), identity_zigzag_P R a0 a n
    := snd.

  Let pushgP (a : A) (n : nat)
    : forall (c : ({b : B | R a b} * (identity_zigzag_P R a0 a n))), {b : B & (R a b * (identity_zigzag_Q R a0 b (S n)))}.
  Proof.
    intros [[b r] p].
    exact (b ; (r , (gluePQ r n p))).
  Defined.

  (** These are the maps used in the pushout defining [Q_{n+1}] in the identity zigzag *)
  Let pushfQ (b : B) (n : nat) : forall (c : ({a : A | R a b} * (identity_zigzag_Q R a0 b n))), identity_zigzag_Q R a0 b n
    := snd.

  Let pushgQ (b : B) (n : nat)
    : forall (c : ({a : A | R a b} * (identity_zigzag_Q R a0 b n))), {a : A & (R a b * (identity_zigzag_P R a0 a n))}.
  Proof.
    intros [[a r] q].
    exact (a ; (r , (glueQP r n q))).
  Defined.

  (* The maps we wish to construct: *)
  Let indLn (n : nat) := forall (a : A) (p : identity_zigzag_P R a0 a n), Pn n a p.
  Let indRn (n : nat) := forall (b : B) (q : identity_zigzag_Q R a0 b n), Qn n b q.

  (* The goal of this section is to represent the data needed to produce something of type [indL (S n) a] from something of type [indRn (S n)] and [indLn n]; we are capturing the following situation:

<<
    
                   pushg := (b, r, p) |-> (b, r, gluePQ n r p)                     (b, r) |-> (b, r, indR n+1 b)

  (b : B)x(r : R a b)x(p : a0 ~>n a) -----> (b : B)x(r : R a b)x(q : a0 ~>n+1 b) ----------------------.
               |                                            |                                           \
               |                                            |                                            \
 pushf := pr3  |                                            | (b, r, q) |-> glueQP n+1 r q                \
               |                                            |                                              \
               v                                            v                                               v
         (p : a0 ~>n A) ---------------------------> (p' : a0 ~>n+1 a)                      (b : B)x(r : R a b)xQn n+1 b q
                \                                                                                           |
                 \                iotaP                                                                     |
                  \                                                                   (b, r) |-> e a b r    |
                   \                                                                                        |
                    \                                                                                       v
                     \                                                                          Pn n+1 a (glueQP n+1 r q)
                      `--------------> Pn n+1 a p^+

>>

We don't care about the bottom left map (which is [indL n a] followed by [transport colimp]) but to define [indR (S n)] it is extremely helpful to have the top right square, i.e. the composition of the right map in the pushout followed by the induced map, commute judgementally without any additional transports.

  The right case changes the square slightly, replacing [e] with [einv] and some indexing changes due to the asymmetricity of the zigzag construction.
  *)

  Section ind_dataL.
    Context (n : nat) (ind_indRn : indRn (S n)) (a : A).

    Definition ind_pushcP : forall (c : {b : B & (R a b * (identity_zigzag_Q R a0 b (S n)))}), Pn (S n) a (glueQP (fst (pr2 c)) (S n) (snd (pr2 c)))
      := fun c => (einv a (pr1 c) (fst (pr2 c)) (colimR (snd (pr2 c))) (ind_indRn (pr1 c) (snd (pr2 c)))).

    Record pushout_ind_data_P : Type := {
      ind_pushbP : (forall (p : identity_zigzag_P R a0 a n), Pn (S n) a (iotaP n p));
      ind_pushaP : (forall (c : ({b : B | R a b} * (identity_zigzag_P R a0 a n))), pglue c # (ind_pushbP ((pushfP a n) c)) = ind_pushcP ((pushgP a n) c))
    }.

    (* Take the pushout *)
    Definition pushout_ind_P_res (ind : pushout_ind_data_P) : (forall (p : identity_zigzag_P R a0 a (S n)), Pn (S n) a p).
    Proof.
      snrapply Pushout_ind.
      - exact (ind_pushbP ind).
      - exact ind_pushcP.
      - exact (ind_pushaP ind).
    Defined.

  End ind_dataL.

  (* The goal of this section is to represent the data needed to produce something of type [Rn (S n)] from something of type [Ln n] *)
  Section ind_dataR.
    Context (n : nat) (ind_indLn : indLn n) (b : B).

    Definition ind_pushcQ : forall (c : {a : A & (R a b * (identity_zigzag_P R a0 a n))}), Qn (S n) b (gluePQ (fst (pr2 c)) n (snd (pr2 c)))
      := fun c => (e (pr1 c) b (fst (pr2 c)) (colimL (snd (pr2 c))) (ind_indLn (pr1 c) (snd (pr2 c)))).

    Record pushout_ind_data_Q : Type := {
      ind_pushbQ : (forall (q : identity_zigzag_Q R a0 b n), Qn (S n) b (iotaQ n q));
      ind_pushaQ : (forall (c : ({a : A | R a b} * (identity_zigzag_Q R a0 b n))), pglue c # (ind_pushbQ ((pushfQ b n) c)) = ind_pushcQ ((pushgQ b n) c))
    }.

    (* Take the pushout *)
    Definition pushout_ind_Q_res (ind : pushout_ind_data_Q) : (forall (q : identity_zigzag_Q R a0 b (S n)), Qn (S n) b q).
    Proof.
      snrapply Pushout_ind.
      - exact (ind_pushbQ ind).
      - exact ind_pushcQ.
      - exact (ind_pushaQ ind).
    Defined.
  End ind_dataR.

  (** The following is garbage: *)
    (*

  Record zigzag_identity_record (n : nat) : Type := {
    indR (b : B) (q : identity_zigzag_Q R a0 b n) : Q b (colimR q);
    indL (a : A) (p : identity_zigzag_P R a0 a n) : P a (colimL p);
  }.
  
  Definition zigzag_identity_ind (n : nat) : zigzag_identity_record n.
  Proof.
    induction n.
    + snrapply Build_zigzag_identity_record.
      - intros b [].
      - intros a p; destruct p; exact refl.
    + destruct IHn as [indRp indLp].
      snrapply Build_zigzag_identity_record.
      - 


  (*
  (** The equivalence involving the inverse gluing map. *)
  Let einvr : forall (a : A) (b : B) (r : R a b) (n : nat) (q : identity_zigzag_Q R a0 b n), Q b (colimR q) <~> P a (identity_zigzag_glueQPinf R a0 r (colimR q)).
  Proof.
    intros a b r' n q.
    symmetry.
    transitivity (Q b (identity_zigzag_gluePQinf R a0 r' (identity_zigzag_glueQPinf R a0 r' (colimR q)))).
    + exact (e a b r' (identity_zigzag_glueQPinf R a0 r' (colimR q))).
    + nrapply (equiv_transport (fun x => Q b x) _).
      exact ((ap _ (identity_zigzag_glueQPQ R a0 r' n q)^) @ (@colimp _ (identity_zigzag_Q R a0 b) n (S n) idpath q)).
  Defined.

  Let einve : forall (a : A) (b : B) (r : R a b) (n : nat) (p : identity_zigzag_P R a0 a n), (einv a b r (S n) (gluePQ r n p)) o (e a b r (colimL p)) == (@transport _ 
    (fun y => P a y) 
    (colimL p) 
    (colimL (glueQP r (S n) (gluePQ r n p))) 
    ((@colimp _ (identity_zigzag_P R a0 a) n (S n) idpath p)^ 
      @ (ap colimL (identity_zigzag_gluePQP R a0 r n p)))).
  Proof.
    intros a b r n p x.
    unfold einv.
    simpl.
    snrapply (moveR_equiv_V' (e a b r _)).
    Open Scope long_path_scope.
    rewrite ap_V.
    rewrite <- inv_pp.
    (**

transport 
   (fun y => Q b y)
   ((ap (colimR n+2)
       (glueQPQ n.+1 (gluePQ r n p))^)
    @ colimp n.+1 (gluePQ r n p))^
   (e a b r (colimL p) x)

       ((colimp n+1 (gluePQ r n p))
        @ (ap (colimR n+2) (glueQPQ n+1 (gluePQ r n p))))^

= 

e a b r (colimL (glueQP (gluePQ p)))
  (transport
     (fun y => P a y)
     ((colimp n p)^
      @ ap colimL (gluePQP n p))
     x)
     *)
    
    (*Let einve : forall (a : A) (b : B) (r : R a b) (n : nat) (p : identity_zigzag_P R a0 a n), (einv a b r n (identity_zigzag_gluePQinf R a0 r (colimL p))) o (e a b r (colimL p)) == transport (fun y => P a y) (colimp
     *)
  (* Record zigzag_identity_record (n : nat) : Type := {
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
          rapply (e a b r' (colimL p)).
          exact (indLp a p).
        * intros [[a r'] q].
          simpl.
          (*
transport
  (fun w : (identity_zigzag ?n?)  => Q b (colimR w))
  (pglue ((a; r'), q))
  (transport (fun y => Q b y) (colimp n n.+1%nat 1 q)^ (indRp b q))

=

e a b r'
  (colimL (glueQP R _ b a r' q))
  (indLp a (glueQP R _ b a r' q))
           *)
      
  Admitted.
  
  Definition indR0 (b : B) (q : identity_zigzag_Q R a0 b 0%nat) : Q b (colimR q).
  Proof.
    destruct q.
  Defined.

  Definition indL0 (a : A) (p : identity_zigzag_P R a0 a 0%nat) : P a (colimL p).
  Proof.
    destruct p.
    exact r.
  Defined.

  Definition indR1 (b : B) (q : identity_zigzag_Q R a0 b 1%nat) : Q b (colimR q).
  Proof.
    generalize q.
    snrapply Pushout_ind.
    - intro q'.
      destruct q'.
    - intros  [a [r' p]].
      rapply (e a b r' (@colimL a 0%nat p)).
      exact (indL0 a p).
    - intros [[a r'] q'].
      simpl.
      destruct q'.
  Defined.

  Definition indL1 (a : A) (p : identity_zigzag_P R a0 a 1%nat) : P a (colimL p).
  Proof.
    generalize p.
    snrapply Pushout_ind.
    - intro p'.
      simpl.
      snrapply (transport (fun y => P a y)).
      1: exact (@colimL a 0%nat p').
      1: exact (@colimp _ (identity_zigzag_P R a0 a) 0%nat 1%nat idpath p')^.
      exact (indL0 a p').
    - intros [b [r' q]].
      simpl.
      rapply (einv a b r' 1 q).
      exact (indR1 b q).
    - intros [[b r'] p'].
      unfold dot_step.
      simpl fst.
      simpl snd.
      simpl indR1.
      Check (einv a b r' 1 (pushr (a; (r', p'))) (e a b r' (@colimL _ 0 p') (indL0 a p'))).
transport
  (fun w => P a (colimL w)) 
  (pglue ((b; r'), p'))
  (transport (fun y => P a y)
     (colimp 0%nat 1%nat 1 p')^ 
     (indL0 a p'))

    =

einv a b r' 1 (pushr (a; (r', p'))) (e a b r' (colimL p') (indL0 a p'))

*)*)*)
    
End ZigzagIdentity.
