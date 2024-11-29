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



  Definition transportlemma {X X' Y : Type} (f : X -> X') (g : X -> Y) (g' : X' -> Y) (Z : Y -> Type) {x : X} {y : X'} (p : f x = y) (q : g x = g' (f x)) : (fun z => (transport (Z o g') p (transport Z q z))) == (transport Z (q @ ap g' p)).
  Proof.
    destruct p.
    simpl.
    intro z.
    by rhs apply (ap (fun a => transport Z a z) (concat_p1 q)).
  Defined.

  Definition indL_step (n : nat) (a : A) (indLp : indLn n) 
    (indRp_data : forall (b : B), pushout_ind_data_Q n indLp b)
    : pushout_ind_data_P n (fun b => pushout_ind_Q_res n indLp b (indRp_data b)) a.
  Proof.
    pose (indRp := fun b => pushout_ind_Q_res n indLp b (indRp_data b)).
    snrapply (Build_pushout_ind_data_P n indRp a).
    - intro p.
      apply (transport (fun z => P a z) (colimpL p)^).
      exact (indLp a p).
    - intros [[b r] p].

      transparent assert (bigindLp : (forall (c : {a' : A | (R a' b) * (identity_zigzag_P R a0 a' n)}), {a' : A | (R a' b) * {p'' : identity_zigzag_P R a0 a' n & Pn n a' p''}})). {
        intros [a' [r' p']].
        exact (a' ; (r' , (p' ; indLp a' p'))).
      }

      transparent assert (bige : (forall (c : {a' : A | (R a' b) * {p'' : identity_zigzag_P R a0 a' n & Pn n a' p''}}), Qn (S n) b (gluePQ (fst (pr2 c)) n (pr1 (snd (pr2 c)))))). {
        intros [a' [r' [p'' z]]].
        exact (e a' b r' (colimL p'') z).
      }

      transparent assert (bigindRp : (forall (q : identity_zigzag_Q R a0 b (S n)), Qn (S n) b q)). {
        intro q.
        exact (indRp b q).
      }

      transparent assert (bigglue : (forall (c : {a' : A | (R a' b) * (identity_zigzag_P R a0 a' n)}), (identity_zigzag_Q R a0 b (S n)))). {
        exact pushr.
      }

      (** The top right square commutes judgementally! *)
      transparent assert (please : (forall (c : {a' : A | (R a' b) * (identity_zigzag_P R a0 a' n)}), bigindRp (bigglue c) = bige (bigindLp c))). {
        intro c.
        reflexivity.
      }

      transparent assert (incl : ((identity_zigzag_P R a0 a n) -> {a' : A | (R a' b) * (identity_zigzag_P R a0 a' n)})). {
        intro p'.
        exact (a ; (r , p')).
      }

      (** The top left triangle commutes judgementally! *)
      transparent assert (please2 : (forall (p' : identity_zigzag_P R a0 a n), bigglue (incl p) = (gluePQ r n p))). {
        intro p'.
        reflexivity.
      }

      (** The whole top commutes judgementally! *)
      transparent assert (please3 : (forall (p' : identity_zigzag_P R a0 a n), bigindRp (gluePQ r n p') = bige (bigindLp (incl p')))). {
        intro p'.
        reflexivity.
      }
      change (ind_pushcP n indRp a (pushgP a n ((b; r), p))) with (einv a b r (@colimR b (S n) (gluePQ r n p)) (bige (bigindLp (incl p)))).
      simpl pushfP.
      rhs apply (finv_f (equiv_identity_zigzag_glueinf R a0 r) (e a b r) (colimL p) (pr2 (snd (pr2 (bigindLp (incl p)))))).

      (* FIXME: This hangs Coq *)
      (*rhs apply (transport2 (fun y => P a y) (inverse2 (zigzag_comp_eissect (identity_zigzag_glueQP R a0 r) (identity_zigzag_gluePQ R a0 r) (identity_zigzag_glueQPQ R a0 r) (identity_zigzag_gluePQP R a0 r) n p)) (snd (bigindLp (incl p)).2).2). *)

      (* This is the rest of the proof, if the previous line compiles *)
      transparent assert (term : (transport (Pn n.+1 a) (pglue ((b; r), p))
  (transport (fun z : identity_zigzag_family_half a0 (pushl a) => P a z)
     (colimpL p)^ (indLp a p)) =
       transport (fun y : identity_zigzag_family_half a0 (pushl a) => P a y)
         (ap (inj (identity_zigzag_P R a0 a) n.+1%nat)
            (identity_zigzag_gluePQP R a0 r n p)^ @ 
          colimpL p)^ (snd (bigindLp (incl p)).2).2)). {
            unfold identity_zigzag_gluePQP.
            unfold homotopy_step.
            cbn.
            rewrite inv_pV.
            rewrite ap_V.
            rewrite inv_V.
            cbn.
            change (identity_zigzag_family_half a0 (pushl a)) with (identity_zigzag_Pinf R a0 a).
            refine ((transportlemma _ (@colimL a n) (@colimL a (S n)) (fun y => P a y) (pglue ((b ; r), p)) (@colimpL a n p)^ (indLp a p)) @ _).
            by rewrite inv_V.
          }
    Admitted.
      
End ZigzagIdentity.
