Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.Cocone.
Require Import Diagrams.Sequence.
Require Import Diagrams.CommutativeSquares.
Require Import WildCat.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Types.

(** * Suppose we have sequences [A_i] and [B_i]. An interleaving from [A_i] to [B_i] consists of two natural transformations [d : A_i => B_i] ([d] for down) and [u : B_i => A_i+1] ([u] for up), such that the following diagram is commutative:

<<
    A_0 -------> A_1 ------> A_2 ------>
        \        ^  \        ^ 
         \      /    \      /  
          \    /      \    /         ...
           v  /        v  /
           B_0 ------> B_1 ------->
>>

Given the setup above, we want to say that the colimit of the upper and lower sequences are equivalent same. *)

(** ** Given families of maps [f n : A n -> B n] and [g : B n -> A (n + 1)] with homotopies showing that they form zigzags, construct the actual diagram maps and show that their composition is equal to the successor diagram map. *)

Section Interme.
  Context {A B : Sequence}
    (f : forall (n : nat), A n -> B n)
    (g : forall (n : nat), B n -> A (S n))
    (U : forall (n : nat), (fun (x : A n) => x^+) == (g n) o (f n))
    (L : forall (n : nat), (fun (x : B n) => x^+) == (f (S n)) o (g n)).

  (** The map built from [f]. Note that [zigzag_glue_map_tri] depends heavily on the exact homotopy used here. *)
  Definition zigzag_glue_map : DiagramMap A B.
  Proof.
    snrapply Build_DiagramMap.
    - exact f.
    - intros n m [] x.
      lhs apply (L n).
      apply ap.
      exact (U n x)^.
  Defined.

  (** The map built from [g]. *)
  Definition zigzag_glue_map_inv : DiagramMap B (succ_seq A).
  Proof.
    snrapply Build_DiagramMap.
    - exact g.
    - intros n m [] x.
      lhs apply (U (S n)).
      apply ap.
      exact (L n x)^.
  Defined.

  Local Open Scope path_scope.

  (** Show that the composition of the two maps is the successor map. *)
  Definition zigzag_glue_map_tri : DiagramMap_homotopy (diagram_comp zigzag_glue_map_inv zigzag_glue_map) (seq_to_succ_seq A).
  Proof.
    snrapply (_ ; _).
    - intros n x.
      simpl.
      exact (U n x)^.
    - intros n m [] x.
      simpl.
      unfold CommutativeSquares.comm_square_comp.
      Open Scope long_path_scope.
      rhs nrapply (concat_p1 _).
      apply moveR_pV.
      lhs nrapply (1 @@ ap_pp (g n.+1) (L n (f n x)) (ap (f n.+1) (U n x)^)).
      lhs nrapply (1 @@ ap_V (g n.+1) (L n (f n x)) @@ 1).
      lhs nrapply (concat_pp_p (U n.+1 _) ((ap (g n.+1) _)^) _).
      lhs nrapply (1 @@ concat_V_pp _ _).
      lhs_V nrapply (1 @@ ap_compose (f n.+1) (g n.+1) _).
      exact (concat_Ap _ _)^.
      Close Scope long_path_scope.
  Defined.
End Interme.

(** ** Assuming that there are [A, B : Sequence] that fits in an interleaving diagram, their colimits are isomorphic. *)

Section Interleaving.
  Context {A B : Sequence} 
    (f : forall (n : nat), A n -> B n)
    (g : forall (n : nat), B n -> A (S n))
    (U : forall (n : nat), (fun (x : A n) => x^+) == (g n) o (f n))
    (L : forall (n : nat), (fun (x : B n) => x^+) == (f (S n)) o (g n)).

  Notation d := (zigzag_glue_map f g U L).

  Notation u := (zigzag_glue_map_inv f g U L).

  Definition zigzag_glue_map_inf : Colimit A -> Colimit B
    := functor_Colimit d.

  Definition zigzag_glue_map_inv_inf : Colimit B -> Colimit A
    := functor_Colimit_half u (Colimit_succ A).

  (** Show that the two gluing maps are inverse. *)

  (** A coherence that comes up in the construction of the section: [(L f g) @ (f g L)^] is the same as [(L x^+) @ ((L x)^+)^]. *)
  Local Definition Lfg_coherence (n : nat) (x : B n) : (L n.+1 (f n.+1 (g n x))) @ (ap ((f n.+2) o (g n.+1)) (L n x))^ @ (L (S n) x^+)^ = (ap (fun z => z^+) (L n x))^.
  Proof.
    nrapply (cancelR _ _ (L n.+1 x^+)).
    lhs nrapply concat_pV_p.
    lhs nrapply (1 @@ (ap_V _ _)^).
    rhs nrapply ((ap_V _ _)^ @@ 1).
    nrapply (concat_Ap _ _)^.
  Qed.

  (** Construct a better section for the equivalence which is needed in the proof of the induction principle. *)
  Local Definition better_section : zigzag_glue_map_inf o zigzag_glue_map_inv_inf == idmap.
  Proof.
    snrapply Colimit_ind.
    - intros n x.
      simpl.
      rhs nrapply (@colimp _ B n (S n) idpath x)^.
      apply ap.
      exact (L n x)^.
    - intros n _ [] x.
      simpl.
      Open Scope long_path_scope.
      rewrite 2 inv_V.
      lhs apply (@transport_paths_FlFr _ _ (zigzag_glue_map_inf o zigzag_glue_map_inv_inf) (idmap) (@colim _ B (S n) x^+) _ (colimp n _ _ x) (ap (colim _) (L n.+1 x ^+)^ @' @colimp _ B _ _ _ x ^+)).
      rewrite ap_compose.
      rewrite Colimit_rec_beta_colimp.
      unfold cocone_precompose.
      simpl.
      rewrite ap_pp.
      rewrite <- ap_compose.
      simpl.
      rewrite ap_V.
      rewrite ap_pp.
      rewrite Colimit_rec_beta_colimp.
      unfold cocone_precompose.
      simpl.
      rewrite ! concat_p_pp.
      rewrite ap_idmap.
      rewrite ! ap_V.
      rewrite ! ap_pp.
      rewrite ! inv_pp.
      rewrite ! concat_p_pp.
      rewrite ! inv_V.
      rewrite 2 (ap_compose (f n.+2%nat) _).
      rewrite ap_V.
      rewrite concat_pV_p.
      rewrite <- (ap_compose (g n.+1%nat) (f n.+2%nat)).
      rewrite <- 2 ap_V.
      rewrite <- ap_p_pp.
      rewrite <- ap_p_pp.
      rewrite concat_p_pp.
      rewrite (Lfg_coherence n x).
      rewrite ap_V.
      apply (ap (fun z => z @ (colimp n (S n) idpath x))).
      rewrite <- (inv_V (cglue _)).
      rewrite <- 3 ap_V.
      snrapply (@ap_colim' _ B _ _ idpath (f n.+1 (g n x)) (x^+) (L n x)^).
      Close Scope long_path_scope.
  Defined.

  (** The zigzag gluing map is an equivalence.

  The original proof used [Interme] twice; first on the sequence, then shifting the sequence by one (using [B] and [succ_seq A] instead of [A] and [B], respectively). This required some bookkeeping to fix and the section produced by this method didn't have the necessary computation rule for the induction principle. *)
  Definition zigzag_glue_map_isequiv : IsEquiv zigzag_glue_map_inv_inf.
  Proof.
    snrapply isequiv_adjointify.
    - exact zigzag_glue_map_inf.
    - transitivity (functor_Colimit_half (diagram_comp u d) (Colimit_succ A)).
      + symmetry.
        exact (functor_Colimit_half_compose d u (Colimit_succ A)).
      + transitivity (functor_Colimit_half (seq_to_succ_seq A) (Colimit_succ A)).
        * exact (functor_Colimit_half_homotopy (zigzag_glue_map_tri f g U L) (Colimit_succ A)).
        * exact (Colimit_succ_map_is_idmap A).
    - exact better_section.
  Defined.

  Definition equiv_zigzag_glue : Colimit B <~> Colimit A.
  Proof.
    snrapply Build_Equiv.
    + exact zigzag_glue_map_inv_inf.
    + exact zigzag_glue_map_isequiv.
  Defined.

  (** Prove two computation rules needed for the induction principle: the section and retraction of the equivalence are the inverse of the two input homotopies [U] and [L] concatenated with [colimp] when applied to the colimit of sequence elements. *)

  Context (n : nat).

  Definition zigzag_comp_eisretr (a : A n) : (eisretr equiv_zigzag_glue (@colim _ A n a)) = (ap (@colim _ A n.+1%nat) (U n a)^) @ (@colimp _ A n _ _ a).
  Proof.
    simpl eisretr.
    unfold pointwise_paths_concat.
    simpl functor_Colimit_half_compose.
    simpl functor_Colimit_half_homotopy.
    simpl Colimit_succ_map_is_idmap.
    nrapply concat_1p.
  Defined.

  Definition zigzag_comp_eissect (b : B n) : (eissect equiv_zigzag_glue (@colim _ B n b)) = (ap (@colim _ B n.+1%nat) (L n b)^) @ (@colimp _ B n _ _ b).
  Proof.
    (* FIXME: This is trash. Some of this is induced by [isequiv_adjointify], is it easier to do that ourselves?  *)
    Open Scope long_path_scope.
    simpl.
    unfold pointwise_paths_concat.
    simpl.
    rewrite concat_1p.
    rewrite ! concat_p_pp.
    rewrite inv_V.
    rewrite ap_V.
    rewrite ap_pp.
    rewrite <- (ap_compose _ zigzag_glue_map_inv_inf).
    simpl.
    rewrite ap_V.
    rewrite ap_pp.
    rewrite inv_pp.
    rewrite Colimit_rec_beta_colimp.
    rewrite ap_pp.
    rewrite ! concat_p_pp.
    rewrite <- (ap_compose _ zigzag_glue_map_inf).
    simpl.
    rewrite Colimit_rec_beta_colimp.
    unfold legs_comm; simpl.
    rewrite ! ap_V.
    rewrite ! ap_pp.
    rewrite Colimit_rec_beta_colimp.
    unfold legs_comm; simpl.
    rewrite ! concat_p_pp.
    rewrite ! inv_pp.
    rewrite ! ap_pp.
    rewrite ! concat_p_pp.
    rewrite ! inv_pp.
    rewrite ! inv_V.
    rewrite ! concat_p_pp.
    rewrite ! ap_V.
    rewrite <- 2 (ap_compose (fun x => @colim _ A n.+2%nat x) zigzag_glue_map_inf).
    simpl.
    rewrite ! inv_V.
    rewrite <- (ap_compose (fun x => @colim _ A n.+2%nat (g n.+1%nat x)) zigzag_glue_map_inf).
    rewrite (ap_compose (f n.+2) _).
    simpl.
    rewrite ! concat_pp_p.
    rewrite 2 concat_V_pp.
    rewrite ! concat_p_pp.
    rewrite (ap_compose (f n.+2%nat) (@colim _ B n.+2%nat)).
    rewrite <- ap_V.
    rewrite (ap_compose ((f n.+2%nat) o (g n.+1%nat)) (@colim _ B n.+2%nat)).
    rewrite (ap_homotopic (fun z => (L (S n) z)^)).
    rewrite 2 ap_pp.
    rewrite ! concat_pp_p.
    rewrite <- (ap_pp_p (@colim _ B n.+2%nat)).
    rewrite <- (ap_compose (g n.+1%nat) (f n.+2%nat)).
    rewrite <- ap_pp_p.
    rewrite ! concat_p_pp.
    rewrite (Lfg_coherence n).
    rewrite ap_V.
    rewrite ! concat_pp_p.
    rewrite concat_V_pp.
    rewrite inv_V.
    rewrite concat_p_Vp.
    rewrite ! concat_p_pp.
    unfold colimp.
    rewrite concat_pV.
    rewrite concat_1p.
    reflexivity.
  Defined.
End Interleaving.

Section InverseEquivCoh.

  (** ** Given type families [P : A -> Type], [Q : B -> Type], an equivalence [e : A <~> B], and a family of equivalences [f : forall (a : A), P a <~> Q (e a)], we get a family of equivalences [finv : forall (b : B), Q b <~> P (e^-1 b)] and some results about compositions of [f] and [finv]. *)

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
    lhs nrapply (ap (fun z => (f (e^-1 (e a)))^-1 (transport Q z^ (f a x))) (eisadj e a)).
    nrapply (moveR_equiv_V' (f (e^-1 (e a)))).
    lhs nrapply (ap (fun z => transport Q z (f a x)) (ap_V e _)^).
    by destruct (eissect e a)^.
  Defined.

  Definition f_finv : forall (b : B), (f (e^-1 b)) o (finv b) == transport (fun y => Q y) (eisretr e b)^.
  Proof.
    intros b x.
    by nrapply (moveR_equiv_M' (f (e^-1 b))).
  Defined.
End InverseEquivCoh.
