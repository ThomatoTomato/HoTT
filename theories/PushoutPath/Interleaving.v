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

(** START move to seq *)

(** From a sequence [A], we can produce a diagram map from [A] to [succ_seq A]. It's the map that applies the arrow in the sequence to every element. *)
Definition seq_to_succ_seq (A : Sequence) : DiagramMap A (succ_seq A).
Proof.
  snrapply Build_DiagramMap.
  - intros n a. exact a^+. 
  - intros m n [] x. reflexivity.
Defined.

(** Given a map of sequences we can define a map between their succesor sequences. *)
Definition succ_seq_map_seq_map {A B : Sequence} (f : DiagramMap A B) 
  : DiagramMap (succ_seq A) (succ_seq B).
Proof.
  snrapply Build_DiagramMap.
  - exact (f o S).
  - intros m n []. exact (DiagramMap_comm f _).
Defined.

(** A cocone over a sequence defines a cocone over the successor sequence. *)
Definition succ_seq_cocone_seq_cocone {A : Sequence} (T : Type) (C : Cocone A T)
  : Cocone (succ_seq A) T.
Proof.
  srapply Build_Cocone.
  - exact (C o S).
  - intros m n []. rapply (legs_comm C).
Defined.

(** [cocone_precompose (seq_to_succ_seq A)] is an equivalence. *)
Definition isequiv_cocone_precompose_seq_to_succ_seq
  `{Funext} {A : Sequence} {X : Type} 
  : IsEquiv (cocone_precompose (seq_to_succ_seq A) (X:=X)).
Proof.
  snrapply isequiv_adjointify.
  - exact (succ_seq_cocone_seq_cocone X).
  - intro C.
    snrapply path_cocone.
    + intro n. simpl. exact (legs_comm C n _ idpath).
    + intros m n [] a. simpl.
      exact (concat_1p _ @@ 1).
  - intro C.
    snrapply path_cocone.
    + intro n. simpl. exact (legs_comm C n _ idpath).
    + intros m n [] a. simpl.
      exact (concat_1p _ @@ 1).
Defined.

(** The cocone [colim_A] induces [idmap : A_w -> A_w]. *)
Definition col_legs_induces_idmap `{Funext} {A : Sequence}
  {A_w} (colim_A : IsColimit A A_w) 
  : cocone_postcompose_inv colim_A colim_A = idmap.
Proof.
  snrapply (equiv_inj (cocone_postcompose colim_A)).
  - exact (iscolimit_unicocone colim_A A_w).
  - lhs nrapply (eisretr (cocone_postcompose colim_A)).
    exact (cocone_postcompose_identity colim_A)^.
Defined.

(** We show that the map induced by [succ_seq_to_seq] is an equivalence. *)

(* jdc: Let's use CamelCase names for Sections.  They can also be less descriptive, since they are never looked up. *)
Section Is_Equiv_colim_succ_seq_to_seq_map.
  Context `{Funext} {A : Sequence}
    {A_w : Type} (colim_A : IsColimit A A_w).

  (** The legs of [colim_A] induces a cocone from [succ_seq A] over [A_w]. *)
  Definition cocone_succ_seq_over_col 
    : Cocone (succ_seq A) A_w
    := succ_seq_cocone_seq_cocone A_w colim_A.

  (** We start by showing that [abstr_colim_seq_to_abstr_colim_succ_seq] is a split-monomorphism. Observe that [cocone_succ_seq_over_col] essentially defines the same cocone as [colim_A]. I.e. the following  diagram is commutative:
  
  <<
                  A          succ_seq A
               ______          ______
              |      | =====>  \     |
              |      |         /     |
               ‾‾‾‾‾‾          ‾‾‾‾‾‾
                   \  \      /  /
            colim_A \  \    /  / cocone_succ_seq_over_col
                      colim A
  >>
  *)

  Definition legs_comm_cocone_succ_seq_over_col_with_col 
    (n : sequence_graph) 
    : cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col n
      == colim_A n := (legs_comm (iscolimit_cocone colim_A) _ _ _).

  Definition cocone_succ_seq_over_col_is_ess_col 
    : cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col
      = iscolimit_cocone colim_A.
  Proof.
    apply (path_cocone 
      legs_comm_cocone_succ_seq_over_col_with_col).
    intros m n [] a. 
    unfold legs_comm_cocone_succ_seq_over_col_with_col.
    simpl. exact (concat_1p _ @@ 1).
  Defined.

  (* The cocone of [succ_seq A] over colim A is universal *) (* jdc: I'll let you add periods and remove blank lines throughout. *)

  Instance iscolimit_succ_seq_A_over_A_w : IsColimit (succ_seq A) A_w.
  Proof.
  snrapply (Build_IsColimit cocone_succ_seq_over_col).
  snrapply Build_UniversalCocone.
  intro Y.
  srapply isequiv_adjointify.
  - intro C.
    exact (cocone_postcompose_inv colim_A (cocone_precompose (seq_to_succ_seq A) C)).
  - intro C.
    snrapply (equiv_inj (cocone_precompose (seq_to_succ_seq A))).
    + exact (isequiv_cocone_precompose_seq_to_succ_seq (X:=Y)).
    + lhs_V nrapply cocone_precompose_postcompose.
      lhs nrapply (ap (fun x => cocone_postcompose x _)
        cocone_succ_seq_over_col_is_ess_col).
      nrapply (eisretr (cocone_postcompose colim_A)).
  - intro f.
    nrapply (equiv_inj (cocone_postcompose colim_A)).
    + exact (iscolimit_unicocone colim_A Y).
    + lhs nrapply (eisretr (cocone_postcompose colim_A)).
      lhs_V nrapply cocone_precompose_postcompose.
      exact (ap (fun x => cocone_postcompose x f) cocone_succ_seq_over_col_is_ess_col).
  Defined.

  (** Alias for the above definition. *)

  Definition colim_succ := iscolimit_succ_seq_A_over_A_w.

  (** We take the colimit of [seq_to_succ_seq] and obtain a map [A_w -> A_w] *)

  Definition abstr_colim_seq_to_abstr_colim_succ_seq
    : A_w -> A_w 
    := functor_colimit (seq_to_succ_seq A) colim_A colim_succ.

  Definition abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap
    : abstr_colim_seq_to_abstr_colim_succ_seq = idmap.
  Proof.
    unfold abstr_colim_seq_to_abstr_colim_succ_seq, functor_colimit.
    lhs nrapply (ap (fun x => cocone_postcompose_inv colim_A x)
      cocone_succ_seq_over_col_is_ess_col).
    nrapply (equiv_inj (cocone_postcompose colim_A)).
    - nrapply (iscolimit_unicocone colim_A).
    - lhs nrapply (eisretr (cocone_postcompose colim_A)).
      exact (cocone_postcompose_identity colim_A)^.
  Defined.

  (** The cocone [cocone_succ_seq_over_col] induces a map [A_w -> A_w] *)

  Definition abstr_colim_succ_seq_to_abstr_colim_seq
    : A_w -> A_w 
    := (cocone_postcompose_inv colim_succ cocone_succ_seq_over_col).

  Definition abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap
    : abstr_colim_succ_seq_to_abstr_colim_seq = idmap.
  Proof.
    unfold abstr_colim_succ_seq_to_abstr_colim_seq.
    nrapply (equiv_inj (cocone_postcompose colim_A)).
    - nrapply (iscolimit_unicocone colim_A).
    - lhs nrapply (eisretr (cocone_postcompose colim_A)).
      lhs nrapply (cocone_succ_seq_over_col_is_ess_col).
      exact (cocone_postcompose_identity colim_A)^.
  Defined.

  (** The maps defined above are equivalences *)

  Definition sec_abstr_colim_seq_to_abstr_succ_seq
    : abstr_colim_succ_seq_to_abstr_colim_seq
    o abstr_colim_seq_to_abstr_colim_succ_seq
      = idmap.
  Proof.
    lhs nrapply (ap _ abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap).
    exact abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap.
  Defined.

  Definition ret_abstr_colim_seq_to_abstr_succ_seq
    : abstr_colim_seq_to_abstr_colim_succ_seq 
    o abstr_colim_succ_seq_to_abstr_colim_seq
      = idmap.
  Proof.
    lhs nrapply (ap _ abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap).
    exact abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap.
  Defined.

  (** [abstr_colim_seq_to_abstr_colim_succ_seq] is an equivalence *)
    
  Definition equiv_abstr_colim_seq_to_abstr_colim_succ_seq
    : IsEquiv abstr_colim_seq_to_abstr_colim_succ_seq.
  Proof.
    snrapply isequiv_adjointify.
    - exact abstr_colim_succ_seq_to_abstr_colim_seq.
    - exact (apD10 ret_abstr_colim_seq_to_abstr_succ_seq).
    - exact (apD10 sec_abstr_colim_seq_to_abstr_succ_seq).
  Defined.

End Is_Equiv_colim_succ_seq_to_seq_map.

(**  In intersplitting we will only assume that every other triangle is commutative. In this case, colim A is a retract of colim B. *)

Section Intersplitting.
  Context `{Funext} {A B : Sequence} 
    {A_w : Type} (colim_A : IsColimit A A_w)
    {B_w : Type} (colim_B : IsColimit B B_w)
    (d : DiagramMap A B) 
    (u : DiagramMap B (succ_seq A))
    (comm_triangle : seq_to_succ_seq A = diagram_comp u d).
    
  (** Given the data above, we show that the associated diagram in the
      colimit is also commutative.

  <<
                  id
        col A_i -----> col A_i+1
            \           ^
             \         /
              \       /
               v     /
              col B_i
  >>
  
  It follows that d is split-epi, and u is split-mono, as desired. *)

  Definition colimit_comm_triangle : 
    abstr_colim_seq_to_abstr_colim_succ_seq colim_A
      = (functor_colimit u _ (colim_succ colim_A)) o (functor_colimit d _ _).
  Proof.
    rhs nrapply functor_colimit_compose.
    exact (ap (fun x => functor_colimit x colim_A (colim_succ colim_A)) 
      comm_triangle).
  Defined.

  Definition colim_d_split_epi : 
    idmap = (functor_colimit u _ (colim_succ colim_A)) o (functor_colimit d _ _)
    := ((abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap colim_A)^ @ colimit_comm_triangle).

  Definition isequiv_colim_composite
    : IsEquiv ((functor_colimit u colim_B (colim_succ colim_A)) 
      o (functor_colimit d colim_A colim_B)).
  Proof.
    apply (@isequiv_homotopic A_w _
      (abstr_colim_seq_to_abstr_colim_succ_seq colim_A)
      ((functor_colimit u _ _) o (functor_colimit d _ _))
      (equiv_abstr_colim_seq_to_abstr_colim_succ_seq colim_A)).
    apply apD10.
    exact colimit_comm_triangle.
  Defined.

End Intersplitting.

(** Here we prove some properties related to the colimit of the successor sequence. *)

Section ColimitSucc.
  Context (A : Sequence).

  (** The any cocone over [A] gives a cocone over [succ_seq A]. *)
  Definition Cocone_succ {Q} (HQ : Cocone A Q) : Cocone (succ_seq A) Q.
  Proof.
    snrapply Build_Cocone.
    - intros i x.
      exact (HQ (S i) x).
    - intros i _ [] x.
      exact (legs_comm HQ (S i) (S (S i)) idpath x).
  Defined.

  (** The specific case of the HIT colimit. *)
  Definition Colimit_succ : Cocone (succ_seq A) (Colimit A)
    := Cocone_succ (cocone_colimit A).

  (** The successor endomorphism for the HIT colimit. *)
  Definition Colimit_succ_map : Colimit A -> Colimit A
    := functor_Colimit_half (seq_to_succ_seq A) (Colimit_succ).

  (** The successor map is homotopic to the identity map. *)
  Definition Colimit_succ_map_is_idmap : Colimit_succ_map == idmap.
  Proof.
    snrapply Colimit_rec_homotopy.
    - intros i x; cbn.
      apply colimp.
    - intros m _ [] x; cbn.
      nrefine (_ @@ _).
      + apply concat_1p.
      + symmetry; apply ap_idmap.
  Defined.
End ColimitSucc.

(** The HIT colimit isn't a colimit of the successor sequence without [Funext], but we can use [Colimit_rec] to get maps out of it. *)
Definition functor_Colimit_succ_half {A B : Sequence} (m : DiagramMap (succ_seq A) B) {Q} (HQ : Cocone B Q)
  : Colimit A -> Q
  := functor_Colimit_half (diagram_comp m (seq_to_succ_seq A)) HQ.

(** The "predecessor" map between the HIT colimits of a sequence and its successor. *)
Definition colim_succ_seq_to_seq (A : Sequence) : (Colimit (succ_seq A)) -> Colimit A.
Proof.
  snrapply Colimit_rec.
  snrapply Build_Cocone.
  - intros i x.
    exact (@colim _ A (S i) x).
  - intros i _ [] x.
    exact (@colimp _ A (S i) (S (S i)) _ x).
Defined.

(** Composition of diagram maps commutes with [functor_Colimit_half], provided the first is mapping into [Colimit_succ A]. *)
Definition functor_Colimit_half_compose' {A B : Sequence} (f : DiagramMap A (succ_seq B)) (g : DiagramMap (succ_seq B) (succ_seq A))
  : (functor_Colimit_succ_half g (Colimit_succ A)) o (functor_Colimit_half f (Colimit_succ B)) == functor_Colimit_half (diagram_comp g f) (Colimit_succ A).
Proof.
  symmetry.
  snrapply Colimit_rec_homotopy.
  - intros i x.
    simpl.
    rhs apply (ap (@colim _ A (S (S i))) (DiagramMap_comm g idpath (f i x))^).
    exact (@colimp _ A (S i) (S (S i)) idpath (g i (f i x)))^.
  - intros i _ [] x.
    simpl.
    Open Scope long_path_scope.
    unfold functor_Colimit_succ_half.
    unfold functor_Colimit_half.
    rewrite concat_pp_p, concat_p_Vp.
    rewrite <- 2 ap_V, 2 inv_V, <- ap_pp.
    unfold comm_square_comp.
    rewrite inv_pp.
    rewrite concat_pp_p, concat_Vp, concat_p1.
    rewrite <- ap_V, <- ap_compose, concat_pp_p.
    nrapply moveL_Vp.
    rewrite (ap_compose _ _ (colimp i (S i) idpath x)).
    rewrite Colimit_rec_beta_colimp.
    unfold Colimit_succ.
    simpl.
    rewrite ap_pp.
    rewrite Colimit_rec_beta_colimp.
    rewrite <- ap_compose.
    simpl.
    unfold comm_square_comp.
    simpl.
    rewrite concat_p1, !concat_p_pp.
    rewrite <- (concat_Ap (fun t => ap (inj A i.+3%nat) (DiagramMap_comm g idpath t)) (DiagramMap_comm f idpath x)^).
    rewrite !ap_V, concat_pp_V.
    nrapply moveL_pM.
    rewrite <- (ap_V (fun x0 : B i.+2%nat => inj A i.+2%nat (g i.+1%nat x0)) _).
    rewrite <- (ap_V (fun x0  => inj A i.+3%nat (g i.+1%nat x0) ^+) (DiagramMap_comm f idpath x)).
    rewrite ap_compose.
    rewrite (@thelemma _ A i.+2%nat i.+3%nat idpath _ _ (ap (g i.+1%nat) (DiagramMap_comm f idpath x)^)).
    Close Scope long_path_scope.
    rewrite !ap_V.
    apply (ap (fun p => p^)).
    rewrite <- !ap_compose.
    by apply ap.
Defined.

(** END move to seq *)

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
      snrapply (@thelemma' _ B _ _ idpath (f n.+1 (g n x)) (x^+) (L n x)^).
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
    by lhs nrapply concat_1p.
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

  (** Given type families [P : A -> Type], [Q : B -> Type], an equivalence [e : A <~> B], and a family of equivalences [f : forall (a : A), P a <~> Q (e a)], we get a family of equivalences [finv : forall (b : B), Q b <~> P (e^-1 b)] and some results about compositions of [f] and [finv]. *)

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
