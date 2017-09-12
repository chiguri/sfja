(** * RecordSub: レコードのサブタイプ *)
(*
(** * RecordSub: Subtyping with Records *)
*)

(** In this chapter, we combine two significant extensions of the pure
    STLC -- records (from chapter [Records]) and subtyping (from
    chapter [Sub]) -- and explore their interactions.  Most of the
    concepts have already been discussed in those chapters, so the
    presentation here is somewhat terse.  We just comment where things
    are nonstandard. *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import MoreStlc.

(* ################################################################# *)
(*
(** * Core Definitions *)
*)
(** * 中核部の定義 *)

(* ----------------------------------------------------------------- *)
(*
(** *** Syntax *)
*)
(** *** 構文 *)

Inductive ty : Type :=
  (* proper types *)
  | TTop   : ty
  | TBase  : id -> ty
  | TArrow : ty -> ty -> ty
  (* record types *)
  | TRNil : ty
  | TRCons : id -> ty -> ty -> ty.

Inductive tm : Type :=
  (* proper terms *)
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tproj : tm -> id -> tm
  (* record terms *)
  | trnil :  tm
  | trcons : id -> tm -> tm -> tm.

(* ----------------------------------------------------------------- *)
(** *** Well-Formedness *)

(** The syntax of terms and types is a bit too loose, in the sense
    that it admits things like a record type whose final "tail" is
    [Top] or some arrow type rather than [Nil].  To avoid such cases,
    it is useful to assume that all the record types and terms that we
    see will obey some simple well-formedness conditions.

    [An interesting technical question is whether the basic properties
    of the system -- progress and preservation -- remain true if we
    drop these conditions.  I believe they do, and I would encourage
    motivated readers to try to check this by dropping the conditions
    from the definitions of typing and subtyping and adjusting the
    proofs in the rest of the chapter accordingly.  This is not a
    trivial exercise (or I'd have done it!), but it should not involve
    changing the basic structure of the proofs.  If someone does do
    it, please let me know. --BCP 5/16.] *)

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty TRNil
  | RTcons : forall i T1 T2,
        record_ty (TRCons i T1 T2).

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : forall i t1 t2,
        record_tm (trcons i t1 t2).

Inductive well_formed_ty : ty -> Prop :=
  | wfTTop :
        well_formed_ty TTop
  | wfTBase : forall i,
        well_formed_ty (TBase i)
  | wfTArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty (TArrow T1 T2)
  | wfTRNil :
        well_formed_ty TRNil
  | wfTRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty (TRCons i T1 T2).

Hint Constructors record_ty record_tm well_formed_ty.

(* ----------------------------------------------------------------- *)
(*
(** *** Substitution *)
*)
(** *** 置換 *)

(** Substitution and reduction are as before. *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y => if beq_id x y then s else t
  | tabs y T t1 =>  tabs y T (if beq_id x y then t1
                             else (subst x s t1))
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | tproj t1 i => tproj (subst x s t1) i
  | trnil => trnil
  | trcons i t1 tr2 => trcons i (subst x s t1) (subst x s tr2)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ----------------------------------------------------------------- *)
(*
(** *** Reduction *)
*)
(** *** 簡約 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_rnil : value trnil
  | v_rcons : forall i v vr,
      value v ->
      value vr ->
      value (trcons i v vr).

Hint Constructors value.

Fixpoint Tlookup (i:id) (Tr:ty) : option ty :=
  match Tr with
  | TRCons i' T Tr' =>
      if beq_id i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:id) (tr:tm) : option tm :=
  match tr with
  | trcons i' t tr' =>
      if beq_id i i' then Some t else tlookup i tr'
  | _ => None
  end.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1  t2')
  | ST_Proj1 : forall tr tr' i,
        tr ==> tr' ->
        (tproj tr i) ==> (tproj tr' i)
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi    ->
       (tproj tr i) ==> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 ==> t1' ->
        (trcons i t1 tr2) ==> (trcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 ==> tr2' ->
        (trcons i v1 tr2) ==> (trcons i v1 tr2')

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

(* ################################################################# *)
(*
(** * Subtyping *)
*)
(** * サブタイプ *)

(*
(** Now we come to the interesting part, where the features we've
    added start to interact.  We begin by defining the subtyping
    relation and developing some of its important technical
    properties. *)
*)
(** 追加した要素が関係してくる、おもしろい部分に来ました。
    サブタイプ関係を定義し、その重要な技術的性質のいくつかを調べることから始めます。 *)

(* ================================================================= *)
(*
(** ** Definition *)
*)
(** ** 定義 *)

(*
(** The definition of subtyping is essentially just what we sketched
    in the discussion of record subtyping in chapter [Sub], but we
    need to add well-formedness side conditions to some of the rules.
    Also, we replace the "n-ary" width, depth, and permutation
    subtyping rules by binary rules that deal with just the first
    field. *)
*)
(** サブタイプの定義は、本質的には、[Sub]章で議論したレコードのサブタイプの通りです。
    ただ、いくつかの規則に付加条件として well-formedness を追加する必要があります。
    また、「n引数」の幅、深さ、順列などの規則を一つ目のフィールドを対象にした2引数のものに置き換えます。 *)

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  (* Subtyping between proper types *)
  | S_Refl : forall T,
    well_formed_ty T ->
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    well_formed_ty S ->
    S <: TTop
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    TArrow S1 S2 <: TArrow T1 T2
  (* Subtyping between record types *)
  | S_RcdWidth : forall i T1 T2,
    well_formed_ty (TRCons i T1 T2) ->
    TRCons i T1 T2 <: TRNil
  | S_RcdDepth : forall i S1 T1 Sr2 Tr2,
    S1 <: T1 ->
    Sr2 <: Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    TRCons i S1 Sr2 <: TRCons i T1 Tr2
  | S_RcdPerm : forall i1 i2 T1 T2 Tr3,
    well_formed_ty (TRCons i1 T1 (TRCons i2 T2 Tr3)) ->
    i1 <> i2 ->
       TRCons i1 T1 (TRCons i2 T2 Tr3)
    <: TRCons i2 T2 (TRCons i1 T1 Tr3)

where "T '<:' U" := (subtype T U).

Hint Constructors subtype.

(* ================================================================= *)
(*
(** ** Examples *)
*)
(** ** 例 *)

Module Examples.

Notation x := (Id "x").
Notation y := (Id "y").
Notation z := (Id "z").
Notation j := (Id "j").
Notation k := (Id "k").
Notation i := (Id "i").
Notation A := (TBase (Id "A")).
Notation B := (TBase (Id "B")).
Notation C := (TBase (Id "C")).

Definition TRcd_j  :=
  (TRCons j (TArrow B B) TRNil).     (* {j:B->B} *)
Definition TRcd_kj :=
  TRCons k (TArrow A A) TRcd_j.      (* {k:C->C,j:B->B} *)

Example subtyping_example_0 :
  subtype (TArrow C TRcd_kj)
          (TArrow C TRNil).
(* C->{k:A->A,j:B->B} <: C->{} *)
Proof.
  apply S_Arrow.
    apply S_Refl. auto.
    unfold TRcd_kj, TRcd_j. apply S_RcdWidth; auto.
Qed.

(*
(** The following facts are mostly easy to prove in Coq.  To get full
    benefit, make sure you also understand how to prove them on
    paper! *)
*)
(** 以下の事実のほとんどはCoqで証明することは簡単です。
    最大限理解するために、どのように証明するかを理解していることを紙の上でも確認しなさい！ *)

(*
(** **** Exercise: 2 stars (subtyping_example_1)  *)
*)
(** **** 練習問題: ★★ (subtyping_example_1)  *)
Example subtyping_example_1 :
  subtype TRcd_kj TRcd_j.
(* {k:A->A,j:B->B} <: {j:B->B} *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 1 star (subtyping_example_2)  *)
*)
(** **** 練習問題: ★ (subtyping_example_2)  *)
Example subtyping_example_2 :
  subtype (TArrow TTop TRcd_kj)
          (TArrow (TArrow C C) TRcd_j).
(* Top->{k:A->A,j:B->B} <: (C->C)->{j:B->B} *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 1 star (subtyping_example_3)  *)
*)
(** **** 練習問題: ★ (subtyping_example_3)  *)
Example subtyping_example_3 :
  subtype (TArrow TRNil (TRCons j A TRNil))
          (TArrow (TRCons k B TRNil) TRNil).
(* {}->{j:A} <: {k:B}->{} *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 2 stars (subtyping_example_4)  *)
*)
(** **** 練習問題: ★★ (subtyping_example_4)  *)
Example subtyping_example_4 :
  subtype (TRCons x A (TRCons y B (TRCons z C TRNil)))
          (TRCons z C (TRCons y B (TRCons x A TRNil))).
(* {x:A,y:B,z:C} <: {z:C,y:B,x:A} *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Examples.

(* ================================================================= *)
(*
(** ** Properties of Subtyping *)
*)
(** ** サブタイプの性質 *)

(* ----------------------------------------------------------------- *)
(** *** Well-Formedness *)

(** To get started proving things about subtyping, we need a couple of
    technical lemmas that intuitively (1) allow us to extract the
    well-formedness assumptions embedded in subtyping derivations
    and (2) record the fact that fields of well-formed record types
    are themselves well-formed types.  *)

Lemma subtype__wf : forall S T,
  subtype S T ->
  well_formed_ty T /\ well_formed_ty S.
Proof with eauto.
  intros S T Hsub.
  induction Hsub;
    intros; try (destruct IHHsub1; destruct IHHsub2)...
  - (* S_RcdPerm *)
    split... inversion H. subst. inversion H5...  Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  - (* TRCons *)
    inversion H. subst. unfold Tlookup in H0.
    destruct (beq_id i i0)...  inversion H0; subst...  Qed.

(* ----------------------------------------------------------------- *)
(*
(** *** Field Lookup *)
*)
(** *** フィールド参照 *)

(*
(** The record matching lemmas get a little more complicated in the
    presence of subtyping, for two reasons.  First, record types no
    longer necessarily describe the exact structure of the
    corresponding terms.  And second, reasoning by induction on typing
    derivations becomes harder in general, because typing is no longer
    syntax directed. *)
*)
(** サブタイプがあることで、レコードマッチング補題はいくらか複雑になります。
    それには2つの理由があります。
    1つはレコード型が対応する項の正確な構造を記述する必要がなくなることです。
    2つ目は、[has_type]の導出に関する帰納法を使う推論が一般には難しくなることです。
    なぜなら、[has_type]が構文指向ではなくなるからです。 *)

Lemma rcd_types_match : forall S T i Ti,
  subtype S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ subtype Si Ti.
Proof with (eauto using wf_rcd_lookup).
  intros S T i Ti Hsub Hget. generalize dependent Ti.
  induction Hsub; intros Ti Hget;
    try solve_by_invert.
  - (* S_Refl *)
    exists Ti...
  - (* S_Trans *)
    destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.
    destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.
    exists Si...
  - (* S_RcdDepth *)
    rename i0 into k.
    unfold Tlookup. unfold Tlookup in Hget.
    destruct (beq_id i k)...
    + (* i = k -- we're looking up the first field *)
      inversion Hget. subst. exists S1...
  - (* S_RcdPerm *)
    exists Ti. split.
    + (* lookup *)
      unfold Tlookup. unfold Tlookup in Hget.
      destruct (beq_idP i i1)...
      * (* i = i1 -- we're looking up the first field *)
        destruct (beq_idP i i2)...
        (* i = i2 -- contradictory *)
        destruct H0.
        subst...
    + (* subtype *)
      inversion H. subst. inversion H5. subst...  Qed.

(*
(** **** Exercise: 3 stars (rcd_types_match_informal)  *)
*)
(** **** 練習問題: ★★★ (rcd_types_match_informal)  *)
(*
(** Write a careful informal proof of the [rcd_types_match]
    lemma. *)
*)
(** [rcd_types_match]補題の非形式的証明を注意深く記述しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* ----------------------------------------------------------------- *)
(*
(** *** Inversion Lemmas *)
*)
(** *** 反転補題 *)

(*
(** **** Exercise: 3 stars, optional (sub_inversion_arrow)  *)
*)
(** **** 練習問題: ★★★, optional (sub_inversion_arrow)  *)
Lemma sub_inversion_arrow : forall U V1 V2,
     subtype U (TArrow V1 V2) ->
     exists U1, exists U2,
       (U=(TArrow U1 U2)) /\ (subtype V1 U1) /\ (subtype U2 V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember (TArrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(*
(** * Typing *)
*)
(** * 型付け *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      update Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in TArrow T1 T2 ->
      Gamma |- t2 \in T1 ->
      Gamma |- tapp t1 t2 \in T2
  | T_Proj : forall Gamma i t T Ti,
      Gamma |- t \in T ->
      Tlookup i T = Some Ti ->
      Gamma |- tproj t i \in Ti
  (* Subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      subtype S T ->
      Gamma |- t \in T
  (* Rules for record terms *)
  | T_RNil : forall Gamma,
      Gamma |- trnil \in TRNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- trcons i t tr \in TRCons i T Tr

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(*
(** ** Typing Examples *)
*)
(** ** 型付けの例 *)

Module Examples2.
Import Examples.

(*
(** **** Exercise: 1 star (typing_example_0)  *)
*)
(** **** 練習問題: ★ (typing_example_0)  *)
Definition trcd_kj :=
  (trcons k (tabs z A (tvar z))
           (trcons j (tabs z B (tvar z))
                      trnil)).

Example typing_example_0 :
  has_type empty
           (trcons k (tabs z A (tvar z))
                     (trcons j (tabs z B (tvar z))
                               trnil))
           TRcd_kj.
(* empty |- {k=(\z:A.z), j=(\z:B.z)} : {k:A->A,j:B->B} *)
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 2 stars (typing_example_1)  *)
*)
(** **** 練習問題: ★★ (typing_example_1)  *)
Example typing_example_1 :
  has_type empty
           (tapp (tabs x TRcd_j (tproj (tvar x) j))
                   (trcd_kj))
           (TArrow B B).
(* empty |- (\x:{k:A->A,j:B->B}. x.j) 
              {k=(\z:A.z), j=(\z:B.z)} 
         : B->B *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 2 stars, optional (typing_example_2)  *)
*)
(** **** 練習問題: ★★, optional (typing_example_2)  *)
Example typing_example_2 :
  has_type empty
           (tapp (tabs z (TArrow (TArrow C C) TRcd_j)
                           (tproj (tapp (tvar z)
                                            (tabs x C (tvar x)))
                                    j))
                   (tabs z (TArrow C C) trcd_kj))
           (TArrow B B).
(* empty |- (\z:(C->C)->{j:B->B}. (z (\x:C.x)).j)
              (\z:C->C. {k=(\z:A.z), j=(\z:B.z)})
           : B->B *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Examples2.

(* ================================================================= *)
(*
(** ** Properties of Typing *)
*)
(** ** 型付けの性質 *)

(* ----------------------------------------------------------------- *)
(** *** Well-Formedness *)

Lemma has_type__wf : forall Gamma t T,
  has_type Gamma t T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  - (* T_App *)
    inversion IHHtyp1...
  - (* T_Proj *)
    eapply wf_rcd_lookup...
  - (* T_Sub *)
    apply subtype__wf in H.
    destruct H...
Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr ==> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(*
(** *** Field Lookup *)
*)
(** *** フィールド参照 *)

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  has_type empty v T ->
  Tlookup i T = Some Ti ->
  exists vi, tlookup i v = Some vi /\ has_type empty vi Ti.
Proof with eauto.
  remember empty as Gamma.
  intros t T i Ti Hval Htyp. revert Ti HeqGamma Hval.
  induction Htyp; intros; subst; try solve_by_invert.
  - (* T_Sub *)
    apply (rcd_types_match S) in H0...
    destruct H0 as [Si [HgetSi Hsub]].
    destruct (IHHtyp Si) as [vi [Hget Htyvi]]...
  - (* T_RCons *)
    simpl in H0. simpl. simpl in H1.
    destruct (beq_id i i0).
    + (* i is first *)
      inversion H1. subst. exists t...
    + (* i in tail *)
      destruct (IHHtyp2 Ti) as [vi [get Htyvi]]...
      inversion Hval...  Qed.

(* ----------------------------------------------------------------- *)
(*
(** *** Progress *)
*)
(** *** 進行 *)

(*
(** **** Exercise: 3 stars (canonical_forms_of_arrow_types)  *)
*)
(** **** 練習問題: ★★★ (canonical_forms_of_arrow_types)  *)
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
     has_type Gamma s (TArrow T1 T2) ->
     value s ->
     exists x, exists S1, exists s2,
        s = tabs x S1 s2.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem progress : forall t T,
     has_type empty t T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  - (* T_Var *)
    inversion H.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (tapp t1 t2')...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (tapp t1' t2)...
  - (* T_Proj *)
    right. destruct IHHt...
    + (* rcd is value *)
      destruct (lookup_field_in_value t T i Ti)
        as [t' [Hget Ht']]...
    + (* rcd_steps *)
      destruct H0 as [t' Hstp]. exists (tproj t' i)...
  - (* T_RCons *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2...
      * (* tail steps *)
        right. destruct H2 as [tr' Hstp].
        exists (trcons i t tr')...
    + (* head steps *)
      right. destruct H1 as [t' Hstp].
      exists (trcons i t' tr)...  Qed.

(*
(** _Theorem_ : For any term [t] and type [T], if [empty |- t : T]
    then [t] is a value or [t ==> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given such that [empty |- t : T].  We
    proceed by induction on the given typing derivation.

      - The cases where the last step in the typing derivation is
        [T_Abs] or [T_RNil] are immediate because abstractions and
        [{}] are always values.  The case for [T_Var] is vacuous
        because variables cannot be typed in the empty context.

      - If the last step in the typing derivation is by [T_App], then
        there are terms [t1] [t2] and types [T1] [T2] such that [t =
        t1 t2], [T = T2], [empty |- t1 : T1 -> T2] and [empty |- t2 :
        T1].

        The induction hypotheses for these typing derivations yield
        that [t1] is a value or steps, and that [t2] is a value or
        steps.

        - Suppose [t1 ==> t1'] for some term [t1'].  Then [t1 t2 ==>
          t1' t2] by [ST_App1].

        - Otherwise [t1] is a value.

          - Suppose [t2 ==> t2'] for some term [t2'].  Then [t1 t2 ==>
            t1 t2'] by rule [ST_App2] because [t1] is a value.

          - Otherwise, [t2] is a value.  By Lemma
            [canonical_forms_for_arrow_types], [t1 = \x:S1.s2] for
            some [x], [S1], and [s2].  But then [(\x:S1.s2) t2 ==>
            [x:=t2]s2] by [ST_AppAbs], since [t2] is a value.

      - If the last step of the derivation is by [T_Proj], then there
        are a term [tr], a type [Tr], and a label [i] such that [t =
        tr.i], [empty |- tr : Tr], and [Tlookup i Tr = Some T].

        By the IH, either [tr] is a value or it steps.  If [tr ==>
        tr'] for some term [tr'], then [tr.i ==> tr'.i] by rule
        [ST_Proj1].

        If [tr] is a value, then Lemma [lookup_field_in_value] yields
        that there is a term [ti] such that [tlookup i tr = Some ti].
        It follows that [tr.i ==> ti] by rule [ST_ProjRcd].

      - If the final step of the derivation is by [T_Sub], then there
        is a type [S] such that [S <: T] and [empty |- t : S].  The
        desired result is exactly the induction hypothesis for the
        typing subderivation.

      - If the final step of the derivation is by [T_RCons], then
        there exist some terms [t1] [tr], types [T1 Tr] and a label
        [t] such that [t = {i=t1, tr}], [T = {i:T1, Tr}], [record_ty
        tr], [record_tm Tr], [empty |- t1 : T1] and [empty |- tr :
        Tr].

        The induction hypotheses for these typing derivations yield
        that [t1] is a value or steps, and that [tr] is a value or
        steps.  We consider each case:

        - Suppose [t1 ==> t1'] for some term [t1'].  Then [{i=t1, tr}
          ==> {i=t1', tr}] by rule [ST_Rcd_Head].

        - Otherwise [t1] is a value.

          - Suppose [tr ==> tr'] for some term [tr'].  Then [{i=t1,
            tr} ==> {i=t1, tr'}] by rule [ST_Rcd_Tail], since [t1] is
            a value.

          - Otherwise, [tr] is also a value.  So, [{i=t1, tr}] is a
            value by [v_rcons]. *)
*)
(** 定理： 任意の項[t]と型[T]について、[empty |- t : T]ならば、[t]は値であるか、ある項[t']について [t ==> t'] である。
 
    証明 : [t]と[T]が [empty |- t : T] を満たすとする。
    型付け導出についての帰納法を使う。
 
      - [T_Abs]と[T_RNil]の場合は自明である。関数抽象と[{}]は常に値だからである。
        [T_Var]の場合は考えなくて良い。なぜなら変数は空コンテキストで型付けできないからである。
 
      - 型付け導出の最後のステップが[T_App]の適用だった場合、
        項 [t1] [t2] と型 [T1] [T2] があって [t = t1 t2]、[T = T2]、
        [empty |- t1 : T1 -> T2]、[empty |- t2 : T1] となる。
 
        これらの型付け導出の帰納法の仮定より、[t1]は値であるかステップを進めることができ、
        また[t2]は値であるかステップを進めることができる。
 
        - ある項[t1']について [t1 ==> t1'] とする。
          すると[ST_App1]より [t1 t2 ==> t1' t2] である。
 
        - そうでないならば[t1]は値である。
 
          - ある項[t2']について [t2 ==> t2'] とする。
            すると[t1]が値であることから規則[ST_App2]により [t1 t2 ==> t1 t2'] となる。
 
          - そうでなければ[t2]は値である。補題[canonical_forms_for_arrow_types]により、
            ある[x]、[S1]、[s2]について [t1 = \x:S1.s2] である。
            すると[t2]が値であることから、[ST_AppAbs]により [(\x:S1.s2) t2 ==> [x:=t2]s2] となる。
 
      - 導出の最後のステップが[T_Proj]の適用だった場合、
        項[tr]、型[Tr]、ラベル[i]が存在して [t = tr.i]、[empty |- tr : Tr]、
        [Tlookup i Tr = Some T] となる。
 
        帰納仮定より、[tr]は値であるかステップを進むことができる。
        もしある項[tr']について [tr ==> tr'] ならば、規則[ST_Proj1]より
        [tr.i ==> tr'.i] となる。
 
        もし[tr]が値であれば、補題[lookup_field_in_value]
        により項[ti]が存在して [tlookup i tr = Some ti] となる。
        これから、規則[ST_ProjRcd]より [tr.i ==> ti] となる。
 
      - 導出の最後のステップが[T_Sub]の適用だった場合、
        型[S]が存在して [S <: T] かつ [empty |- t : S] となる。
        求める結果は帰納法の仮定そのものである。
 
      - 導出の最後のステップが[T_RCons]の適用だった場合、
        項[t1] [tr]、型 [T1 Tr]、ラベル[i]が存在して 
        [t = {i=t1, tr}]、[T = {i:T1, Tr}]、[record_tm tr]、
        [record_ty Tr]、[empty |- t1 : T1]、[empty |- tr : Tr] となる。
 
        これらの型付け導出についての帰納法の仮定より、[t1]は値であるか、ステップを進めることができ、
        [tr]は値であるかステップを進めることができることが言える。
        それそれの場合を考える:
 
        - ある項[t1']について [t1 ==> t1'] とする。
          すると規則[ST_Rcd_Head]から [{i=t1, tr} ==> {i=t1', tr}] となる。
 
        - そうではないとき、[t1]は値である。
 
          - ある項[tr']について [tr ==> tr'] とする。
            すると[t1]が値であることから、規則[ST_Rcd_Tail]より 
            [{i=t1, tr} ==> {i=t1, tr'}] となる。
 
          - そうではないとき、[tr]も値である。すると、[v_rcons]から [{i=t1, tr}] は値である。 *)

(* ----------------------------------------------------------------- *)
(*
(** *** Inversion Lemmas *)
*)
(** *** 反転補題 *)

Lemma typing_inversion_var : forall Gamma x T,
  has_type Gamma (tvar x) T ->
  exists S,
    Gamma x = Some S /\ subtype S T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (tvar x) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Var *)
    exists T...
  - (* T_Sub *)
    destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  has_type Gamma (tapp t1 t2) T2 ->
  exists T1,
    has_type Gamma t1 (TArrow T1 T2) /\
    has_type Gamma t2 T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (tapp t1 t2) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_App *)
    exists T1...
  - (* T_Sub *)
    destruct IHHty as [U1 [Hty1 Hty2]]...
    assert (Hwf := has_type__wf _ _ _ Hty2).
    exists U1...  Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     has_type Gamma (tabs x S1 t2) T ->
     (exists S2, subtype (TArrow S1 S2) T
              /\ has_type (update Gamma x S1) t2 S2).
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (tabs x S1 t2) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    assert (Hwf := has_type__wf _ _ _ H0).
    exists T12...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
    Qed.

Lemma typing_inversion_proj : forall Gamma i t1 Ti,
  has_type Gamma (tproj t1 i) Ti ->
  exists T, exists Si,
    Tlookup i T = Some Si /\ subtype Si Ti /\ has_type Gamma t1 T.
Proof with eauto.
  intros Gamma i t1 Ti H.
  remember (tproj t1 i) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Proj *)
    assert (well_formed_ty Ti) as Hwf.
    { (* pf of assertion *)
      apply (wf_rcd_lookup i T Ti)...
      apply has_type__wf in H... }
    exists T. exists Ti...
  - (* T_Sub *)
    destruct IHhas_type as [U [Ui [Hget [Hsub Hty]]]]...
    exists U. exists Ui...  Qed.

Lemma typing_inversion_rcons : forall Gamma i ti tr T,
  has_type Gamma (trcons i ti tr) T ->
  exists Si, exists Sr,
    subtype (TRCons i Si Sr) T /\ has_type Gamma ti Si /\
    record_tm tr /\ has_type Gamma tr Sr.
Proof with eauto.
  intros Gamma i ti tr T Hty.
  remember (trcons i ti tr) as t.
  induction Hty;
    inversion Heqt; subst...
  - (* T_Sub *)
    apply IHHty in H0.
    destruct H0 as [Ri [Rr [HsubRS [HtypRi HtypRr]]]].
    exists Ri. exists Rr...
  - (* T_RCons *)
    assert (well_formed_ty (TRCons i T Tr)) as Hwf.
    { (* pf of assertion *)
      apply has_type__wf in Hty1.
      apply has_type__wf in Hty2... }
    exists T. exists Tr...  Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  has_type empty (tabs x S1 s2) (TArrow T1 T2) ->
     subtype T1 S1
  /\ has_type (update empty x S1) s2 T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...  Qed.

(* ----------------------------------------------------------------- *)
(*
(** *** Context Invariance *)
*)
(** *** コンテキスト不変性 *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tabs y T11 t12)
  | afi_proj : forall x t i,
      appears_free_in x t ->
      appears_free_in x (tproj t i)
  | afi_rhead : forall x i t tr,
      appears_free_in x t ->
      appears_free_in x (trcons i t tr)
  | afi_rtail : forall x i t tr,
      appears_free_in x tr ->
      appears_free_in x (trcons i t tr).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     has_type Gamma' t S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type. intros x0 Hafi.
    unfold update, t_update. destruct (beq_idP x x0)...
  - (* T_App *)
    apply T_App with T1...
  - (* T_RCons *)
    apply T_RCons...  Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; subst; inversion Hafi; subst...
  - (* T_Abs *)
    destruct (IHHtyp H5) as [T Hctx]. exists T.
    unfold update, t_update in Hctx.
    rewrite false_beq_id in Hctx...  Qed.

(* ----------------------------------------------------------------- *)
(*
(** *** Preservation *)
*)
(** *** 保存 *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (update Gamma x U) t S  ->
     has_type empty v U   ->
     has_type Gamma ([x:=v]t) S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  - (* tvar *)
    rename i into y.
    destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].
    unfold update, t_update in Hctx.
    destruct (beq_idP x y)...
    + (* x=y *)
      subst.
      inversion Hctx; subst. clear Hctx.
      apply context_invariance with empty...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    + (* x<>y *)
      destruct (subtype__wf _ _ Hsub)...
  - (* tapp *)
    destruct (typing_inversion_app _ _ _ _ Htypt)
      as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  - (* tabs *)
    rename i into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt)
      as [T2 [Hsub Htypt2]].
    destruct (subtype__wf _ _ Hsub) as [Hwf1 Hwf2].
    inversion Hwf2. subst.
    apply T_Sub with (TArrow T1 T2)... apply T_Abs...
    destruct (beq_idP x y).
    + (* x=y *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (beq_id y x)...
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (beq_idP y z)...
      subst.  rewrite false_beq_id...
  - (* tproj *)
    destruct (typing_inversion_proj _ _ _ _ Htypt)
      as [T [Ti [Hget [Hsub Htypt1]]]]...
  - (* trnil *)
    eapply context_invariance...
    intros y Hcontra. inversion Hcontra.
  - (* trcons *)
    destruct (typing_inversion_rcons _ _ _ _ _ Htypt) as
      [Ti [Tr [Hsub [HtypTi [Hrcdt2 HtypTr]]]]].
    apply T_Sub with (TRCons i Ti Tr)...
    apply T_RCons...
    + (* record_ty Tr *)
      apply subtype__wf in Hsub. destruct Hsub. inversion H0...
    + (* record_tm ([x:=v]t2) *)
      inversion Hrcdt2; subst; simpl...  Qed.

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t ==> t'  ->
     has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T...
  - (* T_Proj *)
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Hty]].
    rewrite H4 in Hget. inversion Hget. subst...
  - (* T_RCons *)
    eauto using step_preserves_record_tm.  Qed.

(*
(** _Theorem_: If [t], [t'] are terms and [T] is a type such that
     [empty |- t : T] and [t ==> t'], then [empty |- t' : T].

    _Proof_: Let [t] and [T] be given such that [empty |- t : T].  We go
     by induction on the structure of this typing derivation, leaving
     [t'] general.  Cases [T_Abs] and [T_RNil] are vacuous because
     abstractions and [{}] don't step.  Case [T_Var] is vacuous as well,
     since the context is empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] [t2] and types [T1] [T2] such that [t = t1 t2],
       [T = T2], [empty |- t1 : T1 -> T2] and [empty |- t2 : T1].

       By inspection of the definition of the step relation, there are
       three ways [t1 t2] can step.  Cases [ST_App1] and [ST_App2]
       follow immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then
       [t1 = \x:S.t12] for some type [S] and term [t12], and
       [t' = [x:=t2]t12].

       By Lemma [abs_arrow], we have [T1 <: S] and [x:S1 |- s2 : T2].
       It then follows by lemma [substitution_preserves_typing] that
       [empty |- [x:=t2] t12 : T2] as desired.

     - If the final step of the derivation is by [T_Proj], then there
       is a term [tr], type [Tr] and label [i] such that [t = tr.i],
       [empty |- tr : Tr], and [Tlookup i Tr = Some T].

       The IH for the typing derivation gives us that, for any term
       [tr'], if [tr ==> tr'] then [empty |- tr' Tr].  Inspection of
       the definition of the step relation reveals that there are two
       ways a projection can step.  Case [ST_Proj1] follows
       immediately by the IH.

       Instead suppose [tr.i] steps by [ST_ProjRcd].  Then [tr] is a
       value and there is some term [vi] such that
       [tlookup i tr = Some vi] and [t' = vi].  But by lemma
       [lookup_field_in_value], [empty |- vi : Ti] as desired.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |- t : S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].

     - If the final step of the derivation is by [T_RCons], then there
       exist some terms [t1] [tr], types [T1 Tr] and a label [t] such
       that [t = {i=t1, tr}], [T = {i:T1, Tr}], [record_ty tr],
       [record_tm Tr], [empty |- t1 : T1] and [empty |- tr : Tr].

       By the definition of the step relation, [t] must have stepped
       by [ST_Rcd_Head] or [ST_Rcd_Tail].  In the first case, the
       result follows by the IH for [t1]'s typing derivation and
       [T_RCons].  In the second case, the result follows by the IH
       for [tr]'s typing derivation, [T_RCons], and a use of the
       [step_preserves_record_tm] lemma. *)
*)
(** 定理: [t]、[t']が項で[T]が型であり [empty |- t : T] かつ [t ==> t'] ならば、
     [empty |- t' : T] である。
 
    証明: [t]と[T]が [empty |- t : T] であるとする。
     [t']を特化しないまま、型付け導出の構造についての帰納法で証明を進める。
     [T_Abs]と[T_RNil]の場合は考える必要はない。関数抽象と[{}]は進まないからである。
     [T_Var]の場合も同様に考える必要はない。コンテキストが空だからである。
 
     - もし導出の最後ステップで使った規則が[T_App]ならば、
       項[t1] [t2]と型[T1] [T2]があり、[t = t1 t2]、
       [T = T2]、[empty |- t1 : T1 -> T2]、[empty |- t2 : T1] である。
 
       ステップ関係の定義を見ることにより、 [t1 t2] がステップを進める方法は3通りであることがわかる。
       [ST_App1]と[ST_App2]の場合は型付け導出の帰納法の仮定と[T_App]を使うことで、
       すぐに証明が完了する。
 
       そうではなく[ST_AppAbs]により [t1 t2] がステップを進めるとする。
       すると、ある型[S]と項[t12]について [t1 = \x:S.t12] かつ [t' = [x:=t2]t12] となる。
 
       補題[abs_arrow]より、[T1 <: S] かつ [x:S1 |- s2 : T2] であるから、
       補題[substitution_preserves_typing]より [empty |- [x:=t2] t12 : T2] となり、これが求める結果である。
 
     - もし導出の最後ステップで使った規則が[T_Proj]ならば、
       項[tr]、型[Tr]、ラベル[i]が存在して [t = tr.i] かつ [empty |- tr : Tr]
       かつ [Tlookup i Tr = Some T] となる。
 
       型付け導出の帰納仮定より、任意の項[tr']について、[tr ==> tr'] ならば [empty |- tr' Tr] である。
       ステップ関係の定義より、射影がステップを進める方法は2つである。
       [ST_Proj1]の場合は帰納仮定からすぐに証明される。
 
       そうではなく[tr.i]のステップが[ST_ProjRcd]による場合、
       [tr]は値であり、ある項[vi]があって [tlookup i tr = Some vi] かつ
       [t' = vi] となる。しかし補題[lookup_field_in_value]より
       [empty |- vi : Ti] となるが、これが求める結果である。
 
     - もし導出の最後ステップで使った規則が[T_Sub]ならば、型[S]が存在して
       [S <: T] かつ [empty |- t : S] となる。
       型付け導出の帰納法の仮定と[T_Sub]の適用により結果がすぐに得られる。
 
     - もし導出の最後ステップで使った規則が[T_RCons]ならば、
       項 [t1] [tr]、型 [T1 Tr]、ラベル[i]が存在して
       [t = {i=t1, tr}]、[T = {i:T1, Tr}]、[record_tm tr]、
       [record_ty Tr]、[empty |- t1 : T1]、[empty |- tr : Tr] となる。
 
       ステップ関係の定義より、[t]は[ST_Rcd_Head]または[ST_Rcd_Tail]
       によってステップを進めたはずである。[ST_Rcd_Head]の場合、
       [t1]の型付け導出についての帰納仮定と[T_RCons]より求める結果が得られる。
       [ST_Rcd_Tail]の場合、[tr]の型付け導出についての帰納仮定、[T_RCons]、
       および[step_preserves_record_tm]補題の使用から求める結果が得られる。 *)

(** $Date: 2017-08-23 17:50:06 -0400 (Wed, 23 Aug 2017) $ *)

