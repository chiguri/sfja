(** * HoareAsLogic: 論理としてのホーア論理 *)
(* begin hide *)
(** * HoareAsLogic: Hoare Logic as a Logic *)
(* end hide *)

(* begin hide *)
(** The presentation of Hoare logic in chapter [Hoare] could be
    described as "model-theoretic": the proof rules for each of the
    constructors were presented as _theorems_ about the evaluation
    behavior of programs, and proofs of program correctness (validity
    of Hoare triples) were constructed by combining these theorems
    directly in Coq.

    Another way of presenting Hoare logic is to define a completely
    separate proof system -- a set of axioms and inference rules that
    talk about commands, Hoare triples, etc. -- and then say that a
    proof of a Hoare triple is a valid derivation in _that_ logic.  We
    can do this by giving an inductive definition of _valid
    derivations_ in this new logic.

    This chapter is optional.  Before reading it, you'll want to read
    the [ProofObjects] chapter in _Logical
    Foundations_ (_Software Foundations_, volume 1). *)
(* end hide *)
(** [Hoare]の章におけるホーア論理の提示を「モデル理論的」("model-theoretic")に行うこともできたでしょう。
    それぞれのコンストラクタに対する証明規則をプログラムの振舞いについての「定理」として提示し、プログラムの正しさ（ホーアの三つ組の正しさ）の証明は、
    それらの定理をCoq内で直接組み合わせることで構成するのです。
 
    ホーア論理を提示するもう一つの方法は、完全に別個の証明体系を定義することです。
    コマンドやホーアの三つ組等についての公理と推論規則の集合を定めます。
    ホーアの三つ組の証明とは、定義されたこの論理で正しく導出されたもののことになります。
    こうするためには、新しい論理で正しい導出(_valid derivations_)の帰納的定義を与えれば良いのです。
 
    この章はオプションです。
    先に「論理の基礎」（「ソフトウェアの基礎」の第一巻）の[ProofObjects]の章を読んだ方がいいかもしれません。 *)

From PLF Require Import Imp.
From PLF Require Import Hoare.

(* ################################################################# *)
(* begin hide *)
(** * Definitions *)
(* end hide *)
(** * 定義 *)

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      hoare_proof P (SKIP) P
  | H_Asgn : forall Q V a,
      hoare_proof (assn_sub V a Q) (V ::= a) Q
  | H_Seq  : forall P c Q d R,
      hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;;d) R
  | H_If : forall P Q b c1 c2,
    hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
    hoare_proof P (TEST b THEN c1 ELSE c2 FI) Q
  | H_While : forall P b c,
    hoare_proof (fun st => P st /\ bassn b st) c P ->
    hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~ (bassn b st))
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

(** We don't need to include axioms corresponding to
    [hoare_consequence_pre] or [hoare_consequence_post], because
    these can be proven easily from [H_Consequence]. *)

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
    apply X.  apply H.  intros. apply H0. Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
    apply X. intros. apply H0.  apply H. Qed.

(* begin hide *)
(** As an example, let's construct a proof object representing a
    derivation for the hoare triple

      {{(X=3) [X |-> X + 2] [X |-> X + 1]}}
      X::=X+1 ;; X::=X+2
      {{X=3}}.

    We can use Coq's tactics to help us construct the proof object. *)
(* end hide *)
(** 例として、ホーアの三つ組
[[
      {{(X=3) [X |-> X + 2] [X |-> X + 1]}} 
      X::=X+1 ;; X::=X+2  
      {{X=3}} 
]]
    の導出を表現する証明オブジェクトを構成しましょう。
    証明オブジェクトを構成するのに Coq のタクティックを使うことができます。*)

Example sample_proof :
  hoare_proof
    ((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
    (X ::= X + 1;; X ::= X + 2)
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq; apply H_Asgn.
Qed.

(*
Print sample_proof.

====>
  H_Seq
  (((fun st : state => st X = 3) [X |-> X + 2]) [X |-> X + 1])
  (X ::= X + 1)
  ((fun st : state => st X = 3) [X |-> X + 2])
  (X ::= X + 2)
  (fun st : state => st X = 3)
  (H_Asgn
     ((fun st : state => st X = 3) [X |-> X + 2])
     X (X + 1))
  (H_Asgn
     (fun st : state => st X = 3)
     X (X + 2))
*)

(* ################################################################# *)
(* begin hide *)
(** * Properties *)
(* end hide *)
(** * 性質 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard (hoare_proof_sound)  

    Prove that such proof objects represent true claims. *)
(* end hide *)
(** **** 練習問題: ★★, standard (hoare_proof_sound)
 
    これらの証明オブジェクトが真の主張を表現することを証明しなさい。*)

Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** We can also use Coq's reasoning facilities to prove metatheorems
    about Hoare Logic.  For example, here are the analogs of two
    theorems we saw in chapter [Hoare] -- this time expressed in terms
    of the syntax of Hoare Logic derivations (provability) rather than
    directly in terms of the semantics of Hoare triples.

    The first one says that, for every [P] and [c], the assertion
    [{{P}} c {{True}}] is _provable_ in Hoare Logic.  Note that the
    proof is more complex than the semantic proof in [Hoare]: we
    actually need to perform an induction over the structure of the
    command [c]. *)
(* end hide *)
(** Coqの推論機構をホーア論理についてのメタ定理を証明することに使うこともできます。
    例えば、[Hoare]で見た2つの定理に対応するものを以下に示します。
    ここではホーアの三つ組の意味論から直接にではなく、ホーア論理の導出（証明可能性）の構文の面から表現します。
 
    最初のものは、すべての[P]と[c]について、表明[{{P}} c {{True}}]がホーア論理で証明可能(_provable_)であることを言うものです。
    [Hoare]における意味論的証明と比べて、この証明はより複雑になることに注意して下さい。
    実際、コマンド[c]の構造についての帰納法を行う必要があります。*)

Theorem H_Post_True_deriv:
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intro c.
  induction c; intro P.
  - (* SKIP *)
    eapply H_Consequence.
    apply H_Skip.
    intros. apply H.
    (* Proof of True *)
    intros. apply I.
  - (* ::= *)
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros. apply I.
  - (* ;; *)
    eapply H_Consequence_pre.
    eapply H_Seq.
    apply (IHc1 (fun _ => True)).
    apply IHc2.
    intros. apply I.
  - (* TEST *)
    apply H_Consequence_pre with (fun _ => True).
    apply H_If.
    apply IHc1.
    apply IHc2.
    intros. apply I.
  - (* WHILE *)
    eapply H_Consequence.
    eapply H_While.
    eapply IHc.
    intros; apply I.
    intros; apply I.
Qed.

(* begin hide *)
(** Similarly, we can show that [{{False}} c {{Q}}] is provable for
    any [c] and [Q]. *)
(* end hide *)
(** 同様に、任意の[c]と[Q]について[{{False}} c {{Q}}]が証明可能であることを示すことができます。*)

Lemma False_and_P_imp: forall P Q,
  False /\ P -> Q.
Proof.
  intros P Q [CONTRA HP].
  destruct CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros c.
  induction c; intro Q.
  - (* SKIP *) pre_false_helper H_Skip.
  - (* ::= *) pre_false_helper H_Asgn.
  - (* ;; *) pre_false_helper H_Seq. apply IHc1. apply IHc2.
  - (* TEST *)
    apply H_If; eapply H_Consequence_pre.
    apply IHc1. intro. eapply False_and_P_imp.
    apply IHc2. intro. eapply False_and_P_imp.
  - (* WHILE *)
    eapply H_Consequence_post.
    eapply H_While.
    eapply H_Consequence_pre.
      apply IHc.
      intro. eapply False_and_P_imp.
    intro. simpl. eapply False_and_P_imp.
Qed.

(** As a last step, we can show that the set of [hoare_proof] axioms
    is sufficient to prove any true fact about (partial) correctness.
    More precisely, any semantic Hoare triple that we can prove can
    also be proved from these axioms.  Such a set of axioms is said to
    be _relatively complete_.  Our proof is inspired by this one:

      http://www.ps.uni-saarland.de/courses/sem-ws11/script/Hoare.html

    To carry out the proof, we need to invent some intermediate
    assertions using a technical device known as _weakest
    preconditions_.  Given a command [c] and a desired postcondition
    assertion [Q], the weakest precondition [wp c Q] is an assertion
    [P] such that [{{P}} c {{Q}}] holds, and moreover, for any other
    assertion [P'], if [{{P'}} c {{Q}}] holds then [P' -> P].  We can
    more directly define this as follows: *)

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

(** **** Exercise: 1 star, standard (wp_is_precondition)  *)

Lemma wp_is_precondition: forall c Q,
  {{wp c Q}} c {{Q}}.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (wp_is_weakest)  *)

Lemma wp_is_weakest: forall c Q P',
   {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
(* FILL IN HERE *) Admitted.

(** The following utility lemma will also be useful. *)

Lemma bassn_eval_false : forall b st, ~ bassn b st -> beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard (hoare_proof_complete)  

    Complete the proof of the theorem. *)

Theorem hoare_proof_complete: forall P c Q,
  {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - (* SKIP *)
    eapply H_Consequence.
     eapply H_Skip.
      intros.  eassumption.
      intro st. apply HT.  apply E_Skip.
  - (* ::= *)
    eapply H_Consequence.
      eapply H_Asgn.
      intro st. apply HT. econstructor. reflexivity.
      intros; assumption.
  - (* ;; *)
    apply H_Seq with (wp c2 Q).
     eapply IHc1.
       intros st st' E1 H. unfold wp. intros st'' E2.
         eapply HT. econstructor; eassumption. assumption.
     eapply IHc2. intros st st' E1 H. apply H; assumption.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** Finally, we might hope that our axiomatic Hoare logic is
    _decidable_; that is, that there is an (terminating) algorithm (a
    _decision procedure_) that can determine whether or not a given
    Hoare triple is valid (derivable).  But such a decision procedure
    cannot exist!

    Consider the triple [{{True}} c {{False}}]. This triple is valid
    if and only if [c] is non-terminating.  So any algorithm that
    could determine validity of arbitrary triples could solve the
    Halting Problem.

    Similarly, the triple [{{True}} SKIP {{P}}] is valid if and only if
    [forall s, P s] is valid, where [P] is an arbitrary assertion of
    Coq's logic. But it is known that there can be no decision
    procedure for this logic.

    Overall, this axiomatic style of presentation gives a clearer
    picture of what it means to "give a proof in Hoare logic."
    However, it is not entirely satisfactory from the point of view of
    writing down such proofs in practice: it is quite verbose.  The
    section of chapter [Hoare2] on formalizing decorated programs
    shows how we can do even better. *)
(* end hide *)
(** 最後に、この公理的ホーア論理が「決定可能(_decidable_)」であればとても喜ばしいでしょう。
    つまり、ある（終了する）アルゴリズム（決定手続き(_decision procedure_)）が、ホーアの三つ組が妥当（導出可能）かを判定してくれると嬉しいでしょう。
    しかしそんな決定手続きは存在しないのです！
 
    [{{True}} c {{False}}] という三つ組を考えてみましょう。
    この三つ組は、[c]が終了しないとき、かつそのときに限り妥当です。
    つまり、これが妥当かを判定するアルゴリズムは、停止性問題を解いてしまうのです。
 
    同様に、任意のCoqの論理における言明 [P] に対して、三つ組 [{{True} SKIP {{P}}] は [forall s, P s] が妥当であるとき、かつそのときに限り妥当です。
    しかし、そのような決定手続きがないことも知られています。
 
    全体として、この表現の公理的形式は「ホーア論理の証明を与えること」がどういう意味なのかについて、より明確なイメージを与えてくれます。
    しかし、実際の証明を記述するという観点からは完全に満足できるものではありません。
    かなりくどいのです。
    [Hoare2]の修飾付きプログラムの形式化の節が、より良い方法を示してくれます。*)

(* Thu Feb 7 20:09:23 EST 2019 *)
