(** * Types: 型システム *)
(* * Types: Type Systems *)

Require Export Smallstep.

Hint Constructors multi.  

(* Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of a very simple
    language with just booleans and numbers, to introduce the basic
    ideas of types, typing rules, and the fundamental theorems about
    type systems: _type preservation_ and _progress_.  Then we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq). *)
(**
   次に取り組む内容は型システムです。型システムは、式をその評価結果の「かたち」で分類する静的解析手法です。まずは、ブール値と数のみから成る言語から始め、型に関する基本的な考え方や型付け規則、型保存（type preservation）や進行（progress）といった型システムに関する基礎的な定理を導入します。その次に単純型付きラムダ計算に移ります。単純型付きラムダ計算は（Coq を含む）近代的な関数型プログラミング言語すべての中心概念になっています。
*)

(* ###################################################################### *)
(* * Typed Arithmetic Expressions *)
(** * 型付きの算術式 *)

(* To motivate the discussion of type systems, let's begin as
    usual with an extremely simple toy language.  We want it to have
    the potential for programs "going wrong" because of runtime type
    errors, so we need something a tiny bit more complex than the
    language of constants and addition that we used in chapter
    [Smallstep]: a single kind of data (just numbers) is too simple,
    but just two kinds (numbers and booleans) already gives us enough
    material to tell an interesting story.

    The language definition is completely routine.  *)
(**
   型システムについての議論を始めるために、例のごとく、ごく単純な言語から始めましょう。この言語は、実行時の型エラーで「まずいことが起きる」可能性のあるものであってほしいので、 [Smallstep] 章で使った、定数と足し算だけの言語よりはもう少し複雑なものでなければなりません。データが一種類だけ（数のみ）では単純すぎますが、二種類（数とブール値）なら、実験のための材料はもう揃っています。

   言語の定義はいつも通り、お決まりの作業です。  *)

(* ###################################################################### *)
(* ** Syntax *)
(** ** 構文 *)

(* Informally:
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
    Formally:
*)
(** 非形式的には:
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
    形式的には:
*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

(* _Values_ are [true], [false], and numeric values... *)
(** 値(_Values_)は [true] や [false] 、そして数値です... *)

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.  
Hint Unfold extend.

(* ###################################################################### *)
(* ** Operational Semantics *)
(** ** 操作的意味論 *)

(* Informally: *)
(** 非形式的には: *)
(**
                    ------------------------------                  (ST_IfTrue)
                    if true then t1 else t2 ==> t1

                   -------------------------------                 (ST_IfFalse)
                   if false then t1 else t2 ==> t2

                              t1 ==> t1'
                      -------------------------                         (ST_If)
                      if t1 then t2 else t3 ==>
                        if t1' then t2 else t3

                              t1 ==> t1'
                         --------------------                         (ST_Succ)
                         succ t1 ==> succ t1'

                             ------------                         (ST_PredZero)
                             pred 0 ==> 0

                           numeric value v1
                        ---------------------                     (ST_PredSucc)
                        pred (succ v1) ==> v1

                              t1 ==> t1'
                         --------------------                         (ST_Pred)
                         pred t1 ==> pred t1'

                          -----------------                     (ST_IszeroZero)
                          iszero 0 ==> true

                           numeric value v1
                      --------------------------                (ST_IszeroSucc)
                      iszero (succ v1) ==> false

                              t1 ==> t1'
                       ------------------------                     (ST_Iszero)
                       iszero t1 ==> iszero t1'
*)

(* Formally: *)
(** 形式的には: *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" 
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred" 
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.
(* Notice that the [step] relation doesn't care about whether
    expressions make global sense -- it just checks that the operation
    in the _next_ reduction step is being applied to the right kinds
    of operands.  

    For example, the term [succ true] (i.e., [tsucc ttrue] in the
    formal syntax) cannot take a step, but the almost as obviously
    nonsensical term
       succ (if true then true else true) 
    can take a step (once, before becoming stuck). *)
(** [step] 関係は式が大域的に意味を持つかは考慮せず、次の簡約が適切な種類の被演算子に適用されているかだけを確認していることに注意してください。

    例えば、 [tm_succ tm_true] (形式的文法では [tsucc ttrue]) は先に進むことはできませんが、明らかに同程度には意味のない項
       succ (if true then true else true) 
    は(行き詰まるまでに1ステップ)進めることができます。 *)

(* ###################################################################### *)
(* ** Normal Forms and Values *)
(** ** 正規形と値 *)

(* The first interesting thing about the [step] relation in this
    language is that the strong progress theorem from the Smallstep
    chapter fails!  That is, there are terms that are normal
    forms (they can't take a step) but not values (because we have not
    included them in our definition of possible "results of
    evaluation").  Such terms are _stuck_. *)
(**
   この言語の [step] 関係について、まず注目に値するのは、 Smallstep 章の強進行性定理（strong progress theorem）が成り立たないということです。すなわち、正規形ではあるのに（これ以上簡約できないのに）、値ではない項があるのです（これは、そのような項を可能な「評価結果」と定義しなかったからです）。そのような項は [stuck] します。
   *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(* **** Exercise: 2 stars (some_term_is_stuck)  *)
(** **** 練習問題: ★★, optional (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* However, although values and normal forms are not the same in this
    language, the former set is included in the latter.  This is
    important because it shows we did not accidentally define things
    so that some value could still take a step. *)
(**
   ただし、この言語では値の集合と正規形の集合は同一ではありませんが、値は正規形に含まれます。これは重要なことで、さらに簡約できる値を定義しまうことはできないことを表しています。
   *)

(* **** Exercise: 3 stars, advanced (value_is_nf)  *)
(** **** 練習問題: ★★★, advanced (value_is_nf)  *)
(* Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)
(**
   ヒント: 証明中で、数値であることがわかっている項に対して帰納的推論をしなければならないことになります。この帰納法は、その項自体にして適用することもできますし、その項が数値であるという事実に対して適用することもできます。どちらでも証明は進められますが、片方はもう片方よりもかなり短かくなります。練習として、ふたつの方法両方で証明を完成させなさい。
   *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* **** Exercise: 3 stars, optional (step_deterministic)  *)
(** **** 練習問題: ★★★, optional (step_deterministic)  *)
(* Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)
(**
   [value_is_nf] を使うと、 [step] 関係もまた決定的であることが示せます。
   *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ###################################################################### *)
(* ** Typing *)
(** ** 型付け *)

(* The next critical observation about this language is that,
    although there are stuck terms, they are all "nonsensical", mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)
(** 次にこの言語から見て取れる非常に重要なことは、行き詰まる項があったとしても、そのような項は、我々としても意味を持ってほしくないようなブール値と数の取り混ぜ方をしたもので、すべて「意味がない」ということです。項とその評価結果の型（数かブール値）を関係づける型付け関係を定義することで、そのような、型の付かない項を除くことができます。
   *)

Inductive ty : Type := 
  | TBool : ty
  | TNat : ty.

(* In informal notation, the typing relation is often written
    [|- t \in T], pronounced "[t] has type [T]."  The [|-] symbol is
    called a "turnstile".  (Below, we're going to see richer typing
    relations where an additional "context" argument is written to the
    left of the turnstile.  Here, the context is always empty.) *)
(** 非形式的な記法では、型付け関係を [|- t \in T] と書き、「[t] の型は [T] である」と読みます。記号 [|-] は「ターンスタイル（turnstile）」と呼びます。（後の章ではターンスタイルの左側に追加の「コンテキスト」引数のある型付け関係もあります。ここでは、コンテキストは常に空です。） *)
(** 
                           ----------------                            (T_True)
                           |- true \in Bool

                          -----------------                           (T_False)
                          |- false \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------                (T_If)
                    |- if t1 then t2 else t3 \in T

                             ------------                              (T_Zero)
                             |- 0 \in Nat
                              
                            |- t1 \in Nat
                          ------------------                           (T_Succ)
                          |- succ t1 \in Nat

                            |- t1 \in Nat
                          ------------------                           (T_Pred)
                          |- pred t1 \in Nat

                            |- t1 \in Nat
                        ---------------------                        (T_IsZero)
                        |- iszero t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* ###################################################################### *)
(* *** Examples *)
(** *** 例 *)

(* It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not calculate
    the type of the normal form of a term. *)
(**
   型付け関係というのは保守的な（または静的な）近似であり、項の正規形の型を計算しているわけではない、ということをよく理解しておいてください。
   *)

Example has_type_1 : 
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof. 
  apply T_If. 
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.  
Qed.

(* (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)
(**
   （型付け関係のすべての構成子をヒントデータベースに登録してあるので、実際には [auto] で証明を自動的に構築することができます。）
   *)

Example has_type_not : 
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
  intros Contra. solve by inversion 2.  Qed.

(* **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat)  *)
(** **** 練習問題: ★, optional (succ_hastype_nat__hastype_nat)  *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.  
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Canonical forms *)

(** The following two lemmas capture the basic property that defines
    the shape of well-typed values.  They say that the definition of value
    and the typing relation agree. *)

Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.

  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.   

  auto.  
Qed.

(* ###################################################################### *)
(* ** Progress *)
(** ** 進行 *)

(* The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)
(**
   型付け関係には重要な性質がふたつあります。最初のものは、型のついた（well-typed）正規形は値である（行き詰まらない）、ということです。
   *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

(* **** Exercise: 3 stars (finish_progress)  *)
(** **** 練習問題: ★★★ (finish_progress)  *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  (* T_True や T_False のような、値であることが明らかな場合は [auto] で片付けられる。 *)
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value".
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, advanced (finish_progress_informal)  *)
(** **** 練習問題: ★★★, advanced (finish_progress_informal)  *)
(* Complete the corresponding informal proof: *)
(** 上と対応する以下の非形式的な証明を完成させなさい。 *)

(* _Theorem_: If [|- t \in T], then either [t] is a value or else 
    [t ==> t'] for some [t']. *)
(** 定理: [|- t \in T] であれば、 [t] は値であるか、さもなければある [t'] に対して [t ==> t'] である。 *)

(** _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].  By the IH, either [t1] is a value or else [t1] can step
        to some [t1'].  

            - If [t1] is a value, then by the canonical forms lemmas
              and the fact that [|- t1 \in Bool] we have that [t1] 
              is a [bvalue] -- i.e., it is either [true] or [false].
              If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
              while if [t1 = false], then [t] steps to [t3] by
              [ST_IfFalse].  Either way, [t] can step, which is what
              we wanted to show.

            - If [t1] itself can take a step, then, by [ST_If], so can
              [t].

    (* FILL IN HERE *)
[] *)
(** 証明: [|- t \in T] の導出に関する帰納法で証明する。

      - 導出で直前に適用した規則が [T_If] である場合、 [t = if t1 then t2 else t3] かつ、 [|- t1 \in Bool]、 [|- t2 \in T] かつ [|- t3 \in T] である。帰納法の仮定から、 [t1] が値であるか、さもなければ [t1] が何らかの [t1'] に簡約できる。

            - [t1] が値のとき、 canonical forms lemma と [|- t1 \in Bool] という事実から [t1] は [bvalue] である。すなわち、 [true] または [false] である。 [t1 = true] のとき、 [ST_IfTrue] より [t] は [t2] に簡約され、 [t1 = false] のときは [ST_IfFalse] から [t] は [t3] に簡約される。どちらの場合も [t] の簡約は進められる。これが示そうとしていたことである。

            - [t1] 自体が簡約できるので、 [ST_If] を用いることで [t] もまた簡約できる。

    (* FILL IN HERE *)
[] *)

(* This is more interesting than the strong progress theorem that we
    saw in the Smallstep chapter, where _all_ normal forms were
    values.  Here, a term can be stuck, but only if it is ill
    typed. *)
(** この定理は Smallstep の章の強進行性定理よりも興味深いものです。 Smallstep のものは正規形はすべて値でした。本章では項が行き詰まることもありますが、行き詰まるようなものは型のつかないものだけです。 *)

(* **** Exercise: 1 star (step_review)  *)
(** **** 練習問題: ★ (step_review)  *)
(* Quick review.  Answer _true_ or _false_.  In this language...
      - Every well-typed normal form is a value.

      - Every value is a normal form.

      - The single-step evaluation relation is
        a partial function (i.e., it is deterministic).

      - The single-step evaluation relation is a _total_ function.

*)
(** おさらい: 「はい」か「いいえ」（true か false）で答えなさい。この言語では、
      - 型のついた正規形はすべて値である。

      - 値はすべて正規形である。

      - ワンステップ評価関係は全域関数である。

*)
(** [] *)

(* ###################################################################### *)
(* ** Type Preservation *)
(** ** 型保存 *)

(* The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term.

    This theorem is often called the _subject reduction_ property,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)
(** 型付けの第二の重要な性質は、型のついた項を一段階簡約すると、簡約結果もまた型のつく項である、ということです。

    この定理は主部簡約（subject reduction）性と呼ばれることが多々あります。これは、この定理が型付け関係の主部が簡約されるときに起こることについて言っているからです。この用語は型付けを文として見たことによるもので、項が主部（subject）、型が述部（predicate）に当たります。 *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(* **** Exercise: 2 stars (finish_preservation)  *)
(** **** 練習問題: ★★ (finish_preservation)  *)
(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
         (* every case needs to introduce a couple of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst; clear HE.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, advanced (finish_preservation_informal)  *)
(** **** 練習問題: ★★★, advanced (finish_preservation_informal)  *)
(* Complete the following proof: *)
(** 以下の証明を完成させなさい。 *)

(* _Theorem_: If [|- t \in T] and [t ==> t'], then [|- t' \in T]. *)
(** 定理: [|- t \in T] かつ [t ==> t'] ならば [|- t' \in T] *)

(* _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].  

        Inspecting the rules for the small-step reduction relation and
        remembering that [t] has the form [if ...], we see that the
        only ones that could have been used to prove [t ==> t'] are
        [ST_IfTrue], [ST_IfFalse], or [ST_If].

           - If the last rule was [ST_IfTrue], then [t' = t2].  But we
             know that [|- t2 \in T], so we are done.

           - If the last rule was [ST_IfFalse], then [t' = t3].  But we
             know that [|- t3 \in T], so we are done.

           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 \in Bool] so,
             by the IH, [|- t1' \in Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 \in T], as required.

    (* FILL IN HERE *)
[] *)
(** 証明: [|- t \in T] の導出に関する帰納法で証明する。

      - 導出で直前に使った規則が [T_If] の場合、 [t = if t1 then t2 else t3]、かつ [|- t1 \in Bool]、 [|- t2 \in T] かつ [|- t3 \in T] である。

        [t] が [if ...] の形式であることとスモールステップ簡約関係を見ると、 [t ==> t'] を示すために使えるのは [ST_IfTrue]、 [ST_IfFalse] または [ST_If] のみである。

           - 直前の規則が [ST_IfTrue] の場合、 [t' = t2] である。 [|- t2 \in T] であるのでこれは求める結果である。

           - 直前の規則が [ST_IfFalse] の場合、 [t' = t3] である。 [|- t3 \in T] であるのでこれは求める結果である。

           - 直前の規則が [ST_If] の場合、 [t' = if t1' then t2 else t3'] である。ここで、 [t1 ==> t1'] である。 [|- t1 \in Bool] であるので、帰納法の仮定から [|- t1' \in Bool] である。また、 [T_If] 規則から [|- if t1' then t2 else t3 \in T] であり、これは求める結果である。

    (* FILL IN HERE *)
[] *)

(* **** Exercise: 3 stars (preservation_alternate_proof)  *)
(** **** 練習問題: ★★★ (preservation_alternate_proof)  *)
(* Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proof to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)
(**
   さらに、同一の性質を型付けの導出ではなく、評価の導出に関する帰納法で証明しなさい。先ほどの証明の最初数行を注意深く読んで考え、各行が何をしているのか理解することから始めましょう。この証明でも設定はよく似ていますが、まったく同じというわけではありません。
   *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(* ** Type Soundness *)
(** ** 型の健全性 *)

(* Putting progress and preservation together, we can see that a
    well-typed term can _never_ reach a stuck state.  *)
(**
   進行と型保存を合わせると、型のついた項は決して行き詰まらないことを示せます。
   *)

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof. 
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.   
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.


(* ###################################################################### *)
(* * Aside: the [normalize] Tactic *)
(** ** 余談: [normalize] タクティック *)

(* When experimenting with definitions of programming languages in
    Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t ==>*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are simple but repetitive to do by hand. Consider for
    example reducing an arithmetic expression using the small-step
    relation [astep]. *)
(**
   Coq でプログラミング言語の定義を扱っていると、ある具体的な項がどのように簡約されるか知りたいことがよくあります。 [t ==>* t'] という形のゴールを、 [t] が具体的な項で [t'] が未知の場合に証明するときです。このような証明は単純ですが、手でやるには繰り返しが多過ぎます。例えば、スモールステップ簡約の関係 [astep] を使って算術式を簡約することを考えてみましょう。
   *)


Definition amultistep st := multi (astep st). 
Notation " t '/' st '==>a*' t' " := (amultistep st t t')
  (at level 40, st at level 39).

Example astep_example1 : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2. 
      apply av_num. 
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

(* We repeatedly apply [multi_step] until we get to a normal
    form. The proofs that the intermediate steps are possible are
    simple enough that [auto], with appropriate hints, can solve
    them. *)
(** 正規形になるまで [multi_step] を繰り返し適用します。証明の途中に出てくる部分は、適切なヒントを与えてやれば [auto] で解けそうです。
   *)

Hint Constructors astep aval.
Example astep_example1' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.


(* The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each [multi_step] we print out the
    current goal, so that the user can follow how the term is being
    evaluated. *)
(** 下の [Tactic Notation] 定義はこのパターンを表現したものです。それに加えて、 [multi_step] を実行する前にゴールを表示します。これは、項がどのように評価されるか利用者が追えるようにするためです。
   *)

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.


Example astep_example1'' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  normalize.
  (* At this point in the proof script, the Coq response shows 
     a trace of how the expression evaluated. 

   (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ANum 15)
   (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) (ANum 15))
   (multi (astep empty_state) (ANum 15) (ANum 15))
*)
  (* 証明スクリプトのこの部分で、 Coq は式がどのように評価されたかのトレースを表示する。

   (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ANum 15)
   (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) (ANum 15))
   (multi (astep empty_state) (ANum 15) (ANum 15))
*)
Qed.


(* The [normalize] tactic also provides a simple way to calculate
    what the normal form of a term is, by proving a goal with an
    existential variable in it. *)
(** またさらに、[normalize] タクティックは存在量化された変数を入れて証明し、ある項の正規形を計算する、という機能を提供します。 *)

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.

(* This time, the trace will be:

    (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ??)
    (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) ??)
    (multi (astep empty_state) (ANum 15) ??)

   where ?? is the variable ``guessed'' by eapply.
*)
(* ここでのトレースは以下のようになります。

    (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ??)
    (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) ??)
    (multi (astep empty_state) (ANum 15) ??)

   ?? はeapplyで作られた(guessed) 変数です。
*)
Qed.


(* **** Exercise: 1 star (normalize_ex)  *)
(** **** 練習問題: ★ (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* **** Exercise: 1 star, optional (normalize_ex')  *)
(** **** 練習問題: ★, optional (normalize_ex')  *)
(* For comparison, prove it using [apply] instead of [eapply]. *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################################### *)
(* ** Additional Exercises *)
(** ** 追加演習 *)

(* **** Exercise: 2 stars (subject_expansion)  *)
(** **** 練習問題: ★★ (subject_expansion)  *)
(* Having seen the subject reduction property, it is reasonable to
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so if you like.)

    (* FILL IN HERE *)
[] *)
(** 主部簡約性が成り立つのなら、その逆の性質、主部展開（subject expansion）性も成り立つかどうか考えるのが合理的でしょう。すなわち、 [t ==> t'] かつ [|- t' \in T] ならば [|- t \in T] は常に成り立つでしょうか。そうだと思うのなら、証明しなさい。そうでないと思うのなら、反例を挙げなさい。(反例をCoqで示す必要はありませんが、示してみるのも面白いでしょう。)

    (* FILL IN HERE *)
[] *)




(* **** Exercise: 2 stars (variation1)  *)
(** **** 練習問題: ★★ (variation1)  *)
(* Suppose, that we add this new rule to the typing relation: 
      | T_SuccBool : forall t,
           |- t \in TBool ->
           |- tsucc t \in TBool
   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]

      - Progress

      - Preservation

[] *)
(** 先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。
      | T_SuccBool : forall t,
           |- t \in TBool ->
           |- tsucc t \in TBool
   以下の性質のうち、この規則を追加しても依然として真であるのはどれでしょう。それぞれについて、「真のままである」か「偽になる」かを書きなさい。偽になる場合には反例を挙げなさい。

      - [step] の決定性

      - 型のつく項に対する [step] の正規化

      - 進行

      - 型保存

[] *)

(* **** Exercise: 2 stars (variation2)  *)
(** **** 練習問題: ★★ (variation2)  *)
(* Suppose, instead, that we add this new rule to the [step] relation: 
      | ST_Funny1 : forall t2 t3,
           (tif ttrue t2 t3) ==> t3
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)
(** 先程の問題とは別に、次の規則を [step] 関係に追加したとしましょう。
      | ST_Funny1 : forall t2 t3,
           (tif ttrue t2 t3) ==> t3
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[] *)

(* **** Exercise: 2 stars, optional (variation3)  *)
(** **** 練習問題: ★★ (variation3)  *)
(* Suppose instead that we add this rule:
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tif t1 t2 t3) ==> (tif t1 t2' t3)
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)
(** 先程の問題とは別に、次の規則を追加したとしましょう。
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tif t1 t2 t3) ==> (tif t1 t2' t3)
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[] *)

(* **** Exercise: 2 stars, optional (variation4)  *)
(** **** 練習問題: ★★, optional (variation4)  *)
(* Suppose instead that we add this rule:
      | ST_Funny3 : 
          (tpred tfalse) ==> (tpred (tpred tfalse))
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)
(** 先程の問題とは別に、次の規則を追加したとしましょう。
      | ST_Funny3 : 
          (tpred tfalse) ==> (tpred (tpred tfalse))
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[] *)

(* **** Exercise: 2 stars, optional (variation5)  *)
(** **** 練習問題: ★★, optional (variation5)  *)
(* Suppose instead that we add this rule:
   
      | T_Funny4 : 
            |- tzero \in TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)
(**
   先程の問題とは別に、次の規則を追加したとしましょう。

      | T_Funny4 : 
            |- tzero \in TBool
   ]]
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[] *)

(* **** Exercise: 2 stars, optional (variation6)  *)
(** **** 練習問題: ★★ (variation6)  *)
(* Suppose instead that we add this rule:
   
      | T_Funny5 : 
            |- tpred tzero \in TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)
(**
   先程の問題とは別に、次の規則を追加したとしましょう。

      | T_Funny5 : 
            |- tpred tzero \in TBool
   ]]
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[] *)

(* **** Exercise: 3 stars, optional (more_variations)  *)
(** **** 練習問題: ★★★, optional (more_variations)  *)
(* Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
[] *)
(**
   上の問題と同様の練習問題を自分で作りなさい。さらに、上の性質を選択的に成り立たなくする方法、すなわち、上の性質のうちひとつだけを成り立たなるするよう定義を変更する方法を探しなさい。
[] *)

(* **** Exercise: 1 star (remove_predzero)  *)
(** **** 練習問題: ★ (remove_predzero)  *)
(* The evaluation rule [E_PredZero] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of zero to
    be undefined, rather than being defined to be zero.  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere? 

(* FILL IN HERE *)
[] *)
(** 評価規則 [E_PredZero] には少し直感に反するところがあります。 0 の前者を 0 と定義するよりは、未定義とした方が意味があるように感じられるでしょう。これは [step] の定義から [E_PredZero] を取り除くだけで実現できるでしょうか？

(* FILL IN HERE *)
[] *)

(* **** Exercise: 4 stars, advanced (prog_pres_bigstep)  *)
(** **** 練習問題: ★★★★, advanced (prog_pres_bigstep)  *)
(* Suppose our evaluation relation is defined in the big-step style.
    What are the appropriate analogs of the progress and preservation
    properties?

(* FILL IN HERE *)
[] *)
(**
   評価関係をビッグステップスタイルで定義したとしましょう。その場合、進行と型保存性に当たるものとしては何が適切でしょうか。

(* FILL IN HERE *)
[] *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)
