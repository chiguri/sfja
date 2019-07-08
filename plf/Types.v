(** * Types: 型システム *)
(* begin hide *)
(** * Types: Type Systems *)
(* end hide *)

(* begin hide *)
(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)
(* end hide *)
(** 次に取り組む内容は型システムです。
    型システムは、式をその評価結果の「かたち」で分類する静的解析手法です。
    まずは、非常に簡単に把握できる言語から始め、型に関する基本的な考え方や型付け規則、型保存(_type preservation_)や進行(_progress_)といった型システムに関する基礎的な定理を導入します。
    [Stlc]章では、単純型付きラムダ計算(_simply typed lambda-calculus_)に移ります。
    単純型付きラムダ計算は（Coq を含む）近代的な関数型プログラミング言語すべての中心概念になっています。 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.

Hint Constructors multi.

(* ################################################################# *)
(* begin hide *)
(** * Typed Arithmetic Expressions *)
(* end hide *)
(** * 型付きの算術式 *)

(* begin hide *)
(** To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter [Smallstep]: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine. *)
(* end hide *)
(** 型システムについての議論を始めるために、例のごとく、ごく単純な言語から始めましょう。
    この言語は、実行時の型エラーでまずいことが起きる可能性のあるものであってほしいので、 [Smallstep] 章で使った、定数と足し算だけの言語よりはもう少し複雑なものでなければなりません。
    データが一種類だけ（数のみ）では単純すぎますが、二種類（数とブール値）なら、実験のための材料はもう揃っています。
 
    言語の定義はいつも通り、お決まりの作業です。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Syntax *)
(* end hide *)
(** ** 構文 *)

(* begin hide *)
(** Here is the syntax, informally:

    t ::= tru
        | fls
        | test t then t else t
        | zro
        | scc t
        | prd t
        | iszro t

    And here it is formally: *)
(* end hide *)
(** 非形式的な構文は以下の通りです。
<<
    t ::= tru 
        | fls 
        | test t then t else t 
        | zro 
        | scc t 
        | prd t 
        | iszro t 
>>
    そして形式的には以下の通りです。 *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

(* begin hide *)
(** _Values_ are [tru], [fls], and numeric values... *)
(* end hide *)
(** 値(_Values_)は [tru] や [fls] 、そして数値です... *)

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

(* ================================================================= *)
(* begin hide *)
(** ** Operational Semantics *)
(* end hide *)
(** ** 操作的意味論 *)

(* begin hide *)
(** Here is the single-step relation, first informally... 

                   -------------------------------                  (ST_TestTru)
                   test tru then t1 else t2 --> t1

                   -------------------------------                  (ST_TestFls)
                   test fls then t1 else t2 --> t2

                               t1 --> t1'
            ----------------------------------------------------       (ST_Test)
            test t1 then t2 else t3 --> test t1' then t2 else t3

                             t1 --> t1'
                         ------------------                             (ST_Scc)
                         scc t1 --> scc t1'

                           ---------------                           (ST_PrdZro)
                           prd zro --> zro

                         numeric value v1
                        -------------------                          (ST_PrdScc)
                        prd (scc v1) --> v1

                              t1 --> t1'
                         ------------------                             (ST_Prd)
                         prd t1 --> prd t1'

                          -----------------                        (ST_IszroZro)
                          iszro zro --> tru

                         numeric value v1
                      ----------------------                       (ST_IszroScc)
                      iszro (scc v1) --> fls

                            t1 --> t1'
                       ----------------------                         (ST_Iszro)
                       iszro t1 --> iszro t1'
*)
(* end hide *)
(** 1ステップ関係について、まず非形式的なものを見ます。
<<
                   -------------------------------                  (ST_TestTru) 
                   test tru then t1 else t2 --> t1 
 
                   -------------------------------                  (ST_TestFls) 
                   test fls then t1 else t2 --> t2 
 
                               t1 --> t1' 
            ----------------------------------------------------       (ST_Test) 
            test t1 then t2 else t3 --> test t1' then t2 else t3 
 
                             t1 --> t1' 
                         ------------------                             (ST_Scc) 
                         scc t1 --> scc t1' 
 
                           ---------------                           (ST_PrdZro) 
                           prd zro --> zro 
 
                         numeric value v1 
                        -------------------                          (ST_PrdScc) 
                        prd (scc v1) --> v1 
 
                              t1 --> t1' 
                         ------------------                             (ST_Prd) 
                         prd t1 --> prd t1' 
 
                          -----------------                        (ST_IszroZro) 
                          iszro zro --> tru 
 
                         numeric value v1 
                      ----------------------                       (ST_IszroScc) 
                      iszro (scc v1) --> fls 
 
                            t1 --> t1' 
                       ----------------------                         (ST_Iszro) 
                       iszro t1 --> iszro t1' 
>>
 *)

(* begin hide *)
(** ... and then formally: *)
(* end hide *)
(** そして形式的なものです。 *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall t1,
      nvalue t1 ->
      (prd (scc t1)) --> t1
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall t1,
       nvalue t1 ->
      (iszro (scc t1)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(* begin hide *)
(** Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.  For example, the term [scc tru] cannot
    take a step, but the almost as obviously nonsensical term

       scc (test tru then tru else tru)

    can take a step (once, before becoming stuck). *)
(* end hide *)
(** [step] 関係は元の式が大域的に意味を持つかは考慮せず、「次の」簡約操作が適切な種類の対象へ適用されることだけを確認していることに注意してください。
    例えば、 [scc tru] は先に進むことはできませんが、明らかに同程度に無意味な項
[[
       scc (test tru then tru else tru) 
]]
    は（行き詰まるまでに1ステップ）進めることができます。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Normal Forms and Values *)
(* end hide *)
(** ** 正規形と値 *)

(* begin hide *)
(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep] chapter
    fails here.  That is, there are terms that are normal forms (they
    can't take a step) but not values (because we have not included
    them in our definition of possible "results of reduction").  Such
    terms are _stuck_. *)
(* end hide *)
(** この言語の [step] 関係について、まず注目に値するのは、 [Smallstep] 章の強進行性定理(strong progress theorem)が成り立たないということです。
    すなわち、正規形ではあるのに（これ以上簡約できないのに）、値ではない項があるのです（これは、そのような項を想定する「簡約結果」と定義しなかったからです）。
    そのような項は「行き詰まる(_stuck_)」ことになります。 *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(* begin hide *)
(** **** Exercise: 2 stars, standard (some_term_is_stuck)  *)
(* end hide *)
(** **** 練習問題: ★★, standard (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** However, although values and normal forms are _not_ the same in
    this language, the set of values is a subset of the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. *)
(* end hide *)
(** ただし、この言語では値の集合と正規形の集合は同一ではありませんが、値の集合は正規形の集合の部分集合になっています。
    これは重要なことで、さらに簡約できる値を定義してしまうことはないことを表しています。 *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (value_is_nf)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard (value_is_nf)  *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.

(* begin hide *)
(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.) 

    [] *)
(* end hide *)
(** （ヒント: 証明中で、数値であることがわかっている項に対して帰納的推論をしなければならないことになります。
    この帰納法は、その項自体にして適用することもできますし、その項が数値であるという事実に対して適用することもできます。
    どちらでも証明は進められますが、片方はもう片方よりもかなり短くなります。
    練習として、ふたつの方法両方で証明を完成させなさい。）
 
    []  *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (step_deterministic)  

    Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (step_deterministic)
 
    [value_is_nf] を使い、 [step] 関係もまた決定的であることを示しなさい。 *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Typing *)
(* end hide *)
(** ** 型付け *)

(* begin hide *)
(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)
(* end hide *)
(** 次にこの言語から見て取れる非常に重要なことは、行き詰まる項があったとしても、そのような項は、我々としても意味を持つことすらやめてほしいようなブール値と数の取り混ぜ方をしたもので、すべて無価値なものであるということです。
    項とその評価結果の型（数かブール値）を関係づける型付け関係を定義することで、そのような、型の付かない項を除くことができます。 *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(* begin hide *)
(** In informal notation, the typing relation is often written
    [|- t \in T] and pronounced "[t] has type [T]."  The [|-] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty. 

    
                           ---------------                     (T_Tru)
                           |- tru \in Bool

                          ---------------                      (T_Fls)
                          |- fls \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------     (T_Test)
                    |- test t1 then t2 else t3 \in T

                             --------------                    (T_Zro)
                             |- zro \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Scc)
                          |- scc t1 \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Prd)
                          |- prd t1 \in Nat

                            |- t1 \in Nat
                        --------------------                 (T_IsZro)
                        |- iszro t1 \in Bool
*)
(* end hide *)
(** 非形式的な記法では、型付け関係を [|- t \in T] と書き、「[t] の型は [T] である」と読みます。
    記号 [|-] は「ターンスタイル（turnstile）」と呼びます。
    後の章ではより複雑になり、ターンスタイルの左側に追加の「コンテキスト」引数を付ける型付け関係もあります。
    ここでは、コンテキストは常に空です。
<<
                           ---------------                     (T_Tru) 
                           |- tru \in Bool 
 
                          ---------------                      (T_Fls) 
                          |- fls \in Bool 
 
             |- t1 \in Bool    |- t2 \in T    |- t3 \in T 
             --------------------------------------------     (T_Test) 
                    |- test t1 then t2 else t3 \in T 
 
                             --------------                    (T_Zro) 
                             |- zro \in Nat 
 
                            |- t1 \in Nat 
                          -----------------                    (T_Scc) 
                          |- scc t1 \in Nat 
 
                            |- t1 \in Nat 
                          -----------------                    (T_Prd) 
                          |- prd t1 \in Nat 
 
                            |- t1 \in Nat 
                        --------------------                 (T_IsZro) 
                        |- iszro t1 \in Bool 
>>
 *)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
    - apply T_Fls.
    - apply T_Zro.
    - apply T_Scc.
       + apply T_Zro.
Qed.

(* begin hide *)
(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)
(* end hide *)
(** （型付け関係のすべての構成子をヒントデータベースに登録してあるので、実際には [auto] で証明を自動的に構築することができます。） *)

(* begin hide *)
(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)
(* end hide *)
(** 型付け関係というのは保守的な（または静的な）近似です。
    型付け関係では、簡約で何が起こるかを考慮しませんし、また特に項の正規形の型を計算しているわけでもありません。 *)

Example has_type_not :
  ~ ( |- test fls zro tru \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (scc_hastype_nat__hastype_nat)  *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (scc_hastype_nat__hastype_nat)  *)
Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t \in Nat ->
  |- t \in Nat.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Progress *)
(* end hide *)
(** ** 進行 *)

(* begin hide *)
(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck -- or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step.  We call this _progress_. *)
(* end hide *)
(** 型付け関係には重要な性質がふたつあります。
    最初のものは、型のついた(well-typed)正規形は行き詰まっていない、というものです。
    別の言い方をすれば、もし項に型がつくなら、項は値であるか、または1ステップは進めるということです。
    この性質を「進行性(_progress_)」と言います。 *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (finish_progress)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard (finish_progress)  *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
Proof with auto.
  intros t T HT.
  induction HT...
  (* The cases that were obviously values, like T_Tru and
     T_Fls, were eliminated immediately by auto *)
  (* T_Tru や T_Fls のような、値であることが明らかな場合は [auto] で片付けられる。 *)
  - (* T_Test *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 can take a step *)
      inversion H as [t1' H1].
      exists (test t1' t2 t3)...
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, advanced (finish_progress_informal)  

    Complete the corresponding informal proof: *)
(* end hide *)
(** **** 練習問題: ★★★, advanced (finish_progress_informal)
 
    上と対応する以下の非形式的な証明を完成させなさい。 *)

(* begin hide *)
(** _Theorem_: If [|- t \in T], then either [t] is a value or else
    [t --> t'] for some [t']. *)
(* end hide *)
(** 定理: [|- t \in T] であれば、 [t] は値であるか、さもなければある [t'] に対して [t --> t'] である。 *)

(* begin hide *)
(** _Proof_: By induction on a derivation of [|- t \in T].

    - If the last rule in the derivation is [T_Test], then [t = test t1
      then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
      \in T].  By the IH, either [t1] is a value or else [t1] can step
      to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas
        and the fact that [|- t1 \in Bool] we have that [t1]
        is a [bvalue] -- i.e., it is either [tru] or [fls].
        If [t1 = tru], then [t] steps to [t2] by [ST_TestTru],
        while if [t1 = fls], then [t] steps to [t3] by
        [ST_TestFls].  Either way, [t] can step, which is what
        we wanted to show.

      - If [t1] itself can take a step, then, by [ST_Test], so can
        [t].

    - (* FILL IN HERE *)
 *)
(* end hide *)
(** 証明: [|- t \in T] の導出に関する帰納法で証明する。
 
    - 導出で直前に適用した規則が [T_Test] である場合、 [t = test t1 then t2 else t3] かつ、 [|- t1 \in Bool]、 [|- t2 \in T] かつ [|- t3 \in T] である。
      帰納法の仮定から、 [t1] は値であるか、さもなければ何らかの [t1'] に簡約できる。
 
      - [t1] が値のとき、 canonical forms lemma と [|- t1 \in Bool] という事実から [t1] は [bvalue] である。
        すなわち、 [tru] または [fls] である。
        [t1 = tru] のとき、 [ST_TestTru] より [t] は [t2] に簡約され、 [t1 = fls] のときは [ST_TestFls] から [t] は [t3] に簡約される。
        どちらの場合も [t] の簡約は進められる。
        これが示そうとしていたことである。
 
      - [t1] 自体が簡約できるなら、 [ST_Test] を用いることで [t] もまた簡約できる。
 
    - (* ここを埋めなさい *)
  *)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** This theorem is more interesting than the strong progress theorem
    that we saw in the [Smallstep] chapter, where _all_ normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed. *)
(* end hide *)
(** この定理は [Smallstep] の章の強進行性定理よりも興味深いものです。
    [Smallstep] の章では、正規形はすべて値でした。
    本章では項が行き詰まることもありますが、行き詰まるようなものは型のつかないものだけです。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Type Preservation *)
(* end hide *)
(** ** 型保存 *)

(* begin hide *)
(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term. *)
(* end hide *)
(** 型付けの第二の重要な性質は、型のついた項を一段階簡約すると、簡約結果もまた型のつく項である、ということです。 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard (finish_preservation)  *)
(* end hide *)
(** **** 練習問題: ★★, standard (finish_preservation)  *)
Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.

(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, advanced (finish_preservation_informal)  

    Complete the following informal proof: *)
(* end hide *)
(** **** 練習問題: ★★★, advanced (finish_preservation_informal)
 
    以下の非形式的証明を完成させなさい。 *)

(* begin hide *)
(** _Theorem_: If [|- t \in T] and [t --> t'], then [|- t' \in T]. *)
(* end hide *)
(** 定理: [|- t \in T] かつ [t --> t'] ならば [|- t' \in T] *)

(* begin hide *)
(** _Proof_: By induction on a derivation of [|- t \in T].

    - If the last rule in the derivation is [T_Test], then [t = test t1
      then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
      \in T].

      Inspecting the rules for the small-step reduction relation and
      remembering that [t] has the form [test ...], we see that the
      only ones that could have been used to prove [t --> t'] are
      [ST_TestTru], [ST_TestFls], or [ST_Test].

      - If the last rule was [ST_TestTru], then [t' = t2].  But we
        know that [|- t2 \in T], so we are done.

      - If the last rule was [ST_TestFls], then [t' = t3].  But we
        know that [|- t3 \in T], so we are done.

      - If the last rule was [ST_Test], then [t' = test t1' then t2
        else t3], where [t1 --> t1'].  We know [|- t1 \in Bool] so,
        by the IH, [|- t1' \in Bool].  The [T_Test] rule then gives us
        [|- test t1' then t2 else t3 \in T], as required.

    - (* FILL IN HERE *)
*)
(* end hide *)
(** 証明: [|- t \in T] の導出に関する帰納法で証明する。
 
    - 導出で直前に使った規則が [T_Test] の場合、 [t = test t1 then t2 else t3]、かつ [|- t1 \in Bool]、 [|- t2 \in T] かつ [|- t3 \in T] である。
 
      [t] が [test ...] の形式であることとスモールステップ簡約関係を見ると、 [t --> t'] を示すために使えるのは [ST_TestTru]、 [ST_TestFls] または [ST_Test] のみである。
 
      - 直前の規則が [ST_TestTru] の場合、 [t' = t2] である。
        [|- t2 \in T] であるのでこれは求める結果である。
 
      - 直前の規則が [ST_TestFls] の場合、 [t' = t3] である。
        [|- t3 \in T] であるのでこれは求める結果である。
 
      - 直前の規則が [ST_Test] の場合、 [t' = test t1' then t2 else t3'] である。
        ここで、 [t1 --> t1'] である。 [|- t1 \in Bool] であるので、帰納法の仮定から [|- t1' \in Bool] である。
        また、 [T_Test] 規則から [|- test t1' then t2 else t3 \in T] であり、これは求める結果である。
 
    - (* ここを埋めなさい *)
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (preservation_alternate_proof)  

    Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)
(* end hide *)
(** **** 練習問題: ★★★, standard (preservation_alternate_proof)
 
    さらに、同一の性質を型付けの導出ではなく、評価の導出に関する帰納法で証明しなさい。
    先ほどの証明の最初数行を注意深く読んで考え、各行が何をしているのか理解することから始めましょう。
    この証明でも設定はよく似ていますが、まったく同じというわけではありません。 *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)
(* end hide *)
(** 型保存定理は「主部簡約（_subject reduction_）」性と呼ばれることが多々あります。
    これは、この定理が型付け関係の主部が簡約されるときに起こることについて言っているからです。
    この用語は型付けを文として見たことによるもので、項が主部（subject）、型が述部（predicate）に当たります。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Type Soundness *)
(* end hide *)
(** ** 型の健全性 *)

(* begin hide *)
(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)
(* end hide *)
(** 進行と型保存を合わせると、型のついた項は決して行き詰まらないことを示せます。 *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Additional Exercises *)
(* end hide *)
(** ** 追加演習 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, recommended (subject_expansion)  

    Having seen the subject reduction property, one might
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t --> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so.)

    (* FILL IN HERE *)
*)
(* end hide *)
(** **** 練習問題: ★★, standard, recommended (subject_expansion)
 
    主部簡約性が成り立つのなら、その逆の性質、主部展開（subject expansion）性も成り立つかも考えるでしょう。
    すなわち、 [t --> t'] かつ [|- t' \in T] ならば [|- t \in T] は常に成り立つでしょうか。
    そうだと思うのなら、証明しなさい。
    そうでないと思うのなら、反例を挙げなさい。
    （反例をCoqで示す必要はありませんが、示してみるのも面白いでしょう。）
 
    (* FILL IN HERE *) 
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_subject_expansion : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard (variation1)  

    Suppose that we add this new rule to the typing relation:

      | T_SccBool : forall t,
           |- t \in Bool ->
           |- scc t \in Bool

   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
            (* FILL IN HERE *)
      - Progress
            (* FILL IN HERE *)
      - Preservation
            (* FILL IN HERE *)
*)
(* end hide *)
(** **** 練習問題: ★★, standard (variation1)
 
    先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。
[[
      | T_SccBool : forall t, 
           |- t \in Bool -> 
           |- scc t \in Bool 
]]
   以下の性質のうち、この規則を追加しても依然として真であるのはどれでしょう。
   それぞれについて、「真のままである」か「偽になる」かを書きなさい。偽になる場合には反例を挙げなさい。
      - [step] の決定性
            (* FILL IN HERE *) 
      - 進行
            (* FILL IN HERE *) 
      - 型保存
            (* FILL IN HERE *) 
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation2)  

    Suppose, instead, that we add this new rule to the [step] relation:

      | ST_Funny1 : forall t2 t3,
           (test tru t2 t3) --> t3

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* FILL IN HERE *)
*)
(* end hide *)
(** **** 練習問題: ★★, standard (variation2)
 
    先程の問題とは別に、次の規則を [step] 関係に追加したとします。
[[
      | ST_Funny1 : forall t2 t3, 
           (test tru t2 t3) --> t3 
]]
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。
   偽になるものについてそれぞれ反例を挙げなさい。
            (* FILL IN HERE *) 
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (variation3)  

    Suppose instead that we add this rule:

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (test t1 t2 t3) --> (test t1 t2' t3)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* FILL IN HERE *)

    [] *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (variation3)
 
    先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | ST_Funny2 : forall t1 t2 t2' t3, 
           t2 --> t2' -> 
           (test t1 t2 t3) --> (test t1 t2' t3) 
]]
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。
   偽になるものについてそれぞれ反例を挙げなさい。
            (* FILL IN HERE *) 
 
    []  *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (variation4)  

    Suppose instead that we add this rule:

      | ST_Funny3 :
          (prd fls) --> (prd (prd fls))

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)

    [] *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (variation4)
 
    先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | ST_Funny3 : 
          (prd fls) --> (prd (prd fls)) 
]]
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。
   偽になるものについてそれぞれ反例を挙げなさい。
(* FILL IN HERE *) 

    []  *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (variation5)  

    Suppose instead that we add this rule:

      | T_Funny4 :
            |- zro \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)

    [] *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (variation5)
 
    先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | T_Funny4 : 
            |- zro \in Bool 
]]
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。
   偽になるものについてそれぞれ反例を挙げなさい。
(* FILL IN HERE *) 
 
    []  *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (variation6)  

    Suppose instead that we add this rule:

      | T_Funny5 :
            |- prd zro \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)

    [] *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (variation6)
 
    先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | T_Funny5 : 
            |- prd zro \in Bool 
]]
   上の性質のうち、この規則を追加すると偽になるのはどれでしょう。
   偽になるものについてそれぞれ反例を挙げなさい。
(* FILL IN HERE *) 
 
    []  *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (more_variations)  

    Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
*)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (more_variations)
 
    上の問題と同様の練習問題を自分で作りなさい。
    さらに、上の性質を選択的に成り立たなくする方法、すなわち、上の性質のうちひとつだけを成り立たなくするよう定義を変更する方法を探しなさい。
 *)
(* FILL IN HERE 

    [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard (remove_prdzro)  

    The reduction rule [ST_PrdZro] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of [zro] to
    be undefined, rather than being defined to be [zro].  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

(* FILL IN HERE *)
*)
(* end hide *)
(** **** 練習問題: ★, standard (remove_predzero)
 
    簡約規則 [ST_PrdZro] には少し直感に反するところがあります。
    [zro] の前者を [zro] と定義するよりは、未定義とした方が意味があるように感じられるでしょう。
    これは [step] の定義から対応する規則を取り除くだけで実現できるでしょうか？
    それとも別の場所に問題が起こるでしょうか？
 
(* FILL IN HERE *) 
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_remove_predzro : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 4 stars, advanced (prog_pres_bigstep)  

    Suppose our evaluation relation is defined in the big-step style.
    State appropriate analogs of the progress and preservation
    properties. (You do not need to prove them.)

    Can you see any limitations of either of your properties?  Do they
    allow for nonterminating commands?  Why might we prefer the
    small-step semantics for stating preservation and progress?

(* FILL IN HERE *)
*)
(* end hide *)
(** **** 練習問題: ★★★★, advanced (prog_pres_bigstep)
 
    評価関係をビッグステップスタイルで定義したとしましょう。
    進行と型保存性に当たるものとして適当なものを記しなさい。
    （証明する必要はありません。）
 
    その性質について何か制限は必要ですか？
    終了しないコマンドを許容しますか？
    なぜ型保存性と進行に関してスモールステップの方が望ましいのでしょうか？
 
(* FILL IN HERE *) 
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)



(* Thu Feb 7 20:09:24 EST 2019 *)
