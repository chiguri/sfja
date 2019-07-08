(** * Smallstep: スモールステップ操作的意味論 *)
(* begin hide *)
(** * Smallstep: Small-step Operational Semantics *)
(* end hide *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

(* begin hide *)
(** The evaluators we have seen so far (for [aexp]s, [bexp]s,
    commands, ...) have been formulated in a "big-step" style: they
    specify how a given expression can be evaluated to its final
    value (or a command plus a store to a final store) "all in one big
    step."

    This style is simple and natural for many purposes -- indeed,
    Gilles Kahn, who popularized it, called it _natural semantics_.
    But there are some things it does not do well.  In particular, it
    does not give us a natural way of talking about _concurrent_
    programming languages, where the semantics of a program -- i.e.,
    the essence of how it behaves -- is not just which input states
    get mapped to which output states, but also includes the
    intermediate states that it passes through along the way, since
    these states can also be observed by concurrently executing code.

    Another shortcoming of the big-step style is more technical, but
    critical in many situations.  Suppose we want to define a variant
    of Imp where variables could hold _either_ numbers _or_ lists of
    numbers.  In the syntax of this extended language, it will be
    possible to write strange expressions like [2 + nil], and our
    semantics for arithmetic expressions will then need to say
    something about how such expressions behave.  One possibility is
    to maintain the convention that every arithmetic expression
    evaluates to some number by choosing some way of viewing a list as
    a number -- e.g., by specifying that a list should be interpreted
    as [0] when it occurs in a context expecting a number.  But this
    is really a bit of a hack.

    A much more natural approach is simply to say that the behavior of
    an expression like [2+nil] is _undefined_ -- i.e., it doesn't
    evaluate to any result at all.  And we can easily do this: we just
    have to formulate [aeval] and [beval] as [Inductive] propositions
    rather than [Fixpoint]s, so that we can make them partial functions
    instead of total ones.

    Now, however, we encounter a serious deficiency.  In this
    language, a command might fail to map a given starting state to
    any ending state for _two quite different reasons_: either because
    the execution gets into an infinite loop or because, at some
    point, the program tries to do an operation that makes no sense,
    such as adding a number to a list, so that none of the evaluation
    rules can be applied.

    These two outcomes -- nontermination vs. getting stuck in an
    erroneous configuration -- should not be confused.  In particular, we
    want to _allow_ the first (permitting the possibility of infinite
    loops is the price we pay for the convenience of programming with
    general looping constructs like [while]) but _prevent_ the
    second (which is just wrong), for example by adding some form of
    _typechecking_ to the language.  Indeed, this will be a major
    topic for the rest of the course.  As a first step, we need a way
    of presenting the semantics that allows us to distinguish
    nontermination from erroneous "stuck states."

    So, for lots of reasons, we'd often like to have a finer-grained
    way of defining and reasoning about program behaviors.  This is
    the topic of the present chapter.  Our goal is to replace the
    "big-step" [eval] relation with a "small-step" relation that
    specifies, for a given program, how the "atomic steps" of
    computation are performed. *)
(* end hide *)
(** ここまで見てきた評価器（例えば[aexp]用、[bexp]用、コマンド用、などなど）は「ビッグステップスタイル」で記述されてきました。
    つまり、与えられた式がどのように最終的な値になるか（またはコマンドと記憶状態の組がどのように最終記憶状態になるか）を「すべて大きな1ステップ」として決定しました。
 
    このスタイルは単純で多くの目的のために自然な方法です。
    実際、この手法を広めた Gilles Kahn は、これを「自然意味論(_natural semantics_)」と呼びました。
    しかし、これではうまくいかないときもあります。
    特に、この方法は、並列プログラミング言語について言及する際には自然ではありません。
    並列プログラミング言語の場合、プログラムの「意味」、つまりプログラムがどのように振る舞うかの本質は、入力状態が出力状態にどのように写像されるかだけではなく、途中で通過する状態も含みます。
    なぜなら、中間状態は並列実行される他のコードからも観測されるからです。
 
    ビッグステップスタイルのもう1つの欠点は、より技術的なことですが、ある種のアプリケーションには致命的です。
    変数が数値だけでなく数値のリストにも束縛されうるImpの変種を考えましょう。
    構文的には、この言語では[2 + nil]のような変な式を書くことができます。
    そして、意味論上では、この式がどのように動くのかについて言及する必要があります。
    一つの動き方としては、リストを適当な数値として扱うことで、全ての算術式を数値に評価するものがあります。
    例えば数値を期待する箇所ではリストを常に[0]として扱う、といった扱い方があります。
    ただ、この方法は少し奇抜な方法です。
 
    より自然な方法としては、[2+nil]のような式の動き方を「未定義(_undefined_)」としてしまうことです。
    つまりどのような結果にも評価されないということです。
    これは簡単に実現できます。
    [aeval]と[beval]を、[Fixpoint] ではなく帰納的([Inductive])命題として定義するだけです。
    すると、全関数ではなく部分関数にすることができます。
 
    しかしながら、この方法で Imp を定義することには深刻な欠陥があります。
    この言語では、コマンドが初期状態を終了状態に写像するのに失敗した際に、「まったく異なる」2種類の原因があり得ます。
    1つは評価が無限ループに陥ることによるもの、もう1つは、どこかの地点でプログラムが、数値をリストに加えるなどの意味のない操作をしようとして、どの評価規則も適用できなくなることによるものです。
 
    この2つの結果、つまり「停止しないこと」と「間違った設定によって行き詰まること」をごちゃ混ぜにしないでください。
    特に、1つ目は「許容」したい（無限ループの可能性を許すことは、プログラミングに [while] のような一般的ループ構造を使う便利さの代償です）一方で、2つ目（これはただの間違いです）は「禁止」したいのです。
    これは例えば言語に何らかの「型チェック(_typechecking_)」を追加することで実現できます。
    実のところ、これはこのコースの残りの部分の主要なトピックです。
    まずは、停止しないことと、間違いによる「行き詰まり状態」を区別することができる別の意味提示方法が必要です。
 
    このように、いろいろな理由で、プログラムの振る舞いを定義し推論するよりきめの細かい方法が欲しいことが度々あります。
    これがこの章のトピックです。
    目標は、与えられたプログラムに対して計算の「アトミックなステップ」がどのように行われるかを定める「スモールステップ」の関係によって、「ビッグステップ」の[eval]関係を置き換えることです。*)

(* ################################################################# *)
(* begin hide *)
(** * A Toy Language *)
(* end hide *)
(** * おもちゃの言語 *)

(* begin hide *)
(** To save space in the discussion, let's go back to an
    incredibly simple language containing just constants and
    addition.  (We use single letters -- [C] and [P] (for Constant and
    Plus) -- as constructor names, for brevity.)  At the end of the
    chapter, we'll see how to apply the same techniques to the full
    Imp language.  *)
(* end hide *)
(** 無駄な議論を省くため、定数と足し算だけの極端に単純な言語に戻りましょう。
    （可読性のために、定数と足し算を表すコンストラクタに[C]と[P]という一文字の名前を用います。）
    この章の終わりには、同じテクニックをImp言語全体に適用する方法がわかるでしょう。*)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

(* begin hide *)
(** Here is a standard evaluator for this language, written in
    the big-step style that we've been using up to this point. *)
(* end hide *)
(** 次がこの言語の標準的な評価器です。
    ここまでやってきたのと同じビッグステップスタイルで記述されています。 *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

(* begin hide *)
(** Here is the same evaluator, written in exactly the same
    style, but formulated as an inductively defined relation.
    We use the notation [t ==> n] for "[t] evaluates to [n]." 

                               ---------                               (E_Const)
                               C n ==> n

                               t1 ==> n1
                               t2 ==> n2
                           -------------------                         (E_Plus)
                           P t1 t2 ==> n1 + n2
*)
(* end hide *)
(** 同じ評価器を、まったく同じスタイルながら、帰納的に定義された関係によって定式化したものです。
    ここでは「[t]が[n]に評価される」を記法 [t ==> n] で表しています。
<<
                               ---------                               (E_Const) 
                               C n ==> n 
 
                               t1 ==> n1 
                               t2 ==> n2 
                           -------------------                         (E_Plus) 
                           P t1 t2 ==> n1 + n2 
>>
 *)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)
where " t '==>' n " := (eval t n).

Module SimpleArith1.

(* begin hide *)
(** Now, here is the corresponding _small-step_ evaluation relation. 

    
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_Plus2)
                      P (C n1) t2 --> P (C n1) t2'
*)
(* end hide *)
(** そして、次が対応する「スモールステップ」版です。
<<
                     -------------------------------        (ST_PlusConstConst) 
                     P (C n1) (C n2) --> C (n1 + n2) 
 
                              t1 --> t1' 
                         --------------------                        (ST_Plus1) 
                         P t1 t2 --> P t1' t2 
 
                              t2 --> t2' 
                      ----------------------------                   (ST_Plus2) 
                      P (C n1) t2 --> P (C n1) t2' 
>>
 *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').

(* begin hide *)
(** Things to notice:

    - We are defining just a single reduction step, in which
      one [P] node is replaced by its value.

    - Each step finds the _leftmost_ [P] node that is ready to
      go (both of its operands are constants) and rewrites it in
      place.  The first rule tells how to rewrite this [P] node
      itself; the other two rules tell how to find it.

    - A term that is just a constant cannot take a step. *)
(* end hide *)
(** 注目すること:
 
    - 定義しているのは簡約のちょうど1ステップです。
      そこでは1つの[P]ノードがその値に置き換えられます。
 
    - 各ステップでは「最左」の準備ができている（つまり、引数が両方とも定数である）[P]ノードを探して、それをその場で書き換えます。
      最初の規則は[P]ノードをどのように書き換えるかを定めます。
      残りの2つの規則は、それをどう探すかを定めます。
 
    - 定数の項は、ステップを進めません。*)

(** Let's pause and check a couple of examples of reasoning with
    the [step] relation... *)

(* begin hide *)
(** If [t1] can take a step to [t1'], then [P t1 t2] steps
    to [P t1' t2]: *)
(* end hide *)
(** もし[t1]が1ステップで[t1']になるならば、
    [P t1 t2] は1ステップで [P t1' t2] になります: *)

Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.

(* begin hide *)
(** **** Exercise: 1 star, standard (test_step_2)  

    Right-hand sides of sums can take a step only when the
    left-hand side is finished: if [t2] can take a step to [t2'],
    then [P (C n) t2] steps to [P (C n) t2']: *)
(* end hide *)
(** **** 練習問題: ★, standard (test_step_2)
 
    和の右側のステップを進められるのは、左側が終了したときだけです：
    もし[t2]が1ステップで[t2']になるならば、 [P (C n) t2] は1ステップで [P (C n) t2'] になります。
    以上を踏まえて次の証明を完成させなさい： *)
(* (訳注: 他のところと比べて、明示的な練習問題としての指示がなかったので、
   意を汲んで追記しました。) *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End SimpleArith1.

(* ################################################################# *)
(** * Relations *)

(** We will be working with several different single-step relations,
    so it is helpful to generalize a bit and state a few definitions
    and theorems about relations in general.  (The optional chapter
    [Rel.v] develops some of these ideas in a bit more detail; it may
    be useful if the treatment here is too dense.)

    A _binary relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X : Type) := X -> X -> Prop.

(** Our main examples of such relations in this chapter will be
    the single-step reduction relation, [-->], and its multi-step
    variant, [-->*] (defined below), but there are many other
    examples -- e.g., the "equals," "less than," "less than or equal
    to," and "is the square of" relations on numbers, and the "prefix
    of" relation on lists and strings. *)

(* begin hide *)
(** One simple property of the [-->] relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t --> t'] is provable). *)
(* end hide *)
(** 関係 [-->] の性質の1つは、Imp プログラムの言語の大ステップ評価関係と同様、決定性を持つ(_deterministic_)ということです。
 
    「定理」: 各[t]に対して、[t]が1ステップで[t']になる（[t --> t'] が証明可能な）[t']は高々1つである。 *)

(* begin hide *)
(** _Proof sketch_: We show that if [x] steps to both [y1] and
    [y2], then [y1] and [y2] are equal, by induction on a derivation
    of [step x y1].  There are several cases to consider, depending on
    the last rule used in this derivation and the last rule in the
    given derivation of [step x y2].

      - If both are [ST_PlusConstConst], the result is immediate.

      - The cases when both derivations end with [ST_Plus1] or
        [ST_Plus2] follow by the induction hypothesis.

      - It cannot happen that one is [ST_PlusConstConst] and the other
        is [ST_Plus1] or [ST_Plus2], since this would imply that [x]
        has the form [P t1 t2] where both [t1] and [t2] are
        constants (by [ST_PlusConstConst]) _and_ one of [t1] or [t2]
        has the form [P _].

      - Similarly, it cannot happen that one is [ST_Plus1] and the
        other is [ST_Plus2], since this would imply that [x] has the
        form [P t1 t2] where [t1] has both the form [P t11 t12] and the
        form [C n]. [] *)
(* end hide *)
(** 「証明スケッチ」:[x]が1ステップで[y1]と[y2]のどちらにもなるとき、[y1]と[y2]
    が等しいことを、[step x y1] の導出についての帰納法で示す。
    この導出と [step x y2] の導出のそれぞれで使われた最後の規則によって、
    いくつかの場合がある。
 
      - もし両者とも [ST_PlusConstConst] ならば、一致は明らかである。
 
      - 導出が両者とも [ST_Plus1] または [ST_Plus2] で終わるならば、帰納法の仮定から成立する。
 
      - 一方が [ST_PlusConstConst] で、他方が [ST_Plus1] または [ST_Plus2] であることはあり得ない。
        なぜなら、そうなるためには、 [x] が [P t1 t2] の形で（[ST_PlusConstConst]より）[t1]と[t2]が両者とも定数であり、「かつ」[t1]または[t2]が [P _] の形でなければならないためである。
 
      - 同様に、一方が [ST_Plus1] で他方が [ST_Plus2] であることもあり得ない。
        なぜなら、そのためには、[x] は [P t1 t2] の形で、 [t1] が [P t11 t12] の形であると同時に [C n] の形でもなければならないからである。 [] *)

(** Formally: *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PlusConstConst *) inversion Hy2.
    + (* ST_PlusConstConst *) reflexivity.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *) inversion H2.
  - (* ST_Plus1 *) inversion Hy2.
    + (* ST_PlusConstConst *)
      rewrite <- H0 in Hy1. inversion Hy1.
    + (* ST_Plus1 *)
      rewrite <- (IHHy1 t1'0).
      reflexivity. assumption.
    + (* ST_Plus2 *)
      rewrite <- H in Hy1. inversion Hy1.
  - (* ST_Plus2 *) inversion Hy2.
    + (* ST_PlusConstConst *)
      rewrite <- H1 in Hy1. inversion Hy1.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *)
      rewrite <- (IHHy1 t2'0).
      reflexivity. assumption.
Qed.

End SimpleArith2.

(** There is some annoying repetition in this proof.  Each use of
    [inversion Hy2] results in three subcases, only one of which is
    relevant (the one that matches the current case in the induction
    on [Hy1]).  The other two subcases need to be dismissed by finding
    the contradiction among the hypotheses and doing inversion on it.

    The following custom tactic, called [solve_by_inverts], can be
    helpful in such cases.  It will solve the goal if it can be solved
    by inverting some hypothesis; otherwise, it fails. *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

(** The details of how this works are not important for now, but it
    illustrates the power of Coq's [Ltac] language for
    programmatically defining special-purpose tactics.  It looks
    through the current proof state for a hypothesis [H] (the first
    [match]) of type [Prop] (the second [match]) such that performing
    inversion on [H] (followed by a recursive invocation of the same
    tactic, if its argument [n] is greater than one) completely solves
    the current goal.  If no such hypothesis exists, it fails.

    We will usually want to call [solve_by_inverts] with argument
    [1] (especially as larger arguments can lead to very slow proof
    checking), so we define [solve_by_invert] as a shorthand for this
    case. *)

Ltac solve_by_invert :=
  solve_by_inverts 1.

(** Let's see how a proof of the previous theorem can be simplified
    using this tactic... *)

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

(* ================================================================= *)
(* begin hide *)
(** ** Values *)
(* end hide *)
(** ** 値 *)

(* begin hide *)
(** Next, it will be useful to slightly reformulate the
    definition of single-step reduction by stating it in terms of
    "values." *)
(* end hide *)
(** 次に、1ステップ簡約を再定義して、「値」であることを明示するようにしましょう。 *)

(* begin hide *)
(** It can be useful to think of the [-->] relation as defining an
    _abstract machine_:

      - At any moment, the _state_ of the machine is a term.

      - A _step_ of the machine is an atomic unit of computation --
        here, a single "add" operation.

      - The _halting states_ of the machine are ones where there is no
        more computation to be done. *)
(* end hide *)
(** 関係 [-->] が抽象機械(_abstract machine_)の定義と考えると便利です:
 
      - どの時点でも、機械の状態(_state_)は項です。
 
      - 機械のステップ(_step_)は、計算のアトミックな単位です。ここでは、1つの加算処理です。
 
      - 機械の停止状態(_halting states_)は、さらなる計算が存在しない状態です。 *)

(* begin hide *)
(** We can then execute a term [t] as follows:

      - Take [t] as the starting state of the machine.

      - Repeatedly use the [-->] relation to find a sequence of
        machine states, starting with [t], where each state steps to
        the next.

      - When no more reduction is possible, "read out" the final state
        of the machine as the result of execution. *)
(* end hide *)
(** このとき、項[t]は以下のように評価できます:
 
      - [t]を機械の開始状態としてとります。
 
      - 次のような機械の状態の列を見つけるために、[-->] 関係を繰り返し使います。
        見つけるのは、[t]から始まり、それぞれの状態から1ステップでその次の状態になる列です。
 
      - もう簡約ができなくなったとき、機械の最終状態を、実行結果として「読み出し」ます。 *)

(* begin hide *)
(** Intuitively, it is clear that the final states of the
    machine are always terms of the form [C n] for some [n].
    We call such terms _values_. *)
(* end hide *)
(** 直観的には、機械の最終状態が常に、
    ある[n]についての [C n] という形の項になることは明らかです。
    そのような項を「値」(_values_)と呼びます。*)

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

(* begin hide *)
(** Having introduced the idea of values, we can use it in the
    definition of the [-->] relation to write [ST_Plus2] rule in a
    slightly more elegant way: *)
(* end hide *)
(** 値の概念を導入したので、これを [-->] 関係の定義に使うことで、
    [ST_Plus2] 規則をもう少しだけきれいなものにできます: *)

(* begin hide *)
(** 
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_Plus2)
                         P v1 t2 --> P v1 t2'

    Again, the variable names here carry important information:
    by convention, [v1] ranges only over values, while [t1] and [t2]
    range over arbitrary terms.  (Given this convention, the explicit
    [value] hypothesis is arguably redundant.  We'll keep it for now,
    to maintain a close correspondence between the informal and Coq
    versions of the rules, but later on we'll drop it in informal
    rules for brevity.) *)
(* end hide *)
(**
<<
                     -------------------------------        (ST_PlusConstConst) 
                     P (C n1) (C n2) --> C (n1 + n2) 
 
                              t1 --> t1' 
                         --------------------                        (ST_Plus1) 
                         P t1 t2 --> P t1' t2 
 
                               value v1 
                              t2 --> t2' 
                         --------------------                        (ST_Plus2) 
                         P v1 t2 --> P v1 t2' 
>>

    再び、変数名が重要な情報を担っています:
    慣習として、[v1]は値のみを変域とし、一方[t1]と[t2]は任意の項を変域とします。
    （この慣習により、明示的に[value]仮定を用いることは冗長となります。
    この時点では非形式的なルールとCoqの記述の対応をわかりやすくするために仮定を取っておきますが、後に可読性を優先して除去します。） *)

(**  Here are the formal rules: *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(* begin hide *)
(** **** Exercise: 3 stars, standard, recommended (redo_determinism)  

    As a sanity check on this change, let's re-verify determinism.
    Here's an informal proof:

    _Proof sketch_: We must show that if [x] steps to both [y1] and
    [y2], then [y1] and [y2] are equal.  Consider the final rules used
    in the derivations of [step x y1] and [step x y2].

    - If both are [ST_PlusConstConst], the result is immediate.

    - It cannot happen that one is [ST_PlusConstConst] and the other
      is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
      the form [P t1 t2] where both [t1] and [t2] are constants (by
      [ST_PlusConstConst]) _and_ one of [t1] or [t2] has the form [P
      _].

    - Similarly, it cannot happen that one is [ST_Plus1] and the other
      is [ST_Plus2], since this would imply that [x] has the form [P
      t1 t2] where [t1] both has the form [P t11 t12] and is a
      value (hence has the form [C n]).

    - The cases when both derivations end with [ST_Plus1] or
      [ST_Plus2] follow by the induction hypothesis. [] *)
(* end hide *)
(** **** 練習問題: ★★★, standard, recommended (redo_determinacy)
 
    この変更のサニティチェックのため、決定性を再検証しましょう。
    非形式的には以下の証明になります。
 
    「証明スケッチ」: もし[x]が1ステップで[y1]にも[y2]にも進むならば、
    [y1]と[y2]が等しいことを示さなければならない。
    [step x y1] と [step x y2] の導出の最後の規則を考える。
 
    - もし両者とも[ST_PlusConstConst]ならば、一致は明らかである。
 
    - 一方が [ST_PlusConstConst] で、他方が [ST_Plus1] または [ST_Plus2]
      であることはあり得ない。なぜなら、そうなるためには、
      [x] が [P t1 t2] の形で（[ST_PlusConstConst]より）
      [t1]と[t2]が両者とも定数であり、かつ[t1]または[t2]が [P _] の形でなければならない。
 
    - 同様に、一方が [ST_Plus1] で他方が [ST_Plus2] であることもあり得ない。
      なぜなら、そのためには、[x] が [P t1 t2] の形で、
      [t1] は [P t11 t12] の形であり、かつ値でもなければならない
      （つまり [C n] の形でもある）からである。
 
    - 導出が両者とも [ST_Plus1] または [ST_Plus2] で終わるならば、
      帰納法の仮定から成立する。[] *)

(* begin hide *)
(** Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write your
    formal version from scratch and just use the earlier one if you
    get stuck. *)
(* end hide *)
(** 証明のほとんどは前のものと同じです。しかし、練習問題の効果を最大にするために、
    ゼロから形式的証明を書き、前のものを見るのは行き詰まった時だけにしなさい。 *)

Theorem step_deterministic :
  deterministic step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Strong Progress and Normal Forms *)
(* end hide *)
(** ** 強進行と正規形 *)

(* begin hide *)
(** The definition of single-step reduction for our toy language
    is fairly simple, but for a larger language it would be easy to
    forget one of the rules and accidentally create a situation where
    some term cannot take a step even though it has not been
    completely reduced to a value.  The following theorem shows that
    we did not, in fact, make such a mistake here. *)
(* end hide *)
(** おもちゃの言語に対する1ステップの簡約の定義はかなり単純です。
    しかし、より大きな言語に対しては、何か規則を忘れてしまうことは簡単に起き、
    項が完全に値に簡約されていないのにステップを進めなくなってしまうことが発生します。
    次の定理は、このような間違いをしていないことを示します。*)

(* begin hide *)
(** _Theorem_ (_Strong Progress_): If [t] is a term, then either [t]
    is a value or else there exists a term [t'] such that [t --> t']. *)
(* end hide *)
(** 「定理(強進行)」(_Strong Progress_): [t] が項であるならば、
    [t]は値であるか、そうでなければある項[t']が存在して [t --> t'] となる。 *)

(* begin hide *)
(** _Proof_: By induction on [t].

    - Suppose [t = C n]. Then [t] is a value.

    - Suppose [t = P t1 t2], where (by the IH) [t1] either is a value
      or can step to some [t1'], and where [t2] is either a value or
      can step to some [t2']. We must show [P t1 t2] is either a value
      or steps to some [t'].

      - If [t1] and [t2] are both values, then [t] can take a step, by
        [ST_PlusConstConst].

      - If [t1] is a value and [t2] can take a step, then so can [t],
        by [ST_Plus2].

      - If [t1] can take a step, then so can [t], by [ST_Plus1].  []

   Or, formally: *)
(* end hide *)
(** 「証明」: [t]についての帰納法で証明する。
 
    - [t = C n] とする。すると、[t] は値である。
 
    - [t = P t1 t2] と仮定する。ここで（帰納仮定から）
      [t1]は値であるか、1ステップである[t1']になり、また、[t2]は値であるか、
      1ステップである[t2']になる。
      ここで必要なのは、[P t1 t2]が値であるか、
      ある[t']に1ステップで進むということを示すことである。
 
      - もし[t1]と[t2]がともに値なら、[ST_PlusConstConst]により
        [t]はステップを進むことができる。
 
      - もし[t1]が値で[t2]がステップを進むことができるならば、[ST_Plus2]により
        [t]もステップを進むことができる。
 
      - もし[t1]がステップを進むことができるならば、[ST_Plus1]により
        [t]もステップを進むことができる。  []
 
   形式的には次の通りです。 *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C *) left. apply v_const.
  - (* P *) right. destruct IHt1 as [IHt1 | [t1' Ht1]].
    + (* l *) destruct IHt2 as [IHt2 | [t2' Ht2]].
      * (* l *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PlusConstConst.
      * (* r *)
        exists (P t1 t2').
        apply ST_Plus2. apply IHt1. apply Ht2.
    + (* r *)
      exists (P t1' t2).
      apply ST_Plus1. apply Ht1.
Qed.

(* begin hide *)
(** This important property is called _strong progress_, because
    every term either is a value or can "make progress" by stepping to
    some other term.  (The qualifier "strong" distinguishes it from a
    more refined version that we'll see in later chapters, called
    just _progress_.) *)
(* end hide *)
(** この重要な性質は「強進行」(_strong progress_)と呼ばれます。
    これは、すべての項が値であるか、別の項に「進行できる」("make progress")
    ことからきた名称です。「強」("strong")という修飾句は、
    後の章のより細分されたバージョン（単に「進行」("progress")と呼ばれる）
    と区別するためのものです。*)

(* begin hide *)
(** The idea of "making progress" can be extended to tell us something
    interesting about values: in this language, values are exactly the
    terms that _cannot_ make progress in this sense.

    To state this observation formally, let's begin by giving a name
    to terms that cannot make progress.  We'll call them _normal
    forms_.  *)
(* end hide *)
(** 「進行する」という概念の拡張から、[value](値)についての興味深い性質がわかります:
    値とはこの意味で進行「できない」項のことに他なりません。
 
    この観察結果を形式的に述べるために、進行できない項に名前をつけましょう。そういう項を「正規形(_normal form_)」と呼びます。*)

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* begin hide *)
(** Note that this definition specifies what it is to be a normal form
    for an _arbitrary_ relation [R] over an arbitrary set [X], not
    just for the particular single-step reduction relation over terms
    that we are interested in at the moment.  We'll re-use the same
    terminology for talking about other relations later in the
    course. *)
(* end hide *)
(** この定義は実際には、任意の集合[X]の上の「任意の」関係[R]について、
    何が正規形であるかを定めています。
    今興味対象としている、項の上の特定の1ステップ簡約関係に限るものではありません。
    このコースで後に、別の関係の議論において同じ用語法を用います。*)

(* begin hide *)
(** We can use this terminology to generalize the observation we made
    in the strong progress theorem: in this language, normal forms and
    values are actually the same thing. *)
(* end hide *)
(** 強進行定理の洞察を一般化するためにこの用語を使います。
    この言語では、正規形と値とは実質的に同じものです。*)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

(* begin hide *)
(** Why is this interesting?

    Because [value] is a syntactic concept -- it is defined by looking
    at the form of a term -- while [normal_form] is a semantic one --
    it is defined by looking at how the term steps.

    It is not obvious that these concepts should coincide!  *)
(* end hide *)
(** なぜこれが興味深いのでしょう？
 
    なぜなら[value](値)は構文的概念です。つまり項の形を見ることで定義されます。
    一方[normal_form]（正規形）は意味論的なものです。
    つまり項がどのようにステップを進むかによって定義されます。
 
    この2つの概念が一致することは自明ではないのです! *)

(* begin hide *)
(** Indeed, we could easily have written the definitions incorrectly
    so that they would _not_ coincide. *)
(* end hide *)
(** 実際、正規形と値の概念が一致「しない」定義を誤って書くことが簡単に起こりえます。*)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (value_not_same_as_normal_form1)  

    We might, for example, wrongly define [value] so that it
    includes some terms that are not finished reducing. 

    (Even if you don't work this exercise and the following ones
    in Coq, make sure you can think of an example of such a term.) *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (value_not_same_as_normal_form1)
 
    例えば、[value](値)の定義を間違えていて、簡約が完了していない項を含んでいるかもしれません。
 
    （この課題や以下のCoqの記述を見なかったとしても、そのような項を思いつくようにしておいてください。） *)

Module Temp1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n2,
                value (P t1 (C n2)).              (* <--- *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* FILL IN HERE *) Admitted.
End Temp1.

(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (value_not_same_as_normal_form2)  

    Alternatively, we might wrongly define [step] so that it
    permits something designated as a value to reduce further. *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (value_not_same_as_normal_form2)
 
    あるいは、[step]の定義を間違えていて、
    値とされたものをさらに簡約するようになっているかもしれません。*)

Module Temp2.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).         (* Original definition *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,   
      C n --> P (C n) (C 0)                  (* <--- NEW *)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* FILL IN HERE *) Admitted.

End Temp2.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (value_not_same_as_normal_form3)  

    Finally, we might define [value] and [step] so that there is some
    term that is not a value but that cannot take a step in the [step]
    relation.  Such terms are said to be _stuck_. In this case this is
    caused by a mistake in the semantics, but we will also see
    situations where, even in a correct language definition, it makes
    sense to allow some terms to be stuck. *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (value_not_same_as_normal_form3)
 
    最後に、[value]と[step]の定義が、ある項について、値でもなく、
    [step]関係で1ステップ進むこともできないようになっているかもしれません。
    そのような項は「行き詰まった」(_stuck_)と言うべきでしょう。この場合の
    原因は意味論の定義の誤りにありますが、正しい定義をしているが行き詰まる項が存在する、
    という状況も現れます。 *)

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

(* begin hide *)
(** (Note that [ST_Plus2] is missing.) *)
(* end hide *)
(** ([ST_Plus2] がないことに注意します。) *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.

End Temp3.
(** [] *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Additional Exercises *)
(* end hide *)
(** *** さらなる練習問題 *)

Module Temp4.

(* begin hide *)
(** Here is another very simple language whose terms, instead of being
    just addition expressions and numbers, are just the booleans true
    and false and a conditional expression... *)
(* end hide *)
(** 以下は、別の非常に簡単な言語です。項は、加算式と数の代わりに、
    真理値 true と false、および条件式です... *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(* begin hide *)
(** **** Exercise: 1 star, standard (smallstep_bools)  

    Which of the following propositions are provable?  (This is just a
    thought exercise, but for an extra challenge feel free to prove
    your answers in Coq.) *)
(* end hide *)
(** **** 練習問題: ★, standard (smallstep_bools)
 
    以下の命題のうち証明できるものはどれでしょう？
    （これは単なる頭の体操です。
    しかしさらなるチャレンジとしてCoqで自分の答えを自由に証明してみなさい。） *)

Definition bool_step_prop1 :=
  fls --> fls.

(* FILL IN HERE *)

Definition bool_step_prop2 :=
     test
       tru
       (test tru tru tru)
       (test fls fls fls)
  -->
     tru.

(* FILL IN HERE *)

Definition bool_step_prop3 :=
     test
       (test tru tru tru)
       (test tru tru tru)
       fls
   -->
     test
       tru
       (test tru tru tru)
       fls.

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_smallstep_bools : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (progress_bool)  

    Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions, as well. *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (progress_bool)
 
    加算式についてと同様に、ブール式についても進行定理が証明できます。
    (やってみなさい。) *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (step_deterministic)  *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (step_deterministic)  *)
Theorem step_deterministic :
  deterministic step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module Temp5.

(* begin hide *)
(** **** Exercise: 2 stars, standard (smallstep_bool_shortcut)  

    Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the [then] and
    [else] branches of a conditional are the same value (either
    [tru] or [fls]) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable:

         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.
*)
(* end hide *)
(** **** 練習問題: ★★ (smallstep_bool_shortcut)
 
    条件式の[then]と[else]の枝が同じ値のとき（ともに[tru]であるか、ともに[fls]であるかのとき）、ガードが値に簡約されていなくても、
    条件式全体を枝の値に簡約するように、ステップ関係にバイパスを追加したいとします。
    例えば次の命題を証明できるようにしたいとします:
[[
         test 
            (test tru tru tru) 
            fls 
            fls 
     --> 
         fls 
]]
 *)

(* begin hide *)
(** Write an extra clause for the step relation that achieves this
    effect and prove [bool_step_prop4]. *)
(* end hide *)
(** ステップ関係にこのための追加の節を記述し、[bool_step_prop4]を証明しなさい。*)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  (* FILL IN HERE *)

  where " t '-->' t' " := (step t t').

Definition bool_step_prop4 :=
         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (properties_of_altered_step)  

    It can be shown that the determinism and strong progress theorems
    for the step relation in the lecture notes also hold for the
    definition of step given above.  After we add the clause
    [ST_ShortCircuit]...

    - Is the [step] relation still deterministic?  Write yes or no and
      briefly (1 sentence) explain your answer.

      Optional: prove your answer correct in Coq. *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (properties_of_altered_step)
 
    講義ノートのステップ関係についての決定性定理と強進行定理が、
    上記のステップの定義についても証明できます。
    [ST_ShortCircuit]節を追加した後で...
 
    - [step]関係はそれでも決定性を持つでしょうか？
      yes または no と書き、簡潔に(1文で)その答えを説明しなさい。
 
      Optional: Coq でその答えが正しいことを証明しなさい。 *)

(* begin hide *)
(* FILL IN HERE 
   - Does a strong progress theorem hold? Write yes or no and
     briefly (1 sentence) explain your answer.

     Optional: prove your answer correct in Coq.
*)
(* 訳注：課題の答えを書く位置が次の課題とかぶっているしコメントの形式もおかしい。 *)
(* end hide *)
(** ここに答えを書きなさい。 *)
(**
   - 強進行定理は成立するでしょうか？
     yes または no と書き、簡潔に(1文で)その答えを説明しなさい。
 
     Optional: Coq でその答えが正しいことを証明しなさい。
 *)

(* begin hide *)
(* FILL IN HERE 
   - In general, is there any way we could cause strong progress to
     fail if we took away one or more constructors from the original
     step relation? Write yes or no and briefly (1 sentence) explain
     your answer.

(* FILL IN HERE *)

    [] *)
(* end hide *)
(** ここに答えを書きなさい。 *)
(** 
   - 一般に、オリジナルのステップ関係から1つ以上のコンストラクタを取り除いて、
     強進行性を持たなくする方法はあるでしょうか？
     yes または no と書き、簡潔に(1文で)その答えを説明しなさい。　*)
(** ここに答えを書きなさい。
 
    []  *)

End Temp5.
End Temp4.

(* ################################################################# *)
(* begin hide *)
(** * Multi-Step Reduction *)
(* end hide *)
(** * マルチステップ簡約 *)

(* begin hide *)
(** We've been working so far with the _single-step reduction_
    relation [-->], which formalizes the individual steps of an
    abstract machine for executing programs.

    We can use the same machine to reduce programs to completion -- to
    find out what final result they yield.  This can be formalized as
    follows:

    - First, we define a _multi-step reduction relation_ [-->*], which
      relates terms [t] and [t'] if [t] can reach [t'] by any number
      (including zero) of single reduction steps.

    - Then we define a "result" of a term [t] as a normal form that
      [t] can reach by multi-step reduction. *)
(* end hide *)
(** ここまでは、1ステップ簡約関係 [-->] に取り組んできました。
    これは、プログラムを実行する抽象機械の1つのステップを形式化したものです。
 
    この機械を使って、プログラムを完全に簡約してみるのもおもしろいでしょう。
    つまり、その最後の結果がどうなるかを調べることです。
    これは以下のように形式化できます:
 
    - 最初に、「マルチステップ簡約関係」(_multi-step reduction relation_) [-->*] を定義します。
      この関係は、[t]から1ステップ簡約を何回か（0回も含みます）行うことで[t']に到達できるとき、
      [t]と[t']を関係づけるものです。
 
    - 次に項[t]の結果("result")を、
      [t]がマルチステップ簡約で到達できる正規形[t]として定義します。*)

(** Since we'll want to reuse the idea of multi-step reduction many
    times, let's take a little extra trouble and define it
    generically.

    Given a relation [R] (which will be [-->] for present purposes),
    we define a relation [multi R], called the _multi-step closure
    of [R]_ as follows. *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** (In the [Rel] chapter of _Logical Foundations_ and
    the Coq standard library, this relation is called
    [clos_refl_trans_1n].  We give it a shorter name here for the sake
    of readability.) *)

(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

       - [x = y], or
       - [R x y], or
       - there is some nonempty sequence [z1], [z2], ..., [zn] such that

           R x z1
           R z1 z2
           ...
           R zn y.

    Thus, if [R] describes a single-step of computation, then [z1] ... [zn] 
    is the sequence of intermediate steps of computation between [x] and 
    [y]. *)

(** We write [-->*] for the [multi step] relation on terms. *)

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(** The relation [multi R] has several crucial properties.

    First, it is obviously _reflexive_ (that is, [forall x, multi R x
    x]).  In the case of the [-->*] (i.e., [multi step]) relation, the
    intuition is that a term can execute to itself by taking zero
    steps of execution. *)

(** Second, it contains [R] -- that is, single-step executions are a
    particular case of multi-step executions.  (It is this fact that
    justifies the word "closure" in the term "multi-step closure of
    [R].") *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

(** In particular, for the [multi step] relation on terms, if
    [t1 -->* t2] and [t2 -->* t3], then [t1 -->* t3]. *)

(* ================================================================= *)
(** ** Examples *)

(** Here's a specific instance of the [multi step] relation: *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  { apply ST_Plus1. apply ST_PlusConstConst. }
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  { apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  apply multi_R.
  { apply ST_PlusConstConst. }
Qed.

(* begin hide *)
(** Here's an alternate proof of the same fact that uses [eapply] to
    avoid explicitly constructing all the intermediate terms. *)
(* end hide *)
(** 以下は別証です。
    [eapply]を使うことで、すべての中間的な項を明示的に構成する必要をなくしたものです。*)

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const.
                       apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_PlusConstConst. }
  apply multi_refl.
Qed.

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (test_multistep_2)  *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (test_multistep_2)  *)
Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (test_multistep_3)  *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (test_multistep_3)  *)
Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard (test_multistep_4)  *)
(* end hide *)
(** **** 練習問題: ★★, standard (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Normal Forms Again *)
(* end hide *)
(** ** 正規形再び *)

(* begin hide *)
(** If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)
(* end hide *)
(** [t]が0以上のステップで[t']に簡約され、[t']が正規形のとき、
    「[t']は[t]の正規形である」と言います。*)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

(* begin hide *)
(** We have already seen that, for our language, single-step reduction is
    deterministic -- i.e., a given term can take a single step in
    at most one way.  It follows from this that, if [t] can reach
    a normal form, then this normal form is unique.  In other words, we
    can actually pronounce [normal_form t t'] as "[t'] is _the_
    normal form of [t]." *)
(* end hide *)
(** この言語が1ステップ簡約が決定性を持つことを既に見ました。
    つまり、項が1ステップ進む方法は高々1種類だということです。
    このことから、[t]が正規形に到達するならば、その正規形は1つに決まることになります。
    言い換えると、 [normal_form t t'] を、（「[t']は[t]の正規形である」と読む以外に）
    「[t]の正規形とは[t']である」と読んでよいということです。
    （訳注：原文では "_the_ normal form of [t]" と定冠詞を使ってよいことと記述されています。） *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (normal_forms_unique)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (normal_forms_unique)  *)
Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1.
  inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** Indeed, something stronger is true for this language (though not
    for all languages): the reduction of _any_ term [t] will
    eventually reach a normal form -- i.e., [normal_form_of] is a
    _total_ function.  Formally, we say the [step] relation is
    _normalizing_. *)
(* end hide *)
(** 実のところ、この言語については、より強いことが成立します
    (これは他のすべての言語で成立することではありません):
    「任意の」項[t]はいつかは正規形に到達する、ということです。
    つまり [normal_form_of] は全関数です。
    形式的には、[step]関係は正規化性を持つ(_normalizing_)と言います。 *)

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

(* begin hide *)
(** To prove that [step] is normalizing, we need a couple of lemmas.

    First, we observe that, if [t] reduces to [t'] in many steps, then
    the same sequence of reduction steps within [t] is also possible
    when [t] appears as the left-hand child of a [P] node, and
    similarly when [t] appears as the right-hand child of a [P]
    node whose left-hand child is a value. *)
(* end hide *)
(** [step]が正規化性を持つことを証明するため、二つの補題を必要とします。
 
    一つは、[t]が[t']に何ステップかで簡約されるならば、
    [t]が [P] ノードの左側の子ノードとして現れるときには、
    [t]内で同じ簡約ステップ列が可能である、ということ、
    そしてまた同様のことが、
    [t]が(左側の子ノードが値である)[P]
    の右側の子ノードとして現れるときにも言える、ということです。 *)

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_Plus1. apply H.
    + apply IHmulti.
Qed.

(* begin hide *)
(** **** Exercise: 2 stars, standard (multistep_congr_2)  *)
(* end hide *)
(** **** 練習問題: ★★, standard (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 -->* t2' ->
     P t1 t2 -->* P t1 t2'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** With these lemmas in hand, the main proof is a straightforward
    induction.

    _Theorem_: The [step] function is normalizing -- i.e., for every
    [t] there exists some [t'] such that [t] steps to [t'] and [t'] is
    a normal form.

    _Proof sketch_: By induction on terms.  There are two cases to
    consider:

    - [t = C n] for some [n].  Here [t] doesn't take a step, and we
      have [t' = t].  We can derive the left-hand side by reflexivity
      and the right-hand side by observing (a) that values are normal
      forms (by [nf_same_as_value]) and (b) that [t] is a value (by
      [v_const]).

    - [t = P t1 t2] for some [t1] and [t2].  By the IH, [t1] and [t2]
      have normal forms [t1'] and [t2'].  Recall that normal forms are
      values (by [nf_same_as_value]); we know that [t1' = C n1] and
      [t2' = C n2], for some [n1] and [n2].  We can combine the [-->*]
      derivations for [t1] and [t2] using [multi_congr_1] and
      [multi_congr_2] to prove that [P t1 t2] reduces in many steps to
      [C (n1 + n2)].

      It is clear that our choice of [t' = C (n1 + n2)] is a value,
      which is in turn a normal form. [] *)
(* end hide *)
(** これらの補題を使えば、後は単純な帰納法で証明できます。
 
    「定理」: [step] 関数は正規化性を持つ。つまり、
    任意の[t]に対して、ある[t']があって、[t]からステップを進めると[t']に到達し、
    かつ[t']は正規形である、が成立する。
 
    「証明スケッチ」:項についての帰納法を使う。考える対象は2つの場合である:
 
    - ある[n]について [t = C n] である場合。
      このとき、[t]はステップを進めることができないことから、
      [t' = t] である。左辺は反射性から導出され、
      右辺は、(a)([nf_same_as_value]より)値は正規形であること、
      (b)([v_const]より)[t]は値であること、から導出される。
 
    - ある[t1]、[t2]について、[t = P t1 t2] である場合。
      帰納仮定より[t1]と[t2]はそれぞれ正規形[t1']と[t2']を持つ。
      ([nf_same_as_value]より)正規形は値であったから、
      ある [n1]、[n2]について、[t1' = C n1] かつ [t2' = C n2]
      である。[t1]と[t2]についての [-->*] 導出を、 [multi_congr_1] と [multi_congr_2] によって組合せると、
      [P t1 t2] が幾つかのステップで [C (n1 + n2)] に簡約されることを証明できる。
 
      [t' = C (plus n1 n2)] が値であることは明らかなので、これは正規形である。*)

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
      rewrite nf_same_as_value. apply v_const.
  - (* P *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1]].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2]].
    rewrite nf_same_as_value in Hnormal1.
    rewrite nf_same_as_value in Hnormal2.
    inversion Hnormal1 as [n1 H1].
    inversion Hnormal2 as [n2 H2].
    rewrite <- H1 in Hsteps1.
    rewrite <- H2 in Hsteps2.
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with
        (P (C n1) (C n2)).
        { apply multistep_congr_2. apply v_const. apply Hsteps2. }
        apply multi_R. { apply ST_PlusConstConst. }
    + (* r *)
      rewrite nf_same_as_value. apply v_const.
Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Equivalence of Big-Step and Small-Step *)
(* end hide *)
(** ** ビッグステップとスモールステップの同値性 *)

(* begin hide *)
(** Having defined the operational semantics of our tiny programming
    language in two different ways (big-step and small-step), it makes
    sense to ask whether these definitions actually define the same
    thing!  They do, though it takes a little work to show it.  The
    details are left as an exercise. *)
(* end hide *)
(** 小さなプログラミング言語に対して2つの異なった方法（ビッグステップとスモールステップ）で操作的意味論を定義したので、
    その2つの定義が本当に同じものを定義しているのかを考えるのは意味があります!
    実際に定義は一致しているのですが、それを示すにはもう少し準備が必要です。
    詳細は練習問題として残しています。　*)

(* begin hide *)
(** **** Exercise: 3 stars, standard (eval__multistep)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard (eval__multistep)  *)
Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.

(** The key ideas in the proof can be seen in the following picture:

       P t1 t2 -->            (by ST_Plus1)
       P t1' t2 -->           (by ST_Plus1)
       P t1'' t2 -->          (by ST_Plus1)
       ...
       P (C n1) t2 -->        (by ST_Plus2)
       P (C n1) t2' -->       (by ST_Plus2)
       P (C n1) t2'' -->      (by ST_Plus2)
       ...
       P (C n1) (C n2) -->    (by ST_PlusConstConst)
       C (n1 + n2)

    That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [-->*]: that it is reflexive, transitive, and
    includes [-->]. *)

Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, advanced (eval__multistep_inf)  

    Write a detailed informal version of the proof of [eval__multistep].

(* FILL IN HERE *)
*)
(* end hide *)
(** **** 練習問題: ★★★, advanced (eval__multistep_inf)
 
    [eval__multistep] の非形式的証明を詳細に記述しなさい。
 
(* ここを埋めなさい *)
 *)

(* Do not modify the following line: *)
Definition manual_grade_for_eval__multistep_inf : option (nat*string) := None.
(** [] *)

(** For the other direction, we need one lemma, which establishes a
    relation between single-step reduction and big-step evaluation. *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (step__eval)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard (step__eval)  *)
Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The fact that small-step reduction implies big-step evaluation is
    now straightforward to prove, once it is stated correctly.

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)

(** Make sure you understand the statement before you start to
    work on the proof.  *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (multistep__eval)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Additional Exercises *)
(* end hide *)
(** ** さらなる練習問題 *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (interp_tm)  

    Remember that we also defined big-step evaluation of terms as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.  (Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!) *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (interp_tm)
 
    大ステップ評価を関数 [evalF] としても定義しました。
    既存の意味論とこの関数が等価であることを示しなさい。
    （ヒント：既に [eval] と [multistep] が等価であることを示しました。
    よってどちらを使っても論理的には何も問題ないはずです。
    とはいえ、一方がより簡単に示せます！） *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 4 stars, standard (combined_properties)  

    We've considered arithmetic and conditional expressions
    separately.  This exercise explores how the two interact. *)
(* end hide *)
(** **** 練習問題: ★★★★, standard (combined_properties)
 
    ここまでに算術式と条件式を別々に考えてきました。
    この練習問題ではこの2つがどのように相互作用するかを調べます。 *)

Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(* begin hide *)
(** Earlier, we separately proved for both plus- and if-expressions...

    - that the step relation was deterministic, and

    - a strong progress lemma, stating that every term is either a
      value or can take a step.

    Formally prove or disprove these two properties for the combined
    language.  (That is, state a theorem saying that the property
    holds or does not hold, and prove your theorem.) *)
(* end hide *)
(** 前には、plus式とif式について、以下のことを別々に証明しました...
 
    - ステップ関係が部分関数であること(つまり、決定性を持つこと)。
 
    - すべての項が値であるか、1ステップ進むことができるかを主張する強進行補題。
 
    結合した言語について、これら二つの性質を形式的に証明、または反証しなさい。
    （つまり、定理として性質が成り立つ、または成り立たない、と明言した上でそれを示すのです。） *)

(* FILL IN HERE *)

End Combined.

(* Do not modify the following line: *)
Definition manual_grade_for_combined_properties : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Small-Step Imp *)
(* end hide *)
(** * スモールステップ Imp *)

(* begin hide *)
(** Now for a more serious example: a small-step version of the Imp
    operational semantics. *)
(* end hide *)
(** ここではより本気の例として、Impの操作的意味論のスモールステップ版を示します。 *)

(** The small-step reduction relations for arithmetic and
    boolean expressions are straightforward extensions of the tiny
    language we've been working up to now.  To make them easier to
    read, we introduce the symbolic notations [-->a] and [-->b] for
    the arithmetic and boolean step relations. *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(* begin hide *)
(** We are not actually going to bother to define boolean
    values, since they aren't needed in the definition of [-->b]
    below (why?), though they might be if our language were a bit
    larger (why?). *)
(* end hide *)
(** ここでは、わざわざブール値の定義をする必要がありません。
    なぜならば、以下の [-->b] の定義にはブール値の定義が必要ないからです(なぜでしょう？)。
    言語がもうちょっと大きかったら必要になったかもしれません(なぜでしょう？)。 *)

Reserved Notation " t '/' st '-->a' t' "
                  (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMult a1 a2) / st -->a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMult v1 a2) / st -->a (AMult v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))

    where " t '/' st '-->a' t' " := (astep st t t').

Reserved Notation " t '/' st '-->b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BEq a1 a2) / st -->b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BEq v1 a2) / st -->b (BEq v1 a2')
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BLe a1 a2) / st -->b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BLe v1 a2) / st -->b (BLe v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : forall st b1 b1',
    b1 / st -->b b1' ->
    (BNot b1) / st -->b (BNot b1')
| BS_NotTrue : forall st,
    (BNot BTrue) / st -->b BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st -->b BTrue
| BS_AndTrueStep : forall st b2 b2',
    b2 / st -->b b2' ->
    (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    b1 / st -->b b1' ->
    (BAnd b1 b2) / st -->b (BAnd b1' b2)
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st -->b BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st -->b BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st -->b BFalse

where " t '/' st '-->b' t' " := (bstep st t t').

(* begin hide *)
(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [SKIP] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [SKIP] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [SKIP], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [WHILE] command by transforming it into a
         conditional followed by the same [WHILE]. *)
(* end hide *)
(** コマンドの意味論は興味深い部分です。
    うまくやるために2つの小さなトリックを使います:
 
       - [SKIP] を「コマンド値」("command value")として使います。
         つまり、正規形に逹したコマンドです。
 
            - 代入コマンドは[SKIP]に簡約されます(その際に状態を更新します)。
 
            - コマンド合成は、左側の部分コマンドが[SKIP]に簡約されるのを待って、
              それを捨ててしまいます。そして続けて右側の部分コマンドの簡約をします。
 
       - [WHILE]コマンドの簡約は、条件文とそれに続く同じ[WHILE]コマンドになります。 *)

(* begin hide *)
(** (There are other ways of achieving the effect of the latter
    trick, but they all share the feature that the original [WHILE]
    command needs to be saved somewhere while a single copy of the loop
    body is being reduced.) *)
(* end hide *)
(** (後者の効果を得るには他にもいろいろな方法がありますが、
    いずれも、もとの[WHILE]コマンドをどこかに保存して、ループ本体の1コピーを簡約することには変わりありません。) *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Open Scope imp_scope.
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st -->b b' ->
      TEST b  THEN c1 ELSE c2 FI / st
      -->
      (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      TEST BTrue THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      TEST BFalse THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_While : forall st b c1,
      WHILE b DO c1 END / st
      -->
      (TEST b THEN c1;; WHILE b DO c1 END ELSE SKIP FI) / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Close Scope imp_scope.

(* ################################################################# *)
(* begin hide *)
(** * Concurrent Imp *)
(* end hide *)
(** * 並行 Imp *)

(* begin hide *)
(** Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)
(* end hide *)
(** 最後に、この定義スタイルの力を示すために、Imp に並行動作のコマンドを拡張しましょう。
    このコマンドは2つのサブコマンドを並行実行し、両者が終了した時点で終了します。
    スケジューリングの予測不能性を反映して、
    サブコマンドのアクションは任意の順序でインターリーブします。
    しかし、同じメモリをシェアし、同じ変数を読み書きすることでコミュニケーションできます。*)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st -->b b' ->
          (TEST b THEN c1 ELSE c2 FI) / st 
      --> (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      (TEST BTrue THEN c1 ELSE c2 FI) / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (TEST BFalse THEN c1 ELSE c2 FI) / st --> c2 / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st 
      --> (TEST b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st --> SKIP / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(* begin hide *)
(** Among the (many) interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)
(* end hide *)
(** この言語で特に興味深い性質は、次のプログラムが変数[X]に任意の値を入れた状態で停止させられるというものです。 *)

Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
  END.

(* begin hide *)
(** In particular, it can terminate with [X] set to [0]: *)
(* end hide *)
(** 特に、[X]を[0]にして停止できます: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(* begin hide *)
(** It can also terminate with [X] set to [2]: *)
(* end hide *)
(** [X]を[2]にして停止できます: *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(* begin hide *)
(** More generally... *)
(* end hide *)
(** より一般に... *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (par_body_n__Sn)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (par_body_n__Sn)  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (par_body_n)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (par_body_n)  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st -->*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** ... the above loop can exit with [X] having any value
    whatsoever. *)
(* end hide *)
(** ... 上のループは[X]に任意の値を入れた状態で終了できます。 *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_st).
    split; unfold t_update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H.
  exists (Y !-> 1 ; st). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite t_update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite t_update_neq. assumption. intro X; inversion X.
Qed.

End CImp.

(* ################################################################# *)
(** * A Small-Step Stack Machine *)

(** Our last example is a small-step semantics for the stack machine
    example from the [Imp] chapter of _Logical Foundations_. *)

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

(** **** Exercise: 3 stars, advanced (compiler_is_correct)  

    Remember the definition of [compile] for [aexp] given in the
    [Imp] chapter of _Logical Foundations_. We want now to
    prove [s_compile] correct with respect to the stack machine.

    State what it means for the compiler to be correct according to
    the stack machine small step semantics and then prove it. *)

Definition compiler_is_correct_statement : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Aside: A [normalize] Tactic *)
(* end hide *)
(** * 余談: [normalize] タクティック *)

(* begin hide *)
(** When experimenting with definitions of programming languages
    in Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t -->*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation [astep]. *)
(* end hide *)
(** Coq でプログラミング言語の定義を扱っていると、ある具体的な項がどのように簡約されるか知りたいことがよくあります。
    [t -->* t'] という形のゴールを、 [t] が具体的な項で [t'] が未知の場合に証明するときです。
    このような証明は手でやるには退屈すぎます。
    例えば、スモールステップ簡約の関係 [astep] を使って算術式を簡約することを考えてみましょう。 *)

Example step_example1 : 
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
    apply ST_Plus2.
      apply v_const.
      apply ST_PlusConstConst.
  apply multi_step with (C 10).
    apply ST_PlusConstConst.
  apply multi_refl.
Qed.

(* begin hide *)
(** The proof repeatedly applies [multi_step] until the term reaches a
    normal form.  Fortunately The sub-proofs for the intermediate
    steps are simple enough that [auto], with appropriate hints, can
    solve them. *)
(* end hide *)
(** 証明では、正規形になるまで [multi_step] を繰り返し適用します。
    幸い、証明の途中に出てくる部分は、適切なヒントを与えてやれば [auto] で解けそうです。 *)

Hint Constructors step value.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(* begin hide *)
(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)
(* end hide *)
(** 下の [Tactic Notation] 定義はこのパターンを表現したものです。
    それに加えて、1ステップ毎にそのときのゴールを表示します。
    これは、項がどのように簡約されるか利用者が追えるようにするためです。 *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  normalize.
(* begin hide *)
  (* The [print_goal] in the [normalize] tactic shows
     a trace of how the expression reduced...
         (P (C 3) (P (C 3) (C 4)) -->* C 10)
         (P (C 3) (C 7) -->* C 10)
         (C 10 -->* C 10)
  *)
(* end hide *)
  (** [normalize]内の[print_goal]が簡約の様子を表示する。
<<
         (P (C 3) (P (C 3) (C 4)) -->* C 10) 
         (P (C 3) (C 7) -->* C 10) 
         (C 10 -->* C 10) 
>>
   *)
Qed.

(* begin hide *)
(** The [normalize] tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable. *)
(* end hide *)
(** また、存在量化された変数を入れたゴールから始めることで、[normalize] タクティックは項の正規形を計算できます。 *)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  -->* e'.
Proof.
  eapply ex_intro. normalize.
(* begin hide *)
(* This time, the trace is:
       (P (C 3) (P (C 3) (C 4)) -->* ?e')
       (P (C 3) (C 7) -->* ?e')
       (C 10 -->* ?e')
   where ?e' is the variable ``guessed'' by eapply. *)
(* end hide *)
(** ここでのトレースは以下のようになります。
<<
       (P (C 3) (P (C 3) (C 4)) -->* ?e') 
       (P (C 3) (C 7) -->* ?e') 
       (C 10 -->* ?e') 
>>
   ここで [?e'] は [eapply] で作られた変数です。 *)
Qed.

(* begin hide *)
(** **** Exercise: 1 star, standard (normalize_ex)  *)
(* end hide *)
(** **** 練習問題: ★, standard (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (normalize_ex')  

    For comparison, prove it using [apply] instead of [eapply]. *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (normalize_ex')
 
    比較のため、[eapply] の代わりに [apply] を使って証明しなさい。 *)

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Thu Feb 7 20:09:24 EST 2019 *)
