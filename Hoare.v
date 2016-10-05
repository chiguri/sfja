(*
(** * Hoare: Hoare Logic, Part I *)
*)
(** * Hoare: ホーア論理、第一部 *)

Require Export Imp.

(*
(** In the past couple of chapters, we've begun applying the
    mathematical tools developed in the first part of the course to
    studying the theory of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than properties of particular programs in the language.
      These included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g. functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the [Equiv] chapter). 

    If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (in some cases, even subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in the course when we discuss _types_ and _type
    soundness_.  In this chapter, though, we'll turn to a different
    set of issues.

    Our goal is to see how to carry out some simple examples of
    _program verification_ -- i.e., using the precise definition of
    Imp to prove formally that particular programs satisfy particular
    specifications of their behavior. We'll develop a reasoning system
    called _Floyd-Hoare Logic_ -- often shortened to just _Hoare
    Logic_ -- in which each of the syntactic constructs of Imp is
    equipped with a single, generic "proof rule" that can be used to
    reason compositionally about the correctness of programs involving
    this construct.

    Hoare Logic originates in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software
    systems. *)
*)
(** これまでのいくつかの章ではコースの最初に用意した数学的道具を、小さなプログラミング言語 Imp の理論の学習に適用し始めています。

    - Imp の抽象構文木(_abstract syntax trees_)の型を定義しました。
      また、操作的意味論(_operational semantics_)を与える評価関係(_evaluation relation_)（状態間の部分関数）も定義しました。
      
      定義した言語は小さいですが、C, C++, Java などの本格的な言語の主要な機能を持っています。
      その中には変更可能な状態や、いくつかのよく知られた制御構造も含まれます。

    - いくつものメタ理論的性質(_metatheoretic properties_)を証明しました。
      "メタ"というのは、言語で書かれた特定のプログラムの性質ではなく言語自体の性質という意味です。
      証明したものには、以下のものが含まれます:

        - 評価の決定性

        - 異なった書き方をした定義の同値性

        - プログラムのあるクラスの、停止性の保証

        - プログラムの動作の同値性([Equiv.v]の章において)

    もしここで止めたとしても、有用なものを持っていることになります。
    それは、プログラミング言語とその特性を定義し議論する、数学的に正確で、柔軟で、使いやすい、主要な性質に適合した道具です。

    これらの性質は、言語を設計する人、コンパイラを書く人、そしてユーザも知っておくべきものです。
    実際、その多くは我々が扱うプログラミング言語を理解する上で本当に基本的なことですので、「定理」と意識することはなかったかもしれません。
    しかし、直観的に明らかだと思っている性質はしばしばとても曖昧で、時には間違っていることもあります!

    この問題については、後に型(_types_)とその健全性(_type soundness_)を議論する際に再度出てきます。

    この章では、この最後の考え方をさらに進めます。
    一般にフロイド-ホーア論理(_Floyd-Hoare Logic_)、あるいは、少々不公平に省略してホーア論理(_Hoare Logic_)と呼ばれている推論システムを作ります。
    この推論システムの中では、Imp の各構文要素に対して1つの一般的な「証明規則(proof rule)」が与えられ、これによってその構文要素を含むプログラムについての推論ができるようになっています。

    ホーア論理の起源は1960年代です。そして今現在まで継続してさかんに研究がされています。
    実際のソフトウェアシステムの仕様を定め検証するために使われている非常に多くのツールは、ホーア論理を核としているのです。*)


  
(* ####################################################### *)
(*
(** * Hoare Logic *)
*)
(** * ホーア論理 *)

(*
(** Hoare Logic combines two beautiful ideas: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that programs are correct with
    respect to such specifications -- where by "compositional" we mean
    that the structure of proofs directly mirrors the structure of the
    programs that they are about. *)
*)
(** ホーア論理は2つの重要なことがらを提供します。プログラムの仕様(_specification_)を自然に記述する方法と、その仕様が適合していることを証明する合成的証明法(_compositional proof technique_)です。
    ここでの「合成的(compositional)」という意味は、証明の構造が証明対象となるプログラムの構造を直接的に反映しているということです。 *)

(* ####################################################### *)
(*
(** ** Assertions *)
*)
(** ** 表明 *)

(*
(** To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when program execution
    reaches that point.  Formally, an assertion is just a family of
    propositions indexed by a [state]. *)
*)
(** プログラムの仕様について話そうとするとき、最初に欲しくなるのは、実行中のある特定の時点で成立している性質
    -- つまり、プログラム実行時にその箇所に来た時の状態に関して成り立つ言明 -- についての表明(_assertions_)を作る方法です。
    形式的には、表明は状態に関する述語です。 *)

Definition Assertion := state -> Prop.

(*
(** **** Exercise: 1 star, optional (assertions)  *)
*)
(** **** 練習問題: ★, optional (assertions) *)
Module ExAssertions.

(*
(** Paraphrase the following assertions in English. *)
*)
(** 以下の表明を日本語に直しなさい。 *)

Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

(* FILL IN HERE *)

End ExAssertions.
(** [] *)

(* ####################################################### *)
(*
(** ** Notation for Assertions *)
*)
(** ** 表明の記法 *)

(*
(** This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables (we will never need
    to talk about two different memory states at the same time).  For
    discussing examples informally, we'll adopt some simplifying
    conventions: we'll drop the initial [fun st =>], and we'll write
    just [X] to mean [st X].  Thus, instead of writing *)
*)
(** この方法で表明を書くことは、2つの理由から、若干ヘビーに見えます。
    (1)すべての個々の表明は、[fun st=> ]から始まっています。
    (2)状態[st]は変数を参照するために使うただ1つのものです
    (2つの別々の状態を同時に考える必要はありません)。
    例について非形式的に議論するときには、いくらか簡単にします。
    最初の[fun st =>]は書かず、[st X]のかわりに単に[X]と書きます。
    つまり、非形式的には、次のように書くかわりに *)
(*
(** 
      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)
    we'll write just
         Z * Z <= m /\ ~((S Z) * (S Z) <= m).
*)
*)
(** 
[[
      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)
]]
    次のように書きます。
[[
         Z * Z <= m /\ ~ ((S Z) * (S Z) <= m)
]]
*)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q] (in ASCII, [P -][>][> Q]), if, whenever [P]
    holds in some state [st], [Q] also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** We'll also have occasion to use the "iff" variant of implication
    between assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ####################################################### *)
(*
(** ** Hoare Triples *)
*)
(** ** ホーアの三つ組 *)

(*
(** Next, we need a way of making formal claims about the
    behavior of commands. *)
*)
(** 次に、コマンドの振舞いについての形式的表明を作る方法が必要です。*)

(*
(** Since the behavior of a command is to transform one state to
    another, it is natural to express claims about commands in terms
    of assertions that are true before and after the command executes:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The property [P] is
    called the _precondition_ of [c], while [Q] is the
    _postcondition_.  Formally: *)
*)
(** 表明を、状態の性質について表明するものとして定義してきました。
    そして、コマンドの振舞いは、状態を別の状態に変換するものです。
    これから、コマンドについての表明は次の形をとります:

      - 「もし [c] が表明 [P] を満たす状態から開始され、また、[c]がいつかは停止するならば、最終状態では、表明[Q]が成立することを保証する。」

    この表明は ホーアの三つ組(_Hoare Triple_)と呼ばれます。
    性質[P]は[c]の事前条件(_precondition_)と呼ばれます。
    [Q]は[c]の事後条件(_postcondition_)と呼ばれます。
    形式的には以下の通りです。 *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

(*
(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:
       {{P}} c {{Q}}.
*)
*)
(** ホーアの三つ組を今後多用するので、簡潔な記法を用意すると便利です:
[[
       {{P}}  c  {{Q}}.
]]
*)
(*
(** (The traditional notation is [{P} c {Q}], but single braces
    are already used for other things in Coq.)  *)
*)
(** （伝統的には、ホーアの三つ組は [{P} c {Q}]と書かれます。
    しかし Coq では一重の中カッコは別の意味で既に使われています。） *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(*
(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)
*)
(** この[hoare_spec_scope]アノテーションは、Coqに、
    この記法はグローバルではなく特定のコンテキストで使うものであることを伝えるものです。
    [Open Scope]は、このファイルがそのコンテキストであることを Coq に伝えます。 *)

(*
(** **** Exercise: 1 star, optional (triples)  *)
*)
(** **** 練習問題: ★, optional (triples) *)
(*
(** Paraphrase the following Hoare triples in English.
   1) {{True}} c {{X = 5}}

   2) {{X = m}} c {{X = m + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = m}} 
      c
      {{Y = real_fact m}}.

   6) {{True}} 
      c 
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}

 *)
*)
(** 以下のホーアの三つ組を日本語に直しなさい。
[[
   1) {{True}} c {{X = 5}}

   2) {{X = m}} c {{X = m + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = m}} 
      c
      {{Y = real_fact m}}

   6) {{True}} 
      c 
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
]]
 *)


(** [] *)









(*
(** **** Exercise: 1 star, optional (valid_triples)  *)
*)
(** **** 練習問題: ★, optional (valid_triples) *)
(*
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?
   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE True DO SKIP END {{False}}

   8) {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}

*)
*)
(** 以下のホーアの三つ組のうち、正しい(_valid_)ものを選択しなさい。
    -- 正しいとは、[P],[c],[Q]の関係が真であるということです。
[[
   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE True DO SKIP END {{False}}

   8) {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}
]]

*)
(* FILL IN HERE *)
(** [] *)

(*
(** (Note that we're using informal mathematical notations for
   expressions inside of commands, for readability, rather than their
   formal [aexp] and [bexp] encodings.  We'll continue doing so
   throughout the chapter.) *)
*)
(** （読みやすくするため、コマンド内の式について、[aexp]や[bexp]による記述ではなく非形式的な数学記法を使います。
    この章の最後までその方針をとります。） *)

(*
(** To get us warmed up for what's coming, here are two simple
    facts about Hoare triples. *)
*)
(** ウォーミングアップとして、ホーアの三つ組についての2つの事実を見てみます。*)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ####################################################### *) 
(*
(** ** Proof Rules *)
*)
(** ** 証明規則 *)

(*
(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of Hoare triples.  That is, the
    structure of a program's correctness proof should mirror the
    structure of the program itself.  To this end, in the sections
    below, we'll introduce one rule for reasoning about each of the
    different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules that are useful for gluing things
    together. We will prove programs correct using these proof rules,
    without ever unfolding the definition of [hoare_triple]. *)
*)
(** ホーア論理のゴールは、ホーアの三つ組の正しさを証明する"合成的"手法を提供することです。
    つまり、プログラムの正しさの証明の構造は、
    プログラムの構造をそのまま反映したものになるということです。
    このゴールのために、以降の節では、Impのコマンドのいろいろな構文要素のそれぞれ対して、
    その構文要素について推論するための規則を1つずつ導入します。代入に1つ、
    コマンド合成に1つ、条件分岐に1つ、等です。それに加えて、
    複数のものを結合するために有用な2つの"構造的"規則を導入します。
    これらの規則を用いて、[hoare_triple]の定義を展開することなしにプログラムの正しさを証明していきます。 *)

(* ####################################################### *) 
(*
(** *** Assignment *)
*)
(** *** 代入 *)

(*
(** The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this (valid) Hoare triple:
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].  That is, the property of being equal
    to [1] gets transferred from [Y] to [X].

    Similarly, in
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment.

    More generally, if [a] is _any_ arithmetic expression, then
       {{ a = 1 }}  X ::= a {{ X = 1 }}
    is a valid Hoare triple. 

    This can be made even more general. To conclude that an
    _arbitrary_ property [Q] holds after [X ::= a], we need to assume
    that [Q] holds before [X ::= a], but _with all occurrences of_ [X]
    replaced by [a] in [Q]. This leads to the Hoare rule for
    assignment
      {{ Q [X |-> a] }} X ::= a {{ Q }}
    where "[Q [X |-> a]]" is pronounced "[Q] where [a] is substituted
    for [X]".

    For example, these are valid applications of the assignment
    rule:
      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}  
      X ::= X + 1  
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3}}  
      X ::= 3  
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5)}}  
      X ::= 3  
      {{ 0 <= X /\ X <= 5 }}
*)
*)
(** 代入の規則は、ホーア論理の証明規則の中で最も基本的なものです。
    この規則は次のように働きます。

    次の(正しい)ホーアの三つ組を考えます。
[[
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
]]
    日本語で言うと、[Y]の値が[1]である状態から始めて、[X]を[Y]に代入するならば、
    [X]が[1]である状態になる、ということです。
    つまり、[1]である、という性質が[X]から[Y]に移された、ということです。

    同様に、
[[
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
]]
    においては、同じ性質(1であること)が代入の右辺の[Y+Z]から[X]に移動されています。

    より一般に、[a]が「任意の」算術式のとき、
[[
       {{ a = 1 }}  X ::= a {{ X = 1 }}
]]
    は正しいホーアの三つ組になります。

    さらに一般化して、「任意の」数についての性質[Q]が[X ::= a]の後に成り立つには、
    [X ::= a]の前で、[Q]内の「出現している全ての」[X]を[a]に置き換えたものが成り立っている必要があります。
    ここから次の、代入に関するホーアの三つ組が導かれます。
[[
       {{ Q[X |-> a] }}  X ::= a {{ Q }}
]]
    ただし、"[Q [X |-> a]]"は「[X]を[a]に置換した[Q]」と読みます。

    例えば、以下は、代入規則の正しい適用です:
[[
      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}  
      X ::= X + 1  
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3}}  
      X ::= 3  
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5)}}  
      X ::= 3  
      {{ 0 <= X /\ X <= 5 }}
]]
*)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion."
    That is, given a proposition [P], a variable [X], and an
    arithmetic expression [a], we want to derive another proposition
    [P'] that is just the same as [P] except that, wherever [P]
    mentions [X], [P'] should instead mention [a].  
   
    Since [P] is an arbitrary Coq proposition, we can't directly
    "edit" its text.  Instead, we can achieve the effect we want by
    evaluating [P] in an updated state: *)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

(** That is, [P [X |-> a]] is an assertion [P'] that is just like [P]
    except that, wherever [P] looks up the variable [X] in the current
    state, [P'] instead uses the value of the expression [a].

    To see how this works, let's calculate what happens with a couple
    of examples.  First, suppose [P'] is [(X <= 5) [X |-> 3]] -- that
    is, more formally, [P'] is the Coq expression
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X (aeval st (ANum 3))),
    which simplifies to 
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X 3)
    and further simplifies to
    fun st => 
      ((update st X 3) X) <= 5)
    and by further simplification to
    fun st => 
      (3 <= 5).
    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected).

    For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X+1]].  Formally, [P'] is the Coq expression
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X (aeval st (APlus (AId X) (ANum 1)))),
    which simplifies to 
    fun st => 
      (((update st X (aeval st (APlus (AId X) (ANum 1))))) X) <= 5
    and further simplifies to
    fun st => 
      (aeval st (APlus (AId X) (ANum 1))) <= 5.
    That is, [P'] is the assertion that [X+1] is at most [5].

*)

(*
(** Now we can give the precise proof rule for assignment: 
      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)
*)
(** これを使って、正確な代入の証明規則を与えます:
[[
      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
]]
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(*
(** Here's a first formal proof using this rule. *)
*)
(** この規則を使った最初の形式的証明が次のものです。*)

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn.  Qed.

(*
(** **** Exercise: 2 stars (hoare_asgn_examples)  *)
*)
(** **** 練習問題: ★★ (hoare_asgn_examples) *)
(*
(** Translate these informal Hoare triples...
    1) {{ (X <= 5) [X |-> X + 1] }}
       X ::= X + 1
       {{ X <= 5 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}
   ...into formal statements [assn_sub_ex1, assn_sub_ex2] 
   and use [hoare_asgn] to prove them. *)
*)
(** 次の非形式的なホーアの三つ組...
[[
    1) {{ (X <= 5) [X |-> X + 1] }}
       X ::= X + 1
       {{ X <= 5 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}
]]
   ...を、形式的記述に直してそれぞれを[assn_sub_ex1, assn_sub_ex2]として記述し、[hoare_asgn_eq]を使って証明しなさい。*)

(* FILL IN HERE *)
(** [] *)

(*
(** **** Exercise: 2 stars (hoare_asgn_wrong)  *)
*)
(** **** 練習問題: ★★ (hoare_asgn_wrong) *)
(*
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)
*)
(** 代入規則は、最初に見たとき、ほとんどの人が後向きの規則であるように感じます。
    もし今でも後向きに見えるならば、前向きバージョンの規則を考えてみるのも良いかもしれません。
    次のものは自然に見えます:
[[
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
]]
    この規則が正しくないことを（非形式的に）示す反例を与えなさい。
    ヒント：この規則は算術式[a]を量化しているので、反例はこの規則がうまく動かないように[a]を提示する必要があります。 *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, advanced (hoare_asgn_fwd)  *)
(** However, using an auxiliary variable [m] to remember the original
    value of [X] we can define a Hoare rule for assignment that does,
    intuitively, "work forwards" rather than backwards.
  ------------------------------------------ (hoare_asgn_fwd)
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P st' /\ st X = aeval st' a }}
  (where st' = update st X m)
    Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct (the first hypothesis is the functional extensionality
    axiom, which you will need at some point). Also note that this
    rule is more complicated than [hoare_asgn].
*)

Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) ->  f = g) ->
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (update st X m) /\ st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality m a P.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_fwd_exists)  *)
(** Another way to define a forward rule for assignment is to
    existentially quantify over the previous value of the assigned
    variable.
  ------------------------------------------ (hoare_asgn_fwd_exists)
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (update st X m) /\
                 st X = aeval (update st X m) a }}
*)
(* This rule was proposed by Nick Giannarakis and Zoe Paraskevopoulou. *)

Theorem hoare_asgn_fwd_exists :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) ->  f = g) ->
  forall a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (update st X m) /\
                st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality a P.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *) 
(*
(** *** Consequence *)
*)
(** *** 帰結 *)

(*
(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while
      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}},
    follows directly from the assignment rule, 
      {{True}} X ::= 3 {{X = 3}}.
    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    equivalent, so if one triple is valid, then the other must
    certainly be as well.  We might capture this observation with the
    following rule:
                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
    Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.
                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q 
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)
*)
(** ホーア規則から得られる事前条件や事後条件が欲しいものと完全には一致しない、ということが身近な場面においてしばしば起こります。
    それらは論理的には証明しようとするゴールと同値にも関わらず、構文上違う形をしているために単一化できない、という場合がありえます。
    あるいは、想定するゴールに比べて、(事前条件について)論理的に弱かったり、(事後条件について)論理的に強かったりすることがあります。

    例えば、
[[
      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}}
]]
    が代入規則に直接従うのに対して、より自然な三つ組
[[
      {{True}} X ::= 3 {{X = 3}}.
]]
    はそうではないのです。この三つ組も正しいのですが、[hoare_asgn] 
    (または [hoare_asgn_eq]) のインスタンスではないのです。
    なぜなら、[True] と [(X = 3) [X |-> 3]] は、構文的に等しい表明ではないからです。
    しかし、これらが論理的に等価である以上、一方の三つ組が正しいのであれば、もう一方も同様に正しくあるべきです。このことを、以下の規則によって表現します。
[[
                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
]]
    Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.
[[
                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q 
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
]]
*)

(*
(** Here are the formal versions: *)
*)
(** 以下が形式化版です: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

(*
(** For example, we might use the first consequence rule like this:
                {{ True }} ->>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
    Or, formally... 
*)
*)
(** (例えば、一つ目の帰結規則を次のように使うことができます:
[[
                {{ True }} =>
                {{ 1 = 1 }}
    X ::= 1
                {{ X = 1 }}
]]
    あるいは、形式化すると...
*)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> ANum 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, update. simpl. reflexivity.
Qed.

(** Finally, for convenience in some proofs, we can state a "combined"
    rule of consequence that allows us to vary both the precondition
    and the postcondition. 
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* ####################################################### *)
(*
(** *** Digression: The [eapply] Tactic *)
*)
(** *** 余談: [eapply] タクティック *)

(*
(** This is a good moment to introduce another convenient feature of
    Coq.  We had to write "[with (P' := ...)]" explicitly in the proof
    of [hoare_asgn_example1] and [hoare_consequence] above, to make
    sure that all of the metavariables in the premises to the
    [hoare_consequence_pre] rule would be set to specific
    values.  (Since [P'] doesn't appear in the conclusion of
    [hoare_consequence_pre], the process of unifying the conclusion
    with the current goal doesn't constrain [P'] to a specific
    assertion.)

    This is a little annoying, both because the assertion is a bit
    long and also because for [hoare_asgn_example1] the very next
    thing we are going to do -- applying the [hoare_asgn] rule -- will
    tell us exactly what it should be!  We can use [eapply] instead of
    [apply] to tell Coq, essentially, "Be patient: The missing part is
    going to be filled in soon." *)
*)
(** ここで、良い機会ですので、Coq の別の便利な機能を紹介しておきましょう。
    上述の例で明示的に[P']を書かなければならないことは、少々やっかいです。
    なぜなら、すぐ次にやること、つまり[hoare_asgn]規則を適用すること、が、
    まさに、それがどうでなければならないかを決定することだからです。    
    こういう場合、[apply]の代わりに[eapply]を使うことができます。
    そうすることは、本質的に、「抜けている部分は後で埋めます」と 
    Coq に伝えることになります。*)

Example hoare_asgn_example1' :
  {{fun st => True}} 
  (X ::= (ANum 1)) 
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

(** In general, [eapply H] tactic works just like [apply H] except
    that, instead of failing if unifying the goal with the conclusion
    of [H] does not determine how to instantiate all of the variables
    appearing in the premises of [H], [eapply H] will replace these
    variables with so-called _existential variables_ (written [?nnn])
    as placeholders for expressions that will be determined (by
    further unification) later in the proof. *)

(** In order for [Qed] to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Coq
    will (rightly) refuse to accept the proof. Remember that the Coq
    tactics build proof objects, and proof objects containing
    existential variables are not complete. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.

(** Coq gives a warning after [apply HP]:
     No more subgoals but non-instantiated existential variables:
     Existential 1 =
     ?171 : [P : nat -> nat -> Prop
             Q : nat -> Prop
             HP : forall x y : nat, P x y
             HQ : forall x y : nat, P x y -> Q x |- nat] 
  
     (dependent evars: ?171 open,)

     You can use Grab Existential Variables.
   Trying to finish the proof with [Qed] gives an error:
<<
    Error: Attempt to save a proof with existential variables still
    non-instantiated
>> *)

Abort.

(** An additional constraint is that existential variables cannot be
    instantiated with terms containing (ordinary) variables that did
    not exist at the time the existential variable was created. *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
(** Doing [apply HP'] above fails with the following error:
     Error: Impossible to unify "?175" with "y".
    In this case there is an easy fix:
    doing [destruct HP] _before_ doing [eapply HQ].
*)

Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(** In the last step we did [apply HP'] which unifies the existential
    variable in the goal with the variable [y]. The [assumption]
    tactic doesn't work in this case, since it cannot handle
    existential variables. However, Coq also provides an [eassumption]
    tactic that solves the goal if one of the premises matches the
    goal up to instantiations of existential variables. We can use
    it instead of [apply HP']. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

    

(** **** Exercise: 2 stars (hoare_asgn_examples_2)  *)
(** Translate these informal Hoare triples...
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
   ...into formal statements [assn_sub_ex1', assn_sub_ex2'] and 
   use [hoare_asgn] and [hoare_consequence_pre] to prove them. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** *** Skip *)

(*
(** Since [SKIP] doesn't change the state, it preserves any
    property P:
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)
*)
(** [SKIP]は状態を変えないことから、任意の性質 P を保存します:
[[
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
]]
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ####################################################### *) 
(*
(** *** Sequencing *)
*)
(** *** コマンド合成 *)

(*
(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
*)
*)
(** より興味深いことに、コマンド[c1]が、[P]が成立する任意の状態を[Q]が成立する状態にし、
    [c2]が、[Q]が成立する任意の状態を[R]が成立する状態にするとき、
    [c1]に続いて[c2]を行うことは、[P]が成立する任意の状態を[R]が成立する状態にします:
[[
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
]]
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(*
(** Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule: the natural way to construct a Hoare-logic proof is
    to begin at the end of the program (with the final postcondition)
    and push postconditions backwards through commands until we reach
    the beginning. *)
*)
(** 形式的規則[hoare_seq]においては、
    前提部分が「逆順」である([c1]の前に[c2]が来る)ことに注意してください。
    この順は、規則を使用する多くの場面で情報の自然な流れにマッチするのです。
    ホーア論理における証明の構築はプログラムの終わりから（最後の事後条件を用いて）、プログラムの始めにたどり着くまでコマンドをさかのぼる方が自然なのです。 *)

(*
(** Informally, a nice way of recording a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
      {{ a = n }}
    X ::= a;;
      {{ X = n }}      <---- decoration for Q
    SKIP
      {{ X = n }}
*)
*)
(** 非形式的には、この規則を利用した証明を記録する良い方法は、
    [c1]と[c2]の間に中間表明[Q]を記述する"修飾付きプログラム"の様にすることです:
[[
      {{ a = n }}
    X ::= a;
      {{ X = n }}      <---- 修飾 Q
    SKIP
      {{ X = n }}
]]
*)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}} 
  (X ::= a;; SKIP) 
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H. subst. reflexivity. Qed.

(** You will most often use [hoare_seq] and
    [hoare_consequence_pre] in conjunction with the [eapply] tactic,
    as done above. *)

(*
(** **** Exercise: 2 stars (hoare_asgn_example4)  *)
*)
(** **** 練習問題: ★★ (hoare_asgn_example4) *)
(*
(** Translate this "decorated program" into a formal proof:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)
*)
(** 次の修飾付きプログラムを形式的証明に直しなさい:
[[
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
]]
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 3 stars (swap_exercise)  *)
*)
(** **** 練習問題: ★★★ (swap_exercise) *)
(*
(** Write an Imp program [c] that swaps the values of [X] and [Y]
    and show (in Coq) that it satisfies the following
    specification:
      {{X <= Y}} c {{Y <= X}}
*)
*)
(** [X]と[Y]の値を交換するImpプログラム[c]を書き、それが次の仕様を満たすことを(Coq で)示しなさい:
[[
      {{X <= Y}} c {{Y <= X}}
]]
*)

Definition swap_program : com :=
  (* FILL IN HERE *) admit.

Theorem swap_exercise :
  {{fun st => st X <= st Y}} 
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 3 stars (hoarestate1)  *)
*)
(** **** 練習問題: ★★★ (hoarestate1) *)
(*
(** Explain why the following proposition can't be proven:
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
         (X ::= (ANum 3);; Y ::= a)
         {{fun st => st Y = n}}.
*)
*)
(** 次の命題が証明できない理由を説明しなさい:
[[
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
         (X ::= (ANum 3);; Y ::= a)
         {{fun st => st Y = n}}.
]]
*)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *) 
(*
(** *** Conditionals *)
*)
(** *** 条件分岐 *)

(*
(** What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
   However, this is rather weak. For example, using this rule,
   we cannot show that:
     {{ True }} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
     {{ X <= Y }}
   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)
*)
(** 条件分岐コマンドについて推論するために、どのような規則が必要でしょうか？
    確かに、分岐のどちらの枝を実行した後でも表明[Q]が成立するならば、条件分岐全体でも[Q]が成立するでしょう。
    これから次のように書くべきかもしれません:
[[
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
]]
   しかし、これはかなり弱いのです。
   例えば、この規則を使っても次のことを示すことができません:
[[
     {{True}}
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1
     FI
     {{ X <= Y }}
]]
   なぜなら、この規則では、"then"部と"else"部のどちらの代入が起こる状態なのかについて、何も言っていないからです。 *)
   
(*
(** But we can actually say something more precise.  In the
   "then" branch, we know that the boolean expression [b] evaluates to
   [true], and in the "else" branch, we know it evaluates to [false].
   Making this information available in the premises of the rule gives
   us more information to work with when reasoning about the behavior
   of [c1] and [c2] (i.e., the reasons why they establish the
   postcondition [Q]). *)
*)
(** しかし、実際には、より詳しいことを言うことができます。
   "then"の枝では、ブール式[b]の評価結果が[true]になることがわかっています。
   また"else"の枝では、それが[false]になることがわかっています。
   この情報を補題の前提部分で利用できるようにすることで、[c1]と[c2]の振舞いについて(つまり事後条件[Q]が成立する理由について)推論するときに、より多くの情報を使うことができるようになります。 *)

(*
(**
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
*)
*)
(**
[[
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
]]
*)

(*
(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)
*)
(** この規則を形式的に解釈するために、もう少しやることがあります。

    厳密には、上述の表明において、表明とブール式の連言[P /\ b]は、型チェックを通りません。
    これを修正するために、ブール式[b]を形式的に「持ち上げ」て、表明にしなければなりません。
    このために[bassn b]と書きます。
    これは"ブール式[b]の評価結果が(任意の状態で)[true]になる"という表明です。*)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(*
(** A couple of useful facts about [bassn]: *)
*)
(** [bassn]についての2つの便利な事実です: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(*
(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)
*)
(** いよいよ条件分岐についてのホーア証明規則を形式化し、正しいことを証明できます。*)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.


(* ####################################################### *) 

(** * Hoare Logic: So Far *)

(** 
Idea: create a _domain specific logic_ for reasoning about properties of Imp programs.

- This hides the low-level details of the semantics of the program
- Leads to a compositional reasoning process


The basic structure is given by _Hoare triples_ of the form:
  {{P}} c {{Q}}
]] 

- [P] and [Q] are predicates about the state of the Imp program
- "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

*)


(** ** Hoare Logic Rules (so far) *)

(**
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 


                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)


(*
(** *** Example *)
*)
(** *** 例 *)
(*
(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)
*)
(** 以下が、最初に挙げたプログラムが与えられた条件を満たすことの証明です。*)

Example if_example : 
    {{fun st => True}} 
  IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update, assert_implies.
    simpl. intros st [_ H].
    apply beq_nat_true in H.
    rewrite H. omega.
  Case "Else".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update, assert_implies.
    simpl; intros st _. omega.
Qed.

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  (* FILL IN HERE *) Admitted.

(* ####################################################### *)
(** *** Exercise: One-sided conditionals *)

(** **** Exercise: 4 stars (if1_hoare)  *)

(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [IF1 b THEN c FI]. Here [b] is a
    boolean expression, and [c] is a command. If [b] evaluates to
    [true], then command [c] is evaluated. If [b] evaluates to
    [false], then [IF1 b THEN c FI] does nothing.

    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)


(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CIF1" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" := 
  (CIf1 b c) (at level 80, right associativity).

(** Next we need to extend the evaluation relation to accommodate
    [IF1] branches.  This is for you to do... What rule(s) need to be
    added to [ceval] to evaluate one-sided conditionals? *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
(* FILL IN HERE *)

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  (* FILL IN HERE *)
  ].

(** Now we repeat (verbatim) the definition and notation of Hoare triples. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Finally, we (i.e., you) need to state and prove a theorem,
    [hoare_if1], that expresses an appropriate Hoare logic proof rule
    for one-sided conditionals. Try to come up with a rule that is
    both sound and as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, prove formally [hoare_if1_good] that your rule is 
    precise enough to show the following valid Hoare triple:
  {{ X + Y = Z }}
  IF1 Y <> 0 THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Hint: Your proof of this triple may need to use the other proof
    rules also. Because we're working in a separate module, you'll
    need to copy here the rules you find necessary. *)


Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof. (* FILL IN HERE *) Admitted.

End If1.
(** [] *)

(* ####################################################### *)
(*
(** *** Loops *)
*)
(** *** ループ *)

(*
(** Finally, we need a rule for reasoning about while loops. *)
*)
(** 最後に、ループについての推論規則が必要です。 *)

(*
(** Suppose we have a loop
      WHILE b DO c END
    and we want to find a pre-condition [P] and a post-condition
    [Q] such that
      {{P}} WHILE b DO c END {{Q}} 
    is a valid triple. *)
*)
(** 次のループを考えます:
      WHILE b DO c END
    そして、次の三つ組が正しくなる事前条件[P]と事後条件[Q]を探します:
[[
      {{P}} WHILE b DO c END {{Q}} 
]]
*)

(** *** *)

(*
(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write: *)
*)
(** まず、[b]が最初から偽であるときを考えましょう。
    このときループの本体はまったく実行されません。
    この場合は、ループは[SKIP]と同様の振舞いをしますので、次のように書いても良いかもしれません。 *)

(*
(**
      {{P}} WHILE b DO c END {{P}}.
*)
*)
(**
[[
      {{P}} WHILE b DO c END {{P}}.
]]
*)

(*
(** 
    But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
*)
*)
(**
    しかし、条件分岐について議論したのと同様に、最後でわかっていることはもう少し多いのです。
    最終状態では[P]であるだけではなく[b]が偽になっているのです。
    そこで、事後条件にちょっと付け足すことができます:
*)
(*
(** 
      {{P}} WHILE b DO c END {{P /\ ~b}}
*)
*)
(** 
[[
      {{P}} WHILE b DO c END {{P /\ ~b}}
]]
*)

(*
(** 
    What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule:
*)
*)
(**
    それでは、ループの本体が実行されるときはどうなるでしょう？
    ループを最後に抜けるときには[P]が成立することを確実にするために、コマンド[c]の終了時点で常に[P]が成立することを確認する必要があるのは確かでしょう。
    さらに、[P]が[c]の最初の実行の前に成立しており、[c]を実行するたびに、終了時点で[P]の成立が再度確立されることから、[P]が[c]の実行前に常に成立していると仮定することができます。
    このことから次の規則が得られます:
*)
(*
(** 
                   {{P}} c {{P}}
        -----------------------------------  
        {{P}} WHILE b DO c END {{P /\ ~b}}
*)
*)
(** 
[[
                   {{P}} c {{P}}
        -----------------------------------  
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]
*)
(*
(** 
    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state.  This gives us a little more information to use in
    reasoning about [c] (showing that it establishes the invariant by
    the time it finishes).  This gives us the final version of the rule:
*)
*)
(**
    これで求める規則にかなり近付いたのですが、もうちょっとだけ改良できます。
    ループ本体の開始時点で、[P]が成立しているだけでなく、ガード[b]が現在の状態で真であるということも言えます。
    このことは、[c]についての（[P]が[c]の終了時にも成立することの）推論の際にいくらかの情報を与えてくれます。
    結局、規則の最終バージョンはこうなります:
*)
(*
(**
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
    The proposition [P] is called an _invariant_ of the loop.
*)
*)
(**
[[
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]
    命題[P]は不変条件(_invariant_)と呼ばれます。
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on [He], because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just [c]. *)
  (* 先に見たように、[He]についての帰納法を使う必要があります。
     なぜなら、ループを抜けない場合には、仮定は[c]だけでなくループ全体について言及しているからです。*)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.
  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(**
    One subtlety in the terminology is that calling some assertion [P]
    a "loop invariant" doesn't just mean that it is preserved by the
    body of the loop in question (i.e., [{{P}} c {{P}}], where [c] is
    the loop body), but rather that [P] _together with the fact that
    the loop's guard is true_ is a sufficient precondition for [c] to
    ensure [P] as a postcondition.

    This is a slightly (but significantly) weaker requirement.  For
    example, if [P] is the assertion [X = 0], then [P] _is_ an
    invariant of the loop
    WHILE X = 2 DO X := 1 END
    although it is clearly _not_ preserved by the body of the
    loop.
*)





Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post. 
  apply hoare_while. 
  eapply hoare_consequence_pre. 
  apply hoare_asgn. 
  unfold bassn, assn_sub, assert_implies, update. simpl.
    intros st [H1 H2]. apply ble_nat_true in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb]. 
    simpl in Hb. destruct (ble_nat (st X) 2) eqn : Heqle. 
    apply ex_falso_quodlibet. apply Hb; reflexivity.  
    apply ble_nat_false in Heqle. omega. 
Qed.






(** *** *)
(*
(** We can use the while rule to prove the following Hoare triple,
    which may seem surprising at first... *)
*)
(** while規則を使うと、次のホーアの三つ組も証明できます。
    これは最初は驚くでしょう...*)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. apply I. 
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.  Qed.

(*
(** Of course, this result is not surprising if we remember that
    the definition of [hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition. *)
*)
(** もちろん、この結果は驚くことではないのです。
    ふり返って[hoare_triple]の定義を見てみると、
    コマンドが停止した場合「のみ」に意味がある表明をしているのです。
    もしコマンドが終了しないなら、なんでも望むものが事後条件として示せます。 *)

(*
(** Hoare rules that only talk about terminating commands are
    often said to describe a logic of "partial" correctness.  It is
    also possible to give Hoare rules for "total" correctness, which
    build in the fact that the commands terminate. However, in this
    course we will only talk about partial correctness. *)
*)
(** 停止するコマンドについてだけを議論するホーア規則は、「部分」正当性("partial" correctness)
    を記述していると言われます。
    「完全」正当性("total" correctness)についてのホーア規則を与えることも可能です。
    それは、コマンドが停止するという事実を組み込んだものです。
    ただし、このコースでは部分正当性についてのみ説明します。 *)

(* ####################################################### *)
(*
(** *** Exercise: [REPEAT] *)
*)
(** *** 練習問題: [REPEAT] *)

Module RepeatExercise.

(*
(** **** Exercise: 4 stars, advanced (hoare_repeat)  *)
*)
(** **** 練習問題: ★★★★, advanced (hoare_repeat) *)
(*
(** In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [UNTIL] a [END]. You will write the
    evaluation rule for [repeat] and add a new Hoare rule to
    the language for programs involving it. *)
*)
(** この練習問題では、言語に新たなコマンドを追加します。
    [REPEAT] c [UNTIL] a [END]という形のコマンドです。
    [repeat]の評価規則を記述し、このコマンドを含むプログラムについての評価規則と新たなホーア論理の規則を追加しなさい。 *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(*
(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)
*)
(** [REPEAT]は[WHILE]と同じように振舞います。
    ただし、ループのガードが本体の実行の「後で」評価され、それが「偽」である間はループがくりかえされるという点が違います。
    このことにより、本体は常に少なくとも1回は実行されることになります。*)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "CRepeat" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

(*
(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)
*)
(** 以下の[ceval]に[REPEAT]の新たな規則を追加しなさい。
    [WHILE]の規則を参考にして構いません。
    ただ、[REPEAT]の本体は1度は実行されることと、ループの終了はガードが真になったときであることは忘れないで下さい。
    そして、この場合を扱えるように、[ceval_cases]タクティックを更新しなさい。*)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
(* FILL IN HERE *)
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass"
  | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
(* FILL IN HERE *)
].

(*
(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)
*)
(** 上記から2つの定義のコピーし、新しい[ceval]を使うようにしました。*)

Notation "c1 '/' st '||' st'" := (ceval st c1 st') 
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) 
                        : Prop :=
  forall st st', (c / st || st') -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** To make sure you've got the evaluation rules for [REPEAT] right,
    prove that [ex1_repeat evaluates correctly. *)

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state ||
               update (update empty_state X 1) Y 1.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:
  {{ X > 0 }}
  REPEAT
    Y ::= X;;
    X ::= X - 1
  UNTIL X = 0 END
  {{ X = 0 /\ Y > 0 }}
*)


End RepeatExercise.
(** [] *)

(* ####################################################### *)
(** ** Exercise: [HAVOC] *)

(** **** Exercise: 3 stars (himp_hoare)  *)

(** In this exercise, we will derive proof rules for the [HAVOC] command
    which we studied in the last chapter. First, we enclose this work
    in a separate module, and recall the syntax and big-step semantics
    of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st || update st X n

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Havoc" ].

(** The definition of Hoare triples is exactly as before. Unlike our
    notion of program equivalence, which had subtle consequences with
    occassionally nonterminating commands (exercise [havoc_diverge]),
    this definition is still fully satisfactory. Convince yourself of
    this before proceeding. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st || st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre] and prove that the resulting rule is correct. *)

Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
(* FILL IN HERE *) admit.

Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

End Himp.
(** [] *)


(* ####################################################### *)
(** ** Complete List of Hoare Logic Rules *)

(** Above, we've introduced Hoare Logic as a tool to reasoning
    about Imp programs. In the reminder of this chapter we will
    explore a systematic way to use Hoare Logic to prove properties
    about programs. The rules of Hoare Logic are the following: *)

(**
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
    In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior.
*)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

