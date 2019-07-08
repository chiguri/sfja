(** * Hoare: ホーア論理、第一部 *)
(* begin hide *)
(** * Hoare: Hoare Logic, Part I *)
(* end hide *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From PLF Require Import Imp.

(* begin hide *)
(** In the final chaper of _Logical Foundations_ (_Software
    Foundations_, volume 1), we began applying the mathematical tools
    developed in the first part of the course to studying the theory
    of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than of particular programs in the language.  These
      included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the [Equiv]
          chapter). *)
(* end hide *)
(** 「論理の基礎」（「ソフトウェアの基礎」第一巻）の最後の章では、コースの最初に用意した数学的道具を、小さなプログラミング言語 Imp の理論の学習に適用してみました。
 
    - Imp の抽象構文木(_abstract syntax trees_)の型を定義しました。
      また、操作的意味論(_operational semantics_)を与える評価関係(_evaluation relation_)（状態間の部分関数）も定義しました。
 
      定義した言語は小さいですが、C, C++, Java などの本格的な言語の主要な機能を持っています。
      その中には変更可能な状態や、いくつかのよく知られた制御構造も含まれます。
 
    - いくつものメタ理論的性質(_metatheoretic properties_)を証明しました。
      "メタ"というのは、言語で書かれた特定のプログラムの性質ではなく言語自体の性質という意味です。
      証明したものには、以下のものが含まれます:
 
        - 評価の決定性
 
        - 異なった書き方をした定義の同値性（例：算術式の関数による評価と関係による評価）
 
        - プログラムのあるクラスの、停止性の保証
 
        - いくつかの有用なプログラム変換の正当性（意味の保存）
 
        - プログラムの動作の同値性（[Equiv]の章において） *)

(* begin hide *)
(** If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (sometimes also subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in this volume when we discuss _types_ and _type
    soundness_.  In this chapter, though, we turn to a different set
    of issues.

    Our goal is to carry out some simple examples of _program
    verification_ -- i.e., to use the precise definition of Imp to
    prove formally that particular programs satisfy particular
    specifications of their behavior.  We'll develop a reasoning
    system called _Floyd-Hoare Logic_ -- often shortened to just
    _Hoare Logic_ -- in which each of the syntactic constructs of Imp
    is equipped with a generic "proof rule" that can be used to reason
    compositionally about the correctness of programs involving this
    construct.

    Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software systems.

    Hoare Logic combines two beautiful ideas: a natural way of writing
    down _specifications_ of programs, and a _compositional proof
    technique_ for proving that programs are correct with respect to
    such specifications -- where by "compositional" we mean that the
    structure of proofs directly mirrors the structure of the programs
    that they are about. *)
(* end hide *)
(** もしここで止めたとしても、有用なものを持っていることになります。
    それは、プログラミング言語とその特性を定義し議論する、数学的に正確で、柔軟で、使いやすい、主要な性質に適合した道具です。
    これらの性質は、言語を設計する人、コンパイラを書く人、そしてユーザも知っておくべきものです。
    実際、その多くは我々が扱うプログラミング言語を理解する上で本当に基本的なことですので、「定理」と意識することはなかったかもしれません。
    しかし、直観的に明らかだと思っている性質はしばしばとても曖昧で、時には間違っていることもあります!
 
    言語に対するメタな性質については、この巻の後ろで型(_types_)とその健全性(_type soundness_)を議論する際に再度出てきます。
    この章では、別の問題について進めます。
 
    本章のゴールは、「プログラム検証(_program verification_)」をいくつか行うことです。
    そのために、Imp言語の特定のプログラムがある性質を満たすかについて、形式的に証明するための適切な定義を用います。
    一般にフロイド-ホーア論理(_Floyd-Hoare Logic_)、あるいは、単にホーア論理(_Hoare Logic_)と呼ばれる推論システムを作ります。
    この推論システムの中では、Imp の各構文要素に対してそれぞれ一般的な「証明規則(proof rule)」が与えられ、プログラムの構造に基づいて正当性を推論できるようになっています。
 
    ホーア論理の起源は1960年代です。
    そして今現在まで継続してさかんに研究がされています。
    実際のソフトウェアシステムの仕様を定め検証するために使われている非常に多くのツールは、ホーア論理を核としているのです。
 
    ホーア論理は2つの重要なことがらを提供します。プログラムの仕様(_specification_)を自然に記述する方法と、その仕様が適合していることを証明する合成的証明法(_compositional proof technique_)です。
    ここでの「合成的(compositional)」という意味は、証明の構造が証明対象となるプログラムの構造を直接的に反映しているということです。 *)

(** Overview of this chapter...
    
    Topic:      
      - A systematic method for reasoning about the _functional
        correctness_ of programs in Imp

    Goals:
      - a natural notation for _program specifications_ and
      - a _compositional_ proof technique for program correctness

    Plan:
      - specifications (assertions / Hoare triples)
      - proof rules
      - loop invariants
      - decorated programs
      - examples *)

(* ################################################################# *)
(* begin hide *)
(** * Assertions *)
(* end hide *)
(** * 表明 *)

(* begin hide *)
(** To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when execution reaches that
    point.  Formally, an assertion is just a family of propositions
    indexed by a [state]. *)
(* end hide *)
(** プログラムの仕様について話そうとするとき、最初に欲しくなるのは、実行中のある特定の時点で成立している性質
    -- つまり、プログラム実行時にその箇所に来た時の状態に関して成り立つ言明 -- についての表明(_assertions_)を作る方法です。
    形式的には、表明は状態に関する述語です。 *)

Definition Assertion := state -> Prop.

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (assertions)  

    Paraphrase the following assertions in English (or your favorite
    natural language). *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (assertions)
 
    以下の表明を日本語（または好きな自然言語）に直しなさい。 *)

Module ExAssertions.
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

(* begin hide *)
(** This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables in assertions (we
    will never need to talk about two different memory states at the
    same time).  For discussing examples informally, we'll adopt some
    simplifying conventions: we'll drop the initial [fun st =>], and
    we'll write just [X] to mean [st X].  Thus, instead of writing 

      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)

    we'll write just

      Z * Z <= m /\ ~((S Z) * (S Z) <= m).
*)
(* end hide *)
(** この方法で表明を書くことは、2つの理由から、若干ヘビーに見えます。
    (1)すべての個々の表明は、[fun st => ]から始まっています。
    (2)状態[st]は表明から変数を参照するために使う唯一の状態です（2つの別々の状態を同時に考える必要はありません）。
    例について非形式的に議論するときには、いくらか簡単にします。
    最初の[fun st =>]は書かず、[st X]のかわりに単に[X]と書きます。
    つまり、非形式的には、次のように書くかわりに
[[
      fun st => (st Z) * (st Z) <= m /\ 
                ~ ((S (st Z)) * (S (st Z)) <= m) 
]]
    次のように書きます。
[[
      Z * Z <= m /\ ~((S Z) * (S Z) <= m) 
]]
 *)

(* begin hide *)
(** This example also illustrates a convention that we'll use
    throughout the Hoare Logic chapters: in informal assertions,
    capital letters like [X], [Y], and [Z] are Imp variables, while
    lowercase letters like [x], [y], [m], and [n] are ordinary Coq
    variables (of type [nat]).  This is why, when translating from
    informal to formal, we replace [X] with [st X] but leave [m]
    alone. *)
(* end hide *)
(** この例は、ホーア論理の章を通じて使う慣習に則っています。
    非形式的な表明では、[X]、[Y]、[Z]のような大文字の変数をImpの変数とし、[x]、[y]、[m]、[n]などの小文字の変数をCoqの（[nat]型の）変数とします。
    そのため、この非形式的な表明を形式的な表明に変換する際には、[X]を[st X]に置き換えますが、[m]はそのままにします。 *)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(* begin hide *)
(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)
(* end hide *)
(** この[hoare_spec_scope]アノテーションは、Coqに、この記法はグローバルではなく特定のコンテキストで使うものであることを伝えるものです。
    [Open Scope]は、このファイルがそのコンテキストであることを Coq に伝えます。 *)

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ################################################################# *)
(* begin hide *)
(** * Hoare Triples *)
(* end hide *)
(** * ホーアの三つ組 *)

(* begin hide *)
(** Next, we need a way of making formal claims about the
    behavior of commands. *)
(* end hide *)
(** 次に、コマンドの振舞いについての形式的表明を作る方法が必要です。*)

(* begin hide *)
(** In general, the behavior of a command is to transform one state to
    another, so it is natural to express claims about commands in
    terms of assertions that are true before and after the command
    executes:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The assertion [P] is
    called the _precondition_ of [c], while [Q] is the
    _postcondition_.  *)
(* end hide *)
(** 一般に、コマンドの振舞いは、状態を別の状態に変換するものです。
    そのため、コマンドについて言及するには、コマンドの実行前と後の状態で真になる表明を用いるのが自然でしょう。
 
      - 「もし [c] が表明 [P] を満たす状態から開始され、また、[c]がいつかは停止するならば、最終状態では、表明[Q]が成立する。」
 
    このような言明は ホーアの三つ組(_Hoare Triple_)と呼ばれます。
    表明[P]は[c]の事前条件(_precondition_)と呼ばれます。
    [Q]は[c]の事後条件(_postcondition_)と呼ばれます。 *)

(* begin hide *)
(** Formally: *)
(* end hide *)
(** 形式的には以下の通りです。 *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

(* begin hide *)
(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:

       {{P}} c {{Q}}.

    (The traditional notation is [{P} c {Q}], but single braces
    are already used for other things in Coq.)  *)
(* end hide *)
(** ホーアの三つ組を今後多用するので、簡潔な記法を用意すると便利です:
[[
       {{P}} c {{Q}} 
]]
    （伝統的には、ホーアの三つ組は [{P} c {Q}]と書かれます。
    しかし Coq では一重の波カッコは別の意味で既に使われています。） *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (triples)  

    Paraphrase the following Hoare triples in English.

   1) {{True}} c {{X = 5}}

   2) {{X = m}} c {{X = m + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = m}}
      c
      {{Y = real_fact m}}   

   6) {{X = m}}
      c
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
*)
(* end hide *)
(** **** 練習問題: ★, standard, optional (triples)
 
    以下のホーアの三つ組を日本語に直しなさい。
[[
   1) {{True}} c {{X = 5}} 
 
   2) {{X = m}} c {{X = m + 5}} 
 
   3) {{X <= Y}} c {{Y <= X}} 
 
   4) {{True}} c {{False}} 
 
   5) {{X = m}} 
      c 
      {{Y = real_fact m}} 
 
   6) {{X = m}} 
      c 
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}} 
]]
 *)
(* FILL IN HERE 

    [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (valid_triples)  

    Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5;; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE true DO SKIP END {{False}}

   8) {{X = 0}}
        WHILE X = 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
        WHILE ~(X = 0) DO X ::= X + 1 END
      {{X = 100}}
*)
(* end hide *)
(** **** 練習問題: ★, standard, optional (valid_triples)
 
    以下のホーアの三つ組のうち、正しい(_valid_)ものを選択しなさい。
    -- 正しいとは、[P],[c],[Q]の関係が真であるということです。
[[
   1) {{True}} X ::= 5 {{X = 5}} 
 
   2) {{X = 2}} X ::= X + 1 {{X = 3}} 
 
   3) {{True}} X ::= 5;; Y ::= 0 {{X = 5}} 
 
   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}} 
 
   5) {{True}} SKIP {{False}} 
 
   6) {{False}} SKIP {{True}} 
 
   7) {{True}} WHILE true DO SKIP END {{False}} 
 
   8) {{X = 0}} 
        WHILE X = 0 DO X ::= X + 1 END 
      {{X = 1}} 
 
   9) {{X = 1}} 
        WHILE ~(X = 0) DO X ::= X + 1 END 
      {{X = 100}} 
]]
 *)
(* FILL IN HERE 

    [] *)

(* begin hide *)
(** To get us warmed up for what's coming, here are two simple facts
    about Hoare triples.  (Make sure you understand what they mean.) *)
(* end hide *)
(** ウォーミングアップとして、ホーアの三つ組についての2つの事実を見てみます。
    （何を意味しているのかしっかり理解してください。） *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ################################################################# *)
(* begin hide *)
(** * Proof Rules *)
(* end hide *)
(** * 証明規則 *)

(* begin hide *)
(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [hoare_triple]. *)
(* end hide *)
(** ホーア論理のゴールは、特定のホーアの三つ組の正しさを証明する"合成的"手法を提供することです。
    つまり、プログラムの正しさの証明の構造を、プログラムの構造を反映させたものにしたいということです。
    このために、以降の節では、Impのコマンドの構文要素それぞれに対して、推論するための規則を1つずつ導入します。
    つまり、代入に1つ、コマンド合成に1つ、条件分岐に1つ、等です。
    それに加えて、複数のものを結合するために有用な2つの"構造的"規則を導入します。
    これらの規則を用いて、[hoare_triple]の定義を展開することなしにプログラムの正しさを証明していきます。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Assignment *)
(* end hide *)
(** ** 代入 *)

(* begin hide *)
(** The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this valid Hoare triple:

       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}

    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1]. 
    That is, the property of being equal to [1] gets transferred
    from [Y] to [X]. *)
(* end hide *)
(** 代入の規則は、ホーア論理の証明規則の中で最も基本的なものです。
    この規則は次のように働きます。
 
    次の正しいホーアの三つ組を考えます。
[[
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }} 
]]
    日本語で言うと、[Y]の値が[1]である状態から始めて、[X]に[Y]を代入すれば、[X]が[1]である状態になる、ということです。
    つまり、[1]である、という性質が[Y]から[X]に移された、ということです。 *)

(* begin hide *)
(** Similarly, in

       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}

    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment. *)
(* end hide *)
(** 同様に、
[[
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }} 
]]
    においては、同じ性質（1であること）が代入の右辺の[Y + Z]から[X]に移動されています。 *)

(* begin hide *)
(** More generally, if [a] is _any_ arithmetic expression, then

       {{ a = 1 }}  X ::= a  {{ X = 1 }}

    is a valid Hoare triple. *)
(* end hide *)
(** より一般に、[a]が「任意の」算術式のとき、
[[
       {{ a = 1 }}  X ::= a  {{ X = 1 }} 
]]
    は正しいホーアの三つ組になります。 *)

(* begin hide *)
(** Even more generally, to conclude that an arbitrary assertion [Q]
    holds after [X ::= a], we need to assume that [Q] holds before [X
    ::= a], but _with all occurrences of_ [X] replaced by [a] in
    [Q]. This leads to the Hoare rule for assignment

      {{ Q [X |-> a] }} X ::= a {{ Q }}

    where "[Q [X |-> a]]" is pronounced "[Q] where [a] is substituted
    for [X]". *)
(* end hide *)
(** さらに一般化して、任意の性質[Q]が[X ::= a]の後に成り立つには、[X ::= a]の前で、[Q]内の「出現している全ての」[X]を[a]に置き換えたものが成り立っている必要があります。
    ここから次の、代入に関するホーアの三つ組が導かれます。
[[
      {{ Q [X |-> a] }} X ::= a {{ Q }} 
]]
    ただし、"[Q [X |-> a]]"は「[X]を[a]に置換した[Q]」と読みます。 *)

(* begin hide *)
(** For example, these are valid applications of the assignment
    rule:

      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}
      X ::= X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3 }}
      X ::= 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5) }}
      X ::= 3
      {{ 0 <= X /\ X <= 5 }}
*)
(* end hide *)
(** 例えば、以下は、代入規則の正しい適用です:
[[
      {{ (X <= 5) [X |-> X + 1] 
         i.e., X + 1 <= 5 }} 
      X ::= X + 1 
      {{ X <= 5 }} 
 
      {{ (X = 3) [X |-> 3] 
         i.e., 3 = 3 }} 
      X ::= 3 
      {{ X = 3 }} 
 
      {{ (0 <= X /\ X <= 5) [X |-> 3] 
         i.e., (0 <= 3 /\ 3 <= 5) }} 
      X ::= 3 
      {{ 0 <= X /\ X <= 5 }} 
]]
 *)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assn_sub].  That
    is, given a proposition [P], a variable [X], and an arithmetic
    expression [a], we want to derive another proposition [P'] that is
    just the same as [P] except that [P'] should mention [a] wherever
    [P] mentions [X]. *)

(** Since [P] is an arbitrary Coq assertion, we can't directly "edit"
    its text.  However, we can achieve the same effect by evaluating
    [P] in an updated state: *)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

(** That is, [P [X |-> a]] stands for an assertion -- let's call it [P'] --
    that is just like [P] except that, wherever [P] looks up the
    variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)

(** To see how this works, let's calculate what happens with a couple
    of examples.  First, suppose [P'] is [(X <= 5) [X |-> 3]] -- that
    is, more formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st 3 ; st),

    which simplifies to

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> 3 ; st)

    and further simplifies to

    fun st =>
      ((X !-> 3 ; st) X) <= 5

    and finally to

    fun st =>
      3 <= 5.

    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected). *)

(** For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X + 1]].  Formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1) ; st),

    which simplifies to

    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5

    and further simplifies to

    fun st =>
      (aeval st (X + 1)) <= 5.

    That is, [P'] is the assertion that [X + 1] is at most [5].
*)

(* begin hide *)
(** Now, using the concept of substitution, we can give the precise
    proof rule for assignment:

      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)
(* end hide *)
(** 置換を用いることで、正確な代入の証明規則を与えます:
[[
      ------------------------------ (hoare_asgn) 
      {{Q [X |-> a]}} X ::= a {{Q}} 
]]
 *)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(* begin hide *)
(** Here's a first formal proof using this rule. *)
(* end hide *)
(** この規則を使った最初の形式的証明が次のものです。*)

Example assn_sub_example :
  {{(fun st => st X < 5) [X |-> X + 1]}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_asgn.  Qed.

(** Of course, what would be even more helpful is to prove this
    simpler triple:

      {{X < 4}} X ::= X + 1 {{X < 5}}

   We will see how to do so in the next section. *)		 

(* begin hide *)
(** **** Exercise: 2 stars, standard (hoare_asgn_examples)  

    Translate these informal Hoare triples...

    1) {{ (X <= 10) [X |-> 2 * X] }}
       X ::= 2 * X
       {{ X <= 10 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}

   ...into formal statements (use the names [assn_sub_ex1]
   and [assn_sub_ex2]) and use [hoare_asgn] to prove them. *)
(* end hide *)
(** **** 練習問題: ★★, standard (hoare_asgn_examples)
 
    次の非形式的なホーアの三つ組...
[[
    1) {{ (X <= 10) [X |-> 2 * X] }} 
       X ::= 2 * X 
       {{ X <= 10 }} 
 
    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }} 
       X ::= 3 
       {{ 0 <= X /\ X <= 5 }} 
]]
   ...を、形式的記述に直し（それぞれの名前を[assn_sub_ex1]、[assn_sub_ex2]とする）、[hoare_asgn]を使って証明しなさい。*)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_asgn_examples : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, recommended (hoare_asgn_wrong)  

    The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:

      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}

    Give a counterexample showing that this rule is incorrect and
    argue informally that it is really a counterexample.  (Hint:
    The rule universally quantifies over the arithmetic expression
    [a], and your counterexample needs to exhibit an [a] for which
    the rule doesn't work.) *)
(* end hide *)
(** **** 練習問題: ★★, standard, recommended (hoare_asgn_wrong)
 
    代入規則は、最初に見たとき、ほとんどの人が後向きの規則であるように感じます。
    もし今でもパズルのように見えるならば、「前向き」バージョンの規則を考えてみるのも良いでしょう。
    次のものは自然に見えます:
[[
      ------------------------------ (hoare_asgn_wrong) 
      {{ True }} X ::= a {{ X = a }} 
]]
    この規則が正しくないことを示す反例を挙げ、それが実際に反例となっていることを非形式的に示しなさい。
    （ヒント：この規則は算術式[a]を量化しているので、反例はこの規則がうまく動かないように[a]を提示する必要があります。） *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_asgn_wrong : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced (hoare_asgn_fwd)  

    However, by using a _parameter_ [m] (a Coq number) to remember the
    original value of [X] we can define a Hoare rule for assignment
    that does, intuitively, "work forwards" rather than backwards.

       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X ::= a
       {{fun st => P st' /\ st X = aeval st' a }}
       (where st' = (X !-> m ; st))

    Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct.  (Also note that this rule is more complicated than
    [hoare_asgn].)
*)

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_asgn_fwd_exists)  

    Another way to define a forward rule for assignment is to
    existentially quantify over the previous value of the assigned
    variable.  Prove that it is correct.

      ------------------------------------ (hoare_asgn_fwd_exists)
      {{fun st => P st}}
        X ::= a
      {{fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a }}
*)

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a }}.
Proof.
  intros a P.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Consequence *)
(* end hide *)
(** ** 帰結 *)

(* begin hide *)
(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while

      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}},

    follows directly from the assignment rule,

      {{True}} X ::= 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    _equivalent_, so if one triple is valid, then the other must
    certainly be as well.  We can capture this observation with the
    following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)
(* end hide *)
(** ホーア規則から得られる事前条件や事後条件が欲しいものと完全には一致しない、ということが身近な場面においてしばしば起こります。
    それらは論理的には証明しようとするゴールと同値にも関わらず、構文上違う形をしているために単一化できない、という場合がありえます。
    あるいは、想定するゴールに比べて、（事前条件について）論理的に弱かったり、（事後条件について）論理的に強かったりすることがあります。
 
    例えば、
[[
      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}} 
]]
    が代入規則に直接従うのに対して、より自然な三つ組
[[
      {{True}} X ::= 3 {{X = 3}} 
]]
    はそうではないのです。
    この三つ組も正しいのですが、[hoare_asgn] のインスタンスではないのです。
    なぜなら、[True] と [(X = 3) [X |-> 3]] は、構文的に等しい表明ではないからです。
    しかし、これらが論理的に「等価」である以上、一方の三つ組が正しいのであれば、もう一方も同様に正しくあるべきです。
    このことを、以下の規則によって表現します。
[[
                {{P'}} c {{Q}} 
                  P <<->> P' 
         -----------------------------   (hoare_consequence_pre_equiv) 
                {{P}} c {{Q}} 
]]
 *)

(* begin hide *)
(** Taking this line of thought a bit further, we can see that
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
(* end hide *)
(** これを進めていくと、ある正しい三つ組から別の記述による正しい三つ組を生成する、事前条件の弱化と事後条件の強化が出てきます。
    これは以下の「帰結に関する規則」に集約されます。
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

(* begin hide *)
(** Here are the formal versions: *)
(* end hide *)
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

(* begin hide *)
(** For example, we can use the first consequence rule like this:

      {{ True }} ->>
      {{ 1 = 1 }}
    X ::= 1
      {{ X = 1 }}

    Or, formally... *)
(* end hide *)
(** 例えば、一つ目の帰結規則を次のように使うことができます:
[[
      {{ True }} ->> 
      {{ 1 = 1 }} 
    X ::= 1 
      {{ X = 1 }} 
]]
    あるいは、形式化すると... *)

Example hoare_asgn_example1 :
  {{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.

(** We can also use it to prove the example mentioned earlier.

      {{ X < 4 }} ->>
      {{ (X < 5)[X |-> X + 1] }}
    X ::= X + 1
      {{ X < 5 }}

   Or, formally ... *)

Example assn_sub_example2 :
  {{(fun st => st X < 4)}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre
    with (P' := (fun st => st X < 5) [X |-> X + 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. omega.
Qed.

(** Finally, for convenience in proofs, here is a combined rule of
    consequence that allows us to vary both the precondition and the
    postcondition in one go.

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

(* ================================================================= *)
(* begin hide *)
(** ** Digression: The [eapply] Tactic *)
(* end hide *)
(** ** 余談: [eapply] タクティック *)

(* begin hide *)
(** This is a good moment to take another look at the [eapply] tactic,
    which we introduced briefly in the [Auto] chapter of
    _Logical Foundations_.

    We had to write "[with (P' := ...)]" explicitly in the proof of
    [hoare_asgn_example1] and [hoare_consequence] above, to make sure
    that all of the metavariables in the premises to the
    [hoare_consequence_pre] rule would be set to specific
    values.  (Since [P'] doesn't appear in the conclusion of
    [hoare_consequence_pre], the process of unifying the conclusion
    with the current goal doesn't constrain [P'] to a specific
    assertion.)

    This is annoying, both because the assertion is a bit long and
    also because, in [hoare_asgn_example1], the very next thing we are
    going to do -- applying the [hoare_asgn] rule -- will tell us
    exactly what it should be!  We can use [eapply] instead of [apply]
    to tell Coq, essentially, "Be patient: The missing part is going
    to be filled in later in the proof." *)
(* end hide *)
(** 良い機会ですので、「論理の基礎」の [Auto] 章で概要を説明した [eapply] を別の観点から説明しましょう。
 
    上述の [hoare_asgn_example1] や [hoare_consequence] の証明では、 [hoare_consequence_pre] 規則のメタ変数を明示するために、[with (P' := ...)] のように書かなければいけませんでした。
    （というのも、[hoare_consequence_pre] の [P'] は帰結に出ないので、帰結と現在のゴールを単一化しても [P'] を特定することはできません。）
 
    これは少し鬱陶しいです。
    というのも、それなりに長くなりますし、また [hoare_asgn_example1] では、直後に行う [hoare_asgn] 規則の適用がそこに入る表明を明らかにするからです。
    このような場合に、[apply] の代わりに [eapply] を使えます。
    これは基本的に「少し我慢してください、抜けている部分は後で埋めます」と Coq に伝えることに相当します。*)

Example hoare_asgn_example1' :
  {{fun st => True}}
  X ::= 1
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

(** In general, the [eapply H] tactic works just like [apply H] except
    that, instead of failing if unifying the goal with the conclusion
    of [H] does not determine how to instantiate all of the variables
    appearing in the premises of [H], [eapply H] will replace these
    variables with _existential variables_ (written [?nnn]), which
    function as placeholders for expressions that will be
    determined (by further unification) later in the proof. *)

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

(** Coq gives a warning after [apply HP].  ("All the remaining goals
    are on the shelf," means that we've finished all our top-level
    proof obligations but along the way we've put some aside to be
    done later, and we have not finished those.)  Trying to close the
    proof with [Qed] gives an error. *)
Abort.

(** An additional constraint is that existential variables cannot be
    instantiated with terms containing ordinary variables that did not
    exist at the time the existential variable was created.  (The
    reason for this technical restriction is that allowing such
    instantiation would lead to inconsistency of Coq's logic.) *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].

(** Doing [apply HP'] above fails with the following error:

      Error: Impossible to unify "?175" with "y".

    In this case there is an easy fix: doing [destruct HP] _before_
    doing [eapply HQ]. *)
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

(** The [apply HP'] in the last step unifies the existential variable
    in the goal with the variable [y].

    Note that the [assumption] tactic doesn't work in this case, since
    it cannot handle existential variables.  However, Coq also
    provides an [eassumption] tactic that solves the goal if one of
    the premises matches the goal up to instantiations of existential
    variables. We can use it instead of [apply HP'] if we like. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(** **** Exercise: 2 stars, standard (hoare_asgn_examples_2)  

    Translate these informal Hoare triples...

       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}

   ...into formal statements (name them [assn_sub_ex1'] and
   [assn_sub_ex2']) and use [hoare_asgn] and [hoare_consequence_pre]
   to prove them. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_asgn_examples_2 : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Skip *)

(* begin hide *)
(** Since [SKIP] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)
(* end hide *)
(** [SKIP]は状態を変えないことから、任意の表明 [P] を保存します:
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

(* ================================================================= *)
(* begin hide *)
(** ** Sequencing *)
(* end hide *)
(** ** コマンド合成 *)

(* begin hide *)
(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
*)
(* end hide *)
(** より興味深いことに、コマンド[c1]が[P]が成立する任意の状態を[Q]が成立する状態にし、[c2]が[Q]が成立する任意の状態を[R]が成立する状態にするとき、
    [c1]に続いて[c2]を行うことは、[P]が成立する任意の状態を[R]が成立する状態にします:
[[
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }} 
       ----------------------  (hoare_seq) 
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

(* begin hide *)
(** Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)
(* end hide *)
(** 形式的規則[hoare_seq]においては、前提部分が「逆順」である（[c1]の前に[c2]が来る）ことに注意してください。
    この順は、規則を使用する多くの場面で情報の自然な流れにマッチするのです。
    ホーア論理における証明の構築はプログラムの終わりから（最後の事後条件を用いて）、プログラムの始めにたどり着くまでコマンドをさかのぼる方が自然なのです。 *)

(* begin hide *)
(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

      {{ a = n }}
    X ::= a;;
      {{ X = n }}    <--- decoration for Q
    SKIP
      {{ X = n }}
*)
(* end hide *)
(** 非形式的には、この規則を利用した証明を表す良い方法は、[c1]と[c2]の間に中間表明[Q]を記述する"修飾付きプログラム"の様にすることです:
[[
      {{ a = n }} 
    X ::= a;; 
      {{ X = n }}    <--- 修飾 Q
    SKIP 
      {{ X = n }} 
]]
 *)

(** Here's an example of a program involving both assignment and
    sequencing. *)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

(** We typically use [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic, as in this
    example. *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, recommended (hoare_asgn_example4)  

    Translate this "decorated program" into a formal proof:

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}

   (Note the use of "[->>]" decorations, each marking a use of
   [hoare_consequence_pre].) *)
(* end hide *)
(** **** 練習問題: ★★, standard, recommended (hoare_asgn_example4)
 
    次の修飾付きプログラムを形式的証明に直しなさい:
[[
                   {{ True }} ->> 
                   {{ 1 = 1 }} 
    X ::= 1;; 
                   {{ X = 1 }} ->> 
                   {{ X = 1 /\ 2 = 2 }} 
    Y ::= 2 
                   {{ X = 1 /\ Y = 2 }} 
]]
   （"[->>]"という記法は[hoare_consequence_pre]を使ったことを示しています。） *)

Example hoare_asgn_example4 :
  {{fun st => True}}
  X ::= 1;; Y ::= 2
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (swap_exercise)  

    Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:

      {{X <= Y}} c {{Y <= X}}

    Your proof should not need to use [unfold hoare_triple].  (Hint:
    Remember that the assignment rule works best when it's applied
    "back to front," from the postcondition to the precondition.  So
    your proof will want to start at the end and work back to the
    beginning of your program.)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard (swap_exercise)
 
    [X]と[Y]の値を交換するImpプログラム[c]を書き、それが次の仕様を満たすことを示しなさい:
[[
      {{X <= Y}} c {{Y <= X}} 
]]
    証明に[unfold hoare_triple]を使わないようにすること。
    （ヒント：代入の規則は「後ろから前」、つまり事後条件から事前条件に向かって用いることを覚えておいてください。
    結果的にプログラムの後ろから前に向かって証明することになるでしょう。） *)

Definition swap_program : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (hoarestate1)  

    Explain why the following proposition can't be proven:

      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
           X ::= 3;; Y ::= a
         {{fun st => st Y = n}}.
*)
(* end hide *)
(** **** 練習問題: ★★★, standard (hoarestate1)
 
    次の命題が証明できない理由を説明しなさい:
[[
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
           X ::= 3;; Y ::= a 
         {{fun st => st Y = n}}.
]]
 *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_hoarestate1 : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Conditionals *)
(* end hide *)
(** ** 条件分岐 *)

(* begin hide *)
(** What sort of rule do we want for reasoning about conditional
    commands? 

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional. 
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} TEST b THEN c1 ELSE c2 {{Q}}
*)
(* end hide *)
(** 条件分岐コマンドについて推論するために、どのような規則が必要でしょうか？
 
    もちろん、分岐のどちらの枝を実行した後でも表明[Q]が成立するならば、条件分岐全体でも[Q]が成立するでしょう。
    これから次のように書くべきかもしれません:
[[
              {{P}} c1 {{Q}} 
              {{P}} c2 {{Q}} 
      --------------------------------- 
      {{P}} TEST b THEN c1 ELSE c2 {{Q}} 
]]
 *)
(* 訳注：TEST文の後ろにFIが足りないように見えるかもしれないが、原文から抜けている。 *)

(* begin hide *)
(** However, this is rather weak. For example, using this rule,
   we cannot show

     {{ True }}
     TEST X = 0
       THEN Y ::= 2
       ELSE Y ::= X + 1
     FI
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)
(* end hide *)
(** しかし、これはかなり弱いのです。
   例えば、この規則を使っても次のことを示すことができません:
[[
     {{ True }} 
     TEST X = 0 
       THEN Y ::= 2 
       ELSE Y ::= X + 1 
     FI 
     {{ X <= Y }} 
]]
   なぜなら、この規則では、"then"部と"else"部のどちらの代入が起こる状態なのかについて、何も言っていないからです。 *)

(* begin hide *)
(** Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]). 

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}
*)
(* end hide *)
(** 実際にはより詳しいことを言うことができます。
   "then"部では、ブール式[b]の評価結果が[true]になることがわかっています。
   また"else"部では、それが[false]になることがわかっています。
   この情報を補題の前提部分で利用できるようにすることで、[c1]と[c2]の振舞いについて（つまり事後条件[Q]が成立する理由について）推論するときに、より多くの情報を使うことができるようになります。
[[
              {{P /\   b}} c1 {{Q}} 
              {{P /\ ~ b}} c2 {{Q}} 
      ------------------------------------  (hoare_if) 
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}} 
]]
 *)

(* begin hide *)
(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)
(* end hide *)
(** この規則を形式的に解釈するために、もう少しやることがあります。
 
    厳密には、上述の表明において、表明とブール式の連言[P /\ b]は、型チェックを通りません。
    これを修正するために、ブール式[b]を形式的に「持ち上げ」て、表明にしなければなりません。
    このために[bassn b]と書きます。
    これは"ブール式[b]の評価結果が（任意の状態で）[true]になる"という表明です。*)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(* begin hide *)
(** A couple of useful facts about [bassn]: *)
(* end hide *)
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

(* begin hide *)
(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)
(* end hide *)
(** いよいよ条件分岐についてのホーア証明規則を形式化し、正しいことを証明できます。*)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Example *)
(* end hide *)
(** *** 例 *)

(* begin hide *)
(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)
(* end hide *)
(** 以下が、最初に挙げたプログラムが与えられた条件を満たすことの証明です。*)

Example if_example :
    {{fun st => True}}
  TEST X = 0
    THEN Y ::= 2
    ELSE Y ::= X + 1
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply eqb_eq in H.
    rewrite H. omega.
  - (* Else *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
Qed.

(** **** Exercise: 2 stars, standard (if_minus_plus)  

    Prove the following hoare triple using [hoare_if].  Do not
    use [unfold hoare_triple].  *)

Theorem if_minus_plus :
  {{fun st => True}}
  TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Exercise: One-sided conditionals *)

(** **** Exercise: 4 stars, standard (if1_hoare)  

    In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [IF1 b THEN c FI]. Here [b] is a boolean
    expression, and [c] is a command. If [b] evaluates to [true], then
    command [c] is evaluated. If [b] evaluates to [false], then [IF1 b
    THEN c FI] does nothing.

    We recommend that you complete this exercise before attempting the
    ones that follow, as it should help solidify your understanding of
    the material. *)

(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "X '::=' a" :=
  (CAss X a) (at level 60) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity) : imp_scope.

(** Next we need to extend the evaluation relation to accommodate
    [IF1] branches.  This is for you to do... What rule(s) need to be
    added to [ceval] to evaluate one-sided conditionals? *)

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Open Scope imp_scope.
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
(* FILL IN HERE *)

  where "st '=[' c ']=>' st'" := (ceval c st st').
Close Scope imp_scope.

(** Now we repeat (verbatim) the definition and notation of Hoare triples. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
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
  IF1 ~(Y = 0) THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Hint: Your proof of this triple may need to use the other proof
    rules also. Because we're working in a separate module, you'll
    need to copy here the rules you find necessary. *)

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  (IF1 ~(Y = 0) THEN
    X ::= X + Y
  FI)%imp
  {{ fun st => st X = st Z }}.
Proof. (* FILL IN HERE *) Admitted.

End If1.

(* Do not modify the following line: *)
Definition manual_grade_for_if1_hoare : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Loops *)
(* end hide *)
(** ** ループ *)

(* begin hide *)
(** Finally, we need a rule for reasoning about while loops. *)
(* end hide *)
(** 最後に、ループについての推論規則が必要です。 *)

(* begin hide *)
(** Suppose we have a loop

      WHILE b DO c END

    and we want to find a precondition [P] and a postcondition
    [Q] such that

      {{P}} WHILE b DO c END {{Q}}

    is a valid triple. *)
(* end hide *)
(** 次のループを考えます:
[[
      WHILE b DO c END 
]]
    そして、次の三つ組が正しくなる事前条件[P]と事後条件[Q]を探します:
[[
      {{P}} WHILE b DO c END {{Q}} 
]]
 *)

(* begin hide *)
(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write: *)
(* end hide *)
(** まず、[b]が最初から偽であるときを考えましょう。
    このときループの本体はまったく実行されません。
    この場合は、ループは[SKIP]と同様の振舞いをしますので、次のように書いても良いかもしれません。 *)

(* begin hide *)
(**

      {{P}} WHILE b DO c END {{P}}.
*)
(* end hide *)
(**
[[
      {{P}} WHILE b DO c END {{P}} 
]]
 *)

(* begin hide *)
(** But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little: 

      {{P}} WHILE b DO c END {{P /\ ~ b}}
*)
(* end hide *)
(** しかし、条件分岐について議論したのと同様に、最後でわかっていることはもう少し多いのです。
    最終状態では[P]であるだけではなく[b]が偽になっているのです。
    そこで、事後条件にちょっと付け足すことができます:
[[
      {{P}} WHILE b DO c END {{P /\ ~ b}} 
]]
 *)

(* begin hide *)
(** What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule: 

                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~ b}}

    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state. *)
(* end hide *)
(** それでは、ループの本体が実行されるときはどうなるでしょう？
    ループを最後に抜けるときには[P]が成立することを確実にするために、コマンド[c]の終了時点で常に[P]が成立することを確認する必要があるのは確かでしょう。
    さらに、[P]が[c]の最初の実行の前に成立しており、[c]を実行するたびに、終了時点で[P]の成立が再度確立されることから、[P]が[c]の実行前に常に成立していると仮定することができます。
    このことから次の規則が得られます:
[[
                   {{P}} c {{P}} 
        ----------------------------------- 
        {{P}} WHILE b DO c END {{P /\ ~ b}} 
]]
    これで求める規則にかなり近付いたのですが、もうちょっとだけ改良できます。
    ループ本体の開始時点で、[P]が成立しているだけでなく、ガード[b]が現在の状態で真であるということも言えます。 *)

(* begin hide *)
(** This gives us a little more information to use in reasoning
    about [c] (showing that it establishes the invariant by the time
    it finishes).  

    And this leads us to the final version of the rule: 

               {{P /\ b}} c {{P}}
        ----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~ b}}

    The proposition [P] is called an _invariant_ of the loop.
*)
(* end hide *)
(** このことは、[c]についての（[P]が[c]の終了時にも成立することの）推論の際にいくらかの情報を与えてくれます。
 
    結局、規則の最終バージョンはこうなります:
[[
               {{P /\ b}} c {{P}} 
        ----------------------------------  (hoare_while) 
        {{P}} WHILE b DO c END {{P /\ ~ b}} 
]]
    命題[P]は不変条件(_invariant_)と呼ばれます。 *)

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on [He], because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just [c]. *)
  (* 先に見たように、[He]についての帰納法を使う必要があります。
     なぜなら、ループを抜けない場合には、仮定は[c]だけでなくループ全体について言及しているからです。*)
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *) 
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(** One subtlety in the terminology is that calling some assertion [P]
    a "loop invariant" doesn't just mean that it is preserved by the
    body of the loop in question (i.e., [{{P}} c {{P}}], where [c] is
    the loop body), but rather that [P] _together with the fact that
    the loop's guard is true_ is a sufficient precondition for [c] to
    ensure [P] as a postcondition.

    This is a slightly (but importantly) weaker requirement.  For
    example, if [P] is the assertion [X = 0], then [P] _is_ an
    invariant of the loop

      WHILE X = 2 DO X := 1 END

    although it is clearly _not_ preserved by the body of the
    loop. *)

Example while_example :
    {{fun st => st X <= 3}}
  WHILE X <= 2
  DO X ::= X + 1 END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H1 H2]. apply leb_complete in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct ((st X) <=? 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.
(* begin hide *)
(** We can use the WHILE rule to prove the following Hoare triple... *)
(* end hide *)
(** WHILE規則を使うと、次のホーアの三つ組も証明できます... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor.  Qed.

(* begin hide *)
(** Of course, this result is not surprising if we remember that
    the definition of [hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    postcondition. *)
(* end hide *)
(** もちろん、この結果は驚くことではないのです。
    ふり返って[hoare_triple]の定義を見てみると、コマンドが停止した場合「のみ」に意味がある表明をしているのです。
    もしコマンドが終了しないなら、なんでも望むものが事後条件として示せます。 *)

(* begin hide *)
(** Hoare rules that only talk about what happens when commands
    terminate (without proving that they do) are often said to
    describe a logic of "partial" correctness.  It is also possible to
    give Hoare rules for "total" correctness, which build in the fact
    that the commands terminate. However, in this course we will only
    talk about partial correctness. *)
(* end hide *)
(** コマンドが停止したときに関してのみ（しかも停止することを示すことなく）何が起こるかを議論するホーア規則は、「部分」正当性("partial" correctness)を記述していると言われます。
    「完全」正当性("total" correctness)についてのホーア規則を与えることも可能です。
    それは、コマンドが停止するという事実を組み込んだものです。
    ただし、このコースでは部分正当性についてのみ説明します。 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Exercise: [REPEAT] *)
(* end hide *)
(** *** 練習問題: [REPEAT] *)

(* begin hide *)
(** **** Exercise: 4 stars, advanced (hoare_repeat)  

    In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [UNTIL] b [END]. You will write the
    evaluation rule for [REPEAT] and add a new Hoare rule to the
    language for programs involving it.  (You may recall that the
    evaluation rule is given in an example in the [Auto] chapter.
    Try to figure it out yourself here rather than peeking.) *)
(* end hide *)
(** **** 練習問題: ★★★★, advanced (hoare_repeat)
 
    この練習問題では、言語に新たなコマンドを追加します。
    [REPEAT] c [UNTIL] b [END]という形のコマンドです。
    [REPEAT]の評価規則を記述し、このコマンドを含むプログラムについての評価規則と新たなホーア論理の規則を追加しなさい。
    （評価規則については[Auto]章でも例として使っていますが、それを見ないでやってみましょう。） *)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(* begin hide *)
(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)
(* end hide *)
(** [REPEAT]は[WHILE]と同じように振舞います。
    ただし、ループのガードが本体の実行の「後で」評価され、それが「偽」である間はループがくりかえされるという点が違います。
    このことにより、本体は常に少なくとも1回は実行されることになります。*)

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

(* begin hide *)
(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true. *)
(* end hide *)
(** 以下の[ceval]に[REPEAT]の新たな規則を追加しなさい。
    [WHILE]の規則を参考にして構いません。
    ただし、[REPEAT]の本体は1度は実行されること、ループの終了はガードが真になったときであることを忘れないで下さい。 *)

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
(* FILL IN HERE *)

where "st '=[' c ']=>' st'" := (ceval st c st').

(* begin hide *)
(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)
(* end hide *)
(** 上記からいくつかの定義のコピーし、新しい[ceval]を使うようにしました。*)

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** To make sure you've got the evaluation rules for [REPEAT] right,
    prove that [ex1_repeat] evaluates correctly. *)

Definition ex1_repeat :=
  REPEAT
    X ::= 1;;
    Y ::= Y + 1
  UNTIL X = 1 END.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
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

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_repeat : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Summary *)

(** So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs. The rules of Hoare Logic are:

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}

    In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (hoare_havoc)  

    In this exercise, we will derive proof rules for a [HAVOC]
    command, which is similar to the nondeterministic [any] expression
    from the the [Imp] chapter.

    First, we enclose this work in a separate module, and recall the
    syntax and big-step semantics of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
  | E_Havoc : forall st X n,
      st =[ HAVOC X ]=> (X !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

(** The definition of Hoare triples is exactly as before. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre] and prove that the resulting rule is correct. *)

Definition havoc_pre (X : string) (Q : Assertion) : Assertion
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

End Himp.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (assert_vs_assume)  *)

Module HoareAssertAssume.

(** In this exercise, we will extend IMP with two commands,
     [ASSERT] and [ASSUME]. Both commands are ways
     to indicate that a certain statement should hold any time this part
     of the program is reached. However they differ as follows:

    - If an [ASSERT] statement fails, it causes the program to go into
      an error state and exit.

    - If an [ASSUME] statement fails, the program fails to evaluate
      at all. In other words, the program gets stuck and has no
      final state.

    The new set of commands is: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'ASSERT' b" :=
  (CAssert b) (at level 60).
Notation "'ASSUME' b" :=
  (CAssume b) (at level 60).

(** To define the behavior of [ASSERT] and [ASSUME], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ SKIP ]=> RNormal st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ;; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ;; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ WHILE b DO c END ]=> r ->
      st  =[ WHILE b DO c END ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ WHILE b DO c END ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ ASSERT b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ ASSERT b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ ASSUME b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** To test your understanding of this modification, give an example
    precondition and postcondition that are satisfied by the [ASSUME]
    statement but not by the [ASSERT] statement.  Then prove that any
    triple for [ASSERT] also works for [ASSUME]. *)

Theorem assert_assume_differ : exists P b Q,
       ({{P}} ASSUME b {{Q}})
  /\ ~ ({{P}} ASSERT b {{Q}}).
Proof.
(* FILL IN HERE *) Admitted.

Theorem assert_implies_assume : forall P b Q,
     ({{P}} ASSERT b {{Q}})
  -> ({{P}} ASSUME b {{Q}}).
Proof.
(* FILL IN HERE *) Admitted.

(** Your task is now to state Hoare rules for [ASSERT] and [ASSUME],
    and use them to prove a simple program correct.  Name your hoare
    rule theorems [hoare_assert] and [hoare_assume].
     
    For your benefit, we provide proofs for the old hoare rules
    adapted to the new semantics. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

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
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ']].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ]].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _]].
     inversion C.
Qed.

(** State and prove your hoare rules, [hoare_assert] and
    [hoare_assume], below. *)

(* FILL IN HERE *)

(** Here are the other proof rules (sanity check) *)
Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split. reflexivity. split.
    assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2. reflexivity.
    clear IHHe2 He2 r.
    unfold hoare_triple in Hhoare.
    apply Hhoare in He1.
    + destruct He1 as [st1 [Heq Hst1]].
        inversion Heq; subst.
        assumption.
    + split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _]]. inversion C.
     + split; assumption.
Qed.

Example assert_assume_example:
  {{fun st => True}}
  ASSUME (X = 1);;
  X ::= X + 1;;
  ASSERT (X = 2)
  {{fun st => True}}.
Proof.
(* FILL IN HERE *) Admitted.

End HoareAssertAssume.
(** [] *)

(* Thu Feb 7 20:09:23 EST 2019 *)
