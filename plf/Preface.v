(** * Preface: 前書き *)
(*
(** * Preface *)
*)

(* ################################################################# *)
(*
(** * Welcome *)
*)
(** * ようこそ *)

(*
(** This electronic book is a survey of basic concepts in the
    mathematical study of programs and programming languages.  Topics
    include advanced use of the Coq proof assistant, operational
    semantics, Hoare logic, and static type systems.  The exposition
    is intended for a broad range of readers, from advanced
    undergraduates to PhD students and researchers.  No specific
    background in logic or programming languages is assumed, though a
    degree of mathematical maturity will be helpful.

    As with all of the books in the _Software Foundations_ series,
    this one is one hundred percent formalized and machine-checked:
    the entire text is literally a script for Coq.  It is intended to
    be read alongside (or inside) an interactive session with Coq.
    All the details in the text are fully formalized in Coq, and most
    of the exercises are designed to be worked using Coq.

    The files are organized into a sequence of core chapters, covering
    about one half semester's worth of material and organized into a
    coherent linear narrative, plus a number of "offshoot" chapters
    covering additional topics.  All the core chapters are suitable
    for both upper-level undergraduate and graduate students.

    The book builds on the material from _Logical Foundations_
    (_Software Foundations_, volume 1).  It can be used together with
    that book for a one-semester course on the theory of programming
    languages.  Or, for classes where students who are already
    familiar with some or all of the material in _Logical
    Foundations_, there is plenty of additional material to fill most
    of a semester from this book alone. *)
*)
(** この本はプログラムとプログラミング言語に対する数学的基礎の基本的コンセプトをまとめたものです。
    主な内容は、Coqの高度な利用方法、操作的意味論、ホーア論理、静的型システムです。
    解説は、学部生から博士課程の学生や研究者に至るまで、広範囲の読者を想定しています。
    論理学やプログラミング言語についての知識は仮定しませんが、ある程度の数学的素養は理解に有用です。
 
    他の「ソフトウェアの基礎」シリーズと同様、ここで取り扱う内容もすべて形式化されて、さらに機械によって確かめられています。
    これは、それぞれのテキストがCoqのスクリプトファイルそのものとなっていることで実現されています。
    このシリーズでは、Coqのインタラクティブモードを横で動かしながら（またはエディタで一行ずつ進めながら）読み進めることを想定しています。
    内容の細部まですべてCoqで形式化され、また演習もCoqを使って行うように設計されています。
 
    内容としては、主要部とそれ以外の「派生」からなります。
    主要部は1学期分の講義として十分な量が、順序だって記述されています。
    また、派生部分は主要部に関連する項目をカバーしています。
    主要部は学部後半の学生や院生にちょうどいい内容でしょう。
 
    この本は、「論理の基礎(_Logical Foundations_)」（「ソフトウェアの基礎」第一巻）を基本としています。
    これと合わせて、プログラミング言語の理論に関する一学期分の講義ができると思います。
    また、「論理の基礎」の内容に既に馴染んでいる学生向けには、この本の派生部を利用して単体で講義を構成できるでしょう。 *)


(* ################################################################# *)
(*
(** * Overview *)
*)
(** * 概要 *)

(*
(** The book develops two main conceptual threads:

    (1) formal techniques for _reasoning about the properties of
        specific programs_ (e.g., the fact that a sorting function or
        a compiler obeys some formal specification); and

    (2) the use of _type systems_ for establishing well-behavedness
        guarantees for _all_ programs in a given programming
        language (e.g., the fact that well-typed Java programs cannot
        be subverted at runtime).

    Each of these is easily rich enough to fill a whole course in its
    own right, and tackling both together naturally means that much
    will be left unsaid.  Nevertheless, we hope readers will find that
    these themes illuminate and amplify each other and that bringing
    them together creates a good foundation for digging into any of
    them more deeply.  Some suggestions for further reading can be
    found in the [Postscript] chapter.  Bibliographic information
    for all cited works can be found in the file [Bib]. *)
*)
(** この本は二つの主題があります。
 
    (1) 「特定のプログラムの仕様の推論」に関する形式手法
        （例：ソート関数やコンパイラが形式仕様を満たす）
 
    (2) あるプログラミング言語で書かれた「全ての」プログラムの挙動を保証する「型システム(_type system_)」
        （例：Javaの型付けされたプログラムは実行時に型が原因で止まったりしない）
 
    これらはそれぞれ単体でも講義を構成できるほど豊富な内容を含んでいるので、両方を同時に進めるということは言及しない部分があるということでもあります。
    それでも、皆さんが、これらのテーマ同士が互いに関連して理解を深め、その全体像がそれぞれをより深く掘り進めるための基礎となることに気づいてくれれば幸いです。
    この本の後に読むとよい資料については、[Postscript]の章に記載しています。
    これらの本の参照情報は[Bib]ファイルにあります。 *)

(* ================================================================= *)
(*
(** ** Program Verification *)
*)
(** ** プログラム検証 *)

(*
(** In the first part of the book, we introduce two broad topics of
    critical importance in building reliable software (and hardware):
    techniques for proving specific properties of particular
    _programs_ and for proving general properties of whole programming
    _languages_.

    For both of these, the first thing we need is a way of
    representing programs as mathematical objects, so we can talk
    about them precisely, plus ways of describing their behavior in
    terms of mathematical functions or relations.  Our main tools for
    these tasks are _abstract syntax_ and _operational semantics_, a
    method of specifying programming languages by writing abstract
    interpreters.  At the beginning, we work with operational
    semantics in the so-called "big-step" style, which leads to simple
    and readable definitions when it is applicable.  Later on, we
    switch to a lower-level "small-step" style, which helps make some
    useful distinctions (e.g., between different sorts of
    nonterminating program behaviors) and which is applicable to a
    broader range of language features, including concurrency.

    The first programming language we consider in detail is _Imp_, a
    tiny toy language capturing the core features of conventional
    imperative programming: variables, assignment, conditionals, and
    loops.

    We study two different ways of reasoning about the properties of
    Imp programs.  First, we consider what it means to say that two
    Imp programs are _equivalent_ in the intuitive sense that they
    exhibit the same behavior when started in any initial memory
    state.  This notion of equivalence then becomes a criterion for
    judging the correctness of _metaprograms_ -- programs that
    manipulate other programs, such as compilers and optimizers.  We
    build a simple optimizer for Imp and prove that it is correct.

    Second, we develop a methodology for proving that a given Imp
    program satisfies some formal specifications of its behavior.  We
    introduce the notion of _Hoare triples_ -- Imp programs annotated
    with pre- and post-conditions describing what they expect to be
    true about the memory in which they are started and what they
    promise to make true about the memory in which they terminate --
    and the reasoning principles of _Hoare Logic_, a domain-specific
    logic specialized for convenient compositional reasoning about
    imperative programs, with concepts like "loop invariant" built in.

    This part of the course is intended to give readers a taste of the
    key ideas and mathematical tools used in a wide variety of
    real-world software and hardware verification tasks. *)
*)
(** この本の前半ではまず、高信頼ソフトウェア（またはハードウェア）を構築するのに非常に重要な二つの内容に関して述べます。
    一方は「プログラム」における特定の性質の証明、そしてもう一方は「プログラミング言語」における一般的性質の証明です。
 
    このどちらも、まず最初にすることはプログラムを数学的対象として正確に表現することです。
    これにより、プログラムについて正確な議論をできるようになります。
    加えて、数学における関数や関係(relation)によってその動作を記述することもできます。
    プログラミング言語を数学的対象として表現するために、「抽象構文(_abstract syntax_)」と「操作的意味論(_operational semantics_)」を用いて抽象解釈器を記述します。
    初めはまず、いわゆる「大ステップ("big-step")」形式の操作的意味論を使います。
    これは利用可能な範囲では単純で読みやすい定義になっています。
    その後、より細かな「小ステップ("small-step")」形式に移行します。
    これはプログラムの区別に有用で（例えば「異なる要因で終了しない」プログラムの区別）、また並行性など広範の言語機能に対応できます。
 
    最初に対象とするプログラミング言語は、 _Imp_ と呼ばれる非常に小さな、おもちゃのような言語ですが、命令型プログラミングの核となる機能を持っています。
    変数、代入、条件分岐、そして繰り返しです。
 
    この本では、Impプログラムに対して、二つの観点で性質を解釈していきます。
    一つ目は、Impプログラムの任意の初期状態に対する振る舞いが同じか、という直観的な意味で「等しい(_equivalent_)」か、というものです。
    この観点は、「メタプログラム(_metaprogram_)」に対する正当性の基準につながります。
    メタプログラムとは、他のプログラムを操作するプログラムのことで、例えばコンパイラや最適化器があります。
    この本では、Impへの簡単な最適化器を作り、それが正しいことを示します。
 
    二つ目は、与えられたImpプログラムの振る舞いがある形式仕様を満たすか、というものです。
    これを記述するために「ホーアの三つ組(_Hoare triple_)」を導入します。
    ホーアの三つ組は、Impプログラムと、事前条件、事後条件の三つで構成されていて、事前条件を満たす状態から始めてImpプログラムを実行すると、終了するなら終了時の状態は事後条件を満たす、ということを表します。
    また、ホーアの三つ組について論じる「ホーア論理(_Hoare Logic_)」を導入します。
    ホーア論理は命令型プログラムの合成的検証に特化した領域特化論理(domain-specific logic)であり、「ループ不変条件("loop invariant")」などの概念が組み込まれています。
 
    この部分では、実世界のソフトウェアやハードウェアの検証に広く利用されるアイディアと数学の道具を経験してもらいます。 *)

(* ================================================================= *)
(*
(** ** Type Systems *)
*)
(** ** 型システム *)

(*
(** Our other major topic, covering approximately the second half of
    the book, is _type systems_ -- powerful tools for establishing
    properties of _all_ programs in a given language.

    Type systems are the best established and most popular example of
    a highly successful class of formal verification techniques known
    as _lightweight formal methods_.  These are reasoning techniques
    of modest power -- modest enough that automatic checkers can be
    built into compilers, linkers, or program analyzers and thus be
    applied even by programmers unfamiliar with the underlying
    theories.  Other examples of lightweight formal methods include
    hardware and software model checkers, contract checkers, and
    run-time monitoring techniques.

    This also completes a full circle with the beginning of the book:
    the language whose properties we study in this part, the _simply
    typed lambda-calculus_, is essentially a simplified model of the
    core of Coq itself!
*)
 *)
(** この本の後半で述べるもう一方の主題は「型システム(_type system_)」です。
    これは、導入した言語の全てのプログラムに対する性質を保証する強力な道具です。
 
    型システムは形式検証技術の中でも「軽量形式手法(_lightweight formal method_)」と呼ばれるものの一つで、大きな成功を納めています。
    形式検証としては、型システムの保証する性質は控えめですが、その控えめさ故に自動検査としてコンパイラやリンカや解析器に組み込め、またその理論に精通していない人にも使いやすいものとなっています。
    他の軽量形式手法としてはハードウェアやソフトウェアのモデル検査器(model checker)や契約検査器(contract checker)、実行時モニタリング手法などがあります。
 
    ここまで来るとこの本の最初の目標に戻ってきます。
    ここでは「単純型付きラムダ計算(_simply typed lambda-calculus_)」と呼ばれる言語について学びます。
    これはCoqの核をさらに単純化したものなのです。
 *)

(* ================================================================= *)
(*
(** ** Further Reading *)
*)
(** ** 参考文献 *)

(*
(** This text is intended to be self contained, but readers looking
    for a deeper treatment of particular topics will find some
    suggestions for further reading in the [Postscript]
    chapter. *)
*)
(** この本は単体で読めるようにしてありますが、それぞれの内容でより進んだ話を見たければ、[Postscript]章に挙げた参考文献を見ると良いでしょう。 *)

(* ################################################################# *)
(*
(** * Note for Instructors *)
*)
(** * 教育関係者へ *)

(*
(** If you plan to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!  Please see the [Preface]
    to _Logical Foundations_ for instructions. *)
*)
(** この資料を自分のコースで使おうと思った場合、ほぼまちがいなく書き直しや追加したいところが出てくるでしょう。
    そういった貢献は大歓迎です。
    「論理の基礎(_Logical Foundations_)」の[Preface]章にある案内を見てください。 *)

(* ################################################################# *)
(** * Thanks *)

(** Development of the _Software Foundations_ series has been
    supported, in part, by the National Science Foundation under the
    NSF Expeditions grant 1521523, _The Science of Deep
    Specification_. *)

(** $Date$ *)
