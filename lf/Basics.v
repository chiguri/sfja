(** * Basics: 関数プログラミングとプログラムの証明 *)
(* begin hide *)
(** * Basics: Functional Programming in Coq *)
(* end hide *)

(* begin hide *)
(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.)
*)
(* end hide *)
(** 再掲：
<<
          ############################################################
          ### 誰もが見えるところに課題の解答を置かないでください！ ###
          ############################################################
>>
   （理由については [Preface] を参照)
 *)

(* ################################################################# *)
(* begin hide *)
(** * Introduction *)
(* end hide *)
(** * 導入 *)

(* begin hide *)
(** The functional programming style is founded on simple, everyday
    mathematical intuition: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions (or methods) as
    _first-class_ values -- i.e., values that can be passed as
    arguments to other functions, returned as results, included in
    data structures, etc.  The recognition that functions can be
    treated as data gives rise to a host of useful and powerful
    programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and sophisticated
    _polymorphic type systems_ supporting abstraction and code reuse.
    Coq offers all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language, called
    _Gallina_.  The second half introduces some basic _tactics_ that
    can be used to prove properties of Coq programs. *)
(* end hide *)
(** 関数型プログラミングスタイルは単純な数学的直観を基礎としています。
    手続きやメソッドが副作用を持たなければ、（効率を無視すれば）理解に必要なのは入力をどの出力に割り当てるかだけです。
    つまり、手続きやメソッドを、数学的な関数を計算する具体的な手法として理解することとも考えられます。
    これが「関数型プログラミング(functional programming)」における「関数型(functional)」という語の意図の一つです。
    プログラムと数学的な対象を直接関係づけることは、正当性の形式的証明やプログラムの挙動の健全な非形式的解釈という両面で役に立ちます。
 
    もう一つの関数型プログラミングが「関数型」であるという意図は、関数（やメソッド）を「一級(_first class_)」値として扱うことから来ます。
    ここで、一級値であるとは、関数の引数にしたり、関数の結果として返したり、データ構造に含めたり、といったことができることを意味します。
    関数をデータとして取り扱えることで、有用かつ強力な表現が可能になります。
 
    このほかの関数型言語に存在する機能としては、「代数的データ型(_algebraic data type_)」や「パターンマッチ(_pattern matching_)」があります。
    これらは、データ構造の構成と操作を容易にしてくれます。
    また、「多相型システム(_polymorphic type system_)」という、抽象化やコードの再利用に有用な機能もあります。
    上に挙げた機能は全てCoqに含まれています。
 
    本章の最初半分は _Gallina_ と呼ばれるCoqの関数型プログラミング言語としての基本部分の紹介となります。
    後ろ半分は、Coqのプログラムの性質を示すために使う、基本的な「タクティック(_tactic_)」を説明します。 *)

(* ################################################################# *)
(* begin hide *)
(** * Data and Functions *)
(* end hide *)
(** * データと関数 *)
(* ================================================================= *)
(* begin hide *)
(** ** Enumerated Types *)
(* end hide *)
(** ** 列挙型 *)

(* begin hide *)
(** One notable aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the Coq distribution comes preloaded with an extensive
    standard library providing definitions of booleans, numbers, and
    many common data structures like lists and hash tables.  But there
    is nothing magic or primitive about these library definitions.  To
    illustrate this, we will explicitly recapitulate all the
    definitions we need in this course, rather than just getting them
    implicitly from the library. *)
(* end hide *)
(** Coqに組み込まれた機能は、「極限まで」小さいものです。
    ブール値や自然数、文字列といった基本データ型を提供する代わりに、Coqには新しい型やそれを処理するための強力な機構が用意されています。
    この機構により、よくあるデータ型は全て定義することができます。
 
    当然、配布されているCoqにはブール値や数値、リストやハッシュテーブルといったよく使われるデータ構造を定義した大規模な標準ライブラリが付属しています。
    しかし、このライブラリの定義には魔法や基底型のようなものは使われていません。
    これを説明するために、この資料では、必要となる定義をライブラリから暗黙的に得るのではなく、明示的に再現します。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Days of the Week *)
(* end hide *)
(** ** 曜日の表し方 *)

(* begin hide *)
(** To see how this definition mechanism works, let's start with
    a very simple example.  The following declaration tells Coq that
    we are defining a new set of data values -- a _type_. *)
(* end hide *)
(** 機構がどのように動くかを知るために、簡単な例から始めましょう。
    次の宣言によって、Coqに新しいデータの集合である「型(_type_)」を定義します。 *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* begin hide *)
(** The type is called [day], and its members are [monday],
    [tuesday], etc. 

    Having defined [day], we can write functions that operate on
    days. *)
(* end hide *)
(** 型の名前は[day]で、要素は[monday]、[tuesday]...などです。
 
    [day]が何かを定義できれば、それを利用した関数を書くこともできます。 *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(* begin hide *)
(** One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often figure out these types for
    itself when they are not given explicitly -- i.e., it can do _type
    inference_ -- but we'll generally include them to make reading
    easier. *)
(* end hide *)
(** 一つ注意しておかなければならないことがあります。
    この関数の定義では、引数の型と戻り値の型が明示されていることです。
    他の多くの関数型プログラミング言語と同様、Coqはこのように型を明示的に書かずともちゃんと動くようになっています。
    つまりCoqは「型推論(_type inference_)」が可能なのですが、この講義ではプログラムを読みやすいように、常に型を明示することにします。 *)

(* begin hide *)
(** Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.  First, we can use the command [Compute] to evaluate a
    compound expression involving [next_weekday]. *)
(* end hide *)
(** 関数の定義ができたら、いくつかの例を挙げてそれが正しいものであることをチェックしなければなりません。
    それを実現するために、Coqには三つの方法が用意されています。
    一つ目は [Compute] コマンドを使って、関数[next_weekday]を含んだ式を評価させることです。 *)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

(* begin hide *)
(** (We show Coq's responses in comments, but, if you have a
    computer handy, this would be an excellent moment to fire up the
    Coq interpreter under your favorite IDE -- either CoqIde or Proof
    General -- and try this for yourself.  Load this file, [Basics.v],
    from the book's Coq sources, find the above example, submit it to
    Coq, and observe the result.) *)
(* end hide *)
(** （もし今手元にコンピュータがあるなら、CoqのIDEのうち好きなもの（CoqIdeやProofGeneralなど）を選んで起動し、実際に上のコマンドを入力し動かしてみるといいでしょう。
    この本に付随するCoqのソースから [Basics.v] を開き、上のサンプルを探してCoqに読み込ませ、結果を観察してください。） *)

(* begin hide *)
(** Second, we can record what we _expect_ the result to be in the
    form of a Coq example: *)
(* end hide *)
(** 二番目の方法は、評価の結果として我々が期待しているものをCoqに対してあらかじめ以下のような形で例示しておくというものです。 *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(* begin hide *)
(** This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later.  Having made the assertion, we can also ask Coq to verify
    it, like this: *)
(* end hide *)
(** この宣言は二つのことを行っています。
    ひとつは、[saturday]の次の次にあたる平日が、[tuesday]であるということを確認する必要があるということを示すこと。
    もう一つは、後で参照しやすいように、その確認事項に[test_next_weekday]という名前を与えていることです。
    この確認事項を記述すれば、次のようなコマンドを流すだけで、Coqによって正しさを検証できます。 *)

Proof. simpl. reflexivity.  Qed.

(* begin hide *)
(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality evaluate to the same thing, after some simplification."

    Third, we can ask Coq to _extract_, from our [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to go from proved-correct algorithms written in Gallina to
    efficient machine code.  (Of course, we are trusting the
    correctness of the OCaml/Haskell/Scheme compiler, and of Coq's
    extraction facility itself, but this is still a big step forward
    from the way most software is developed today.) Indeed, this is
    one of the main uses for which Coq was developed.  We'll come back
    to this topic in later chapters. *)
(* end hide *)
(** この文について細かいことは今は置いておきますが（じきに戻ってきます）、本質的には以下のような意味になります。
    「我々が作成した確認事項は等式の両辺が同じものに簡約されることで証明できます。」
 
    三番目の方法は、Coqで（[Definition]を使って）定義したものから、もう少し普通の言語（OCamlやScheme、Haskell）のプログラムを「抽出(_extract_)」してしまうことです。
    この機能はGallinaで記述し、正しいと証明されたアルゴリズムを、効率的な機械語まで持っていくことができるという意味でとても興味深いものです。
    （もちろん、OCaml、Haskell、Schemeなどのコンパイラや、抽出機能そのものを信頼すれば、というものではあります。
    しかし、現在のソフトウェア開発からは大きな一歩であることには違いありません。）
    これはCoqの開発動機の一つです。
    この話については後の章で詳しく見ます。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Homework Submission Guidelines *)
(* end hide *)
(** ** 宿題提出のガイドライン *)

(* begin hide *)
(** If you are using _Software Foundations_ in a course, your
    instructor may use automatic scripts to help grade your homework
    assignments.  In order for these scripts to work correctly (so
    that you get full credit for your work!), please be careful to
    follow these rules:
      - The grading scripts work by extracting marked regions of the
        [.v] files that you submit.  It is therefore important that
        you do not alter the "markup" that delimits exercises: the
        Exercise header, the name of the exercise, the "empty square
        bracket" marker at the end, etc.  Please leave this markup
        exactly as you find it.
      - Do not delete exercises.  If you skip an exercise (e.g.,
        because it is marked Optional, or because you can't solve it),
        it is OK to leave a partial proof in your [.v] file, but in
        this case please make sure it ends with [Admitted] (not, for
        example [Abort]).
      - It is fine to use additional definitions (of helper functions,
        useful lemmas, etc.) in your solutions.  You can put these
        between the exercise header and the theorem you are asked to
        prove.

    You will also notice that each chapter (like [Basics.v]) is
    accompanied by a _test script_ ([BasicsTest.v]) that automatically
    calculates points for the finished homework problems in the
    chapter.  These scripts are mostly for the auto-grading
    infrastructure that your instructor may use to help process
    assignments, but you may also like to use them to double-check
    that your file is well formatted before handing it in.  In a
    terminal window either type [make BasicsTest.vo] or do the
    following:

       coqc -Q . LF Basics.v
       coqc -Q . LF BasicsTest.v

    There is no need to hand in [BasicsTest.v] itself (or [Preface.v]).

    _If your class is using the Canvas system to hand in assignments_:
      - If you submit multiple versions of the assignment, you may
        notice that they are given different names.  This is fine: The
        most recent submission is the one that will be graded.
      - To hand in multiple files at the same time (if more than one
        chapter is assigned in the same week), you need to make a
        single submission with all the files at once using the button
        "Add another file" just above the comment box. *)
(* end hide *)
(** 「ソフトウェアの基礎」を講義で使用する場合、おそらく講師が宿題の採点用自動スクリプトを使うでしょう。
    このスクリプトが正常に動くように（皆さんの解答が適切に採点されるように）、以下の規則を守ってください。
      - 採点スクリプトは、[.v]ファイルのなかから、マークのついた箇所を抜き出して採点します。
        演習問題についている「マーク付け」を変更しないでください。
        マークは、演習問題のヘッダ、名前、末尾の「空の角括弧」などです。
        これらのマークを編集したりしないでください。
      - 演習問題自体を消さないでください。
        もし（オプションとなっていたり、解けなかったりして）演習問題を飛ばしたとしても、そのまま[.v]のなかに残して問題ありません。
        ただし、この場合は（[Abort]などではなく）[Admitted]で終わるようにしてください。
      - 解答に追加の定義（補助関数、補題、など）を書くのは全く問題ありません。
        これらは課題の宣言から証明を書く場所の間に書いてください。
 
    それぞれの章（例えば[Basics.v]）には「テストスクリプト」（[BasicsTest.v]）が付随しています。
    これは各章の演習問題の採点を自動で行う物です（訳注：現在の翻訳バージョンにはこのスクリプトは含まれていません）。
    このスクリプトは講師が採点を自動化するために使うのが主目的ですが、自分で規則を守っているかを確認するためにも使えます。
    ターミナルを開いて[make BasicsTest.vo]と打つか、次の二つのコマンドを打ってください。
<<
       coqc -Q . LF Basics.v 
       coqc -Q . LF BasicsTest.v 
>>
    [BasicsTest.v]を編集する必要はありません（[Preface.v]も不要です）。
 
    （訳注：ここには特定の課題提出システムの話がありますが、明らかに翻訳不要なので省略します） *)

(* ================================================================= *)
(* begin hide *)
(** ** Booleans *)
(* end hide *)
(** ** ブール型 *)

(* begin hide *)
(** In a similar way, we can define the standard type [bool] of
    booleans, with members [true] and [false]. *)
(* end hide *)
(** 同様にして、[true]と[false]を値とする[bool]型を定義することができます。 *)

Inductive bool : Type :=
  | true
  | false.

(* begin hide *)
(** Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans, together with a
    multitude of useful functions and lemmas.  (Take a look at
    [Coq.Init.Datatypes] in the Coq library documentation if you're
    interested.)  Whenever possible, we'll name our own definitions
    and theorems so that they exactly coincide with the ones in the
    standard library.

    Functions over booleans can be defined in the same way as
    above: *)
(* end hide *)
(** このように我々は独自のbool型を一から作っていますが、もちろんCoqにはbool型が多くの有用な関数、補題と一緒に用意されています。
    （もし興味があるなら、Coqライブラリドキュメントの[Coq.Init.Datatypes]を参照してください。）
    ここでは可能な限り標準ライブラリと同じ機能をもつ関数や定理を、同じ名前で定義していくことにしましょう。
 
    bool型を使用する関数は、Day型と同じように定義することができます。 *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* begin hide *)
(** The last two of these illustrate Coq's syntax for
    multi-argument function definitions.  The corresponding
    multi-argument application syntax is illustrated by the following
    "unit tests," which constitute a complete specification -- a truth
    table -- for the [orb] function: *)
(* end hide *)
(** 後ろ二つでは、Coqでの引数を複数持つ関数の定義の仕方を例示しています。
    対応する、複数の引数への関数適用は次の単体テスト(unit test)で示しています。
    これら単体テストは、関数[orb]が取り得るすべての引数についての完全な仕様（真理値表）となっています。 *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(* begin hide *)
(** We can also introduce some familiar syntax for the boolean
    operations we have just defined. The [Notation] command defines a new
    symbolic notation for an existing definition. *)
(* end hide *)
(** これらのブール演算に見慣れた表記法を導入することができます。
    [Notation]コマンドで、定義したものに記号表記を割り当てることができます。 *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* begin hide *)
(** _A note on notation_: In [.v] files, we use square brackets
    to delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the HTML version of the
    files, these pieces of text appear in a [different font].

    The command [Admitted] can be used as a placeholder for an
    incomplete proof.  We'll use it in exercises, to indicate the
    parts that we're leaving for you -- i.e., your job is to replace
    [Admitted]s with real proofs. *)
(* end hide *)
(** 記述方法について: [.v] ファイルのコメントの中に Coqのコード片を含める場合には、角括弧を使用してコメントと区切ります。
    この慣習は[coqdoc]というドキュメント作成ツールでも利用されているのですが、コード片を周囲のコメントから視覚的に分離することができます。
    CoqソースのHTML版では、ソースはコメントとは[別のフォント]で表示されます。
 
    [Admitted]コマンドにより、定義や証明を不完全な状態でひとまず埋めておくことができます。
    これは以降の練習問題で、課題として埋める箇所を示すのに使われます。
    つまり、練習問題を解くということは[Admitted]と書かれた部分をちゃんとした証明に書き直す作業になります。 *)

(* begin hide *)
(** **** Exercise: 1 star, standard (nandb)  

    Remove "[Admitted.]" and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (I.e., fill in each proof, following the
    model of the [orb] tests above.) The function should return [true]
    if either or both of its inputs are [false]. *)
(** **** Exercise: 1 star (nandb)  *)
(* end hide *)
(** **** 練習問題: ★, standard (nandb)
 
    [Admitted.]を消し、次の関数定義を完成させなさい。
    そして[Example]で記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。
    （つまり、各テストの証明を、上の[orb]のテストを参考にして埋めなさい。）
    この関数は引数のどちらか、もしくは両方が[false]だったときに[true]を返すものである。 *)

Definition nandb (b1:bool) (b2:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard (andb3)  

    Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)
(* end hide *)
(** **** 練習問題: ★, standard (andb3)
 
    同様のことを以下の [andb3] 関数についてしなさい。
    この関数は全ての入力が [true] である場合に [true]を返し、そうでない場合は [false] を返すものである。 *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_andb31:                 (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Types *)
(* end hide *)
(** ** 型 *)

(* begin hide *)
(** Every expression in Coq has a type, describing what sort of
    thing it computes. The [Check] command asks Coq to print the type
    of an expression. *)
(* end hide *)
(** Coqの全ての式は、どのような類のものかを表す型を持っています。
    [Check]コマンドを使うと、Coqに、指定した式の型を表示させることができます。 *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(* begin hide *)
(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)
(* end hide *)
(** [negb] のような関数は、それ自身が [true] や [false] と同じように値であると考えることもできます。
    そのようにとらえた場合の値の型を「関数型(_function type_)」と呼び、以下のように矢印を使った型として表します。 *)

Check negb.
(* ===> negb : bool -> bool *)

(* begin hide *)
(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)
(* end hide *)
(** [negb]の型は[bool -> bool]と書き、「[bool]から[bool]」と読み、「[bool]型の引数をとって[bool]型の戻り値を返す関数」と解釈します。
    同様に、[andb]の型は[bool -> bool -> bool]と書き、「二つの[bool]型の引数をとって[bool]型の戻り値を返す関数」と解釈します。 *)

(* ================================================================= *)
(* begin hide *)
(** ** New Types from Old *)
(* end hide *)
(** ** 既存の型から作る新しい型 *)

(* begin hide *)
(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements, each of which is just a bare constructor.  Here is a
    more interesting type definition, where one of the constructors
    takes an argument: *)
(* end hide *)
(** 我々がここまでで定義してきた型は「列挙型」でした。
    このような型は、有限の要素をすべて列挙することによって定義されます。
    もう少し興味深い型定義として、コンストラクタが引数を取る場合を説明します。 *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(* begin hide *)
(** Let's look at this in a little more detail.

    Every inductively defined type ([day], [bool], [rgb], [color],
    etc.) contains a set of _constructor expressions_ built from
    _constructors_ like [red], [primary], [true], [false], [monday],
    etc. 

    The definitions of [rgb] and [color] say how expressions in the
    sets [rgb] and [color] can be built:

    - [red], [green], and [blue] are the constructors of [rgb];
    - [black], [white], and [primary] are the constructors of [color];
    - the expression [red] belongs to the set [rgb], as do the
      expressions [green] and [blue];
    - the expressions [black] and [white] belong to the set [color];
    - if [p] is an expression belonging to the set [rgb], then
      [primary p] (pronounced "the constructor [primary] applied to
      the argument [p]") is an expression belonging to the set
      [color]; and
    - expressions formed in these ways are the _only_ ones belonging
      to the sets [rgb] and [color]. *)
(* end hide *)
(** この例を少し細かく見ていきましょう。
 
    それぞれ帰納的に定義された型（[day]、 [bool]、 [rgb]、 [color]、などなど）は[red]や[primary]、[true]、[false]、[monday]などの「コンストラクタ(_constructor_)」から作られる「コンストラクタ式(_constructor expressions_)」を含んでいます。
 
    [rgb]や[color]の定義はそれぞれの型に含まれる式がどのように作られるかを表しています。
 
    - [red]や[green]、[blue]は[rgb]のコンストラクタです。
    - [black]や[white]、[primary]は[color]のコンストラクタです。
    - [red]という式は[rgb]の集合に属します。
      [green]や[blue]も同様です。
    - [black]や[white]といった式は[color]の集合に属します。
    - もし[p]が[rgb]に属する式ならば、[primary p]（"引数[p]に適用されたコンストラクタ[primary]"と読みます）は[color]の集合に属します。
    - これらによって作られる式「だけ」が[rgb]や[color]の集合に含まれます。 *)

(* begin hide *)
(** We can define functions on colors using pattern matching just as
    we have done for [day] and [bool]. *)
(* end hide *)
(** [day]や[bool]に対するものと同じように、色に関するパターンマッチを用いた関数が定義できます。 *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

(* begin hide *)
(** Since the [primary] constructor takes an argument, a pattern
    matching [primary] should include either a variable (as above --
    note that we can choose its name freely) or a constant of
    appropriate type (as below). *)
(* end hide *)
(** 構築子の一つである[primary]は引数を取るので、[primary]に関するパターンマッチは変数（上記の[q]のように -- なお、名前は他の名前と重ならない限り自由につけられます）か、または適切な型の定数を含めなければなりません。 *)

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(* begin hide *)
(** The pattern [primary _] here is shorthand for "[primary] applied
    to any [rgb] constructor except [red]."  (The wildcard pattern [_]
    has the same effect as the dummy pattern variable [p] in the
    definition of [monochrome].) *)
(* end hide *)
(** 最後のパターン[primary _]は「[primary]を[rgb]型の[red]以外の構築子に適用していた場合」の略記です。
    （ワイルドカードパターン [_] は [monochrome] の定義にあるような使わない変数 [p] を書くことと同じです。） *)

(* ================================================================= *)
(** ** Tuples *)

(** A single constructor with multiple parameters can be used
    to create a tuple type. As an example, consider representing
    the four bits in a nybble (half a byte). We first define
    a datatype [bit] that resembles [bool] (using the
    constructors [B0] and [B1] for the two possible bit values),
    and then define the datatype [nybble], which is essentially
    a tuple of four bits. *)

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).
(* ==> bits B1 B0 B1 B0 : nybble *)

(** The [bits] constructor acts as a wrapper for its contents.
    Unwrapping can be done by pattern-matching, as in the [all_zero]
    function which tests a nybble to see if all its bits are O.
    Note that we are using underscore (_) as a _wildcard pattern_ to
    avoid inventing variable names that will not be used. *)

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

(* ================================================================= *)
(* begin hide *)
(** ** Modules *)
(* end hide *)
(** ** モジュール *)

(* begin hide *)
(** Coq provides a _module system_, to aid in organizing large
    developments.  In this course we won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to introduce the definition of the type [nat] in an inner
    module so that it does not interfere with the one from the
    standard library (which we want to use in the rest because it
    comes with a tiny bit of convenient special notation).  *)
(* end hide *)
(** Coqは大規模な開発を支援するために「モジュールシステム」を提供しています。
    このコースではこれらはほとんど必要のないものですが、一つだけ有用な機能があります。
    プログラムの中のいくつかの要素を[Module X]と[End X]で囲んでおくと、[End X]以降の部分からは、囲まれた中で[foo]と定義したものを[foo]ではなく[X.foo]という形で呼び出すようになります。
    という訳で、今回はこの機能を使って[nat]という型を内部モジュールに定義します。
    そうすることで、標準ライブラリの同じ名前の定義に干渉せずに済みます。
    （というのも、標準ライブラリの[nat]には便利な記法があるので、これを使うためです。） *)

Module NatPlayground.

(* ================================================================= *)
(* begin hide *)
(** ** Numbers *)
(* end hide *)
(** ** 数値 *)

(** The types we have defined so far, "enumerated types" such as
    [day], [bool], and [bit], and tuple types such as [nybble] built
    from them, share the property that each type has a finite set of
    values. The natural numbers are an infinite set, and we need to
    represent all of them in a datatype with a finite number of
    constructors. There are many representations of numbers to choose
    from. We are most familiar with decimal notation (base 10), using
    the digits 0 through 9, for example, to form the number 123.  You
    may have encountered hexadecimal notation (base 16), in which the
    same number is represented as 7B, or octal (base 8), where it is
    173, or binary (base 2), where it is 1111011. Using an enumerated
    type to represent digits, we could use any of these to represent
    natural numbers. There are circumstances where each of these
    choices can be useful.

    Binary is valuable in computer hardware because it can in turn be
    represented with two voltage levels, resulting in simple
    circuitry. Analogously, we wish here to choose a representation
    that makes _proofs_ simpler.

    Indeed, there is a representation of numbers that is even simpler
    than binary, namely unary (base 1), in which only a single digit
    is used (as one might do while counting days in prison by scratching
    on the walls). To represent unary with a Coq datatype, we use
    two constructors. The capital-letter [O] constructor represents zero.
    When the [S] constructor is applied to the representation of the
    natural number _n_, the result is the representation of _n+1_.
    ([S] stands for "successor", or "scratch" if one is in prison.)
    Here is the complete datatype definition. *)

Inductive nat : Type :=
  | O
  | S (n : nat).

(** With this definition, 0 is represented by [O], 1 by [S O],
    2 by [S (S O)], and so on. *)

(* begin hide *)
(** The clauses of this definition can be read:
      - [O] is a natural number (note that this is the letter "[O],"
        not the numeral "[0]").
      - [S] can be put in front of a natural number to yield another
        one -- if [n] is a natural number, then [S n] is too. *)
(* end hide *)
(** この定義の各句は、以下のように解釈できます。
      - [O]は自然数である（[0]（数字のゼロ）ではなく[O]（アルファベットのオー）であることに注意）。
      - [S]は自然数の前に置くことで別の自然数を生成できる。つまり、[n]が自然数なら[S n]も自然数である。 *)

(* begin hide *)
(** Again, let's look at this in a little more detail.  The definition
    of [nat] says how expressions in the set [nat] can be built:

    - [O] and [S] are constructors;
    - the expression [O] belongs to the set [nat];
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat]. *)
(* end hide *)
(** もう一度この定義をより詳細に見ていきましょう。
    [nat]の定義は、[nat]の要素となる式がどのように構築されるかを表しています。
 
    - [O]と[S]はコンストラクタである。
    - 式[O]（オー）は、[nat]に属する。
    - もし[n]が[nat]に属するならば、[S n]もまた[nat]に属する。
    - これら二つの方法で表された式のみが[nat]に属するものの全てである。*)

(* begin hide *)
(** The same rules apply for our definitions of [day], [bool],
    [color], etc.

    The above conditions are the precise force of the [Inductive]
    declaration.  They imply that the expression [O], the expression
    [S O], the expression [S (S O)], the expression [S (S (S O))], and
    so on all belong to the set [nat], while other expressions built
    from data constructors, like [true], [andb true false], [S (S
    false)], and [O (O (O S))] do not.

    A critical point here is that what we've done so far is just to
    define a _representation_ of numbers: a way of writing them down.
    The names [O] and [S] are arbitrary, and at this point they have
    no special meaning -- they are just two different marks that we
    can use to write down numbers (together with a rule that says any
    [nat] will be written as some string of [S] marks followed by an
    [O]).  If we like, we can write essentially the same definition
    this way: *)
(* end hide *)
(** 同様のルールが[day]や[bool]、[color]などにも当てはまります。
 
    これらの条件によって、帰納的([Inductive])な宣言を厳格に定義しています。
    条件から、式 [O]、式 [S O]、式  [S (S O)]、式 [S (S (S O))]...が全て[nat]に属する式であることがわかります。
    また同時に、[true]や[andb true false]、[S (S false)]、[O (O (O S))]が[nat]に属さないことも明確にされています。
 
    重要な点は、ここでは数の「表現(_representation_)」、つまり書き下し方を定義したに過ぎないと言うことです。
    [O]や[S]という名前は特別な意味があるわけではなく、なんでもよいのです。
    これらは単に数を書くための異なる二つの記号でしかありません。
    （それに付随して、[S]が[O]の前に並ぶことで任意の[nat]が記述されるという規則もありますが。）
    望むなら、同じ定義を次のように書いても良いのです。 *)

Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

(* begin hide *)
(** The _interpretation_ of these marks comes from how we use them to
    compute. *)
(* end hide *)
(** これらの記号の「解釈(_interpretation_)」は計算でどのように使用するかによって決まります。 *)

(* begin hide *)
(** We can do this by writing functions that pattern match on
    representations of natural numbers just as we did above with
    booleans and days -- for example, here is the predecessor
    function: *)
(* end hide *)
(** そのために、[bool]や[day]のとき同様にパターンマッチを使って、自然数の表現に対する関数を書いてみましょう。
    例えば、一つ前(predecessor)の[nat]を返す関数は以下のよう書けます。 *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(* begin hide *)
(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)
(* end hide *)
(** この２番目の句は「もし[n]が何らかの[n']を用いて[S n']と表せるなら、[n']を返す」と読めます。 *)

End NatPlayground.

(* begin hide *)
(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary decimal numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in decimal form by default: *)
(* end hide *)
(** 自然数というのは非常に一般的な型なので、Coqは自然数を扱ったり表したりするときに若干特別な扱いをします。
    [S]や[O]を使った「1進数(_unary_)」表記の代わりに一般的に使われる10進数表記を使うことができます。
    実際、Coqは数値を表示する際、デフォルトでは10進数表記を用います。 *)
(** 訳注：1進数は記号を並べた長さで数の大きさを表します。ここでは[S]の数がそれに当たります。 *)

Check (S (S (S (S O)))).
  (* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
  (* ===> 2 : nat *)

(* begin hide *)
(** The constructor [S] has the type [nat -> nat], just like
    [pred] and functions like [minustwo]: *)
(* end hide *)
(** [nat]のコンストラクタ[S]は[nat -> nat]型に属します。
    [pred]や[minustwo]などの関数と同じ型になっています。 *)
(* 訳注：[pred]も関数のはずだが、英語の説明はまるで[pred]が関数でないかのように見える。改訂前はそうなっていなかったが。 *)

Check S.
Check pred.
Check minustwo.

(* begin hide *)
(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference between the
    first one and the other two: functions like [pred] and [minustwo]
    come with _computation rules_ -- e.g., the definition of [pred]
    says that [pred 2] can be simplified to [1] -- while the
    definition of [S] has no such behavior attached.  Although it is
    like a function in the sense that it can be applied to an
    argument, it does not _do_ anything at all!  It is just a way of
    writing down numbers.  (Think about standard decimal numerals: the
    numeral [1] is not a computation; it's a piece of data.  When we
    write [111] to mean the number one hundred and eleven, we are
    using [1], three times, to write down a concrete representation of
    a number.)

    For most function definitions over numbers, just pattern matching
    is not enough: we also need recursion.  For example, to check that
    a number [n] is even, we may need to recursively check whether
    [n-2] is even.  To write such functions, we use the keyword
    [Fixpoint]. *)
(* end hide *)
(** これらが表しているのは、いずれの関数も数を引数にとって数を生成できる、ということです。
    しかしながら最初の一つと残り二つには根本的な違いがあります。
    [pred]や[minustwo]といった関数には「計算ルール(_computation rule_)」というものが定義されています。
    例えば、[pred]の定義は、[pred 2]が[1]に簡約されることを記述したものですが、一方[S]にはそのような定義がありません。
    コンストラクタは引数に適用するという面では関数と同様ではありますが、コンストラクタは「何も」しないのです！
    コンストラクタは単に数を書くための手段でしかありません。
    （10進数表記を思い浮かべてください。
    [1]という数字は計算方法などを表すのではなく、ただのデータ片にすぎません。
    [111]を百十一の意味で書いているとき、百十一の具体的な表現として[1]という数字を三回使っているだけなのです。）
    （訳注：ここでは「数」と「数字」を明確に使い分けています。数字はただの文字であり値ではありません。）
 
    数値を扱う多くの関数は、単なるパターンマッチだけでは記述できず、再帰が必要になってきます。
    例えば、[n]が偶数かどうかを調べて返す関数[evenb]は、[n-2]が偶数であるかどうかを調べる、という再帰的な定義を必要とします。
    そういう関数を定義する場合、[Fixpoint]というキーワードを使用します。 *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(* begin hide *)
(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition: *)
(* end hide *)
(** 同じように[Fixpoint]を使って関数[oddb]を定義することもできますが、ここでは次のようにもっとシンプルな方法で作ります。 *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(* begin hide *)
(** (You will notice if you step through these proofs that
    [simpl] actually has no effect on the goal -- all of the work is
    done by [reflexivity].  We'll see more about why that is shortly.)

    Naturally, we can also define multi-argument functions by
    recursion.  *)
(* end hide *)
(** （1ステップずつ実行していくと、ここでは[simpl]がゴールに何も起こしていないことに気づくかもしれません。
    実際のところ、この証明は[reflexivity]が全てを担っています。
    なぜこうなるのかすぐ後で述べます。）
 
    当然ながら、引数を複数持つ関数も再帰的に定義することができます。 *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(* begin hide *)
(** Adding three to two now gives us five, as we'd expect. *)
(* end hide *)
(** 3に2を加えた結果は、5になるべきですね。 *)

Compute (plus 3 2).

(* begin hide *)
(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)
(* end hide *)
(** Coqがこの計算をどう進めて（簡約して）結論を導くかは以下のように表現できます。 *)

(* begin hide *)
(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))]
      by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))]
      by the second clause of the [match]
==> [S (S (S (S (S O))))]
      by the first clause of the [match]
*)
(* end hide *)
(**
[[
    plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O)))
      match の二つ目の節での置き換え
==> S (S (plus (S O) (S (S O))))
      match の二つ目の節での置き換え
==> S (S (S (plus O (S (S O)))))
      match の二つ目の節での置き換え
==> S (S (S (S (S O))))
      match の一つ目の節での置き換え
]]
 *)

(* begin hide *)
(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)
(* end hide *)
(** 表記を簡便にするため、複数の引数が同じ型を持つときは、型の記述をまとめることができます。
    [(n m : nat)]は[(n : nat) (m : nat)]と書いたのとまったく同じ意味になります。 *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(* begin hide *)
(** You can match two expressions at once by putting a comma
    between them: *)
(* end hide *)
(** matchに引数を与える際、複数の引数を次のようにカンマで区切って一度に渡すことができます。 *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(* begin hide *)
(** **** Exercise: 1 star, standard (factorial)  

    Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)
(* end hide *)
(** **** 演習問題: ★, standard (factorial)
 
    数学での一般的な階乗(factorical)関数の定義を思い出してください :
<<
       factorial(0)  =  1 
       factorial(n)  =  n * factorial(n-1)     (if n>0) 
>>
    これをCoqでの定義に書き直しなさい。 *)

Fixpoint factorial (n:nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_factorial1:          (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** Again, we can make numerical expressions easier to read and write
    by introducing notations for addition, multiplication, and
    subtraction. *)
(* end hide *)
(** 表記法を利用して、加算、減算、乗算のような数値を扱う式をずっと読みやすく、書きやすくしておきます。 *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

(* begin hide *)
(** (The [level], [associativity], and [nat_scope] annotations
    control how these notations are treated by Coq's parser.  The
    details are not important for our purposes, but interested readers
    can refer to the "More on Notation" section at the end of this
    chapter.)

    Note that these do not change the definitions we've already made:
    they are simply instructions to the Coq parser to accept [x + y]
    in place of [plus x y] and, conversely, to the Coq pretty-printer
    to display [plus x y] as [x + y]. *)
(* end hide *)
(** （[level]、[associativity]、[nat_scope]という記述は、Coqのパーザーにこれらの表記法をどう扱うかを指示するものです。
    詳細は重要ではないのですが、もし興味があれば本章の末尾にある「表記法をより詳しく」の項を読んでください。）
 
    これらは、これまで我々が定義してきたものを何ら変えるわけではありません。
    NotationはCoqのパーサに対して[x + y]を[plus x y]と解釈させたり、逆に[plus x y]を[x + y]と表記させたりするためのものです。 *)

(* begin hide *)
(** When we say that Coq comes with almost nothing built-in, we really
    mean it: even equality testing is a user-defined operation!

    Here is a function [eqb], which tests natural numbers for
    [eq]uality, yielding a [b]oolean.  Note the use of nested
    [match]es (we could also have used a simultaneous match, as we did
    in [minus].) *)
(* end hide *)
(** 最初の方で、Coqにはほとんど何も用意されていない、という話をしましたが、実際に、数値を比較する関数すら自分で作れる演算なのです！
 
    では自然数を比較して等しい([eq]uality)かを[b]ool値で返す[eqb]関数を定義します。
    入れ子になった[match]に気をつけて、以下のソースを読んでください。
    （[minus]同様に、二つの変数を一度に[match]させる方法でも書けます。） *)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

(* begin hide *)
(** Similarly, the [leb] function tests whether its first argument is
    less than or equal to its second argument, yielding a boolean. *)
(** The [leb] function tests whether its first argument is less than or
  equal to its second argument, yielding a boolean. *)
(* end hide *)
(** 似たようにして、[leb]関数は一つ目の自然数が二つ目の自然数より小さい(less than)か等しい(equal)か、ということをbool値で返します。 *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** Since we'll be using these (especially [eqb]) a lot, let's give
    them infix notations. *)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3':             (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.

(* begin hide *)
(** **** Exercise: 1 star, standard (ltb)  

    The [ltb] function tests natural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined
    function.  (It can be done with just one previously defined
    function, but you can use two if you need to.) *)
(* end hide *)
(** **** 練習問題: ★, standard (ltb)
 
    [ltb]関数は、二つの自然数を比較して小さい([l]ess-[t]han)か、ということを[b]ool値で返します。
    [Fixpoint]を使用して1から作成するのではなく、すでにこれまで定義した関数を利用して定義しなさい。
    （他の関数一つで定義できますが、二つ使ってもかまいません。） *)

Definition ltb (n m : nat) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_ltb2:             (ltb 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_ltb3:             (ltb 4 2) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Proof by Simplification *)
(* end hide *)
(** * 簡約を用いた証明 *)

(* begin hide *)
(** Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each [Example] in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use [simpl] to simplify both sides of the
    equation, then use [reflexivity] to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved just
    by observing that [0 + n] reduces to [n] no matter what [n] is, a
    fact that can be read directly off the definition of [plus]. *)
(* end hide *)
(** ここまでに、いくつかの型や関数を定義してきました。
    が、ここからは少し目先を変えて、こういった型や関数の特性や振る舞いをどうやって記述、証明していくかを考えてみることにしましょう。
    実際には、すでにこれまでやってきたことでも、その一部に触れています。
    例えば、これまでのセクションの[Example]は、ある関数にある特定の値を入力した時の振る舞いについて、あらかじめ想定していたものと正確に一致していると主張してくれます。
    それらの主張が証明しているものは、以下のものと同じです。
    「[=]の両側の式を簡約した結果が一致しているかを調べるために、[simpl]を使って両辺を簡単にして、[reflexivity]を使いなさい。」
 
    このような「簡約を用いた証明」は、関数のさらに興味深い性質をうまく証明することができます。
    例えば、[0]が自然数の加算における左単位元（左から加えても値が変わらない値）であることの証明は、[n]が何であっても[0 + n]を注意深く縮小（簡約）したものが[n]になることを、[+]という関数が「最初の引数を引き継いで再帰的に定義されている」ということを考慮した上で示せればいいということです。 *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

(* begin hide *)
(** (You may notice that the above statement looks different in
    the [.v] file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In [.v] files, we write the
    [forall] universal quantifier using the reserved identifier
    "forall."  When the [.v] files are converted to HTML, this gets
    transformed into an upside-down-A symbol.)

    This is a good place to mention that [reflexivity] is a bit
    more powerful than we have admitted. In the examples we have seen,
    the calls to [simpl] were actually not needed, because
    [reflexivity] can perform some simplification automatically when
    checking that two sides are equal; [simpl] was just added so that
    we could see the intermediate state -- after simplification but
    before finishing the proof.  Here is a shorter proof of the
    theorem: *)
(* end hide *)
(** （訳注：原文ではここでHTMLと[.v]ファイルの見え方の違いが説明されているのですが、日本語訳ではHTML側での大きな表記の変更を行わないようにしています。
    翻訳版の特徴として、HTMLには表示されませんが、[.v]ファイルには、（begin hide/end hideというコメントで挟まれた）英語の原文と訳文が交互に記述されています。
    もし訳文を読みづらい、内容が怪しいと感じた場合には、直前にある原文も参照してみてください。）
 
    [reflexivity]はこれまでの使い方よりももっと強力です。
    ここまでの例では[simpl]を使っていましたが、実際にはこれは必要ではありません。
    [reflexivity]は両辺が等しいかを確かめる際にある程度自動で簡約します。
    [simpl]は単に、証明終了前の簡約後の途中状態をみるために書いています。
    以下は証明をより短く書いたものです。 *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(* begin hide *)
(** Moreover, it will be useful later to know that [reflexivity]
    does somewhat _more_ simplification than [simpl] does -- for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword [Theorem] instead of [Example].
    This difference is mostly a matter of style; the keywords
    [Example] and [Theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean pretty much the same thing to Coq.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions.

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters. *)
(* end hide *)
(** [reflexivity]は[simpl]より多くの簡約を行います。
    例えば、定義した項を定義の右辺に置き換える「展開(unfolding)」を行います。
    こう言った差が発生する理由は、[reflexivity]が成功するなら、簡約結果がどうなっているかを出す必要がないからです。
    [simpl]の場合はこうは行かず、簡約した結果を画面に出すため、定義をむやみに展開したりしません。
 
    この定理と証明の様式は、以前示した例とほとんど同じですが、いくつか違いがあります。
 
    まず、[Example]の代わりに[Theorem]キーワードが使用されていることです。
    これはほとんど単なるスタイルの違いで、[Example]と[Theorem]（他にも[Lemma]、[Fact]、[Remark]など）はCoqから見るとすべてほぼ同じ意味です。
 
    他に、量化子（[forall n:nat]）が加えられていることが挙げられます。
    これにより、定理は「全ての」自然数[n]について言及できます。
    非形式的には、こういった定理の証明ではまず「ある数[n]が存在して...」と始めます。
    形式的には、この動きは[intros n]によって実現できます。
    実際には、これは量化子をゴールから仮定の「文脈(_context_)」に移動しています。
 
    [intros]や[simpl]、[reflexivity]は「タクティック(_tactic_)」の例です。
    タクティックは、[Proof]と[Qed]の間に記述され、示そうとしている言明を確かめる方法を表します。
    本章の残りでは、まだ出てきていないタクティックのうちのいくつかを紹介していきましょう。
    さらにその後の講義ではもっと色々出てきます。 *)

(* begin hide *)
(** Other similar theorems can be proved with the same pattern. *)
(* end hide *)
(** 似た定理も、同じパターンで証明できます。 *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(* begin hide *)
(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)
(* end hide *)
(** 定理の名前についている[_l]という接尾辞は、「左の」と読みます。 *)

(* begin hide *)
(** It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [reflexivity] to see the simplifications that Coq performs
    on the terms before checking that they are equal. *)
(* end hide *)
(** 文脈やゴールがどのように変化していくかを見ていきましょう。
    [simpl]を[reflexivity]の前に呼ぶことで、等価かを判定する前に簡約できます。 *)

(* ################################################################# *)
(* begin hide *)
(** * Proof by Rewriting *)
(* end hide *)
(** * 書き換え（[Rewriting]）による証明*)

(* begin hide *)
(** This theorem is a bit more interesting than the others we've
    seen: *)
(* end hide *)
(** ここまでの定理より、もう少し面白い定理を見てみましょう。 *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(* begin hide *)
(** Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when [n
    = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)
(* end hide *)
(** この定理は、あらゆる[n]や[m]について成り立つと言っているわけではなく、[n = m]が成り立つときに限って成立する、というものです。
    この矢印は"ならば"と読みます。
 
    前と同じように、[n]と[m]をある数として仮定する必要があります。
    また、[n = m]という仮定を置く必要もあります。
    [intros]タクティックはこれら三つを全てゴールから仮定の文脈に移動します。
 
    [n]と[m]が両方とも任意の数なのですから、これまでの証明でやってきたように簡約することはできません。
    その代わりに、[n = m]ならば、イコールの両側の[n]を[m]に書き換えても等しさは変わらない、というところに注目します。
    このような書き換えをしてくれるのが[rewrite]タクティックです。 *)

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.

(* begin hide *)
(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.) *)
(* end hide *)
(** 証明の1行目は、全称量化子（forall）がついた、つまり「あらゆる[n],[m]について」の部分をコンテキストに移しています。
    2行目は、[n = m]ならば、という仮定をコンテキストに移し、[H]という名前をこれに与えています。
    3行目は、ゴールになっている式([n + n = m + m])に仮定[H]の左側を右側にするような書き換えを施しています。
 
    （[rewrite]の矢印は含意とは関係ありません。
    左側を右側に置き換えよ、という指示を出しているだけです。
    逆に右側を左側に置き換えたい場合は、[rewrite <-]と書きます。
    この逆の置き換えも上の証明で試して、どのように変わるかを観察してください。） *)

(* begin hide *)
(** **** Exercise: 1 star, standard (plus_id_exercise)  

    Remove "[Admitted.]" and fill in the proof. *)
(* end hide *)
(** **** 練習問題: ★, standard (plus_id_exercise)
 
    [Admitted.]を削除し、証明を完成させなさい。*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** The [Admitted] command tells Coq that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [Admitted] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [Admitted] you
    are leaving a door open for total nonsense to enter Coq's nice,
    rigorous, formally checked world! *)
(* end hide *)
(** [Admitted]コマンドは、Coqに対して「この証明はあきらめたので、この定理はこれでいいことにしてください」と指示するものです。
    この機能は、より長い証明をする際に便利です。
    何か大きな論証を構築しているときには、今のところ信用している補足的な命題を示したいことがあります。
    そんな時、[Admitted]を使用すると、その命題を一時的に信用できることにして、主としている論証がうまくいくまで続けられます。
    そしてそれが完成したのち、あらためて保留していた命題の証明を埋めればいいのです。
    ただし注意して下さい。
    [Admitted]を使用することは、一時的にドアを開けて、「全て形式的なチェックを受け証明済みの、信用するに足るCoqの世界」から、信用に値しない下界へ足を踏み出していることに他なりません。 *)

(* begin hide *)
(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. If the statement
    of the previously proved theorem involves quantified variables,
    as in the example below, Coq tries to instantiate them
    by matching with the current goal. *)
(* end hide *)
(** [rewrite]タクティックを使うときには、仮定の代わりに、前もって証明された定理も利用できます。
    以下のように、利用する定理の言明が量化子付きの場合、Coqがゴールに合う形に具体化しようとします。 *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(* begin hide *)
(** **** Exercise: 2 stars, standard (mult_S_1)  *)
(* end hide *)
(** **** 練習問題: ★★, standard (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.

(* begin hide *)
  (* (N.b. This proof can actually be completed with tactics other than
     [rewrite], but please do use [rewrite] for the sake of the exercise.) 

    [] *)
(* end hide *)
  (** （注意：この証明は[rewrite]以外のタクティックでできますが、ここでは課題のためと思って[rewrite]を使ってください。）
 
    [] *)

(* ################################################################# *)
(* begin hide *)
(** * Proof by Case Analysis *)
(* end hide *)
(** * 場合分け(Case Analysis)による証明 *)

(* begin hide *)
(** Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck.  (We then
    use the [Abort] command to give up on it for the moment.)*)
(* end hide *)
(** もちろん、どんな命題でも簡単な計算や書き換えだけで証明できるという訳ではありません。
    一般に、未知だったり仮定の値（任意の自然数、bool値、リストなど）は、簡単化を止めてしまいます。
    例えば、下の命題を[simpl]タクティックだけで証明しようとすると、すぐに行き詰まってしまいます。
    （そういう場合は諦めたことを表すために[Abort]コマンドを使います。） *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

(* begin hide *)
(** The reason for this is that the definitions of both
    [eqb] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [eqb] is the compound
    expression [n + 1]; neither can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [(n + 1) =? 0] and check that it is, indeed, [false].  And
    if [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] yields, we can calculate that, at least, it
    will begin with one [S], and this is enough to calculate that,
    again, [(n + 1) =? 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)
(* end hide *)
(** その原因は、[eqb]と[+]の定義で、共に最初の引数が[match]に渡されていることです。
    つまり、[+]に渡す最初の引数は[n]という未知数な上に、[eqb]の引数は[n + 1]という複合式になっているため、そのまま簡約できないのです。
 
    証明を進めるには、[n]を何らかの条件に分割できないかの検討が必要です。
    もし[n]が[O]なら、[(n + 1) =? 0]の結果を得ることはできます。
    もちろん結果は[false]です。
    もし[n]が何かの[n']を使って[n = S n']と表せる場合、我々は[n + 1]の値を得ることはできません。
    ただ、少なくともその式が一つの[S]で始まることはわかります。
    これが分かれば、[(n + 1) =? 0]の結果が[false]になることまでは計算できます。
 
    このことから、求められるタクティックはCoqに[n = O]の場合と[n = S n']の場合に分けて考えるように求めるもので、これを実現するのが[destruct]タクティックです。 *)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.

(* begin hide *)
(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem.

    The annotation "[as [| n']]" is called an _intro pattern_.  It
    tells Coq what variable names to introduce in each subgoal.  In
    general, what goes between the square brackets is a _list of
    lists_ of names, separated by [|].  In this case, the first
    component is empty, since the [O] constructor is nullary (it
    doesn't have any arguments).  The second component gives a single
    name, [n'], since [S] is a unary constructor.

    In each subgoal, Coq remembers the assumption about [n] that is
    relevant for this subgoal -- either [n = 0] or [n = S n'] for some
    n'.  The [eqn:E] annotation tells [destruct] to give the name [E] to
    this equation.  (Leaving off the [eqn:E] annotation causes Coq to
    elide these assumptions in the subgoals.  This slightly
    streamlines proofs where the assumptions are not explicitly used,
    but it is better practice to keep them for the sake of
    documentation, as they can help keep you oriented when working
    with the subgoals.)

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to each
    generated subgoal.  The proof script that comes after a bullet is
    the entire proof for a subgoal.  In this example, each of the
    subgoals is easily proved by a single use of [reflexivity], which
    itself performs some simplification -- e.g., the second one
    simplifies [(S n' + 1) =? 0] to [false] by first rewriting [(S n'
    + 1)] to [S (n' + 1)], then unfolding [eqb], and then simplifying
    the [match].

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)
(* end hide *)
(** この証明では、[destruct]タクティックは二つのサブゴールを作っています。
    その両方を別々に証明することで、全体が定理として認められます。
 
    [destruct]についている注釈"[as [| n']]"は、「イントロパターン(_intro pattern_)」と呼ばれるものです。
    これはCoqに対して、サブゴール毎に出てくる変数をどんな変数名で扱うかを指示するものです。
    一般的に[[]]の間にあるものは [|] によって区切った「名前のリスト」のリストです。
    今回のリストの最初の要素は空ですが、これは[nat]の最初のコンストラクタである[O]が引数をとらないからです。
    二つ目のコンストラクタ[S]は引数を一つ取りますので、二つ目の要素では変数名を一つ、[n']を指定しています。
 
    それぞれのサブゴールで、Coqは[n]が[n = 0]だったか、それともある[n']に対して[n = S n']と表されるのだったかを覚えています。
    [eqn:E]という注釈はこの等式を[E]という名前で覚えておくように[destruct]に要求します。
    （[eqn:E]を書かない場合、Coqはこれらの等式を覚えておきません。
    もしこの等式を使わないのであれば覚えないのは合理的なのですが、実際にはサブゴールで何を示そうとしているのかを明記するために覚えさせた方がよいでしょう。）
 
    二行目と三行目にある[-]という記号は「バレット(_bullet_)」と呼ばれるもので、ある時点で存在したサブゴールそれぞれの証明の開始を表しています。
    バレットの後ろに続く証明スクリプトは、あるサブゴールの一連の証明になります。
    この例では、どちらのサブゴールも単に[reflexivity]による簡単化と比較で証明できています。
    例えば、二つ目は [(S n' + 1)] を [S (n' + 1)] に書き換え、 [eqb] の定義を展開し、最後に [match] を簡単化することで、 [(S n' + 1) ?= 0] 全体を [false] に簡単化します。
 
    バレットを付けるのは必須ではありません。
    もしバレットがないと、Coqは単に、順に次々とサブゴールの証明を求めます。
    しかし、バレットを使っておくと、証明の構成がはっきり見え、読みやすくなります。
    また、バレットによって、次のサブゴールに行く前に、一つ前のサブゴールが証明完了していることを確かめることができ、証明が混ざったりすることを防げます。
    大規模になると、証明が壊れたときのデバッグが非常に難しくなるため、こういった要素が重要になります。
 
    Coqでの証明の書き方の、厳格なルールというものはありません。
    特に、どこで行を折り返すか、証明のネストを表すための字下げをどの単位で行うか、などは全く決まっていません。
    しかし、複数のゴールができたときにバレットを明示すれば、他の部分をどうしても大体読みやすくなるでしょう。
 
    一行の長さについて少し語っておきます。
    Coq初心者の中には極端な人がいて、一行に一つのタクティックしか書かない人や、一行に全ての証明を詰め込む人がいます。
    好い加減というのは、大体その間にあります。
    一行を80文字に押さえるというのは扱いやすい慣習の一つです。
 
    [destruct]タクティックは帰納的に定義された型に対して使用できます。
    例として、bool値の否定が対合(_involutive_)であること、つまり否定の否定が元と同じになることを証明してみましょう。 *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.

(* begin hide *)
(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [|]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  This is generally considered bad style, since Coq
    often makes confusing choices of names when left to its own
    devices.

    It is sometimes useful to invoke [destruct] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example: *)
(* end hide *)
(** ここで使われている[destruct]には[as]句がありませんが、ここで展開している[b]の型[bool]の二つのコンストラクタが両方とも引数をとらないため、名前を指定する必要がないのです。
    このような場合、"[as [|]]"や"[as []]"のように書くこともできます。
    実は、[destruct]の[as]句はどんなときでも省略可能です。
    その際はCoqの側で自動的に変数名をつけてくれます。
    しかし、これはあまりよくない書き方でもあります。
    Coqに任せておくと、しばしば混乱しやすい名前を付けるからです。
 
    [destruct]を、まだ他のサブゴールが残っている状態で使うこともあります。
    このとき、バレットを使うときは異なる「レベル」を表すために異なる記号をバレットとして使います。 *)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

(* begin hide *)
(** Each pair of calls to [reflexivity] corresponds to the
    subgoals that were generated after the execution of the [destruct c]
    line right above it. *)
(* end hide *)
(** 2つ並んだ[reflexivity]は、その直前の行の[destruct c]を実行することで作られたサブゴールに対応しています。 *)

(* begin hide *)
(** Besides [-] and [+], we can use [*] (asterisk) as a third kind of
    bullet.  We can also enclose sub-proofs in curly braces, which is
    useful in case we ever encounter a proof that generates more than
    three levels of subgoals: *)
(* end hide *)
(** バレットとしては、[-]や[+]の他に[*] （アスタリスク）が使用できます。
    また、証明のブロックを波括弧（[{}]）で囲むこともできます。
    これは、3つ以上のレベルでサブゴールが出来てしまった場合に有用です。 *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(* begin hide *)
(** Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof: *)
(* end hide *)
(** この例のように、波括弧で証明の始めと終わりを囲むことで、ネストしてレベルを表現することができます。
    また、波括弧で囲むことで、既にバレットとして使ってしまった記号を再利用することができます。 *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

(* begin hide *)
(** Before closing the chapter, let's mention one final
    convenience.  As you may have noticed, many proofs perform case
    analysis on a variable right after introducing it:

       intros x y. destruct y as [|y] eqn:E.

    This pattern is so common that Coq provides a shorthand for it: we
    can perform case analysis on a variable when introducing it by
    using an intro pattern instead of a variable name. For instance,
    here is a shorter proof of the [plus_1_neq_0] theorem
    above.  (You'll also note one downside of this shorthand: we lose
    the equation recording the assumption we are making in each
    subgoal, which we previously got from the [eqn:E] annotation.) *)
(* end hide *)
(** この章を締めくくる前に、便利な記法を一つ挙げておきます。
    既に気づいたかもしれませんが、変数の場合分けは、以下のように変数の導入直後に行われることが多々あります。
[[
       intros x y. destruct y as [|y] eqn:E. 
]]
    この書き方があまりに多いので、Coqではこの簡略版として、導入する変数を、名前の代わりにイントロパターンによって導入することができます。
    例えば上で証明した [plus_1_neq_0] にその略記法を使うと以下のようになります。
    （ただし欠点もあります。
    この略記法では、これまで [eqn:E] を使って覚えていた等式が残らなくなってしまいます。） *)


Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(* begin hide *)
(** If there are no arguments to name, we can just write [[]]. *)
(* end hide *)
(** もし全ての場合で名前を付ける必要がないのなら、[[]]と書くことができます。 *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* begin hide *)
(** **** Exercise: 2 stars, standard (andb_true_elim2)  

    Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)
(* end hide *)
(** **** 練習問題: ★★, standard (andb_true_elim2)
 
    以下の言明を、[destruct]を使ったときの場合分けそれぞれにバレットを使用して証明しなさい。 *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard (zero_nbeq_plus_1)  *)
(* end hide *)
(** **** 練習問題: ★, standard (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** More on Notation (Optional) *)
(* end hide *)
(** ** オプション：表記法をより詳しく *)

(* begin hide *)
(** (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times: *)
(* end hide *)
(** （「オプション」と付けた節は、他の章で同じく「オプション」と付いている節以外には必須ではありません。
    初めて読むときは、今後のために軽く目を通すくらいにしておくと良いでしょう。）
 
    中置記法の加算と乗算の記法の定義を再掲します。 *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(* begin hide *)
(** For each notation symbol in Coq, we can specify its _precedence
    level_ and its _associativity_.  The precedence level [n] is
    specified by writing [at level n]; this helps Coq parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for [+] and
    [*] say that the expression [1+2*3*4] is shorthand for
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and
    _left_, _right_, or _no_ associativity.  We will see more examples
    of this later, e.g., in the [Lists]
    chapter.

    Each notation symbol is also associated with a _notation scope_.
    Coq tries to guess what scope is meant from context, so when it
    sees [S(O*O)] it guesses [nat_scope], but when it sees the
    cartesian product (tuple) type [bool*bool] (which we'll see in
    later chapters) it guesses [type_scope].  Occasionally, it is
    necessary to help it out with percent-notation by writing
    [(x*y)%nat], and sometimes in what Coq prints it will use [%nat]
    to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation ([3], [4], [5],
    etc.), so you may sometimes see [0%nat], which means [O] (the
    natural number [0] that we're using in this chapter), or [0%Z],
    which means the Integer zero (which comes from a different part of
    the standard library).

    Pro tip: Coq's notation mechanism is not especially powerful.
    Don't expect too much from it! *)
(* end hide *)
(** Coqで表記法を定義する際、「優先度(_precedence level_)」と「結合性(_associativity_)」を定義できます。
    優先度に [n] を割り当てる際には[at level n]のように書きます。
    優先度は、Coqが複雑な式を解釈するのに使います。
    結合性は同じ表記法が複数回現れたときの解釈を定めるために付けます。
    例えば、この章では[+]と[*]を定義しましたので、[1+2*3*4]を[(1+((2*3)*4))]の略記版として利用できます。
    Coqでは優先度として0から100のレベルを、また結合性として「左結合(left)」「右結合(right)」または「結合性なし(no)」を指定できます。
    これ以降、例えば[Lists]の章などで、これらの宣言が多数使われます。
 
    Coqでの表記法は、それぞれが「表記スコープ(_notation scope_)」と関連します。
    今どの表記スコープで書かれているかは、Coqが自動で判定しようとします。
    例えば[S(O*O)]と書いていれば[nat_scope]だと判定し、デカルト積（タプル）型（後の章で出ます）である[bool*bool]という記述からは[type_scope]と判定します。
    判定を誤ることもあるので、パーセント記号を使って、[(x*y)%nat]のように明示しないといけないこともあります。
    また、Coqが特定の表記スコープでの表記法であることを明示するために[%nat]という記法を使うこともあります。
 
    表記スコープは[3],[4],[5]などの数の表記法にも使われます。
    例えば[0%nat]と書くと本章で使っている自然数（[nat]）の[O]を意味しますが、[0%Z]と書くと標準ライブラリで提供されている整数（[Z]）のゼロを意味します。
 
    プロ向け情報：Coqの表記法の記法はそれほど強力ではありません。
    過剰な期待はやめましょう。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Fixpoints and Structural Recursion (Optional) *)
(* end hide *)
(** ** オプション：[Fixpoint]と構造的再帰 *)

(* begin hide *)
(** Here is a copy of the definition of addition: *)
(* end hide *)
(** 加算の定義をそのまま持ってきました。 *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(* begin hide *)
(** When Coq checks this definition, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is "decreasing."

    This requirement is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. *)
(* end hide *)
(** 上の定義をCoqが検査すると、[plus']が「第一引数が減少している（"decreasing on 1st argument"）」というメッセージを出します。
    これは引数[n]に関する「構造的再帰(_structural recursion_)」を行っていることを意味します。
    つまり、再帰呼び出しの際には、必ず[n]が厳密に小さくなっているということです。
    これにより、どんな引数でも[plus']の呼び出しが必ずいつか終了することを保証できます。
    Coqは[Fixpoint]での定義で、ある特定の引数が「減少している」ことを求めます。
 
    この要求はCoqの設計の基礎部分から来ています。
    この要求により、Coqで定義できる関数が、どんな入力に対しても終了することを保証できます。
    しかし、Coqの「減少性解析」はそれほど洗練されていないため、場合によっては関数を不自然な形で書かなければならないこともあります。 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (decreasing)  

    To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will reject because
    of this restriction.  (If you choose to turn in this optional
    exercise as part of a homework assignment, make sure you comment
    out your solution so that it doesn't cause Coq to reject the whole
    file!) *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (decreasing)
 
    これを具体的に感じるため、（自然数の単純な関数でかまわないので）全ての入力で停止するが、Coqが制限のため受け入れないような[Fixpoint]による定義の書き方を見つけなさい。
    （もしこれを宿題として解く場合は、Coqがこのファイルを受け入れられるように、回答をコメントアウトしなさい。） *)

(* FILL IN HERE 

    [] *)

(* ################################################################# *)
(* begin hide *)
(** * More Exercises *)
(* end hide *)
(** * 発展課題 *)

(** Each SF chapter comes with a tester file (e.g.  [BasicsTest.v]),
    containing scripts that check most of the exercises. You can run
    [make BasicsTest.vo] in a terminal and check its output to make
    sure you didn't miss anything. *)

(* begin hide *)
(** **** Exercise: 1 star, standard (indentity_fn_applied_twice)  

    Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)
(* end hide *)
(** **** 練習問題: ★, standard (identity_fn_applied_twice)
 
    ここまでで学んだタクティックを使い、次のブール関数についての定理を証明しなさい。 *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard (negation_fn_applied_twice)  

    Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x]. *)
(* end hide *)
(** **** Exercise: ★, standard (negation_fn_applied_twice)
 
    また、[negation_fn_applied_twice]という名前で、
    上の定理とほとんど同じで、二つ目の[f]に関する仮定が[f x = negb x]になっている定理を記述し、証明しなさい。 *)

(* FILL IN HERE *)
(* The [Import] statement on the next line tells Coq to use the
   standard library String module.  We'll use strings more in later
   chapters, but for the moment we just need syntax for literal
   strings for the grader comments. *)
From Coq Require Export String.

(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (andb_eq_orb)  

    Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (andb_eq_orb)
 
    次の定理を証明しなさい。
    （ヒント：証明方針によっては、かなりトリッキーな手法が必要になるでしょう。
    [destruct]と[rewrite]のどちらも必要でしょうが、手当たり次第に展開するのは良策ではありません。） *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (binary)  

    We can generalize our unary representation of natural numbers to
    the more efficient binary representation by treating a binary
    number as a sequence of constructors [A] and [B] (representing 0s
    and 1s), terminated by a [Z]. For comparison, in the unary
    representation, a number is a sequence of [S]s terminated by an
    [O].

    For example:

        decimal            binary                           unary
           0                   Z                              O
           1                 B Z                            S O
           2              A (B Z)                        S (S O)
           3              B (B Z)                     S (S (S O))
           4           A (A (B Z))                 S (S (S (S O)))
           5           B (A (B Z))              S (S (S (S (S O))))
           6           A (B (B Z))           S (S (S (S (S (S O)))))
           7           B (B (B Z))        S (S (S (S (S (S (S O))))))
           8        A (A (A (B Z)))    S (S (S (S (S (S (S (S O)))))))

    Note that the low-order bit is on the left and the high-order bit
    is on the right -- the opposite of the way binary numbers are
    usually written.  This choice makes them easier to manipulate. *)
(* end hide *)
(** **** 練習問題: ★★★, standard (binary)
 
    1進数による自然数の表現と同様の考えから、二つのコンストラクタ [A] と [B] （それぞれ0と1を表します）が並び、[Z]で終わる列によって、より効率的な2進数を定義できます。
    なお、1進数での自然数は、[S]が並び、[O]で終わる列で表されていました。
 
    例：
<<
        10進数               2進数                           1進数
           0                   Z                              O
           1                 B Z                            S O
           2              A (B Z)                        S (S O)
           3              B (B Z)                     S (S (S O))
           4           A (A (B Z))                 S (S (S (S O)))
           5           B (A (B Z))              S (S (S (S (S O))))
           6           A (B (B Z))           S (S (S (S (S (S O)))))
           7           B (B (B Z))        S (S (S (S (S (S (S O))))))
           8        A (A (A (B Z)))    S (S (S (S (S (S (S (S O)))))))
>>
    一般的な2進数表記とは逆に、この表現では、下位ビットが左に、上位ビットが右に来るようになっています。
    この方がCoqでは扱いやすくなります。 *)

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

(* begin hide *)
(** (a) Complete the definitions below of an increment function [incr]
        for binary numbers, and a function [bin_to_nat] to convert
        binary numbers to unary numbers. *)
(* end hide *)
(** (a) 以下の2進数用のインクリメント関数[incr]と、2進数から1進数へ変換する関数[bin_to_nat]を完成させなさい。 *)

Fixpoint incr (m:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Fixpoint bin_to_nat (m:bin) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* begin hide *)
(**    (b) Write five unit tests [test_bin_incr1], [test_bin_incr2], etc.
        for your increment and binary-to-unary functions.  (A "unit
        test" in Coq is a specific [Example] that can be proved with
        just [reflexivity], as we've done for several of our
        definitions.)  Notice that incrementing a binary number and
        then converting it to unary should yield the same result as
        first converting it to unary and then incrementing. *)
(* end hide *)
(**    (b) [test_bin_incr1]や[test_bin_incr2]といった名前で[incr]や[bin_to_nat]に関する5つの単体テストを書きなさい。
        （ここまでやってきたとおり、Coqでの「単体テスト」とは[Example]で書かれた、[reflexivity]だけで証明できるものです。）
        2進数をインクリメントして1進数に変換したものは、1進数に変換して1加えたものと一致するということに注意してください。 *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_binary : option (nat*string) := None.
(** [] *)

(* Wed Jan 9 12:02:44 EST 2019 *)
