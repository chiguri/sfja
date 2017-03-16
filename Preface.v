(*
(** * Preface *)
*)
(** * 前書き *)

(* ###################################################################### *)
(*
(** * Welcome *)
*)
(** * ようこそ *)

(*
(** This electronic book is a course on _Software Foundations_, the
    mathematical underpinnings of reliable software.  Topics include
    basic concepts of logic, computer-assisted theorem proving, the
    Coq proof assistant, functional programming, operational
    semantics, Hoare logic, and static type systems.  The exposition
    is intended for a broad range of readers, from advanced
    undergraduates to PhD students and researchers.  No specific
    background in logic or programming languages is assumed, though a
    degree of mathematical maturity will be helpful.

    The principal novelty of the course is that it is one hundred per
    cent formalized and machine-checked: the entire text is literally
    a script for Coq.  It is intended to be read alongside an
    interactive session with Coq.  All the details in the text are
    fully formalized in Coq, and the exercises are designed to be
    worked using Coq.

    The files are organized into a sequence of core chapters, covering
    about one semester's worth of material and organized into a
    coherent linear narrative, plus a number of "appendices" covering
    additional topics.  All the core chapters are suitable for both
    upper-level undergraduate and graduate students. *)
*)
(** この資料は「ソフトウェアの基礎」という、高信頼ソフトウェアの数学的基礎に関するものです。
    この講義では、Coq上で関数プログラミング、論理、演算の意味論、ラムダ計算、静的型システムの基礎を学ぶことができます。
    解説は、学部生から博士課程の学生や研究者に至るまで、広範囲の読者を想定しています。
    論理学やプログラミング言語についての知識は仮定しませんが、ある程度の数学的素養は理解に有用です。

    このコースの特徴は、取り扱う内容がすべて形式化されて、さらに機械によって確かめられることです。
    これは、教材のテキストがCoqのスクリプトファイルそのものとなっていることで実現されています。
    このコースでは、Coqのインタラクティブモードを使って、ソースを1行1行読み進めていきます。
    この資料の細部まですべてCoqで形式化され、また演習もCoqを使って行うように設計されています。

    この資料は、主要部とそれ以外の"付録"からなります。
    主要部は1学期分の講義として十分な量が、順序だって記述されています。
    また、付録部分は主要部に関連する項目をカバーしています。
    主要部は学部後半の学生や院生にちょうどいい内容でしょう。 *)


(* ###################################################################### *)
(*
(** * Overview *)
*)
(** * 概要 *)

(*
(** Building reliable software is hard.  The scale and complexity of
    modern systems, the number of people involved in building them,
    and the range of demands placed on them make it extremely
    difficult even to build software that is more or less correct,
    much less to get it 100%% correct.  At the same time, the
    increasing degree to which information processing is woven into
    every aspect of society continually amplifies the cost of bugs and
    insecurities.

    Computer scientists and software engineers have responded to these
    challenges by developing a whole host of techniques for improving
    software reliability, ranging from recommendations about managing
    software projects and organizing programming teams (e.g., extreme
    programming) to design philosophies for libraries (e.g.,
    model-view-controller, publish-subscribe, etc.) and programming
    languages (e.g., object-oriented programming, aspect-oriented
    programming, functional programming, ...) and to mathematical
    techniques for specifying and reasoning about properties of
    software and tools for helping validate these properties.

    The present course is focused on this last set of techniques.  The
    text weaves together five conceptual threads:

    (1) basic tools from _logic_ for making and justifying precise
        claims about programs;

    (2) the use of _proof assistants_ to construct rigorous logical
        arguments;

    (3) the idea of _functional programming_, both as a method of
        programming and as a bridge between programming and logic;

    (4) formal techniques for _reasoning about the properties of
        specific programs_ (e.g., the fact that a loop terminates on
        all inputs, or that a sorting function or a compiler obeys a
        particular specification); and

    (5) the use of _type systems_ for establishing well-behavedness
        guarantees for _all_ programs in a given programming
        language (e.g., the fact that well-typed Java programs cannot
        be subverted at runtime).

    Each of these topics is easily rich enough to fill a whole course
    in its own right; taking all of them together naturally means that
    much will be left unsaid.  But we hope readers will find that the
    themes illuminate and amplify each other in useful ways, and that
    bringing them together creates a foundation from which it will be
    easy to dig into any of them more deeply.  Some suggestions for
    further reading can be found in the [Postscript] chapter. *)
*)
(** 信頼性の高いソフトウェアを構築することは非常に困難です。
    現代のシステムは大きく複雑に、関係者の数は膨大に、さらには要求も多岐にわたっています。
    これらが原因で、100%%正しいかどうか以前に、そもそもソフトウェアを構築すること自体が難しくなっています。
    しかし同時に、情報処理が社会の至る所に利用されることで、バグや不具合によるコストが増大し続けています。
 
    計算機科学者やソフトウェア技術者は、これらに対して、ソフトウェアの信頼性を向上させる技術や、プロジェクト管理やチーム構築の手法（例：extreme programming）、ライブラリの設計思想（例：モデル-ビュー-コントローラ、出版-購読(publish-subscribe)など）、プログラミング言語（例：オブジェクト指向プログラミング、アスペクト指向プログラミング、関数型プログラミングなど）、ソフトウェアの性質を表現する数学的手法、性質を確かめるためのツールを開発・提案することで対応してきました。
 
    本講義ではこれらのうち最後の技術について学びます。
    資料は以下の5つのコンセプトのもと作られています：
 
    (1) 「論理」を基にして、プログラムに対する正確な言明を記述し、確かめる。
 
    (2) 「証明支援系」により、厳格で論理的な主張を構成する。
 
    (3) 「関数型プログラミング」によって、プログラミングを行い、さらに論理との橋渡しを行う。
 
    (4) 「プログラムの性質の推論」のための形式手法を用いる。
 
    (5) 「型システム」を通じて、適切な挙動を設定し、あるプログラミング言語で書かれた「すべての」プログラムに対して、うまく動くことを保証する。
        （例：型が付くJavaのプログラムは実行時にクラッシュしたりしない）
 
    これらの内容は、それぞれが単体で一つの講義を簡単に組めるくらい、話題が豊富です。
    これらをすべて合わせて説明するため、かなりの部分を言及しないままになります。
    もし皆さんが、これらのテーマ同士の関係によって理解を深め、さらにより深く掘り進められる基礎を成していることに気づいてくれれば幸いです。
    この講義以降に読むとよい本については、[Postscript]の章に記載しています。 *)

(*
(** ** Logic *)
*)
(** ** 論理 *)

(*
(** Logic is the field of study whose subject matter is _proofs_ --
    unassailable arguments for the truth of particular propositions.
    Volumes have been written about the central role of logic in
    computer science.  Manna and Waldinger called it "the calculus of
    computer science," while Halpern et al.'s paper _On the Unusual
    Effectiveness of Logic in Computer Science_ catalogs scores of
    ways in which logic offers critical tools and insights.  Indeed,
    they observe that "As a matter of fact, logic has turned out to be
    significiantly more effective in computer science than it has been
    in mathematics.  This is quite remarkable, especially since much
    of the impetus for the development of logic during the past one
    hundred years came from mathematics."

    In particular, the fundamental notion of inductive proofs is
    ubiquitous in all of computer science.  You have surely seen them
    before, in contexts from discrete math to analysis of algorithms,
    but in this course we will examine them much more deeply than you
    have probably done so far. *)
*)
(** 論理とは、「証明」を対象とした学問領域です。
    ここでいう証明とは、特定の命題が真実であることの、反証しようのない根拠を指します。
    計算機科学において論理が果たす役割に関しては、非常にたくさんの文献で述べられています。
    MonnaとWaldingerは、この役割を"計算機科学における微分"と呼び、またHalpernらの論文「On the Unusual Effectiveness of Logic in Computer Science」では論理から出てきたいくつもの重要な道具や洞察が紹介されています。
    この論文にはこうあります。
    "実際のところ、論理は数学においてよりはるかに計算機科学において有効活用されている。
     特筆すべきなのは、このことが、論理が数学から生まれて100年における、論理の発展の大きな推進剤になっていることである。"
 
    特に、帰納法の原理は計算機科学の世界においてあまねく存在します。
    離散数学やアルゴリズムの解析において見てきたと思いますが、このコースではこれまでよりも深くまで利用することになるでしょう。 *)
(* 訳注：calculusをここでは微分と訳しているが、計算機科学では一般に計算と訳す。「基礎を成すもの」のニュアンスなのか、それとも素直に「微分」なのか、元の文書を見ないことには分からないが、そもそも元の文書がなにかもよく分からない。本があるようだが、中身が見られないので現状放置。 *)

(*
(** ** Proof Assistants *)
*)
(** ** 証明支援系 *)

(*
(** The flow of ideas between logic and computer science has not been
    in just one direction: CS has also made important contributions to
    logic.  One of these has been the development of software tools
    for helping construct proofs of logical propositions.  These tools
    fall into two broad categories:

       - _Automated theorem provers_ provide "push-button" operation:
         you give them a proposition and they return either _true_,
         _false_, or _ran out of time_.  Although their capabilities
         are limited to fairly specific sorts of reasoning, they have
         matured tremendously in recent years and are used now in a
         huge variety of settings.  Examples of such tools include SAT
         solvers, SMT solvers, and model checkers.

       - _Proof assistants_ are hybrid tools that automate the more
         routine aspects of building proofs while depending on human
         guidance for more difficult aspects.  Widely used proof
         assistants include Isabelle, Agda, Twelf, ACL2, PVS, and Coq,
         among many others.

    This course is based around Coq, a proof assistant that has been
    under development since 1983 at a number of French research labs
    and universities.  Coq provides a rich environment for interactive
    development of machine-checked formal reasoning.  The kernel of
    the Coq system is a simple proof-checker which guarantees that
    only correct deduction steps are performed.  On top of this
    kernel, the Coq environment provides high-level facilities for
    proof development, including powerful tactics for constructing
    complex proofs semi-automatically, and a large library of common
    definitions and lemmas.

    Coq has been a critical enabler for a huge variety of work across
    computer science and mathematics:

    - As a _platform for modeling programming languages_, it has become
      a standard tool for researchers who need to describe and reason
      about complex language definitions.  It has been used, for
      example, to check the security of the JavaCard platform,
      obtaining the highest level of common criteria certification,
      and for formal specifications of the x86 and LLVM instruction
      sets.

    - As an _environment for developing formally certified software_,
      Coq has been used to build CompCert, a fully-verified optimizing
      compiler for C, for proving the correctness of subtle algorithms
      involving floating point numbers, and as the basis for
      Certicrypt, an environment for reasoning about the security of
      cryptographic algorithms.

    - As a _realistic environment for programming with dependent
      types_, it has inspired numerous innovations.  For example, the
      Ynot project at Harvard embeds "relational Hoare reasoning" (an
      extension of the _Hoare Logic_ we will see later in this course)
      in Coq.

    - As a _proof assistant for higher-order logic_, it has been used
      to validate a number of important results in mathematics.  For
      example, its ability to include complex computations inside
      proofs made it possible to develop the first formally verified
      proof of the 4-color theorem.  This proof had previously been
      controversial among mathematicians because part of it included
      checking a large number of configurations using a program. In
      the Coq formalization, everything is checked, including the
      correctness of the computational part.  More recently, an even
      more massive effort led to a Coq formalization of the
      Feit-Thompson Theorem -- the first major step in the
      classification of finite simple groups.

   By the way, in case you're wondering about the name, here's what
   the official Coq web site says: "Some French computer scientists
   have a tradition of naming their software as animal species: Caml,
   Elan, Foc or Phox are examples of this tacit convention. In French,
   'coq' means rooster, and it sounds like the initials of the
   Calculus of Constructions (CoC) on which it is based."  The rooster
   is also the national symbol of France, and "Coq" are the first
   three letters of the name of Thierry Coquand, one of Coq's early
   developers. *)
*)
(** 論理と計算機科学の間の影響は一方方向ではありません。
    計算機科学もまた論理の発展に寄与してきました。
    そのうちの一つが、論理命題に対する証明の構築を助けるソフトウェアの開発です。
    これらのソフトウェアは大きく二種類に分類されます。
 
       - 「自動定理証明器」は"開始ボタン"によって証明の構築を行います。
         証明器に命題を与えると、証明器はその命題について「真」か「偽」か「時間切れ」を返します。
         証明器の能力が発揮できる範囲は限定されてはいますが、近年急速に発達し、様々な用途に使われています。
         例としては、SATソルバー、SMTソルバー、モデル検査器が挙げられます。
 
       - 「証明支援系」は単純な操作を自動化し、難しい部分を人間が指示するというハイブリッドなツールです。
         広く使われている証明支援系には、Isabelle、Agda、Twelf、ACL2、PVS、Coqなどがあります。
 
    このコースは、Coqを用いて進めていきます。
    Coqは1983年から、フランスの研究機関や大学で開発されている証明支援系です。
    Coqの提供する機能は、機械的に検証された形式推論の対話的な開発に有効です。
    Coqの核(kernel)は、演繹が正しく進められているかを確かめるだけの、シンプルな証明検査器です。
    Coqは、この核を基礎として、証明の構築に便利な機能を提供しています。
    この機能には、例えば複雑な証明を半自動で生成するタクティクや、よく使われる定理や補題のライブラリなどがあります。
 
    Coqは計算機科学と数学を通じて、多くのことを実現してきました。
 
    - 「プログラミング言語をモデル化する基盤」として、複雑な言語の記述と推論に用いられています。
      例えばJavaCardプラットフォームにおいて、Common Criteria Certificationの最高レベルを得るためにセキュリティの検査に利用されたり、x86やLLVMの命令セットに対する形式仕様を与えたりしています。
      （訳注：調べてみたが、JavaCardに関しては若干誇張が入っている気がする。総合評価は7段階あるうちの5+、ただし脆弱性評価は確かに最高ランク。）
      （http://www.commoncriteriaportal.org/products/ や http://www.commoncriteriaportal.org/cc/ のPart.3を参照のこと。）
 
    - 「証明付きソフトウェアの開発環境」として、CompCertという最適化付きCのコンパイラの開発や、浮動小数点数を使った繊細なアルゴリズムの正しさの証明、また暗号化アルゴリズムのセキュリティ検査の環境Certicryptoの基盤として使われています。
 
    - 「現実的な依存型プログラミングの環境」として、非常に多くの革新を起こしています。
      例えば、ハーバード大学で行われたYnotプロジェクトでは"関係ホーア推論(relational Hoare reasoning)"（このコースで説明する「ホーア論理」の拡張）をCoqに埋め込んでいます。
 
    - 「高階論理の証明支援系」として、いくつもの数学における重要な性質を検証しました。
      例えば、証明に複雑な計算を組み込めたので、四色定理(4-color theorem)の最初の形式検証された証明作ることができました。
      この証明は一時議論を呼びました。
      というのも、この証明にはプログラムを使った大量の背景の検証が含まれていたためです。
      Coqによる検証では、計算部分を含む全てのものが検査されます。
      最近では、Feit-Thompsonの定理のCoqによる定式化が行われました。
      これは、有限単純群の分類における第一歩です。
 
   ところで、このソフトウェア"Coq"という名前がどこから来たか疑問に思うかもしれません。
   オフィシャルのwebサイトでは次のように説明されています。
   「フランスの計算機科学者には、作ったソフトに動物の名前を付ける伝統があります。
     例えばCaml（訳注：ラクダ・英語のcamel）、Elan（訳注：ヘラジカ）、Foc（訳注：アザラシ・フランス語のphoqueと音が同じ）、Phox（訳注：キツネ・英語のfox）などがこの暗黙の了解に従っています。
     フランス語で'coq'は雄鶏を意味し、また音がCoqの基礎であるCalculus of Constructionsの頭文字(CoC)と似ています。」
   なお、雄鶏はフランスのシンボルでもありますし、また"Coq"はThierry CoquandというCoqの初期の開発者の名前の三文字でもあります。 *)

(*
(** ** Functional Programming *)
*)
(** ** 関数型プログラミング *)

(*
(** The term _functional programming_ refers both to a collection of
    programming idioms that can be used in almost any programming
    language and to a family of programming languages designed to
    emphasize these idioms, including Haskell, OCaml, Standard ML,
    F##, Scala, Scheme, Racket, Common Lisp, Clojure, Erlang, and Coq.

    Functional programming has been developed over many decades --
    indeed, its roots go back to Church's lambda-calculus, which was
    invented in the 1930s before the era of the computer began!  But
    since the early '90s it has enjoyed a surge of interest among
    industrial engineers and language designers, playing a key role in
    high-value systems at companies like Jane St. Capital, Microsoft,
    Facebook, and Ericsson.

    The most basic tenet of functional programming is that, as much as
    possible, computation should be _pure_, in the sense that the only
    effect of execution should be to produce a result: the computation
    should be free from _side effects_ such as I/O, assignments to
    mutable variables, redirecting pointers, etc.  For example,
    whereas an _imperative_ sorting function might take a list of
    numbers and rearrange its pointers to put the list in order, a
    pure sorting function would take the original list and return a
    _new_ list containing the same numbers in sorted order.

    One significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about how that
    structure is being shared and whether a change by one part of the
    program might break an invariant that another part of the program
    relies on.  These considerations are particularly critical in
    concurrent programs, where every piece of mutable state that is
    shared between threads is a potential source of pernicious bugs.
    Indeed, a large part of the recent interest in functional
    programming in industry is due to its simple behavior in the
    presence of concurrency.

    Another reason for the current excitement about functional
    programming is related to the first: functional programs are often
    much easier to parallelize than their imperative counterparts.  If
    running a computation has no effect other than producing a result,
    then it does not matter _where_ it is run.  Similarly, if a data
    structure is never modified destructively, then it can be copied
    freely, across cores or across the network.  Indeed, the MapReduce
    idiom that lies at the heart of massively distributed query
    processors like Hadoop and is used by Google to index the entire
    web is a classic example of functional programming.

    For purposes of this course, functional programming has yet
    another significant attraction: it serves as a bridge between
    logic and computer science.  Indeed, Coq itself can be viewed as a
    combination of a small but extremely expressive functional
    programming language plus with a set of tools for stating and
    proving logical assertions.  Moreover, when we come to look more
    closely, we find that these two sides of Coq are actually aspects
    of the very same underlying machinery -- i.e., _proofs are
    programs_.  *)
*)
(** 「関数型プログラミング」という語には、どの言語でも使えるプログラミング手法としての用法と、これらの手法に重点を置いたプログラミング言語としての用法があります。
    なお、後者における言語としては、HaskellやOCaml、Standard ML、F##、Scala、Scheme、Racket、Common Lisp、Clojure、Erlang、そしてCoqが挙げられます。
 
    関数型プログラミングは数十年にわたって用いられてきました。
    そのルーツは、1930年代初頭、コンピュータが開発されるより前に、チャーチが提案したラムダ計算にさかのぼります。
    しかし、1990年初めから、エンジニアや言語設計者の関心を引き、またJane St. CapitalやMicrosoft、Facebook、Ericssonなどの企業で重要な役割を担っています。
 
    関数型プログラミングの基本となる信念は、可能な限り計算は「純粋(pure)」であるべき、というものです。
    純粋であるとは、その実行が結果となる値を返すだけ、ということです。
    つまり、計算には入出力や変数への代入、ポインタの書き換えなどといった「副作用(side effect)」を含まないようにすべき、ということを意味します。
    例えば、「命令的(imperative)」ソートでは、受け取ったリスト内のポインタを張り替えてソートするでしょうが、純粋なソートでは受け取ったリストとは違う新しいリストをソートした上で返すでしょう。
 
    One significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about how that
    structure is being shared and whether a change by one part of the
    program might break an invariant that another part of the program
    relies on.  These considerations are particularly critical in
    concurrent programs, where every piece of mutable state that is
    shared between threads is a potential source of pernicious bugs.
    Indeed, a large part of the recent interest in functional
    programming in industry is due to its simple behavior in the
    presence of concurrency.
 
    Another reason for the current excitement about functional
    programming is related to the first: functional programs are often
    much easier to parallelize than their imperative counterparts.  If
    running a computation has no effect other than producing a result,
    then it does not matter _where_ it is run.  Similarly, if a data
    structure is never modified destructively, then it can be copied
    freely, across cores or across the network.  Indeed, the MapReduce
    idiom that lies at the heart of massively distributed query
    processors like Hadoop and is used by Google to index the entire
    web is a classic example of functional programming.
  
    For purposes of this course, functional programming has yet
    another significant attraction: it serves as a bridge between
    logic and computer science.  Indeed, Coq itself can be viewed as a
    combination of a small but extremely expressive functional
    programming language plus with a set of tools for stating and
    proving logical assertions.  Moreover, when we come to look more
    closely, we find that these two sides of Coq are actually aspects
    of the very same underlying machinery -- i.e., _proofs are
    programs_.  *)

(** ** Program Verification *)

(** The first third of the book is devoted to developing the
    conceptual framework of logic and functional programming and
    gaining enough fluency with Coq to use it for modeling and
    reasoning about nontrivial artifacts.  From this point on, we
    increasingly turn our attention to two broad topics of critical
    importance to the enterprise of building reliable software (and
    hardware): techniques for proving specific properties of
    particular _programs_ and for proving general properties of whole
    programming _languages_.

    For both of these, the first thing we need is a way of
    representing programs as mathematical objects, so we can talk
    about them precisely, and ways of describing their behavior in
    terms of mathematical functions or relations.  Our tools for these
    tasks are _abstract syntax_ and _operational semantics_, a method
    of specifying the behavior of programs by writing abstract
    interpreters.  At the beginning, we work with operational
    semantics in the so-called "big-step" style, which leads to
    somewhat simpler and more readable definitions, in those cases
    where it is applicable.  Later on, we switch to a more detailed
    "small-step" style, which helps make some useful distinctions
    between different sorts of "nonterminating" program behaviors and
    which is applicable to a broader range of language features,
    including concurrency.

    The first programming language we consider in detail is _Imp_, a
    tiny toy language capturing the core features of conventional
    imperative programming: variables, assignment, conditionals, and
    loops. We study two different ways of reasoning about the
    properties of Imp programs.

    First, we consider what it means to say that two Imp programs are
    _equivalent_ in the sense that they give the same behaviors for
    all initial memories.  This notion of equivalence then becomes a
    criterion for judging the correctness of _metaprograms_ --
    programs that manipulate other programs, such as compilers and
    optimizers.  We build a simple optimizer for Imp and prove that it
    is correct.

    Second, we develop a methodology for proving that Imp programs
    satisfy formal specifications of their behavior.  We introduce the
    notion of _Hoare triples_ -- Imp programs annotated with pre- and
    post-conditions describing what should be true about the memory in
    which they are started and what they promise to make true about
    the memory in which they terminate -- and the reasoning principles
    of _Hoare Logic_, a "domain-specific logic" specialized for
    convenient compositional reasoning about imperative programs, with
    concepts like "loop invariant" built in.

    This part of the course is intended to give readers a taste of the
    key ideas and mathematical tools used for a wide variety of
    real-world software and hardware verification tasks.
*)

(** ** Type Systems *)

(** Our final major topic, covering the last third of the course, is
    _type systems_, a powerful set of tools for establishing
    properties of _all_ programs in a given language.

    Type systems are the best established and most popular example of
    a highly successful class of formal verification techniques known
    as _lightweight formal methods_.  These are reasoning techniques
    of modest power -- modest enough that automatic checkers can be
    built into compilers, linkers, or program analyzers and thus be
    applied even by programmers unfamiliar with the underlying
    theories.  (Other examples of lightweight formal methods include
    hardware and software model checkers, contract checkers, and
    run-time property monitoring techniques for detecting when some
    component of a system is not behaving according to specification).

    This topic brings us full circle: the language whose properties we
    study in this part, called the _simply typed lambda-calculus_, is
    essentially a simplified model of the core of Coq itself!

*)

(* ###################################################################### *)
(*
(** * Practicalities *)
*)
(** * 実際の学習について *)

(* ###################################################################### *)
(*
(** ** Chapter Dependencies *)
*)
(** ** 章間の依存関係 *)

(*
(** A diagram of the dependencies between chapters and some suggested
    paths through the material can be found in the file [deps.html]. *)
*)
(** 章と章の間の依存関係をまとめた図と、学習教材へのパスを、[deps.html]にまとめてあります。 *)

(* ###################################################################### *)
(*
(** ** System Requirements *)
*)
(** ** 学習に必要なもの *)

(*
(** Coq runs on Windows, Linux, and OS X.  You will need:

       - A current installation of Coq, available from the Coq home
         page.  Everything should work with version 8.4.

       - An IDE for interacting with Coq.  Currently, there are two
         choices:

           - Proof General is an Emacs-based IDE.  It tends to be
             preferred by users who are already comfortable with
             Emacs.  It requires a separate installation (google
             "Proof General").

           - CoqIDE is a simpler stand-alone IDE.  It is distributed
             with Coq, but on some platforms compiling it involves
             installing additional packages for GUI libraries and
             such. *)
*)
(** Coqは、Windowsと多くのUNIX変種（LinuxやMacOSを含む）で動きます。具体的には
 
       - Coqホームページにある最新版のCoq。
         全てのサンプルソースはバージョン8.4でコンパイルできることが確認されています。
 
       - Coqを対話的に操作するIDE。現在、以下の二つから選択できます。
 
           - ProofGeneralは、Emacs上に作られたIDEです。
             すでにEmacsに慣れている人向けのものです。
             Coqとは別にインストールする必要があります。
             （詳しくはgoogleで"ProofGeneral"を検索してください）
 
           - CoqIDEは、スタンドアロンで動作するシンプルなIDEです。
             Coqと一緒に配布されています。
             しかしいくつかのプラットホームではGUIライブラリなどの追加パッケージをインストールする必要があります。 *)

(* ###################################################################### *)
(*
(** ** Exercises *)
*)
(** * 練習問題について *)

(*
(** Each chapter includes numerous exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

       - One star: easy exercises that underscore points in the text
         and that, for most readers, should take only a minute or two.
         Get in the habit of working these as you reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (ten
         minutes to half an hour).

       - Four and five stars: more difficult exercises (half an hour
         and up).

    Also, some exercises are marked "advanced", and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge (and, in return, a deeper contact with the material).

    _Please do not post solutions to the exercises in public places_:
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  The authors especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.
*)
*)
(** この資料の各章には、たくさんの練習問題がついています。
    練習問題についている"スターレーティング"には、以下のような意味があります。
 
       - ★：多くの読者が1～2分でできる簡単な問題。
         読者は、この問題に取り組んで、このレベルの問題に慣れておくべきです。
 
       - ★★：　素直で簡単な問題（5～10分でできるでしょう）
 
       - ★★★：　少し考えないといけない問題（10～30分ほどかかるでしょう）
 
       - ★★★★（または★★★★★）：　さらに難しい問題（30分以上）
 
    また、いくつかの練習問題には"advanced"や"optional"とついています。
    これらの付いていない問題だけで広範囲の内容を学習できます。
    "optional"な練習問題は重要な概念へのさらなる演習と、また主題とは少し異なる内容への導入となります。
    "advanced"な練習問題は、さらに難しい問題がほしい読者へのものです。
    結果として、この教材のより深い理解が得られるでしょう。
 
    お願いですので、この教材の練習問題の解答を皆に見える場所には置かないでください！
    ソフトウェアの基礎は自学用と講義用の両側面があります。
    講義の視点では、解答に安易に接することができるのは有効ではありませんし、またこれらの問題は単位認定に関わる課題となります。
    これらの解答を、検索エンジンによって見つけられる場所に置いたりしないでください！
*)

(* ###################################################################### *)
(*
(** ** Downloading the Coq Files *)
*)
(** ** 教材となるCoqファイルの入手方法 *)

(*
(** A tar file containing the full sources for the "release version"
    of these notes (as a collection of Coq scripts and HTML files) is
    available here:
<<
        http://www.cis.upenn.edu/~bcpierce/sf   
>>
    If you are using the notes as part of a class, you may be given
    access to a locally extended version of the files, which you
    should use instead of the release version.
*)
*)
(** この教材のリリース版のソース（CoqスクリプトとHTMLファイル）をtarで固めたものが、以下のURLで取得できます。
<<
        http://www.cis.upenn.edu/~bcpierce/sf 
>>
    この資料の一部だけを使用したい場合は、tarファイルとなっているリリース版を展開して使用してください。
*)

(* ###################################################################### *)
(*
(** * Note for Instructors *)
*)
(** * 教育関係者へ *)

(*
(** If you intend to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!

    Please send an email to Benjamin Pierce describing yourself and
    how you would like to use the materials, and including the result
    of doing "htpasswd -s -n NAME", where NAME is your preferred user
    name.  We'll set you up with read/write access to our subversion
    repository and developers' mailing list; in the repository you'll
    find a [README] with further instructions. *)
*)
(** この資料を自分のコースで使おうと思った場合、ほぼまちがいなくあなたは書き直したり、追加したりしたいところが出てくるでしょう。
    そういった貢献は大歓迎です。
 
    ぜひBenjamin Pierceまでemailをください。
    そうすれば、あなた用のsubversionのリポジトリとメーリングリストのアカウントを用意します。
    リポジトリには、READMEファイルがありますので、次にどうすべきかはそれを参照してください。 *)

(* ###################################################################### *)
(*
(** * Translations *)
*)
(** * 翻訳について *)

(*
(** Thanks to the efforts of a team of volunteer translators, _Software 
    Foundations_ can now be enjoyed in Japanese at [http://proofcafe.org/sf]
*)
*)
(** ボランティアによる翻訳のおかげで、「ソフトウェアの基礎」は日本語で読めます。
    [http://proofcafe.org/sf]
 *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)

