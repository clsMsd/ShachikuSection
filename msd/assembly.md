# アセンブリ言語入門
世はまさに大低レイヤー時代ということで、アセンブリ言語について紹介する。  

アセンブリ言語はCPUアーキテクチャやOS等によっていろいろ違いがあるが、  
今回は基本的にx86-64、Ubuntu(WSL)、gccの組み合わせで話を進める。  

## 基礎知識
C言語のようなVMとか使わずにネイティブで動くコンパイル言語では、プログラムは次の段階を経て生成される。  
  
C言語のコード  
↓(コンパイル)  
アセンブリコード  
↓(アセンブル)  
オブジェクトファイル  
↓(静的リンク)  
実行可能ファイル  

### リンクについて
コンパイラとアセンブラが何をやっているかは分かっている人が多いが、リンカが何をやっているのかが
分かってない人がけっこういる(数週間前の自分含む)ので、簡単に説明する。
C言語では分割コンパイルができるので、ソースコードAにFuncAという関数が定義されているときに、
(ソースコードAの中のFuncAの定義を参照すること無しに)ソースコードAのコンパイル結果である
オブジェクトファイルとFuncAの宣言だけでFuncAを呼び出すことが可能である。

例えば
```c :a.c
int FuncA() {
   return 1;
}
```
```c :main.c
#include<stdio.h>
int FuncA();
int main() {
   printf("%d\n", FuncA());
   return 0;
}
```
という2つのソースコードが合った場合、`a.c`と`main.c`を別々にコンパイルしてオブジェクトファイルを作った後に、
それらのオブジェクトファイルをリンクして実行ファイルを作ることができる
(というか普通はコンパイラはそうやって実行ファイルを作る)。

これはどういう仕組みで成り立っているかというと、C言語での関数定義がオブジェクトファイル中のどの部分に対応するのか
という情報(シンボルテーブル)がオブジェクトファイルに書かれており、リンカはシンボルテーブルを見てどの関数の定義が
どのオブジェクトファイルのどの位置にあるかということを調べて、それらを一つにまとめた実行ファイルを出力してくれる
(シンボルテーブルを探しても関数の定義が見つからない場合はリンクに失敗する)。

リンクはコンパイル直後に実行される(静的リンク)場合もあれば、コンパイル直後はリンクを行わず実行の直前にリンクする(動的リンク)という場合もある。
静的リンクは実行ファイルにライブラリが全て含まれるため実行ファイルのサイズが肥大化する。
動的リンクは共有ライブラリをリンクすることで実行ファイルのサイズを減らすことができるが、実行直前になってライブラリが見つからないと
プログラムがおもむろに実行に失敗するということになる。
また、動的リンクの場合は後からライブラリを差し替えることができるというメリットもある。

## 使う主なコマンド
`gcc`コマンドは単なるコンパイラではなくコンパイルドライバなので、基本的に入力ファイルに応じて自動的にいい感じに処理してくれる。  
(アセンブラのソースファイルが渡されると空気を読んでアセンブルとリンクまでして実行ファイルを作ってくれるし、  
未リンクのオブジェクトファイルが渡されると空気を読んでいろいろリンクして実行ファイルを作ってくれる)。  

### コンパイル
`-S`オプションでコンパイルのみを行う。  
`gcc -S sample.c` (AT&T記法で出力)  
`gcc -S -masm=intel sample.c` (Intel記法で出力)  
デバック用のシンボルなどの無駄な情報を除去したい場合は`-fno-asynchronous-unwind-tables`オプションを付ける。  
32bit環境向けのアセンブラを出力したい場合は`-m32`オプションを付ける。  

### アセンブル
GNUアセンブラ(as)の場合:  
`as -o sample.o sample.s`  

nasmの場合:  
`nasm -g -f elf64 -o sample.o sample.asm` (64bit)  
`nasm -g -f elf -o sample.o sample.asm` (32bit)   

コンパイル+アセンブルまでするときは`gcc -c`でよい。

### リンク
`gcc -o sample sample.o`  

ldを直接使ってリンクする場合:  
`ld sample.o -o sample`  
ただし、ldを直接呼び出した場合はスタートアップルーチンがリンクされない。  

アセンブラ+リンクまでするときは単に`gcc`でよい。

### ディアセンブル
`objdump -d sample.o`

intel記法のアセンブリにディスアセンブルするとき
`objdump -d -M intel sample.o`
<!-- 
TODO:
readelf, nm 等のコマンドについて書く -->

## x86-64のレジスタについて
x86-64アーキテクチャには64bitの16本の汎用レジスタ(rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp, r8 ~ r15)、  
32bitのEFLAGSレジスタ、6つのセグメントレジスタ(今はほぼ使わない)、  
命令ポインタレジスタ(rip)、16本のSSE用レジスタ(xmm0 ~ xmm16)がある。  
rax ~ rsp までのレジスタは32bit のレジスタ(eax, ebx ... esp)として使うことも、16bitのレジスタ(ax, bx ... sp)として使うこともできる。  
さらに、rax, rbx, rcx, rdxの4つのレジスタは、8つの 8bitのレジスタとして使うこともできる。  
(これはもともとx86系の最初のCPUが8bitであり、そこから時代を経るごとに互換性を維持したままレジスタ長を伸ばしていったのでこうなっている)。  
SSEとはいわゆるベクトル演算命令で、複数のレジスタに対して同じ計算を一度に実行できる機能である。x86-64 CPUにはこれが入っている。  
整数演算は普通の汎用レジスタとSSEレジスタの両方でできるが、浮動少数点数演算はSSEレジスタでしかできない。  

この辺の事情は次のような歴史的経緯による
```
もともとCPUは整数演算専用のプロセッサで、浮動少数点数の計算が必要な場合はソフトウェアエミュレーションで計算する(遅い)か、  
浮動少数点数計算専用のプロセッサ(FPU)を買ってきてPCに取り付けるかしていた。  
↓  
やっぱりFPUあった方が便利だよねということで、Intel486からFPUがCPUに内蔵されるようになった。  
↓  
内蔵したはいいものの用途によってはFPUは殆ど使わないので、初代Pentium(の後期型)では遊んでいるFPUのレジスタを整数のSIMD演算にも使えるようにした(MMX)。  
↓  
AMDが浮動少数点数SIMD演算(3DNow!)に対応したCPUを発売。  
↓  
Intelも対抗して、浮動少数点数SIMD演算機能(SSE)を搭載する(Pentium III)  
↓  
SSEが拡張されまくって今に至る（SSE → SSE2 → SSE3 → SSE4 → AVX → AVX2 → AVX-512)  
```
## 文法について
アセンブラの文法には大きく分けてAT&T記法とIntel記法の2つが存在する。  
例えばgccで使用しているGNU AS(GAS)というアセンブラではデフォルトではAT&T記法、NASMというアセンブラではデフォルトではIntel記法を使っている。  
これらはアセンブル時に明示的に指定することで使用する記法を切り替えたり、AT&T記法のアセンブラコードをIntel記法に変換したり等ができる。  
今回はgccを多用するので、GASで使用しているAT&T記法を使って解説する。  
  
また、基本文法は同じであってもターゲットアーキテクチャが違えば使用できる命令は異なるので、アセンブラコードも異なるものになる。  

### AT&T記法
gnuのコンパイラが出力するアセンブリコードや、gccがデフォルトで使うアセンブラ(as)は(デフォルトでは)こっち。  
ただし、`.intel_syntax`ディレクティブを付けるとIntel記法に対応できる。  

実際にgccでコンパイルして生成されるアセンブラを見てみよう。  
次のような何もしないCプログラムを`gcc -S -fno-asynchronous-unwind-tables`でコンパイルすると、次のアセンブラが出力される。
```c
int main() {
   return 0;
}
```
```s
	.file	"nop.c"
	.text
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movl	$0, %eax
	popq	%rbp
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```
上のコードのうち、`.`で始まるものはコンパイラがリンクやデバッグやアセンブル時の  
メタ情報出力のため利用する疑似命令(ディレクティブ)であり、CPUの命令に対応するものではない。  
CPUの命令に対応するのは`pushq %rbp`や`movq %rsp, %rbp`のような命令列である。  
各行の命令列のはじめのキーワードをオペコードといい、実行する命令を指定する。  
2番め及び3番目のキーワードをオペランドといい、命令を実行する対象のデータを指定する。  

`$`記号は即値(リテラル)を、`%`記号はレジスタを意味する。  
オペランドの並びは`opecode src dest`の順番である。  
例えば、`movl	$0, %eax`というコードは`eax`レジスタに`0`を代入せよという意味を表す。  

次にC言語でよくあるHello Worldのコードをコンパイルした結果を見てみよう。
```c
#include<stdio.h>
int main() {
   printf("Hello World!!!\n");
   return 0;
}
```
```s
	.file	"hello.c"
	.text
	.section	.rodata
.LC0:
	.string	"Hello World\n"
	.text
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	leaq	.LC0(%rip), %rax
	movq	%rax, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	puts@PLT
	movl	$0, %eax
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```
コード中に`.LC0:`と`main:`という文字列がある。  
これらはラベルといい、アセンブラコード中にラベルが存在する位置のアドレスを表す。  
基本的にC言語の関数はそのままアセンブラコードのラベルに変換される。  

また`(%rip)`のような表記があるが、これは「`rip`レジスタの値をアドレスとするメモリ領域」を表す(間接参照)。  
例えば`movl ($1000), %rax`ならメモリの1000番地の値をraxレジスタに代入する  
`movl (%rbx), %rax`ならメモリの「rbxレジスタの値」番地の値をraxレジスタに代入する  
`movl 0xc(%rbx), %rax`ならメモリの「rbxレジスタの値 + 0xc」番地の値をraxレジスタに代入する  
といったことができる。  

コメントには`/* */`又は`#`を使う。  

#### 主なディレクティブ

##### セクションの指定
.text: プログラムが書かれている領域  
.data: 初期値を持つstaticな変数を置く領域(プログラム起動時に明示的に初期値が書き込まれる領域)  
.comm: 初期値を持たないstaticな変数を置く領域(bss領域、詳しくは下)  
.rodata: 定数が置かれている領域  
.stack: スタック領域  

##### データを配置する  
.int  
.long  
.short  
.double  
.float  
見たままの意味(配置されるデータ型を示す)  

##### 文字列を配置する  
.ascii: NULL終端なし文字列  
.asciz: NULL終端あり文字列  
.string: .ascizの別名?  

##### その他
.align: アライメントをいい感じにする    
.globl: シンボルをリンカから見えるようにする    
.global: 上と同じ意味  

C言語の関数は分割コンパイル時に他のソースファイルをコンパイルした実行ファイルからでも呼び出せる必要がある。  
そういったときにリンカがどのC言語の関数の関数とアセンブラ上のシンボルが対応するのか分かっていないといけないので、  
コンパイル後のオブジェクトファイルにそのようなシンボルの情報を出力する必要がある。  
.globl指定されたシンボルはオブジェクトにシンボル情報が出力されるようになる。  
C言語で定義されている関数は(static指定されていないものは)基本的に全て`.globl`指定されるものとして考えてよい...はず  

### Intel記法
今回は使わないが、ネット上にはIntel記法を使ったサンプルコードなどもよくあるので一応紹介しておく。  
`opcode dest-register src-register`の並び。  

上で例に挙げた何もしないCプログラムをIntel記法でコンパイルしてみる。
```s
	.file	"nop.c"
	.intel_syntax noprefix
	.text
	.globl	main
	.type	main, @function
main:
	push	rbp
	mov	rbp, rsp
	mov	eax, 0
	pop	rbp
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```

基本はAT&T記法と同じだが、いろいろなところで違いがあるのが分かると思う。

`;`でコメント。  
即値は普通に数字をそのまま使う。  
レジスタもレジスタ名をそのまま使う。  
間接参照は`[]`を使う。  
  
#### 主なディレクティブ
gasのディレクティブは`.`で始まるが、nasmのディレクティブは特にそういうことは無く普通に英語を使う  

section: そのままの意味  
global: gasと同じ  
db: data byte の略で 1byte のデータ  
dw: data word の略で 2byte のデータ  
dd: data double word の略で 4byte のデータ  

ワードとは基本的にCPUが一度に処理できるデータ長(つまり汎用レジスタのサイズ)のことを指すが、  
x86系CPUでは16bit時代の名残からワード=2byte, ダブルワード=4byteの意味で使うことが多い。  

### 主なx86_64の命令
基本的なx86_64の命令を紹介する。  
実際の命令は、各命令にオペランドのサイズを示すサフィックスがついたものになる。  
例えば、`mov`はデータのコピーを行う命令だが、コピーするデータのサイズに応じて、  
`movb`(8bit)、`movw`(16bit)、`movl`(32bit)、`movq`(64bit)等の種類がある。  

#### データ移動系
データの移動を行う  
`mov`: `src`の値を`dest`にコピーする。`src`と`dest`のデータサイズが同じである必要がある。  
`movzx`: `src`の値を`dest`にコピーする。`src`のデータサイズが`dest`より小さい場合に空きビットを0埋めする。  
`movsx`: `src`の値を`dest`にコピーする。`src`のデータサイズが`dest`より小さい場合に空きビットを`src`の符号で埋めする。  
`xchg`: `src`の値と`dest`の値を交換する。  

#### 算術系
計算を行う。整数と浮動少数点数では使用する命令が異なる。
`add`: `src`の値と`dest`の値の和を`dest`に書き込む。桁上りは無視される。  
`adc`: `src`の値と`dest`の値の和を`dest`に書き込む。桁上りがあった場合にはCF(キャリーフラグ)に1がセットされる。  
`sub`: `src`の値と`dest`の値の差を`dest`に書き込む。  
`mul`: `src`の値と`rax`の値を積を`rdx`と`rax`に書き込む(符号無し)。掛け算の場合は演算結果が最長でオペランドの2倍のbit長になるのでこうなっている。  
`imul`: `src`の値と`rax`の値を積を`rdx`と`rax`に書き込む(符号あり)。  
`div`:  
`idiv`:  
`neg`: オペランドの符号を反転する。
`inc`: オペランドをインクリメントする。32bit時代は`add $1, src`より速かったが64bit化で遅くなり今ではほぼ使わない...らしい
`dec`: オペランドをデクリメントする。上に同じ。

`lea`: `src`の実行アドレスを計算し、`dest`に書き込む。(Load Effective Address の略)  
      例えば、`rbx`レジスタの値が`1000`であるとき、`lea $4(%rbx), %rax`を実行すると、`rax`レジスタに`1004`が書き込まれる。  
      ぶっちゃけ足し算でよくね？(上の例では`mov %rbx, %rax (LF) add $4, %rax`と同じ結果になるので)という感じの命令だが、  
      むしろ`add`の代わりとして使われることが多いらしい。というのも`lea`はアドレスを得るための命令なので`add`と異なり   
      フラグレジスタに影響を及ぼさないからである。  

<!-- `adds`: 浮動少数点数用の加算命令。上に述べたように浮動少数点数は汎用レジスタではなくxmmレジスタという専用のレジスタで計算を行う。   -->

#### ビットシフト系
`shl`: 右ビットシフト(Shift Left)  
`shr`: 左ビットシフト(Shift Right)  
`sal`: 符号付き右ビットシフト(Shift Arithmetic Left)  
`sar`: 符号付き左ビットシフト(Shift Arithmetic Right)  

#### 無条件ジャンプ
`jmp`: オペランドのアドレスにジャンプする。  

#### 条件分岐系
`ja`: jump if above (unsigned)  
`jae`: jump if above or equal (unsigned)  
`jb`: jump if below (unsigned)  
`jbe`: jump if below or equal (unsigned)  
`jc`: jump if carry  
`jcxz`: jump if cx register is zero  
`je`: jump if equal  
`jne`: jump if not equal   
`jg`: jump if greater than (signed)  
`jge`: jump if greater than or equal (signed)  
`jl`: jump if less than (signed)  
`jle`: jump if less than or equal (signed)  
...などなど  
これらの条件分岐系の命令はオペランドとしてジャンプ先のアドレスをとる。  
比較対象もオペランドに必要では...?と思うかもしれないが、比較対象の指定は命令を事前に発行しておくことで指定する。  

例えば、`rax`と`rbx`の値が等しい場合に`LABEL`にジャンプしたいという場合、  
`sub %rbx, %rax`を発行すると、`rax`と`rbx`の値が等しい場合(= `sub %rbx, %rax`の結果が0の場合)に、  
フラグレジスタのゼロフラグが1にセットされる。  
そこで次に`je LABEL`を発行すると、CPUはゼロフラグを見て条件分岐してくれる。  
比較したいだけなのにレジスタの値が変更されてしまうのは不便なので、  
「引き算をしたフリをしてフラグレジスタを更新し、引き算の結果自体は破棄する」という命令もある。  

`cmp`: 第1オペランドと第2オペランドの引き算を行い、フラグレジスタを更新する。引き算自体の結果は破棄される。  
`test`: 第1オペランドと第2オペランドのAND演算を行い、フラグレジスタを更新する。AND演算自体の結果は破棄される。  

#### スタック操作系
スタックに値をプッシュしたりポップしたりする  
`push`: `rsp`レジスタの指すアドレスにオペランドをコピーし、`rsp`レジスタをインクリメントする(要するにスタックに値をpushする)  
`pop`: `rsp`レジスタをデクリメントし、`rsp`レジスタの指すアドレスの値をオペランドレジスタにコピーする(要するにスタックから値をpopする)  

#### 関数呼び出し系
関数を呼び出したり、関数から戻ったりする。詳しくは後述。  
`call`: 関数を呼び出す  
`ret`: 関数から戻る(関数呼び出しを行った行の次の行にジャンプする)  
`enter`: 関数に入るときにスタックフレームを確保するのに使う。遅いのであまり使わないらしい。
`leave`: 関数から出るときにスタックフレームを破棄するのに使う。

もっと知りたい人はIntelのソフトウェアマニュアルを読もう！！！

## C言語のコードとの対応
もっとC言語コードと対応するアセンブラコードを見てみよう。

### if文
```c
void iffunc(int a) {
   int b = 1;
   if (a == 0) {
      b = 2;
   } else {
      b = 3;
   }
}
```
```s
	.file	"if.c"
	.text
	.globl	iffunc
	.type	iffunc, @function
iffunc:
	pushq	%rbp
	movq	%rsp, %rbp
	movl	%edi, -20(%rbp)
	movl	$1, -4(%rbp) # b = 1
	cmpl	$0, -20(%rbp) # a - 0
	jne	.L2
	movl	$2, -4(%rbp) # b = 2
	jmp	.L4
.L2:
	movl	$3, -4(%rbp) # b = 3
.L4:
	nop
	popq	%rbp
	ret
	.size	iffunc, .-iffunc
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```

### for文
```c
void forfunc(int a) {
   int b = 0;
   for (int i = 0; i < a; i++) {
      b += 2;
   }
}
```
```s
	.file	"for.c"
	.text
	.globl	forfunc
	.type	forfunc, @function
forfunc:
	pushq	%rbp
	movq	%rsp, %rbp
	movl	%edi, -20(%rbp)
	movl	$0, -8(%rbp) # int b = 0;
	movl	$0, -4(%rbp) # int i = 0;
	jmp	.L2
.L3:
	addl	$2, -8(%rbp) # b += 2
	addl	$1, -4(%rbp) # i += 1
.L2:
	movl	-4(%rbp), %eax
	cmpl	-20(%rbp), %eax # a - i
	jl	.L3
	nop
	popq	%rbp
	ret
	.size	forfunc, .-forfunc
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```

### 関数呼び出し
基本的に関数呼び出しは戻り先が変化する特殊なジャンプ命令と考えられる。  
関数呼び出し時の引数や戻り値の受け渡しは、原理的にはどのレジスタやメモリを使ってもよいし、  
実際にC言語の仕様としてはバイナリレベルでの引数や戻り値の受け渡し方法は特に定められていない。  
しかし、実用上のことを考えると引数や戻り値の受け渡しの方法を定めておいたほうが便利である  
(さもなくば、AとBという2つのC言語コンパイラがあったときに、Aコンパイラでコンパイルした関数を  
Bコンパイラでコンパイルしたバイナリから呼び出すようなことをした際に関数が正しく実行できなくなる)  
このような関数呼び出し時の引数や戻り値の受け渡しの仕様のことを、(関数呼び出しの)ABI(Application Binary Inferface)という。  
x86-64では、LinuxやmacOSで使われているSystem V ABIというABIと、Windowsで使われているMicrosoft ABIの2つのABIがよく使われている。  

System V ABIでは、整数型の引数には第一引数からrdi, rsi, rdx, rcx, r8, r9の各レジスタを使い、第七引数以降はスタック経由で引数を渡す。
戻り値を返すにはraxレジスタを使う。

例えば次のC言語のコードを`gcc -S -fno-asynchronous-unwind-tables`コマンドでコンパイルすると次のアセンブリコードが得られる。
```c
#include<stdio.h>

long add(long a, long b) {
   return a + b;
}

int main() {
   long a = add(1, 2);
   printf("%ld\n", a);

   return 0;
}
```
```s
	.file	"func.c"
	.text
	.globl	add
	.type	add, @function
add:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	%rdi, -8(%rbp)  # ここと
	movq	%rsi, -16(%rbp) # ここで引数を取り出している
	movq	-8(%rbp), %rdx
	movq	-16(%rbp), %rax
	addq	%rdx, %rax # ここで戻り値を入れている
	popq	%rbp
	ret
	.size	add, .-add
	.section	.rodata
.LC0:
	.string	"%ld\n"
	.text
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	movl	$2, %esi # ここと
	movl	$1, %edi # ここで引数をセットしている
	call	add
	movq	%rax, -8(%rbp) # ここで戻り値を取り出している
	movq	-8(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC0(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```
これはUbuntu(WSL)上でコンパイルしたので、System V ABIに従ったやり方で引数と戻り値の受け渡しをしている。  
  
ここで、アセンブリコードを次のように書き換えて、引数の受け渡しにr8, r9レジスタを、戻り値の受け渡しにr10レジスタを使うようにしてみる。  
```s
	.file	"func.c"
	.text
	.globl	add
	.type	add, @function
add:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	%r8, -8(%rbp)
	movq	%r9, -16(%rbp)
	movq	-8(%rbp), %rdx
	movq	-16(%rbp), %r10
	addq	%rdx, %r10
	popq	%rbp
	ret
	.size	add, .-add
	.section	.rodata
.LC0:
	.string	"%ld\n"
	.text
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$32, %rsp
	movq	$1, -24(%rbp)
	movq	$2, -16(%rbp)
	movq	-16(%rbp), %rdx
	movq	-24(%rbp), %rax
	movq	%rdx, %r8
	movq	%rax, %r9
	call	add
	movq	%r10, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC0(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```
```s
	.file	"func.c"
	.text
	.globl	add
	.type	add, @function
add:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	%r8, -8(%rbp)
	movq	%r9, -16(%rbp)
	movq	-8(%rbp), %rdx
	movq	-16(%rbp), %r10
	addq	%rdx, %r10
	popq	%rbp
	ret
	.size	add, .-add
	.section	.rodata
.LC0:
	.string	"%ld\n"
	.text
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	movl	$2, %r8
	movl	$1, %r9
	call	add
	movq	%r10, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC0(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```
これでも(使っているレジスタが変わっただけなので)、同じように動作する。  
しかし、このコードを他のソースファイルからコンパイルしたコードから呼び出すとすると、  
引数や戻り値の受け渡しにr8 ~ r10のレジスタを使っているとは知らないので、正しく関数を実行できない。  
なので普通は、使っている環境に合わせたABIに従ったレジスタの使い方をするのである。

もっとたくさんの引数をとる関数をコンパイルしてみよう。
```c
void many_args_func(
   int a,
   int b,
   int c,
   int d,
   int e,
   int f,
   int g,
   int h
) {
   return;
}

int main() {
   many_args_func(1, 2, 3, 4, 5, 6, 7, 8);

   return 0;
}
```
```s
	.file	"many_args_func.c"
	.text
	.globl	many_args_func
	.type	many_args_func, @function
many_args_func:
	pushq	%rbp
	movq	%rsp, %rbp
	movl	%edi, -4(%rbp)
	movl	%esi, -8(%rbp)
	movl	%edx, -12(%rbp)
	movl	%ecx, -16(%rbp)
	movl	%r8d, -20(%rbp)
	movl	%r9d, -24(%rbp)
	nop
	popq	%rbp
	ret
	.size	many_args_func, .-many_args_func
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	pushq	$8
	pushq	$7
	movl	$6, %r9d
	movl	$5, %r8d
	movl	$4, %ecx
	movl	$3, %edx
	movl	$2, %esi
	movl	$1, %edi
	call	many_args_func
	addq	$16, %rsp
	movl	$0, %eax
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Homebrew GCC 5.5.0_4) 5.5.0"
	.section	.note.GNU-stack,"",@progbits
```
第1 ~ 6引数まではレジスタ経由で、第7引数以降はスタック経由で渡されていることが分かる。

#### スタックフレームの確保
C言語の関数をコンパイルすると、アセンブラコード上の関数の始めと終わりに次のような命令列が出力される。
```s
FUNC:
   pushq	%rbp
   movq	%rsp, %rbp
   subq	$16, %rsp
   …
   popq	%rbp
   ret
```

１つ１つ見てみると、関数の始めの命令列は
1. rbpレジスタの値をスタックにpush
2. rspレジスタの値をrbpレジスタにコピー
3. rspレジスタの値を16(この値は関数ごとに変わる)減算してrspレジスタを上書き

関数の終わりの命令列は
1. スタックから値をpopしてrbpレジスタに代入

という処理をしている。

関数内のローカル変数は基本的にスタック領域に配置される。
そこで、ローカル変数を割り当てるのに必要なバイト数だけスタックポインタ(rspレジスタ)を減算すれば、それだけのスタック領域を確保できる
(このように確保されたスタック領域のことを(関数の)スタックフレームとか、アクティベーションレコードとか言ったりする)。
確保したスタック領域には適当に変数を割り当てればよいのだが、割り当てた変数にアクセスするときにそのままでは問題がある。
スタックポインタの値はローカル変数の確保のとき以外にも式の評価を行うのに一時的な結果を保存するときなどに変更されるので、
スタックポインタからの相対アドレスではローカル変数にアクセスできない。
そこで、関数が使っているスタック領域の始点(= 関数呼び出し直後のスタックポインタの値)を保持するポインタが必要になる。
このようなポインタのことをベースポインタといい、x86-64では主にrbpレジスタがその役割に使われる。
関数呼び出しが終わって呼び出し側に戻るときには、ベースポインタを関数呼び出し前の状態に戻す必要がある。
そこで関数の始めと終わりには上のような定形の命令列が必要になるのである。

(これで分からなかったら下のリンクの解説を読んでくれ)
[https://www.sigbus.info/compilerbook/#%E3%82%B9%E3%83%86%E3%83%83%E3%83%9791%E6%96%87%E5%AD%97%E3%81%AE%E3%83%AD%E3%83%BC%E3%82%AB%E3%83%AB%E5%A4%89%E6%95%B0]

#### 関数とスタック
例えば次のようなjavascriptのコードを考えてみる。
```javascript
function getCounter(n: number): () => void {
	let count = n;
	return () => { console.log(count++) };
}

const counter = getCounter(0);
counter(); // => 1
counter(); // => 2
counter(); // => 3
```
javascriptではよくある何の変哲もないクロージャを使ったコードだが、  
これはローカル変数(`count`)をスタック領域にアロケートしていると動かない。  
なぜなら、スタック領域にアロケートされた変数は`getCounter`関数の実行が終了した時点で開放されるが、
`getCounter`の戻り値のクロージャは`count`を参照しているので、`getCounter`が終了した後も`count`は生き続けている必要がある。

このため、(クロージャが使える言語では)普通はクロージャにキャプチャされたローカル変数はスタック領域ではなくヒープ領域にアロケートする(C++のようにそうじゃない言語もある)。
例えばC#では基本的に値型の変数はスタック領域にアロケートされるが、クロージャにキャプチャされた場合は自動的に参照型にラップされてヒープ領域にアロケートされる。

### ポインタ経由での関数呼び出し
```c
#include<stdio.h>
void call(void f(void)) {
   f();
}

void hello() {
   printf("Hello\n");
}

int main() {
   call(hello);
   return 0;
}
```
```s
	.file	"fptr.c"
	.text
	.globl	call
	.type	call, @function
call:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movq	-8(%rbp), %rax
	call	*%rax
	nop
	leave
	ret
	.size	call, .-call
	.section	.rodata
.LC0:
	.string	"Hello"
	.text
	.globl	hello
	.type	hello, @function
hello:
	pushq	%rbp
	movq	%rsp, %rbp
	leaq	.LC0(%rip), %rdi
	call	puts@PLT
	nop
	popq	%rbp
	ret
	.size	hello, .-hello
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	leaq	hello(%rip), %rdi
	call	call
	movl	$0, %eax
	popq	%rbp
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```
`call`関数の引数として実行するべき関数のアドレスを渡し、引数を受け取った`call`関数は間接参照で関数を呼び出している。

#### GCCのnested functionとトランポリン
C言語の規格としては許されていないが、GCCの独自拡張として関数の中に関数を書くことができるという機能(nested function)がある。
```c
#include <stdio.h>
int main() {
   void hello() {
      printf("Hello\n");
   }

   hello();
   return 0;
}
```

さらに、この関数内関数はレキシカルスコープによる名前解決を行う(要するにクロージャとして動作する)。  
上で説明したように、C言語では変数がクロージャにキャプチャされたからといって寿命が伸びたりはしないが、
変数が生きている間は関数内関数から自由に外側のローカル変数にアクセスできる。
```c
#include <stdio.h>
int main() {
   int count = 0;
   void print_and_inc() {
      printf("count: %d\n", count);
      count++;
   }

   print_and_inc(); // count: 0
   print_and_inc(); // count: 1
   print_and_inc(); // count: 2

   return 0;
}
```
このとき、`print_and_inc`関数はどのように`count`を受け取っているのだろうか?
`count`はローカル変数なので実行時にならないとアドレスが確定しない、
つまり`print_and_inc`のコンパイル時にあらかじめ`count`のアドレスを決め打ちしておくことはできない。
したがって、`print_and_inc`関数は何らかの方法で実行時の`count`のアドレスを受け取る必要がある。
  
アセンブラを調べたところ、`print_and_inc`関数(の定義側と呼び出し側の両方)に細工がしてあり、  
暗黙の引数として`r10`レジスタ経由で`count`のアドレスを受け取っていることが分かる。
```s
	.file	"nest.c"
	.section	.rodata
.LC0:
	.string	"count: %d\n"
	.text
	.type	print_and_inc.2286, @function
print_and_inc.2286:
	pushq	%rbp
	movq	%rsp, %rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%r10, %rbx  # <- ここと
	movq	%r10, -24(%rbp) # <- ここと
	movl	(%rbx), %eax
	movl	%eax, %esi
	movl	$.LC0, %edi
	movl	$0, %eax
	call	printf
	movl	(%rbx), %eax
	addl	$1, %eax
	movl	%eax, (%rbx)
	nop
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	ret
	.size	print_and_inc.2286, .-print_and_inc.2286
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	movl	$0, %eax
	movl	%eax, -16(%rbp)
	leaq	-16(%rbp), %rax
	movq	%rax, %r10  # <- ここ
	movl	$0, %eax
	call	print_and_inc.2286
	leaq	-16(%rbp), %rax
	movq	%rax, %r10
	movl	$0, %eax
	call	print_and_inc.2286
	leaq	-16(%rbp), %rax
	movq	%rax, %r10
	movl	$0, %eax
	call	print_and_inc.2286
	movl	$0, %eax
	movq	-8(%rbp), %rdx
	xorq	%fs:40, %rdx
	je	.L4
	call	__stack_chk_fail
.L4:
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 5.4.0-6ubuntu1~16.04.11) 5.4.0 20160609"
	.section	.note.GNU-stack,"",@progbits
```
こんなことをしていいのかという感じだが、System V ABIでは関数呼び出し時に`r10`レジスタは保存しなくて良いことになっているし、
C言語のレベルではどのようなアセンブラにコンパイルされるかまでは決まっていない(上にそもそも関数内関数自体が独自拡張)なので、
GCCの開発者が好きにしてよいということになる。
また、こういうことをするには関数の定義側と呼び出し側の両方に細工を施す必要があるが、`print_and_inc`は関数内関数なので、
`print_and_inc`の定義側と呼び出し側は必ず同じコンパイル単位に入っていることが保証されるので問題ない。

ここで`print_and_inc`関数を関数ポインタ経由で実行するとどうなるだろうか?

一方で`print_and_inc`のように外側の関数のローカル変数への参照を持つ関数内関数を関数ポインタ経由で実行する場合について考えてみる。
```c
#include<stdio.h>
void callf(void (*f)(void)) {
   f();
}

int main() {
   int count = 0;
   void print_and_inc() {
      printf("count: %d\n", count);
      count++;
   }

   callf(print_and_inc);
   callf(print_and_inc);
   callf(print_and_inc);

   return 0;
}
```
`callf`関数に暗黙の引数として何らかのレジスタを経由して`count`のアドレスを渡し、  
`callf`関数から更に`print_and_inc`にアドレスを渡すということはできない。  
(今回は違うが)もしかしたら`callf`関数は既にコンパイル済みかもしれないし、逆に`callf`関数は
別のオブジェクトファイルから呼び出されるかもしれないので、特別な方法で`callf`関数をコンパイルすることはできない。

System V ABIで保存されるレジスタにアドレスを渡し、`print_and_inc`関数に入ったらそのレジスタから値を受け取ることができると思うかもしれないが、
レジスタの保存は関数呼び出しの始めと終わりでレジスタの値が同じであることを保証するものであって、関数の実行中にずっとレジスタの値が変わらないことを
保証するものではないので、不可能である(関数のはじめにレジスタの値をスタックに退避して、関数からリターンする直前にスタックから元の値をレジスタに復元するということが許される)。

では実際に上のコードをコンパイルしてみた結果を見てみよう。
```s
	.file	"nest_and_fptr.c"
	.text
	.globl	callf
	.type	callf, @function
callf:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movq	-8(%rbp), %rax
	call	*%rax
	nop
	leave
	ret
	.size	callf, .-callf
	.section	.rodata
.LC0:
	.string	"count: %d\n"
	.text
	.type	print_and_inc.2290, @function
print_and_inc.2290:
	pushq	%rbp
	movq	%rsp, %rbp
	pushq	%rbx
	subq	$24, %rsp
	movq	%r10, %rbx
	movq	%r10, -24(%rbp)
	movl	(%rbx), %eax
	movl	%eax, %esi
	movl	$.LC0, %edi
	movl	$0, %eax
	call	printf
	movl	(%rbx), %eax
	addl	$1, %eax
	movl	%eax, (%rbx)
	nop
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	ret
	.size	print_and_inc.2290, .-print_and_inc.2290
	.globl	main
	.type	main, @function
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$48, %rsp
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	leaq	-48(%rbp), %rax
	addq	$4, %rax
	leaq	-48(%rbp), %rdx
	movl	$print_and_inc.2290, %ecx
	movw	$-17599, (%rax)
	movl	%ecx, 2(%rax)
	movw	$-17847, 6(%rax)
	movq	%rdx, 8(%rax)
	movl	$-1864106167, 16(%rax)
	movl	$0, %eax
	movl	%eax, -48(%rbp) # int count = 0;
	leaq	-48(%rbp), %rax 
	addq	$4, %rax
	movq	%rax, %rdi
	call	callf
	leaq	-48(%rbp), %rax
	addq	$4, %rax
	movq	%rax, %rdi
	call	callf
	leaq	-48(%rbp), %rax
	addq	$4, %rax
	movq	%rax, %rdi
	call	callf
	movl	$0, %eax
	movq	-8(%rbp), %rsi
	xorq	%fs:40, %rsi
	je	.L5
	call	__stack_chk_fail
.L5:
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Ubuntu 5.4.0-6ubuntu1~16.04.11) 5.4.0 20160609"
	.section	.note.GNU-stack,"x",@progbits
```
`callf`関数と`print_and_inc`関数は普通にコンパイルされているのが分かる。
一方で`main`関数はよくわからない感じになっていることが分かる(無知の知)。
特に真ん中のあたりでよく分からない即値がいきなり登場し、スタック領域に放り込まれている。

```s
leaq	-48(%rbp), %rax # rbpの値(スタックの底) - 48 を rax に代入
addq	$4, %rax        # rax + 4 を rax に代入 (今の rax の値は スタックの底 - 44)
leaq	-48(%rbp), %rdx 
movl	$print_and_inc.2290, %ecx # print_and_inc関数 のアドレスをecxレジスタに代入
movw	$-17599, (%rax) # スタックの底から44バイト上のメモリに -17599 を代入
movl	%ecx, 2(%rax)   # ecxレジスタの値(print_and_inc関数へのアドレス)を スタックの底から42バイトのところに代入
movw	$-17847, 6(%rax) # スタックの底から38バイト上のメモリに -17847 を代入
movq	%rdx, 8(%rax)
movl	$-1864106167, 16(%rax) # スタックの底から 28バイト上のメモリに -1864106167 を代入
movl	$0, %eax
movl	%eax, -48(%rbp) # int count = 0;
leaq	-48(%rbp), %rax # rbpの値(スタックの底) - 48 を rax に代入
addq	$4, %rax			 # rax + 4 を rax に代入 (今の rax の値は スタックの底 - 44)
movq	%rax, %rdi		 # rax を rdi に代入
call	callf
```
とりあえず謎の即値のことは置いておいて、`callf`関数への引数を見てみよう。  
上のアセンブラをよく読むと分かるが、`callf`関数を呼び出すときの`rdi`レジスタの値は
`print_and_inc`関数のアドレスではなく`rbp - 44`という値、つまりスタック領域のアドレスになっている。

スタック領域にジャンプするとは？謎の即値の正体は？
ここでGDB上の実行に続く！
TODO: gdbでの実行
  
  
  
  
  
スタック上にジャンプするとかヤバイのではという感じだが、実はスタックに突っ込んでいた謎の即値は
x86の機械語の命令列で次の命令を表している。
- `count`のアドレスを(多分`r10`)レジスタに書き込む命令
- `print_and_inc`へ無条件ジャンプする命令
つまり、スタック上にあらかじめ機械語の命令列を用意しておいてから、`callf`関数の引数としてスタック上のアドレスを渡し、
その機械語の命令列を実行するということをしているのである(つまりC言語は動的言語だったんだよ！！！)。
こうすれば、`callf`関数に手を加えることなく`main`関数と`print_adnd_inc`関数に細工をするだけで
暗黙の引数として`count`のアドレスを渡すことができる。

このように、スタック上に別の関数へジャンプするコード片を作ってからそのコード片にジャンプすることで関数を呼び出すテクニックをトランポリンといい、
JVMでの末尾再帰最適化やUnixのシグナルハンドリングなどで使われている。
このテクニックはバッファオーバーフロー攻撃等の対策としてスタック上のデータを実行不可能にするというセキュリティ上の工夫と相反する。
また、トランポリンとは違うもののプログラムの実行中に機械語を生成してメモリ上に展開し、そこにジャンプして生成したコードを実行するという手法はインタープリター言語のJITコンパイラなどでも用いられている。


<!-- ちなみに、上のようなことができるのは関数内関数が参照している外側のローカル変数が生きているからであって、
外側のローカル変数が既に死んでいる場合は動かない。
```c
#include<stdio.h>
void (*outer(void))(void) {
   int count = 0;
   void print_and_inc() {
      printf("count: %d\n", count);
      count++;
   }
   return print_and_inc;
}

int main() {
   void (*f)(void) = outer();
   f();

   return 0;
}
```
これは次のようなコードが動かないのと同じ理由である。
```c
#include<stdio.h>
int *f() {
   int a = 1;
   return &a;
}

int main() {
   int *a = f();
   printf("%d\n", *a);

   return 0;
}
``` -->

## TIPS

### アライメント
メモリは1番地あたり1byte(8bit)のデータが格納され、1byteがアクセスの最小単位となるが、
現代の32bit/64bit CPUは、4byte/8byte単位でメモリにアクセスする。
このとき、メモリ上に適当にデータを置いていくとデータがCPUのアクセス単位をまたいで置かれることになる。

```
-1byte-
+-----+-----+-----+-----+-----+-----+-----+-----+
|char |          int          |   short   |
+-----+-----+-----+-----+-----+-----+-----+-----+
   0     1     2     3     4     5     6     7 
```
例えば上の図のようにメモリ上に変数が置かれているとすると、32bitCPUでメモリ上の2番地から5番地までの
int型の変数を読み込もうとした場合、 0 ~ 3番地へのメモリアクセス(1回目)と、4 ~ 7番地へのメモリアクセス(2回目)が必要になり、効率が悪い。
また、そもそもCPUによってはこのようなメモリアクセスができないものもある(らしい)。

そこで、次のようにメモリ上に変数が置かれている場合を考える。
```
-1byte-
+-----+-----+-----+-----+-----+-----+-----+-----+
|char |/////////////////|          int          | 
+-----+-----+-----+-----+-----+-----+-----+-----+
   0     1     2     3     4     5     6     7 
```
この場合は、int型の変数が 4 ~ 7番地に置いてあるので、1回のメモリアクセスで変数を取得できる。

このように、データの大きさに応じてメモリ上の配置を揃えることをアライメント(整列)という。
コンパイラの出力するアセンブラコードを読んでいるといきなり謎のmov命令が現れたりすることがあるが、
そういうときはデータのアライメントを整えていることが多い。

また、System V ABIでは関数をコールする前は必ずRSPが16でアラインされている(16の倍数になっている)必要がある。
割り込みが発生したときはどうするのか？と思うかもしれないが
(割り込みが発生するといきなり制御が割り込みハンドラに飛ぶので、そのときにrspがアラインされているとは限らないため)、
割り込みが発生したときは特別にCPU側で自動的にアラインしてくれるので問題無いらしい。

### gccの生成するアセンブリについて
ローカルのラベルには.Lプレフィックスが付く  
関数のはじめにはFBサフィックスが、終わりにはFEサフィックスが付く  
ブロックのはじめにはBBサフィックスが、終わりににはBEサフィックスが付く  

### 定数畳み込みの罠
C言語のコードをコンパイルして対応するアセンブリコードを調べるときに注意するべき点は、コンパイラによる定数畳み込みである。
例えば、アセンブラでの足し算の方法を調べるために次のCコードをコンパイルしたとする。

```c
void const_fold() {
   int a = 1 + 2;
}
```
```s
	.file	"const.c"
	.text
	.globl	const_fold
	.type	const_fold, @function
const_fold:
	pushq	%rbp
	movq	%rsp, %rbp
	movl	$3, -4(%rbp)
	nop
	popq	%rbp
	ret
	.size	const_fold, .-const_fold
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```
出力されたアセンブラコードを見ると足し算をしている箇所が見当たらない。
よく見ると、Cコードで足し算を行っている`int a = 1 + 2;`の行は、`movl	$3, -4(%rbp)`に置き換わっている。
これは、コンパイル時に値の分かるリテラル同士の計算についてはそのままアセンブラコードに置き換えるのではなく、
コンパイル時にあらかじめ計算を行って、その計算結果を即値としてアセンブラに埋め込むという最適化をコンパイラが行っているためである
(このような最適化技法を定数畳み込みという)。
この最適化は`gcc`では`-O0`オプションでコンパイルしても行われ、`volatile`修飾子を付けても抑制することができない。

こういうときは、オペランドを関数の引数にすると、定数畳み込みを抑止することができる(関数の引数は定数ではないので、それはそう)。
```c
void not_const_fold(int a, int b) {
   int c = a + b;
}
```
```s
	.file	"not_const.c"
	.text
	.globl	not_const_fold
	.type	not_const_fold, @function
not_const_fold:
	pushq	%rbp
	movq	%rsp, %rbp
	movl	%edi, -20(%rbp)
	movl	%esi, -24(%rbp)
	movl	-20(%rbp), %edx
	movl	-24(%rbp), %eax
	addl	%edx, %eax
	movl	%eax, -4(%rbp)
	nop
	popq	%rbp
	ret
	.size	not_const_fold, .-not_const_fold
	.ident	"GCC: (Ubuntu 7.4.0-1ubuntu1~18.04) 7.4.0"
	.section	.note.GNU-stack,"",@progbits
```

## 参考資料
GAS と NASM を比較する(IBM Developer) [https://www.ibm.com/developerworks/jp/linux/library/l-gas-nasm.html]  
x86アセンブリ言語での関数コール [https://vanya.jp.net/os/x86call/]  
低レイヤを知りたい人のためのCコンパイラ作成入門 [https://www.sigbus.info/compilerbook/]  
x64 アセンブリ言語プログラミング [http://herumi.in.coocan.jp/prog/x64.html]  
実践的低レイヤプログラミング [https://tanakamura.github.io/pllp/docs/]  
IA32（x86）汎用命令一覧  [http://softwaretechnique.jp/OS_Development/Tips/IA32_instructions.html]

### データのアラインメントについて
Ｃプログラミング専門課程 4.3 アラインメント [http://www.pro.or.jp/~fuji/mybooks/cpro/cpro.4.3.1.html]  
データ型のアラインメントとは何か，なぜ必要なのか？ [http://www5d.biglobe.ne.jp/~noocyte/Programming/Alignment.html]  
x86-64 モードのプログラミングではスタックのアライメントに気を付けよう [http://uchan.hateblo.jp/entry/2018/02/16/232029]

### GCCの関数内関数とトランポリンについて
gccの生成するトランポリンコードについて [https://yupo5656.hatenadiary.org/entry/20040602/p1]
アセンブラを混ぜてコンパイルするとスタックが実行可になってしまう話 [https://qiita.com/rarul/items/e1920e7ae5d5a28eec03]
兼雑記 2008-07-01 トランポリン [http://shinh.hatenablog.com/entry/20080701/1214845715]
なんでも継続 [http://practical-scheme.net/docs/cont-j.html]
Trampoline(computing) [https://en.wikipedia.org/wiki/Trampoline_(computing)]
