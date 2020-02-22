# GNU Makeの使い方

## はじめに
> GNU Make is a tool which controls the generation of executables and other non-source files of a program from the program's source files.  
> Make gets its knowledge of how to build your program from a file called the makefile, which lists each of the non-source files and how to compute it from other files.  
> When you write a program, you should write a makefile for it, so that it is possible to use Make to build and install the program.

make とは、プログラムのビルド作業の自動化ツールである。  
基本的にUnix環境でC/C++のプログラムをビルドする際に用いられることが多いがそれ以外に使うこともでき、  
最近ではGoのプログラムのビルドに使われたり、webpackが登場する前にJavaScriptのビルドに使われたりされていたらしい。  

もともとは1977年にベル研で作られたツールだが、GNU や BSD や他の有志により再実装されている。  
基本的な使い方は各実装で同じだが微妙な動作の違いがあるらしい(よく知らん)。  
make の実装の中では GNU make が一番広く使われている(macですらデフォルトのmakeコマンドはGNU make になっている)ので、  
今回は GNU make についてのみ扱い、以下で単に make と行った場合は GNU make のことを指すものとする。  

最近では cmake や meson や ninja といった make の代替のビルドツールが多く登場しているが、  
なんだかんだでまだ make が一番良く使われている(ほんまか？)気がするので

## Makeの必要性
C/C++ではプログラムはコンパイル->アセンブル->リンクという流れで生成されるが、

例えば、次のようなソースファイルの構成のプログラムがあったとしよう。
- main.c (プログラムのエントリーポイント)
- libA.c (main.cから呼び出しているライブラリ1)
- libB.c (main.cから呼び出しているライブラリ2)
- libA.h (libA.cのヘッダファイル)
- libB.h (libB.cのヘッダファイル)

このプログラムをコンパイルする場合、普通は次のコマンドを実行すればよい。  
```bash
$ gcc main.c libA.c libB.c -o main
```

ここで、`libB.c`のコードを変更した場合のことを考えよう。  
もう一度同じコマンドを実行すれば実行ファイルを作ることができるが、`libB.c`しか変更されていないのに
他のファイルまでコンパイルをし直すのは無駄である。  

そこで各々のファイルを分割コンパイルし、各ソースに対応したオブジェクトファイルを生成してからそれらをリンクしてみよう。    
```bash
$ gcc -c main.c -o main.o
$ gcc -c libA.c -o libA.o
$ gcc -c libB.c -o libB.o
$ gcc main.o libA.o libB.o -o main
```
こうすれば、`libB.c`に変更があった場合は`libB.c`をコンパイルして新しい`libB.o`を作り、  
新しくなった`libB.o`と他のファイルをリンクすればよい。  
  
`libB.c`を更新した場合
```bash
$ gcc -c libB.c -o libB.o
$ gcc main.o libA.o libB.o -o main
```

ここで、新たに`libC.c`という内部で `libA.c` を呼び出しているライブラリを追加した場合のことを考えよう。  
この場合、`main.c` `libB.c` `libC.c` を更新した場合はそれぞれのファイルを再コンパイルするだけでよいが、  
`libA.c` を更新した場合は `libC.c` も同時に再コンパイルする必要がある。  

このような複雑な依存関係のあるソースファイルを手作業で分割コンパイルすることが大変な作業であることは想像に難くないだろう。  

## Makefileの書き方
make はデフォルトではコマンド実行時に`Makefile`または`makefile`という名前のファイルを探し、  
そのファイルに書かれた手順でプログラムをビルドしたりタスクを実行したりする。  

### ルール
基本的にMakefileは次のように`ターゲット名` `依存ファイル` `実行コマンド` を書いていく(この3要素のひとまとまりを*ルール*という)。  
ターゲット名は別に何でも良いが、基本的には実行コマンドにより生成されるファイル名を書く。  

```makefile
# シャープの後ろはコメント

# ルール
ターゲット名: 依存ファイル1 依存ファイル2 ...
	コマンド1
	コマンド2
	...
```

例:
```makefile
main: main.c
	gcc main.c -o main
```
インデントにはスペースではなくTabを使う必要がある。  

Makefileがあるディレクトリで、`make ターゲット名` を実行するとMakefileで指定したコマンドが実行される。  

例:
```makefile
# Makefile
hello: # 依存ファイルは無い
	echo hello
```
```bash
$ make hello
echo hello
hello
```

コマンドの前に`@`を付けると、その行はコマンドをエコーしないようになる。  

例:
```makefile
# Makefile
hello:
	@echo hello
```
```bash
$ make hello
hello
```

ルールは複数書くことができる。  

例:
```makefile
hello:
	@echo hello

goodbye:
	@echo goodbye
```
```bash
$ make hello
hello
$ make goodbye
goodbye
```

`make`コマンドでターゲット名の指定が省略された場合は、一番上にあるルールが実行される。  
```bash
$ make
hello
```

1つのルールに複数のターゲットを書くこともできる。
```makefile
hello bonjour konitiha:
	@echo hello
```

これは次のように書くのと同じ意味になる。
```makefile
hello:
	@echo hello

bonjour:
	@echo hello

konitiha:
	@echo hello
```

### 依存ファイル
ターゲット名と一緒に依存ファイルを書くと、make は依存ファイルのタイムスタンプを見て
コンパイルが必要かどうかを自動で判定してくれる。  

例えば、最初で述べたような `main.c` `libA.c` `libB.c` の3つのソースファイルがあったとする。  
この場合ビルドを自動化するには次のようなmakefileを書けばよい。  

```makefile
main: main.o libA.o libB.o
	gcc main.o libA.o libB.o -o main

main.o: main.c
	gcc -c main.c -o main.o

libA.o: libA.c
	gcc -c libA.c -o libA.o

libB.o: libB.c
	gcc -c libB.c -o libB.o
```

この状態で `make main` を実行すると、まず `make` は `main` というファイルがあるかどうかを調べる。  
ファイルが存在しない場合は main のルールに書かれたコマンドを実行しようとするが、その前に依存ファイルである `main.o` `libA.o` `libB.o` が存在するかどうかを調べる。  
依存ファイルが存在しない場合は、各依存ファイルを生成するために先に依存ファイルと同名のターゲットのコマンドを実行するので、  
この場合は main.o, libA.o, libB.o に書かれたコマンドが実行され、各依存ファイルが生成されてから main のコマンドが実行される。  

```bash
$ make main
gcc -c main.c -o main.o
gcc -c libA.c -o libA.o
gcc -c libB.c -o libB.o
gcc main.o libA.o libB.o -o main
```

この状態でもう1度 `make main`を実行してみよう。  
この場合、既に `main` というファイルが存在しており、`main` は各依存ファイルよりも後に更新されていて、  
さらに各依存ファイルのソースファイルも更新されていないので何も起こらない。  

```bash
$ make main
make: 'main' is up to date.
```

ここで、`libB.c` を更新してから `make main` を実行してみよう。  
この場合、まず make は main の依存ファイルに更新が必要かどうかを調べる。  
ここで main の依存ファイルを見てみると、`main.o` と `libA.o` はタイムスタンプが `ターゲット > 依存ファイル` の順番になっているが、  
`libB.o` は `ターゲット < 依存ファイル` の順番になっている (`libB.c`を更新したので) ので、
make は `libB.o` のコマンドを実行してから `main` のコマンドを実行する。  

```bash
$ make main
gcc -c libB.c -o libB.o
gcc main.o libA.o libB.o -o main
```

### フォニーターゲット
make はビルドの自動化だけでなくタスクランナーとしても良くつかわれる。  

例えばMakefileに次のように書いておいたとする。  
```makefile
clean:
	rm main *.o
```
こうすると`make clean`コマンドを実行すればコンパイル時に生成したファイルを削除するすることができる。  

一方でこのようにタスクランナーとして make を使う場合少し困ったことがある。  
make ではターゲット名と同名のファイルが存在する(かつ依存ファイルが存在しない)場合、
そのルールのコマンドは実行されないので、`clean`という名前のファイルが存在すると`make clean`は実行されなくなってしまう。  
cleanなんて名前のファイルを作ることはあまり無いかもしれないが、例えば`test`という名前のディレクトリにテストを入れておいて
`make test`でテストを実行したい、などということはよくあるだろう。  

このようにタスク名としてターゲット名を使う場合、タスク名をフォニーターゲットに指定しておくとよい。  
フォニーターゲットとは疑似ターゲットという意味(phony=偽の)で、これを指定されたターゲットは
同名のファイルがあっても無くても関係なしにコマンドを実行してくれるようになる。  

```makefile
clean:
	rm main *.o

# clean をフォニーターゲットに指定する
.PHONY: clean
```

### 変数
makefile中で変数を利用することもできる。  
`変数名 := 値` で変数を宣言し、`$(変数名)`または`${変数名}`で変数を参照する。  

```makefile
NAME := shirasawa

hello:
	echo "hello, $(NAME)"
```
```bash
$ make hello
echo "hello, shirasawa"
hello, shirasawa
```

変数に代入した値は全て文字列として展開される。
```makefile
A := 1 + 2
a:
	@echo $(A)
```
```bash
$ make a
1 + 1
```

他によく使う便利な機能として、変数を展開する際に値の一部を置換することができる。  
```makefile
SRCS := main.c lib.c
OBJS := $(SRCS:%.c=%.o)

foo:
	@echo $(OBJS)
```
```bash
$ make
main.o lib.o
```

### いろいろなルール

#### 暗黙のルール
上に書いたMakefileでは、各オブジェクトファイルをターゲットとしてルールを書き、それらの依存ファイルとしてソースファイルを指定していた。  
しかし、C言語を使う場合は普通は `.c`ファイルから同名の`.o`ファイルを生成することを前提とすることが多いのでそのようなルールをわざわざ書くのは無駄である。  

そこで make には暗黙のルールというものがあり、`hoge.o`というターゲットは

```makefile
main: main.o libA.o libB.o
	gcc main.o libA.o libB.o -o main
```
こう書くだけで、`main.o` `libA.o` `libB.o` が存在しない場合は  
`main.c` `libA.c` `libB.c` を探してコンパイルしてくれる。   

#### 暗黙のルールで使用される変数
暗黙のルールで勝手にコンパイルしてくれるのは便利なのだが、これではコンパイルオプション等を指定することができない。  
そこで、暗黙のルールでコンパイルを行う際にコンパイラやコンパイルオプションを指定するために次のような変数が用意されている。  

- CC: .cファイルのコンパイルコマンド。デフォルトでは`cc`
- CXX: .cppファイルのコンパイルコマンド。デフォルトでは`g++`
- CFLAGS: .cファイルのコンパイル時のオプション。 
- CXXFLAGS: .cppファイルのコンパイル時のオプション。
- CPPFLAGS: .c/.cppファイルのプリプロセス時のオプション。

例えば `hoge.o` というターゲットは、
`hoge.c`というファイルがあった場合は`$(CC) -c $(CPPFLAGS) $(CFLAGS) hoge.c`で、
`hoge.cpp`というファイルがあった場合は`$(CXX) -c $(CPPFLAGS) $(CXXFLAGS) hoge.cpp`で生成される。    
(`hoge.c`と`hoge.cpp`の両方があった場合は`hoge.c`が優先される)

例えばCコンパイラとしてgccではなくclangを使いたい場合は、`CC = clang` と定義しておけばよいということになる。  

#### パターンルール
```makefile
PROG = main
CC = gcc
CFLAGS = -o2 -g -Wall
SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)

$(PROG): $(OBJS)
	$(cc) $(CFLAGS) $(OBJS) -o $(PROG) 

clean:
	rm $(PROG) $(OBJS)

.PHONY: clean
```

## 参考資料
[http://quruli.ivory.ne.jp/document/make_3.79.1/make-jp_toc.html]
