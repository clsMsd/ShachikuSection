# アプリケーションの翻訳ツールの紹介
アプリケーションのメッセージを他言語に対応させるためのgettextというツールについて紹介する。

## gettextとは

> GNU gettextは、他の多くのステップを構築する資産であり、翻訳プロジェクトにとって重要なステップです。このパッケージは、プログラマー、翻訳者、そしてユーザーにたいして、統合されたツールとドキュメントを提供します。特に GNU gettextユーティリティーは、他のパッケージに多言語化されたメッセージを生成するためのフレームワークを提供するツール群です。このツールには以下のものが含まれます:
>
> - メッセージカタログをサポートするために、プログラムをどのように記述すべきかの規則。
> - メッセージカタログのディレクトリーやファイル名の命名方式。
> - 翻訳されたメッセージの取得をサポートする実行時ライブラリー。
> - 翻訳可能なメッセージや、既に翻訳されたメッセージを取り扱うための、スタンドアローンプログラム群。
> - 翻訳可能なメッセージが含まれたファイルの解析、生成をサポートするライブラリー。
> - これらのセットを準備して最新の状態に保つための、Emacs1用のスペシャルモード。
>
> [GNU gettext utilities](https://ayatakesi.github.io/gettext/0.19.8.1/gettext.html)より

gettextでは下図のようにプログラムファイルから翻訳のためのファイルを生成する。
- `.pot` : プログラムファイルから翻訳する文字列を抽出した翻訳テンプレートファイル
- `.po` : テンプレートファイルから翻訳対象国ごとに生成された翻訳ファイル
- `.mo` : プログラムから読み込める形の翻訳バイナリファイル

> ![](https://upload.wikimedia.org/wikipedia/commons/thumb/6/6b/Gettext.svg/220px-Gettext.svg.png)
> 
> [gettext - Wikipedia](https://ja.wikipedia.org/wiki/Gettext)

## gettext開発環境の構築

Windows10でgettextを利用するときはMSYS2が一番うまく行った。

- MSYS2 http://repo.msys2.org/distrib/x86_64/msys2-x86_64-20180531.exe

MSYS2で次のパッケージをインストールする。

```
$ pacman -S gcc make gettext-devel
```

## プログラム

ディレクトリ構成を以下のようにする。

```
|--hello.c
|--locale
   |--ja
      |--LC_MESSAGES
```

翻訳対象のプログラムは次のように記述する。

```c
#include <stdio.h>
#include <libintl.h>
#include <locale.h>

#define _(STRING) gettext(STRING)

int main()
{
  setlocale (LC_ALL, "");
  bindtextdomain ("hello", "./locale");
  textdomain ("hello");

  printf(_("Hello World\n"));

  return 0;
}
```

はじめに`.pot`ファイルを生成する。

```
$ xgettext --keyword=_ --language=C --add-comments --sort-output -o locale/hello.pot hello.c
```

```
$ cat locale/hello.pot
# SOME DESCRIPTIVE TITLE.
# Copyright (C) YEAR THE PACKAGE'S COPYRIGHT HOLDER
# This file is distributed under the same license as the PACKAGE package.
# FIRST AUTHOR <EMAIL@ADDRESS>, YEAR.
#
#, fuzzy
msgid ""
msgstr ""
"Project-Id-Version: PACKAGE VERSION\n"
"Report-Msgid-Bugs-To: \n"
"POT-Creation-Date: 2019-04-21 04:07+0000\n"
"PO-Revision-Date: YEAR-MO-DA HO:MI+ZONE\n"
"Last-Translator: FULL NAME <EMAIL@ADDRESS>\n"
"Language-Team: LANGUAGE <LL@li.org>\n"
"Language: \n"
"MIME-Version: 1.0\n"
"Content-Type: text/plain; charset=CHARSET\n"
"Content-Transfer-Encoding: 8bit\n"

#: hello.c:13
#, c-format
msgid "Hello World\n"
msgstr ""
```

`.pot`ファイルを編集する。

```diff
$ diff -u hello.pot.orig hello.pot
--- hello.pot.orig      2019-04-21 04:10:00.368942282 +0000
+++ hello.pot   2019-04-21 04:10:28.722640351 +0000
@@ -14,7 +14,7 @@
 "Language-Team: LANGUAGE <LL@li.org>\n"
 "Language: \n"
 "MIME-Version: 1.0\n"
-"Content-Type: text/plain; charset=CHARSET\n"
+"Content-Type: text/plain; charset=UTF-8\n"
 "Content-Transfer-Encoding: 8bit\n"
 
 #: hello.c:13
```

`.pot`から日本語を対象に`.po`を生成する。

```
$ msginit --input=locale/hello.pot --locale=ja --output=locale/ja/LC_MESSAGES/hello.po
```

```
$ cat locale/ja/LC_MESSAGES/hello.po 
# Japanese translations for PACKAGE package.
# Copyright (C) 2019 THE PACKAGE'S COPYRIGHT HOLDER
# This file is distributed under the same license as the PACKAGE package.
#  <nozo@fluorite.c.isnozo-191211.internal>, 2019.
#
msgid ""
msgstr ""
"Project-Id-Version: PACKAGE VERSION\n"
"Report-Msgid-Bugs-To: \n"
"POT-Creation-Date: 2019-04-21 04:07+0000\n"
"PO-Revision-Date: 2019-04-21 04:17+0000\n"
"Last-Translator:  <nozo@fluorite.c.isnozo-191211.internal>\n"
"Language-Team: Japanese\n"
"Language: ja\n"
"MIME-Version: 1.0\n"
"Content-Type: text/plain; charset=UTF-8\n"
"Content-Transfer-Encoding: 8bit\n"
"Plural-Forms: nplurals=1; plural=0;\n"

#: hello.c:13
#, c-format
msgid "Hello World\n"
msgstr ""
```

`.po`ファイルを編集する。

```diff
$ diff -u hello.po.orig hello.po
--- hello.po.orig       2019-04-21 04:30:39.750894167 +0000
+++ hello.po    2019-04-21 04:31:09.981770801 +0000
@@ -20,4 +20,4 @@
 #: hello.c:13
 #, c-format
 msgid "Hello World\n"
-msgstr ""
+msgstr "ハロー・ワールド\n"
```

`.po`から日本語を対象に`.mo`を生成する。

```
$ msgfmt --output-file=locale/ja/LC_MESSAGES/hello.mo locale/ja/LC_MESSAGES/hello.po
```

コンパイルして、`LANG`の設定を日本語にしたとき`.po`で翻訳したメッセージが表示される。

```
$ gcc -o hello hello.c -lintl
$ ./hello
Hello World
$ LANG=ja_JP.UTF-8 ./hello
ハロー・ワール
```

## 参考文献
- [A Quick Gettext Tutorial](http://www.labri.fr/perso/fleury/posts/programming/a-quick-gettext-tutorial.html)

- [GNU gettext utilities](https://ayatakesi.github.io/gettext/0.19.8.1/gettext.html)

