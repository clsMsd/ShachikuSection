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

```c
#include <stdio.h>
#include <libintl.h>
#include <locale.h>

#define _(STRING) gettext(STRING)

int main()
{
  setlocale (LC_ALL, "");
  bindtextdomain ("hello", ".");
  textdomain ("hello");

  printf(_("Hello World\n"));

  return 0;
}
```

```
$ gcc -o test main.c -lintl
$ ./test.exe
hello world.
```

`pot`ファイルの作成。

```
$ xgettext -o messages.pot --keyword=_ main.c
```

`messags.pot`

```
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
"POT-Creation-Date: 2019-04-14 18:01+0900\n"
"PO-Revision-Date: YEAR-MO-DA HO:MI+ZONE\n"
"Last-Translator: FULL NAME <EMAIL@ADDRESS>\n"
"Language-Team: LANGUAGE <LL@li.org>\n"
"Language: \n"
"MIME-Version: 1.0\n"
"Content-Type: text/plain; charset=CHARSET\n"
"Content-Transfer-Encoding: 8bit\n"

#: main.c:12
#, c-format
msgid "hello world.\n"
msgstr ""
```

## 参考文献
- [A Quick Gettext Tutorial](http://www.labri.fr/perso/fleury/posts/programming/a-quick-gettext-tutorial.html)

- [GNU gettext utilities](https://ayatakesi.github.io/gettext/0.19.8.1/gettext.html)

