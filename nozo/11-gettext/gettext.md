# アプリケーションの翻訳ツールの紹介
アプリケーションのメッセージを他言語に対応させるためのgettextというツールについて紹介する。

## gettextとは

> ![](https://upload.wikimedia.org/wikipedia/commons/thumb/6/6b/Gettext.svg/220px-Gettext.svg.png)
> 
> [gettext - Wikipedia](https://ja.wikipedia.org/wiki/Gettext)

## gettextの利用

MinGWでは`mingw-developer-toolkit-bin`パッケージにgettextが含まれている。

```c
#include <stdio.h>
#include <locale.h>
#include <libintl.h>

#define _(String) gettext (String)

int main() {
    setlocale(LC_ALL, "");
    bindtextdomain("test", ".");
    textdomain("test");

    printf(_("hello world.\n"));

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
- gettext - GNU Project - Free Software Foundation (FSF), https://www.gnu.org/software/gettext/manual/index.html
