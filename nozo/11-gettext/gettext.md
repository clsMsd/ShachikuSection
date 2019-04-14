# アプリケーションの翻訳ツールの紹介
アプリケーションのメッセージを他言語に対応させるためのgettextというツールについて紹介する。（特にWindowsに向けて）

## gettextとは

> ![](https://upload.wikimedia.org/wikipedia/commons/thumb/6/6b/Gettext.svg/220px-Gettext.svg.png)
> 
> [gettext - Wikipedia](https://ja.wikipedia.org/wiki/Gettext)

## MinGWでgettextをインストールする

```
$ gcc --version
gcc.exe (MinGW.org GCC-8.2.0-3) 8.2.0
Copyright (C) 2018 Free Software Foundation, Inc.
This is free software; see the source for copying conditions.  There is NO
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
```

```c
#include <stdio.h>
#include <locale.h>
#include <libintl.h>

int main() {
    setlocale(LC_ALL, "");
    bindtextdomain("test", ".");
    textdomain("test");

    puts("hello world.\n");

    return 0;
}
```

```
$ gcc main.c
c:/mingw/bin/../lib/gcc/mingw32/8.2.0/../../../../mingw32/bin/ld.exe: C:\Users\nozo\AppData\Local\Temp\cc2E72BY.o:main.c:(.text+0x1e): undefined reference to `libintl_setlocale'
c:/mingw/bin/../lib/gcc/mingw32/8.2.0/../../../../mingw32/bin/ld.exe: C:\Users\nozo\AppData\Local\Temp\cc2E72BY.o:main.c:(.text+0x32): undefined reference to `libintl_bindtextdomain'
c:/mingw/bin/../lib/gcc/mingw32/8.2.0/../../../../mingw32/bin/ld.exe: C:\Users\nozo\AppData\Local\Temp\cc2E72BY.o:main.c:(.text+0x3e): undefined reference to `libintl_textdomain'
collect2.exe: error: ld returned 1 exit status
```

[I get a linker error “undefined reference to libintl_gettext” - FAQ for GNU gettext](https://www.gnu.org/software/gettext/FAQ.html#integrating_undefined)



## 参考文献
- gettext - GNU Project - Free Software Foundation (FSF), https://www.gnu.org/software/gettext/manual/index.html
