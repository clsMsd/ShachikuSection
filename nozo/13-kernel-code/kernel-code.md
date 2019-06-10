# Kernelコードの紹介

`Tag:v5.1`のものを見ていく。
https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/?h=v5.1

## リストマクロ

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/types.h?h=v5.1#n186

```c
struct list_head {
	   struct list_head *next, *prev;
	   
};
```
