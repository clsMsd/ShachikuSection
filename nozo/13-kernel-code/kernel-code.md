# Kernelコードの紹介

Kernelのソースコードの中のちょっとした面白い実装を紹介する。

ソースコードは`Tag:v5.1`のものを見ていく。

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/?h=v5.1

## リストの実装

kernelのリスト型データ構造の定義を紹介する。

リストのエントリは`list_head`構造体で定義される。
メンバーは`next`と`prev`で、それぞれ前と後ろのエントリへのポインタを保持する。（つまり双方向リンクとなっている）

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/types.h?h=v5.1#n186

```c
struct list_head {
	struct list_head *next, *prev;
};
```

リストへエントリを追加する関数は次のように定義される。

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/list.h?h=v5.1#n50

```c
/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_add(struct list_head *new,
			      struct list_head *prev,
			      struct list_head *next)
{
	if (!__list_add_valid(new, prev, next))
		return;

	next->prev = new;
	new->next = next;
	new->prev = prev;
	WRITE_ONCE(prev->next, new);
}

/**
 * list_add - add a new entry
 * @new: new entry to be added
 * @head: list head to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 */
static inline void list_add(struct list_head *new, struct list_head *head)
{
	__list_add(new, head, head->next);
}
```

`list_add`の第１引数`new`に新規エントリを、第２引数`head`に追加先のエントリを渡す。

`new`エントリは`head`エントリの後ろに接続される。

```
[head]<->[]
=>
[head]<->[new]<->[]
```
