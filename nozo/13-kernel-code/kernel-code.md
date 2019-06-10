# Kernelコードの紹介

`Tag:v5.1`のものを見ていく。
https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/?h=v5.1

## リストの実装

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/types.h?h=v5.1#n186

```c
struct list_head {
       struct list_head *next, *prev;
};
```

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/list.h?h=v5.1#n83

```c
/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
static inline void list_add_tail(struct list_head *new, struct list_head *head)
{
	__list_add(new, head->prev, head);
}
```

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
```