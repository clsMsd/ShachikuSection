# Kernelコードの紹介

kernelのリスト型データ構造の定義を紹介する。
ソースコードは`Tag:v5.1`のものを見ていく。

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/?h=v5.1

## リストの定義

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

## サンプルコード

実際にリストを利用するカーネルモジュールの例を以下に示す。

```c
#include <linux/init.h>
#include <linux/module.h>
#include <linux/slab.h>

MODULE_LICENSE("Dual BSD/GPL");

struct sample_data {
  int id;
  char *name;
  struct list_head list;	/* list_headをメンバーに持たせる */
};

struct list_head root;

void add_data(int id)
{
  struct sample_data *new;

  new = kmalloc(sizeof(struct sample_data), GFP_KERNEL);
  if (new) {
    new->id = id;
    list_add(&new->list, &root); /* 新しいエントリを追加 */
  }
}

void show_data(void)
{
  struct list_head *listptr;
  struct sample_data *entry;

  printk("===\n");
  printk("\t\t(root %p, next %p, prev %p)\n", &root, root.next, root.prev);
  
  list_for_each(listptr, &root) {
    entry = list_entry(listptr, struct sample_data, list);
    
    printk("id=%d\t(list %p, next %p, prev %p)\n",
	   entry->id, &entry->list, entry->list.next, entry->list.prev);
  }
}

void free_data(void)
{
  struct list_head *listptr;
  struct sample_data *entry;

  list_for_each(listptr, &root) {
    entry = list_entry(listptr, struct sample_data, list);

    printk("Free id=%d (list %p, next %p, prev %p)\n",
	   entry->id, &entry->list, entry->list.next, entry->list.prev);

    kfree(entry);
  }
}

static int sample_init(void)
{
  printk(KERN_ALERT "sample driver installed.\n");

  INIT_LIST_HEAD(&root);	/* リストの初期化 */
  show_data();
  
  add_data(100);
  show_data();

  add_data(110);
  show_data();
    
  add_data(120);
  show_data();
  
  return 0;
}

static void sample_exit(void)
{
  free_data();
  
  printk(KERN_ALERT "sample driver removed.\n");
}

module_init(sample_init);
module_exit(sample_exit);
```

上のカーネルモジュールをロード・アンロードすると次のような結果となる。

```
$ ls
main.c  Makefile
$ make
$ sudo insmod ./sample.ko
$ dmesg
...
[ 3269.730506] sample driver installed.
[ 3269.730507] ===
[ 3269.730509] 		(root 00000000bda3dbd2, next 00000000bda3dbd2, prev 00000000bda3dbd2)
[ 3269.730510] ===
[ 3269.730511] 		(root 00000000bda3dbd2, next 000000004bb6a517, prev 000000004bb6a517)
[ 3269.730512] id=100	(list 000000004bb6a517, next 00000000bda3dbd2, prev 00000000bda3dbd2)
[ 3269.730512] ===
[ 3269.730512] 		(root 00000000bda3dbd2, next 00000000db485738, prev 000000004bb6a517)
[ 3269.730513] id=110	(list 00000000db485738, next 000000004bb6a517, prev 00000000bda3dbd2)
[ 3269.730514] id=100	(list 000000004bb6a517, next 00000000bda3dbd2, prev 00000000db485738)
[ 3269.730514] ===
[ 3269.730515] 		(root 00000000bda3dbd2, next 00000000d2de6847, prev 000000004bb6a517)
[ 3269.730516] id=120	(list 00000000d2de6847, next 00000000db485738, prev 00000000bda3dbd2)
[ 3269.730517] id=110	(list 00000000db485738, next 000000004bb6a517, prev 00000000d2de6847)
[ 3269.730518] id=100	(list 000000004bb6a517, next 00000000bda3dbd2, prev 00000000db485738)
$ sudo rmmod sample
...
[ 3316.205340] Free id=120 (list 00000000d2de6847, next 00000000db485738, prev 00000000bda3dbd2)
[ 3316.205342] Free id=110 (list 00000000db485738, next 000000004bb6a517, prev 00000000d2de6847)
[ 3316.205342] Free id=100 (list 000000004bb6a517, next 00000000bda3dbd2, prev 00000000db485738)
[ 3316.205343] sample driver removed.
```

## リストのマクロ定義

リストの先頭から各エントリをたどるマクロは次のように定義される。

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/list.h?h=v5.1#n484

```c
/**
 * list_for_each	-	iterate over a list
 * @pos:	the &struct list_head to use as a loop cursor.
 * @head:	the head for your list.
 */
#define list_for_each(pos, head) \
	for (pos = (head)->next; pos != (head); pos = pos->next)
```

また、`list_head`型をメンバーに持つ構造体の先頭アドレスを取得するマクロは次のように定義される。

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/list.h?h=v5.1#n423

```c
/**
 * list_entry - get the struct for this entry
 * @ptr:	the &struct list_head pointer.
 * @type:	the type of the struct this is embedded in.
 * @member:	the name of the list_head within the struct.
 */
#define list_entry(ptr, type, member) \
	container_of(ptr, type, member)
```

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/kernel.h?h=v5.1#n970

```c
/**
 * container_of - cast a member of a structure out to the containing structure
 * @ptr:	the pointer to the member.
 * @type:	the type of the container struct this is embedded in.
 * @member:	the name of the member within the struct.
 *
 */
#define container_of(ptr, type, member) ({				\
	void *__mptr = (void *)(ptr);					\
	BUILD_BUG_ON_MSG(!__same_type(*(ptr), ((type *)0)->member) &&	\
			 !__same_type(*(ptr), void),			\
			 "pointer type mismatch in container_of()");	\
	((type *)(__mptr - offsetof(type, member))); })
```

例えば、`entry = list_entry(listptr, struct sample_data, list)`は次のように展開される。

```c
entry = ({
void *__mptr = (void *)(listptr);
BUILD_BUG_ON_MSG(!__same_type(*(listptr), ((struct sample_data *)0)->list) &&
		 !__same_type(*(listptr), void),
		 "pointer struct sample_data mismatch in container_of()");
((struct sample_data *)(__mptr - offsetof(struct sample_data, list)));
})
```

これは下図のように、`sample_data`構造体が持つ`list_head`メンバーのポインターからそのメンバーのオフセットを差し引いて`sample_data`構造体の先頭アドレスを算出している。

```
     struct sample_data
+--------------------------+
|          int id          | <- __mptr - offsetof(struct sample_data, list)
+--------------------------+
|        char *name        |
+--------------------------+
|  struct list_head list   | <- __mptr
+--------------------------+
```

# 参考文献
- Linuxデバイスドライバプログラミング,平田豊著
