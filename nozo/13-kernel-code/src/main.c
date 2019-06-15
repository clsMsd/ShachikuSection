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
