#include <linux/module.h>
#include <linux/init.h>

MODULE_LICENSE("Dual BSD/GPL");

static int ioremap_test_init(void)
{
  printk("ioremap_test is loaded.\n");
  return 0;
}
module_init(ioremap_test_init);

static void ioremap_test_exit(void)
{
  printk("ioremap_test is unloaded.\n");
}
module_exit(ioremap_test_exit);
