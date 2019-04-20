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